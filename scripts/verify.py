#!/usr/bin/env python3
"""Build the release, verify provenance, and fail closed on the axiom audits."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}


def run(command, logfile):
    lines = []
    with logfile.open("w") as output:
        with subprocess.Popen(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT) as proc:
            for line in proc.stdout:
                print(line, end="", flush=True)
                output.write(line)
                lines.append(line)
            if proc.wait() != 0:
                raise RuntimeError(f"Command failed: {' '.join(command)}")
    return "".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-build", action="store_true", help="Audit an already built checkout")
    args = parser.parse_args()
    metadata = json.loads((ROOT / "docs/upstream.json").read_text())
    for name, expected in metadata["unchanged_files"].items():
        actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError(f"Upstream provenance mismatch: {name}")
    # Preserve the upstream legacy entry points byte-for-byte.
    source_files = []
    for directory in ("Constants",):
        source_files.extend((ROOT / directory).rglob("*.lean"))
    for source in source_files:
        if not re.search(r"^module\s*$", source.read_text(), re.M):
            raise RuntimeError(f"Missing module header: {source.relative_to(ROOT)}")
    # Use the repository's exact Lean options for scripts run outside Lake targets.
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    options = []
    def flatten(prefix, value):
        if isinstance(value, dict):
            for key, child in value.items():
                flatten(f"{prefix}.{key}" if prefix else key, child)
        else:
            options.append(f"-D{prefix}={str(value).lower() if isinstance(value, bool) else value}")
    flatten("", config["leanOptions"])
    logs = ROOT / ".lake/verification"
    logs.mkdir(parents=True, exist_ok=True)
    if not args.no_build:
        run(["lake", "build", "Solution", "ETHConstants"], logs / "build.log")
    expected = json.loads((ROOT / "scripts/axioms.json").read_text())
    total = 0
    for group, script in (("upstream", "PrintAxioms.lean"), ("constants", "PrintConstantsAxioms.lean")):
        output = run(["lake", "env", "lean", *options, f"scripts/{script}"], logs / f"{group}-axioms.log")
        if re.search(r"\b(?:warning|error):|sorryAx", output):
            raise RuntimeError(f"Unexpected diagnostic in {script}")
        found = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
        if len(found) != len(expected[group]) or {name for name, _ in found} != set(expected[group]):
            raise RuntimeError(f"Missing, duplicate, or unexpected axiom entries in {script}")
        for name, values in found:
            axioms = {v.strip() for v in values.split(",") if v.strip()}
            if not axioms <= PERMITTED:
                raise RuntimeError(f"Unpermitted axioms for {name}: {sorted(axioms - PERMITTED)}")
        total += len(found)
    print(f"Verified {total} theorem axiom closures and {len(metadata['unchanged_files'])} unchanged upstream files.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(f"verification failed: {error}", file=sys.stderr)
        sys.exit(1)
