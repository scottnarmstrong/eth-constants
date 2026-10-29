# Explicit constants for Anthropic’s 3-SAT algorithm

[![Build and verify](https://github.com/scottnarmstrong/eth-constants/actions/workflows/build.yml/badge.svg)](https://github.com/scottnarmstrong/eth-constants/actions/workflows/build.yml)

This is a fork of the [ETH development in `anthropics/formal-math`](https://github.com/anthropics/formal-math/tree/main/eth).
It provides Lean proofs of an explicit fallback cutoff for a modified version of
Anthropic’s counting algorithm, together with sharper partition and recursion estimates.

## Purpose

Ben Recht’s [tweet about OpenAI’s ETH algorithm](https://x.com/beenwrekt/status/2115445861006368787)
criticizes a threshold for an exponential-time subroutine quoted as
$10^{10^{25}}$ variables, calling it “infinity plus 1.” That raises a concrete
question: how much of an astronomical threshold comes from loose constants,
and how far can it be reduced without losing a checked proof?

This fork investigates that question using Anthropic’s publicly available Lean
development. The goal is to make the constants explicit, improve them, and
verify the resulting finite cutoff against the actual program’s branch guards.
The cutoff proved here has exponent $2.9\times10^{8}$, roughly 34 quadrillion
times smaller than the exponent in the quoted number.

These are different algorithms. This result does not establish that the quoted
OpenAI threshold was miscalculated, and it does not make either algorithm
practical. It gives a reproducible, formally checked measure of how much the
constants can be improved in the Anthropic construction.

## Certified result

For every valid 3-CNF formula on

$$
n \ge 10^{290,000,000}
$$

variables, the modified program **does not select its top-level exhaustive
assignment-counting fallback**. This is a sufficient upper bound on the fallback
threshold, with no clause-density assumption. It does not say that all smaller
inputs take the fallback.

The program’s counting correctness is proved for every valid input, including
below the cutoff, when supplied with its specified padding. “Valid” uses the
upstream definition: each clause has at most three literals and there are no
duplicate clauses. Duplicate clauses may be removed without changing the count.

The cutoff is still astronomical. It is not a practical runtime claim or a
certified Turing-step crossover against brute force. Recursive base cases remain.
The polynomial simulation degree and its constants have not been made explicit.

## Read the results

| Result | Lean declaration |
|---|---|
| Neither selected branch takes the exhaustive fallback above the cutoff | [`ETHConstants.SAT.no_fallback`](Constants/SATFallback.lean) |
| The merged program’s padding exponent is strictly below the variable count | [`ETHConstants.SAT.budget_lt`](Constants/SATFallback.lean) |
| The modified program counts satisfying assignments correctly | [`ETHConstants.SAT.algorithm_correct`](Constants/SATFallback.lean) |
| The program and budget computation are polynomial-time in their encoded inputs, including the pad | [`ETHConstants.SAT.algorithm_poly`](Constants/SATFallback.lean) |
| Recursive exponent bound improves from 0.85 to 0.66 times the geometric rate | [`ETHConstants.SAT.e_tight`](Constants/SATRates.lean) |
| The networks are given Calabro's occurrence bound, 2^26 instead of 2^198 at width 3 and precision 4 | [`StepSparsify.lcCal_le_betaD`](proof/sparsification/StepSparsify/CalNumbers.lean) |
| With the inclusion–exclusion cutoff n̄ about n/(32·log₂(2Δ)), the parity checks use at most 4.5n marks, not 14n | [`VariableBound.Ineq.large_half`](proof/variables/VariableBound/Params/Ineq.lean) |
| Explicit partition lower bound with power 16 | [`ETHConstants.Partition.explicit_partition_lower_bound`](Constants/SharperPartitions.lean) |
| Level growth bound improves from the tenth to the fourth power | [`ETHConstants.next_level_le_fourth_power`](Constants/SharperSchedule.lean) |

The program is `ETHConstants.SAT.algorithm`; its exponent function is
`ETHConstants.SAT.budget`. Both are defined in
[`Constants/SATFallback.lean`](Constants/SATFallback.lean).

The exact level used is 20, with

$$
K_{20}^{17}=2^{962,590,082}.
$$

The decimal cutoff is a certified upward rounding. All numerical comparisons
in the Lean proofs use exact arithmetic. See [the constants and cost bounds](docs/CONSTANTS.md)
for the derivation, and [further improvement targets](docs/NEXT_STEPS.md) for the
remaining bottlenecks. Retaining the exact network logarithm lowered the outer
exponent by a factor of 16 relative to the first release. Bounding the
parity-check marks by $9n$ instead of $14n$ lowered it by a further factor of 4.
Giving the networks the occurrence bound of the sparsification actually used,
$2^{26}$ instead of $2^{198}$, lowered it by a further factor of 32. Cutting
inclusion–exclusion off at about $n/(32\log_2 2\Delta)$ instead of
$n/\log_2 2\Delta$ marks, so that at most $4.5n$ parity-check marks are needed,
halves it again.

## Build and verify

Install [elan](https://github.com/leanprover/elan), Git, and Python 3.11 or later.
From a fresh clone:

```sh
git clone https://github.com/scottnarmstrong/eth-constants.git
cd eth-constants
lake exe cache get
LEAN_NUM_THREADS=4 python3 scripts/verify.py
```

The toolchain is pinned to Lean `v4.33.1`; Mathlib and its dependencies are pinned
in [`lake-manifest.json`](lake-manifest.json). The first build downloads the
Mathlib cache and compiles the project. Allow several gigabytes of disk space
and memory. Lower `LEAN_NUM_THREADS` on a shared or smaller machine.

The verification command builds `Solution` and `ETHConstants`, checks the
unchanged upstream statement and dependency files, and audits the axioms of
all advertised results and their principal supporting theorems. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. Failure or a missing
audit entry makes the command fail.

To build without the audits, run `lake build`. The public build workflow runs
the full verification command on pushes and pull requests.

## Upstream and scope

This GitHub fork is based on the `eth` project in
[`anthropics/formal-math`](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth),
pinned at commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
The `constants` branch places the ETH project at the repository root and is the
default branch; the fork’s `main` branch retains the upstream repository.
This is an independent extension, not an official Anthropic release.

Anthropic’s paper, [*A 2^o(n) Time Algorithm for 3-SAT*](paper.pdf), and the
underlying formalization are credited to Anthropic. The additions here are in
`Constants/`; the upstream development is in `proof/`. The original
[`MainResults.lean`](MainResults.lean) and [`Solution.lean`](Solution.lean)
are unchanged. Their ETH and counting-runtime theorems remain results of the
upstream development. This repository’s additional claims are the explicit
estimates and fallback/correctness theorems listed above. No new explicit
Turing-runtime theorem is claimed for the revised precision rule.

[Changes from the upstream source](docs/UPSTREAM.md) lists all modified proof
files and distinguishes parameter changes from the new theorems.
The retained [`comparator.json`](comparator.json) and
[`Challenge.lean`](Challenge.lean) concern only the two original upstream
headline theorems. The two intentional `sorry` declarations in `Challenge.lean`
are reference statements, are excluded from the default build, and are not
used by any proof. Comparator and NanoDa verification of the new constants is
not claimed; the provided verification uses Lean’s kernel and axiom audit.

This extension was developed by Scott Armstrong with AI assistance.

## License

Apache 2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE) for the upstream
attribution and notices. Dependencies are fetched separately under their
respective licenses.
