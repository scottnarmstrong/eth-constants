# Changes from the upstream source

Upstream: `anthropics/formal-math`, directory `eth`, commit
`16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.

This repository includes the upstream Lean development and paper under their
Apache 2.0 license. It makes no claim of an error in the upstream paper.

## Parameter changes: 31 existing proof files

The minimum admissible starting exponent is lowered from 18 to 16, and the
associated numerical estimates and interfaces are strengthened accordingly.
The definitions of the recursive schedule and exponent recurrence are preserved.
The function choosing the initial parameter now uses
`max 16 (Nat.clog 2 (c+5))`. Modified files carry a modification notice.

- [`proof/maintheorem/CountedRoute/Defs.lean`](../proof/maintheorem/CountedRoute/Defs.lean)
- [`proof/rates/ClauseBound/Gen/PartA.lean`](../proof/rates/ClauseBound/Gen/PartA.lean)
- [`proof/rates/ClauseBound/Gen/Rate.lean`](../proof/rates/ClauseBound/Gen/Rate.lean)
- [`proof/rates/ClauseBound/Gen/Seq.lean`](../proof/rates/ClauseBound/Gen/Seq.lean)
- [`proof/rates/CountedRecursion/CallParts.lean`](../proof/rates/CountedRecursion/CallParts.lean)
- [`proof/rates/CountedRecursion/EndBounds.lean`](../proof/rates/CountedRecursion/EndBounds.lean)
- [`proof/rates/CountedRecursion/LabelCrude.lean`](../proof/rates/CountedRecursion/LabelCrude.lean)
- [`proof/rates/CountedRecursion/RecursionDefs.lean`](../proof/rates/CountedRecursion/RecursionDefs.lean)
- [`proof/rates/GeneralPieces/Defs.lean`](../proof/rates/GeneralPieces/Defs.lean)
- [`proof/rates/GeneralPieces/Num/Asymptotic.lean`](../proof/rates/GeneralPieces/Num/Asymptotic.lean)
- [`proof/rates/GeneralPieces/Num/PartA.lean`](../proof/rates/GeneralPieces/Num/PartA.lean)
- [`proof/rates/GeneralPieces/Num/PartAUse.lean`](../proof/rates/GeneralPieces/Num/PartAUse.lean)
- [`proof/rates/GeneralPieces/Num/TopDisplay.lean`](../proof/rates/GeneralPieces/Num/TopDisplay.lean)
- [`proof/rates/GeneralPieces/Rec/Chain.lean`](../proof/rates/GeneralPieces/Rec/Chain.lean)
- [`proof/rates/GeneralPieces/Rec/PartB.lean`](../proof/rates/GeneralPieces/Rec/PartB.lean)
- [`proof/rates/GeneralPieces/Rec/Rate.lean`](../proof/rates/GeneralPieces/Rec/Rate.lean)
- [`proof/rates/GeneralPieces/Rec/Seq.lean`](../proof/rates/GeneralPieces/Rec/Seq.lean)
- [`proof/rates/GeneralPieces/ThmRunningTime.lean`](../proof/rates/GeneralPieces/ThmRunningTime.lean)
- [`proof/rates/GeneralPieces/Tied/BoundDefs.lean`](../proof/rates/GeneralPieces/Tied/BoundDefs.lean)
- [`proof/rates/GeneralPieces/Tied/Defs.lean`](../proof/rates/GeneralPieces/Tied/Defs.lean)
- [`proof/rates/OccurM/TiedDefs.lean`](../proof/rates/OccurM/TiedDefs.lean)
- [`proof/statements/AppRunningTimeStatement.lean`](../proof/statements/AppRunningTimeStatement.lean)
- [`proof/statements/ClausesOccurStatement.lean`](../proof/statements/ClausesOccurStatement.lean)
- [`proof/statements/CountedInstanceStatement.lean`](../proof/statements/CountedInstanceStatement.lean)
- [`proof/statements/LevelsStatement.lean`](../proof/statements/LevelsStatement.lean)
- [`proof/statements/VariablesFixedWidthStatement.lean`](../proof/statements/VariablesFixedWidthStatement.lean)
- [`proof/variables/CountedInstance/Main.lean`](../proof/variables/CountedInstance/Main.lean)
- [`proof/variables/FixedWidthSteps/RouteDefs.lean`](../proof/variables/FixedWidthSteps/RouteDefs.lean)
- [`proof/variables/PairsToBound/Defs.lean`](../proof/variables/PairsToBound/Defs.lean)
- [`proof/variables/PairsToBound/Pairs.lean`](../proof/variables/PairsToBound/Pairs.lean)
- [`proof/variables/RecursionWithPieces/Master.lean`](../proof/variables/RecursionWithPieces/Master.lean)

## Mark bound: 8 existing proof files

The budget function `UbD` of the variable route charges the marks of the
parity checks through `markD`, which uses at most `9n` marks when the
occurrence bound is at least `2^15` and the upstream `14n` otherwise. The new
estimate is `VariableBound.Ineq.large_nine`. The program's counting steps are
unchanged; its budget and the plan guard that uses it change, and the upstream
theorems are re-proved for the revised budget. Modified files carry a
modification notice.

- [`proof/variables/RecursionToBound/Numbers.lean`](../proof/variables/RecursionToBound/Numbers.lean)
- [`proof/variables/VariableBound/Count/Correct.lean`](../proof/variables/VariableBound/Count/Correct.lean)
- [`proof/variables/VariableBound/Net/CertEv.lean`](../proof/variables/VariableBound/Net/CertEv.lean)
- [`proof/variables/VariableBound/Net/Defs.lean`](../proof/variables/VariableBound/Net/Defs.lean)
- [`proof/variables/VariableBound/Net/Fit.lean`](../proof/variables/VariableBound/Net/Fit.lean)
- [`proof/variables/VariableBound/Net/Main.lean`](../proof/variables/VariableBound/Net/Main.lean)
- [`proof/variables/VariableBound/Params/Defs.lean`](../proof/variables/VariableBound/Params/Defs.lean)
- [`proof/variables/VariableBound/Params/Ineq.lean`](../proof/variables/VariableBound/Params/Ineq.lean)

## Additions

The twelve modules in `Constants/` contain the strengthened estimates, explicit
instantiations, and the modified SAT program. The precision rule of this program
differs from the upstream rule; its correctness and fallback behavior are
proved for the named program. These are new results, not transcriptions of
claims from the upstream paper.

## Preserved statements and dependencies

`MainResults.lean`, `Solution.lean`, `Challenge.lean`, `comparator.json`,
`lean-toolchain`, `lake-manifest.json`, `LICENSE`, and `paper.pdf` are byte-for-byte
unchanged. Their SHA-256 hashes are recorded in [`upstream.json`](upstream.json) and
checked by `scripts/verify.py`. That metadata also records the modified proof-file
list above.

`lakefile.toml` adds the `ETHConstants` library and makes the original Solution
and the constants library the default build targets. The two placeholder
Challenge theorems remain available for the upstream Comparator configuration.
The upstream copyright and license notices are preserved.
