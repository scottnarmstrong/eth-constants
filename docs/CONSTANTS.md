# Constants and the certified cutoff

The cutoff theorem follows the actual `planD` and `planM` branch guards in the
merged counting program. It concerns full-assignment exhaustive counting, not
the absence of every exponential subroutine inside the recursion.

## Numerical parameters

| Parameter | Certified value |
|---|---:|
| Geometric contraction rate | `1 / sqrt(2)` |
| Minimum starting exponent | 16, reduced from 18 |
| Piece-program constants | `(2, 95)` |
| Padded piece constant | 190 |
| Padded recursion overhead coefficient | `6*190+17 = 1157` |
| Sufficient selected level | 28 |
| Logarithm to base two of the level-28 clique size | 14,495,514,418 |
| Exact level threshold in variables | `2^246423745106` |
| Rounded sufficient threshold in variables | `10^75000000000` |

The level schedule is unchanged apart from its starting parameter. The new
precision rule is

$$
s(\ell)=\max\{4,\lfloor\ell/2\rfloor-12\}.
$$

`ETHConstants.SAT.precisionProgram`, in `Constants/SATNumerics.lean`, is a
concrete polynomial-time program for this rule. The proof
keeps the sparsification exponent separate from the clique-recursion exponent.
For every selected level at least 32 it bounds the complete variable-route
padding exponent by

$$
\frac{\mathrm{needD}}{n}
\le [420(24s+103)+1]e_\ell+2^{-s}\lt 1.
$$

For levels 28 through 31, `s=4` and `betaU 3 4=198`. Retaining the exact
network logarithm gives

$$
\lceil\log_2(96\cdot 2^{198}\cdot199)\rceil=213,
$$

and, for `n >= 199`,

$$
U=18(n+199)+84n\cdot213+18K^{16}
\le17928n+18K^{16}.
$$

`SATNeed.ubD_precision_four_le` proves this inequality. The generalized helper
`SATNeed.needD_le_of_ub` propagates it to the complete budget estimate

$$
\frac{\mathrm{needD}}n\le17929e_\ell+\frac1{16}<1.
$$

At level 28, the proved recurrence estimate gives the rational upper bound
`135743/163840`, approximately 0.82851. The earlier estimate remains in use
from level 32 onward, where the precision eventually increases. All three
plan feasibility conditions are checked. The merged program uses an exponent
no larger than that of the variable route. If it selects the clause route,
that route's plan must therefore also exist.

The numerical witness 1157 is extracted from the constructive upstream proof
by `WitnessExtraction`. The resulting proof term is checked by Lean’s kernel;
it adds no axiom or evaluation oracle.

## Other quantitative results

- `SharperPartitions` proves, for every integer `E ≥ 1`,
  `p(E) ≥ exp(-3) * E^(-16) * exp(pi*sqrt(2*E/3))`.
- `PartitionEncoding` proves that subsets of `{2,...,lambda+1}` inject into
  partitions of `2*lambda^2`. Consequently the partition weight required by
  the factorization is at most `2*lambda^2`.
- `ExplicitPieces` propagates these estimates through the existing piece
  programs and tensor identities, obtaining the explicit constants above.
- `SharperSchedule` proves `K_(l+1) ≤ K_l^4`; equality at the first step makes
  the uniform exponent four optimal for this schedule.
- `ExplicitRecursion` and `FiniteBound` give a separate counted-query clique
  theorem with overhead coefficient 61515 and a finite bound at `K=2^64`,
  `lambda=B=2^27`. This is a different cost interface from the padded
  coefficient 1157 used for the SAT fallback theorem.

## Limits and further improvements

This result has no clause-density hypothesis. It uses the standard upstream
validity condition of width at most three and a duplicate-free clause list.
It neither requires every variable to occur nor excludes unsatisfiable inputs.

The threshold remains far beyond feasible input sizes. The padding exponent
being below `n` does not show that the resulting Turing machine runs faster
than brute force: a polynomial simulation raises the padded cost to a power,
and that degree and its constants are not explicit here.

At level 27 the improved budget expression still exceeds one, even when the
recurrence is evaluated tightly and the smallest permitted precision is used.
See [the next targets](NEXT_STEPS.md) for a quantitative assessment, including
the proposed threshold of `10^100000` variables. These are limitations of the
current estimates, not lower bounds on the program’s actual runtime.
