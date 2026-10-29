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
| Parity-check marks, for occurrence bound `Δ ≥ 2^15` | `M ≤ 9n`, reduced from `14n` |
| Recursive exponent constant | `e_l ≤ 0.66 ρ^l` for `l ≥ 1`, reduced from 0.7 |
| Sufficient selected level | 26 |
| Logarithm to base two of the level-26 clique size | 3,623,878,462 |
| Exact level threshold in variables | `2^61605933854` |
| Rounded sufficient threshold in variables | `10^18600000000` |

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

For levels 26 through 31, `s=4` and `betaU 3 4=198`. Retaining the exact
network logarithm gives

$$
\lceil\log_2(96\cdot 2^{198}\cdot199)\rceil=213.
$$

Each of the `M` marks of the parity checks costs at most 213 bits at each of
its `k=3` tests, counted at both ends. The upstream estimate `M ≤ 14n` gave the
coefficient `84·213`. For `Δ ≥ 2^15` the program's budget now uses `M ≤ 9n`
(see below), so for `n >= 199`

$$
U=18(n+199)+54n\cdot213+18K^{16}
\le11538n+18K^{16}.
$$

`SATNeed.ubD_precision_four_le` proves this inequality. The generalized helper
`SATNeed.needD_le_of_ub` propagates it to the complete budget estimate

$$
\frac{\mathrm{needD}}n\le11539e_\ell+\frac1{16}<1.
$$

`SAT.e_tight` proves `e_l ≤ 0.66 ρ^l` for `l ≥ 1`; the limit of `e_l/ρ^l` is
about 0.645. At level 26 the expression is therefore at most
`11539·0.66·2^-13 + 1/16`, approximately 0.99215. The earlier estimate remains
in use from level 32 onward, where the precision eventually increases.

## The mark bound

The program computes the parameters of Appendix D exactly: `n̄`, then
`β = n + ⌈log₂ C(m, n̄+1)⌉ + 1`, the number of checks `r̄`, and the number of
marks `M = r̄ + β − 1`. The upstream estimate of display (61), `M ≤ 14n`,
bounds `log₂(3m/(n̄+1))` by `3 log₂(2Δ)`. With `L = log₂(2Δ)` and `Δ ≥ 2^15`,
`VariableBound.Ineq.beta_le_large` uses instead

$$
\log_2\frac{3m}{\bar n+1}\le\log_2(6\Delta L)=L+\log_2(3L)\le\tfrac32L,
$$

so that `β ≤ 2.5n + 1.5L + 2`. With `r̄ ≤ 2.41β + 1` this gives `M ≤ 9n` for
`n ≥ 29L + 19` (`VariableBound.Ineq.large_nine`). The budget function charges
`2kn·markD(Δ)` bits for the marks, where

$$
\mathrm{markD}(\Delta)=\max\bigl(9\,\mathrm{lgD}(\Delta),\;14\,\mathrm{lgD}(\min(\Delta,2^{15}))\bigr),
\qquad \mathrm{lgD}(\Delta)=\lceil\log_2(96\Delta\lceil\log_2 2\Delta\rceil)\rceil.
$$

The second term keeps the budget increasing in `Δ`, which the upstream
asymptotic argument uses; for the program's `Δ = 2^198` it is inactive. All three
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

At level 25 the improved budget expression is about 1.347, even when the
recurrence is evaluated tightly and the smallest permitted precision is used.
See [the next targets](NEXT_STEPS.md) for a quantitative assessment, including
the proposed threshold of `10^100000` variables. These are limitations of the
current estimates, not lower bounds on the program’s actual runtime.
