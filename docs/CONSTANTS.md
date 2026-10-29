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
| Occurrence bound handed to the network, width 3, precision 4 | `Δ = 2^26`, reduced from `2^198` |
| Inclusion–exclusion cutoff `n̄` | about `n/(32·log₂(2Δ))`, reduced from `n/log₂(2Δ)` |
| Parity-check marks | `M ≤ 4.5n`, reduced from `14n` |
| Recursive exponent constant | `e_l ≤ 0.66 ρ^l` for `l ≥ 1`, reduced from 0.7 |
| Sufficient selected level | 20 |
| Logarithm to base two of the level-20 clique size | 56,622,946 |
| Exact level threshold in variables | `2^962590082` |
| Rounded sufficient threshold in variables | `10^290000000` |

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

For levels 20 through 31, `s=4`, and the networks are given the occurrence
bound `Δ = 2^26` (see below). With `n̄` chosen for `scaleD Δ = 2^31·Δ^32`,
a check has fewer than `32Δ·log₂(2·scaleD Δ)` clauses, so

$$
\lceil\log_2(96\cdot 2^{26}\cdot864)\rceil=43,
$$

each of the at most `4.5n` marks of the parity checks costs at most 43 bits at
each of its `k=3` tests, counted at both ends, and for `n >= 486`

$$
U=18(n+27)+27n\cdot43+18K^{16}
\le1180n+18K^{16}.
$$

`SATNeed.ubD_precision_four_le` proves this inequality. The generalized helper
`SATNeed.needD_le_of_ub` propagates it to the complete budget estimate

$$
\frac{\mathrm{needD}}n\le1181e_\ell+\frac1{16}<1.
$$

`SAT.e_tight` proves `e_l ≤ 0.66 ρ^l` for `l ≥ 1`; the limit of `e_l/ρ^l` is
about 0.645. Since `ρ^20 = 2^-10`, the expression at level 20 is at most
`1181·0.66·2^-10 + 1/16`, approximately 0.824; with the exact recurrence it is
about 0.806. The earlier estimate remains in use from level 32 onward,
where the precision eventually increases.

## The occurrence bound

The program sparsifies with Calabro's thresholds `θ₀ = 2`, `θ_c = α·β_c`, where
for width at most three `α = 8·2^s·(s+7)`. A leaf has at most
`2(θ₀+θ₁+θ₂) = 4 + 4α + 32α²` clauses in which a variable occurs. The upstream
program handed the networks the larger bound `2^(2k(4s+17))`, which also bounds
the depth of the sparsification tree. It now hands them `2^β`, where
`β = betaD k s = ⌈log₂(32α² + 4α + 6)⌉` for `k ≤ 3` and the upstream exponent
for larger `k` (`StepSparsify.lcCal_le_betaD`). At `s = 4`, `α = 1408` and
`β = 26`. The depth bound, the stack of the walk and the plan's guard keep the
upstream exponent; `betaD ≤ betaU` (`UniformInK.ArithNat.betaD_le_betaU`) lets
the remaining estimates use either.

## The mark bound

The program computes the parameters of Appendix D exactly: `n̄`, then
`β = n + ⌈log₂ C(m, n̄+1)⌉ + 1`, the number of checks `r̄`, and the number of
marks `M = r̄ + β − 1`. Inclusion–exclusion is cut off at `n̄` marked clauses,
and `β` grows with `n̄`. The paper takes `n̄` to be the power of two with
`n/(2 log₂ 2Δ) < n̄ ≤ n/log₂ 2Δ`; the program now computes it for
`scaleD Δ = 2^31·Δ^32`, so that `n/(64 log₂ 2Δ) < n̄ ≤ n/(32 log₂ 2Δ)`. A check
then has fewer than `32Δ·log₂(2·scaleD Δ) = 1024Δ·log₂(2Δ)` clauses, which
costs 5 more bits per mark. With `L = log₂(2Δ)`,
`VariableBound.Ineq.beta_le_scaled` gives

$$
\log_2\frac{3m}{\bar n+1}\le\log_2(6\Delta\cdot32L)=L+\log_2(96L)\le5L,
\qquad \beta\le\tfrac{37}{32}n+5L+2,
$$

and with `r̄ ≤ 2.41β + 1` this gives `2M ≤ 9n` for every `Δ ≥ 2` and
`n ≥ 64L + 19` (`VariableBound.Ineq.large_half`). The plan's guard is
correspondingly `n ≥ 64·⌈log₂(2Δ)⌉ + 19`, in place of `29·⌈log₂(2Δ)⌉ + 19`,
which also makes `n̄ ≥ 2`. The budget function charges `9kn·lgD(Δ)` bits for
the marks, where `lgD(Δ) = ⌈log₂(96Δ⌈log₂(2·scaleD Δ)⌉)⌉`; it grows with `Δ`.

The lower-order estimates of the upstream proof grow with the larger checks:
for example `g·P ≤ n·2^β·(26756(β+3) + 4·size n)` in place of `842(β+3)`.
These enter only terms that are negligible beside `n` at the cutoff.

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

At level 19 the improved budget expression is about 1.114, even when the
recurrence is evaluated tightly and the smallest permitted precision is used.
See [the next targets](NEXT_STEPS.md) for a quantitative assessment, including
the proposed threshold of `10^100000` variables. These are limitations of the
current estimates, not lower bounds on the program’s actual runtime.
