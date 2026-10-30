# Further improvements and the 10^100000 target

Here the target means `n = 10^(10^5) = 10^100000` variables. It does not mean
100,000 variables. All thresholds discussed here concern avoidance of the
top-level exhaustive-counting fallback, as explained in the README.

## How the cutoff depends on the constants

At precision four the budget proof needs

$$A e_\ell + 1/16 < 1,$$

where `A` is the leading coefficient of the network size per variable and
`e_l ≈ 0.645·2^(-l/2)`. The program selects the largest level with
`K_l^17 <= n`, and `log2 K_l = 54·2^l − 6l − 38`. Since `log K_l` doubles with
each level while `e_l` falls only by `√2`, the outer exponent of the cutoff grows
like `A²`: halving `A` divides it by about four, up to integer rounding of the
level.

The leading coefficient is now `A = 710`. Almost all of it,
`2k·2.5·46 = 690`, pays for the marks of the parity checks: at most `2.5n`
marks, each charged 46 bits at each of its `k = 3` tests. Threefold XOR
amplification improves the guaranteed detection probability from `1/4` to
`7/16`, allowing fewer checks. The occurrence bound is `Δ = 2^26`, and
`scaleD Δ = 2^127·Δ^128` sets `n̄ ≈ n/(128 log₂ 2Δ)`.

## Checked improvements so far

| Step | `A` | Level | Cutoff |
|---|---:|---:|---|
| First release | 83,580 | 32 | `10^1200000000000` |
| Exact network logarithm | 17,929 | 28 | `10^75000000000` |
| At most `9n` marks when `Δ ≥ 2^15` | 11,539 | 26 | `10^18600000000` |
| Calabro's occurrence bound `2^26`, at most `8n` marks | 1,861 | 21 | `10^580000000` |
| Cutoff `n̄ ≈ n/(32 log₂ 2Δ)`, at most `4.5n` marks | 1,181 | 20 | `10^290000000` |
| Cutoff `n̄ ≈ n/(128 log₂ 2Δ)`, at most `3.5n` marks | 965 | 19 | `10^145000000` |
| Triple XOR, detection `7/16`, at most `2.5n` marks | 710 | 18 | `10^72500000` |

## Next steps, with estimates

The estimates below come from a floating-point model of the budget and are
not proofs.

1. **Sharpen the number of marks.** We round the mark bound up to `2.5n`.
   With `r̄ ≤ 1.21β+1` and the existing estimate for `β`, a coefficient
   closer to `2.25n` may be possible by retaining rational coefficients.
   This would improve the budget but, alone, would not save the next level.
2. **Try fivefold XOR or a better original family.** Five XORs give detection
   at least `31/64`, with checks at most five times as large as the original.
   The gain competes with larger mark bit lengths and a family of size up to
   `(32m)^20`. This remains unimplemented and unproved in this repository.
3. **Shorten or charge fewer marks.** Level 17 requires `A < 526.36` under
   the tightly evaluated recurrence, or about `A < 514.26` with the current
   uniform Lean recurrence bound. Reducing 710 to that range likely needs
   stronger checks together with a smaller mark charge or occurrence bound.
4. **Improve the level schedule or grouping.** Replacing the `K^17 ≤ n`
   constraint or lowering the starting schedule could reduce the outer
   exponent without saving a whole level. These require new proofs, rather
   than changing a numeral in the cutoff theorem.

The present exact level threshold has decimal exponent approximately
72,441,577.04. Tighter decimal rounding offers a small numerical saving;
reaching level 17 would reduce it to about 36,220,445.65. The interval script
shows that the current sufficient budget expression is above one at level 17.
This is a limitation of this certificate, not a lower bound on actual runtime.

## What the proposed target requires

`ETHConstants.SAT.selected_at_target` proves in Lean that `10^100000` selects
level 8. Its two surrounding level thresholds are approximately `10^70304.35`
and `10^141018.10`.

Exact rational interval evaluation gives `e_8` approximately 0.04025996.
At precision four, making an expression `A·e_8 + 1/16` smaller than one
would require `A < 23.2862`. The current coefficient is 710, a gap of
about 30.5 times; with it the expression is about 28.65. These are
calculations about a sufficient bound; they are not a lower bound on the
actual runtime or a proof that another analysis cannot reach the target.

`ETHConstants.SAT.level_eight_coefficient_lt` proves in Lean that any
nonnegative coefficient making that expression less than one must be below
30. It uses the rigorous lower bound `e_8 >= 1/32`. The sharper value 23.2862
comes from the accompanying interval calculation, not this Lean theorem.

Reaching `10^100000` requires a much larger change than the XOR improvement.
In the present budget model, even the non-mark leading cost is 18 before
rounding and lower-order allowances. A coefficient below 23.2862 would leave
very little room for parity-check marks. A substantially different reduction,
mark encoding, or faster contraction of the recursive exponent is needed.
This is an assessment of the current proof strategy, not an impossibility theorem.

Run `python3 scripts/analyze_cutoff.py` to reproduce the interval calculations.
They enclose `1/sqrt(2)` by rational numbers and bound every discarded positive
reciprocal term. Decimal logarithms in the output are approximate.

The piece overhead coefficient 1157 and the partition constants mainly enter
lower-order terms already absorbed into the final `+1` of the coefficient.
Making the Turing simulation degree and constants explicit is a separate
requirement for a certified runtime comparison with brute force.
