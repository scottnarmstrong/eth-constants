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

The leading coefficient is now `A = 11539`. Almost all of it,
`2k·9·213 = 11502`, pays for the marks of the parity checks: at most `9n`
marks, each charged `⌈log₂(96Δ⌈log₂ 2Δ⌉)⌉ = 213` bits at each of its `k = 3`
tests. The value 213 comes from the occurrence bound `Δ = 2^198` that the
sparsification hands to the network.

## Checked improvements so far

| Step | `A` | Level | Cutoff |
|---|---:|---:|---|
| First release | 83,580 | 32 | `10^1200000000000` |
| Exact network logarithm | 17,929 | 28 | `10^75000000000` |
| At most `9n` marks when `Δ ≥ 2^15` | 11,539 | 26 | `10^18600000000` |

## Next steps, with estimates

The estimates below come from a floating-point model of the budget and are
not proofs.

1. **Specialize the sparsification to width three.** The thresholds use
   `τ = 2^(4s+17)`, chosen to work uniformly in `k`. For `k = 3`, `s = 4` the
   leaf-count condition `(3/τ)·log₂(e·τ^7) ≤ 2^-s` already holds near
   `τ = 2^12`. Lean also already proves that a leaf has at most
   `2(1 + 4τ + 4τ³)` clauses per variable (`length_occ_le_of_none`), far
   below `τ^6`. Passing that bound, about `2^39`, to the network instead of
   `2^198` would reduce the 213-bit mark cost to about 51 bits. Estimate:
   `A ≈ 2,300`, level 22, cutoff about `10^(1.2·10^9)`. The `9n` mark bound
   already covers this range of `Δ`.
2. **Use a stronger family of parity checks.** Lemma 13 guarantees that a
   quarter of the checks have odd intersection with a large violated set, so
   `r̄ ≈ 2.41β` checks are needed. A family that achieves 0.4–0.45 (a higher
   subsampling rate and a larger field) would give `r̄ ≈ 1.2–1.4β` and about
   `5n` marks. Estimate: level 20–21, cutoff `10^(3·10^8)`–`10^(6·10^8)`.
3. **Smaller corrections.** The top-level grouping on `g = 3K^8` nodes forces
   `K^17 ≤ n`; a sharper concentration argument could replace 17 by about 13.
   Separating `K_0` from the balancing factor in the level schedule would also
   help slightly. Together these may lower the outer exponent by a factor of
   1.3 to 1.7.

After the first step, the sufficient cutoff would lie below the threshold
`log₂ n > 8.5·10^9` that the paper's Appendix D gives as necessary for its own
choice of parameters. The two analyses use different parameters, so this is a
comparison of numbers, not of claims.

## What the proposed target requires

`ETHConstants.SAT.selected_at_target` proves in Lean that `10^100000` selects
level 8. Its two surrounding level thresholds are approximately `10^70304.35`
and `10^141018.10`.

Exact rational interval evaluation gives `e_8` approximately 0.04025996.
At precision four, making an expression `A·e_8 + 1/16` smaller than one
would require `A < 23.2862`. The current coefficient is 11,539, a gap of
about 495 times; with it the expression is about 464.6. These are
calculations about a sufficient bound; they are not a lower bound on the
actual runtime or a proof that another analysis cannot reach the target.

`ETHConstants.SAT.level_eight_coefficient_lt` proves in Lean that any
nonnegative coefficient making that expression less than one must be below
30. It uses the rigorous lower bound `e_8 >= 1/32`. The sharper value 23.2862
comes from the accompanying interval calculation, not this Lean theorem.

Within the present design the target is out of reach. The marks number at
least about `2n`, and each costs at least about `log₂ Δ` bits at each test, so
`A` stays above several hundred, which corresponds to a cutoff no lower than
roughly `10^(10^8)`. Reaching `10^100000` would need new mathematics: pieces
with a contraction rate below `1/√2`, which would change the `A²` law, or a
reduction from 3-SAT with a far smaller coefficient.

Run `python3 scripts/analyze_cutoff.py` to reproduce the interval calculations.
They enclose `1/sqrt(2)` by rational numbers and bound every discarded positive
reciprocal term. Decimal logarithms in the output are approximate.

The piece overhead coefficient 1157 and the partition constants mainly enter
lower-order terms already absorbed into the final `+1` of the coefficient.
Making the Turing simulation degree and constants explicit is a separate
requirement for a certified runtime comparison with brute force.
