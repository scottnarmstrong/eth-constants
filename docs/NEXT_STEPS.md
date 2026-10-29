# Further improvements and the 10^100000 target

Here the target means `n = 10^(10^5) = 10^100000` variables. It does not mean
100,000 variables. All thresholds discussed here concern avoidance of the
top-level exhaustive-counting fallback, as explained in the README.

## A further checked improvement

Keeping the network logarithm exact reduces the leading coefficient at
precision four from 83,580 to 17,928. This lowers the sufficient selected
level from 32 to 28 and the rounded cutoff from `10^1200000000000` to
`10^75000000000`. The exponent of the outer ten is 16 times smaller.
The algorithm and its precision rule are unchanged by this improvement;
the proof of its cutoff is sharper.

The complete budget expression at levels 28 through 31 is bounded by

$$17929e_\ell+1/16.$$

Lean checks both the new network bound and its use in the actual program's
branch guards. The updated theorem is `ETHConstants.SAT.no_fallback`.

## What the proposed target requires

The current schedule has

$$\log_2 K_\ell=54\,2^\ell-6\ell-38,$$

and selects the largest level with `K_l^17 <= n`. In particular,
`ETHConstants.SAT.selected_at_target` proves in Lean that `10^100000`
selects level 8. Its two surrounding level thresholds are approximately
`10^70304.35` and `10^141018.10`.

Exact rational interval evaluation gives `e_8` approximately 0.04025996.
At precision four, making an expression `A*e_8 + 1/16` smaller than one
would require `A < 23.2862`. The current coefficient is 17,929: a gap of
about 770 times. With that coefficient unchanged the expression is about
721.88. These are calculations about a sufficient bound; they are not a
lower bound on the actual runtime or a proof that another analysis cannot
reach the target.

There is also a simpler Lean check:
`ETHConstants.SAT.level_eight_coefficient_lt` proves that any nonnegative
coefficient making that expression less than one must be below 30. It uses
the rigorous lower bound `e_8 >= 1/32`. The sharper value 23.2862 comes from
the accompanying interval calculation, not this Lean theorem.

Run `python3 scripts/analyze_cutoff.py` to reproduce the interval calculations.
They enclose `1/sqrt(2)` by rational numbers and bound every discarded positive
reciprocal term. Decimal logarithms in the output are approximate.

## Where to work next

1. **Specialize sparsification to width three.** The present interface uses
   `beta = 6*(4*s+17)`, hence `beta=198` at the smallest admitted precision
   `s=4`. This drives the network logarithm. A much tighter density versus
   branching tradeoff would reduce the dominant coefficient. Simply choosing
   a smaller precision is not justified by the current guard and proof.
2. **Reduce the network construction cost.** Its exact definition contains
   `28*k*n*ceil(log2(96*Delta*LD(Delta)))`, in addition to other terms. We have
   now removed much of the slack in estimating this definition. Substantial
   further savings require improving the bound supplied to the program and
   proving the revised reduction correct, or finding a better construction.
3. **Improve the recursive contraction relative to clique growth.** The current
   rate is roughly `e_l = 0.645*(1/sqrt(2))^l`. A stronger factorization could
   reduce the level needed for a given coefficient. Its effect on `K_l` must
   be included: a stronger contraction obtained only at much larger clique
   sizes need not lower the cutoff.

For scale, the level-27 expression is about 1.06042. Reducing its leading
coefficient by just over 6%, together with a correspondingly sharp recurrence
proof, could make level 27 sufficient and roughly halve the outer exponent
again. That is a plausible next milestone, not an achieved result.

Much larger gains require combining the first two directions, or a stronger
recursion. Since the present leading schedule behaves like `log(n) ~ 2^l`
while `e_l ~ 2^(-l/2)`, a factor `r` reduction in the leading coefficient
roughly gives a factor `r^2` reduction in the outer exponent, subject to
integer levels and the other costs. This explains both the leverage of a
better reduction and the size of the remaining gap to `10^100000`.

The piece overhead coefficient 1157 and the partition constants mainly enter
lower-order terms already absorbed into the additional `+1` in 17,929.
Improving only those constants is unlikely to deliver the needed orders of
magnitude. Making the Turing simulation degree and constants explicit is a
separate requirement for a certified runtime comparison with brute force.
