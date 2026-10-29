#!/usr/bin/env python3
"""Exact rational intervals for the recurrence; explanatory, separate from Lean.

This evaluates a sufficient budget expression, not the program's runtime.
Decimal logarithms and printed decimal values are approximations. No enormous
clique sizes are constructed: omitted positive reciprocal terms are bounded
above by 2^-1000.
"""
from decimal import Decimal, localcontext
from fractions import Fraction as F
from math import isqrt


def exponent(level):
    return 54 * 2**level - 6 * level - 38


def recurrence_intervals(last):
    scale = 10**40
    root = isqrt(scale * scale // 2)
    rho_lo, rho_hi = F(root, scale), F(root + 1, scale)
    assert rho_lo**2 <= F(1, 2) <= rho_hi**2
    lo = hi = F(1, 2)
    for level in range(last + 1):
        yield level, lo, hi
        x = exponent(level)
        if x <= 1000:
            reciprocal_lo = reciprocal_hi = F(1, 2**x)
        else:
            reciprocal_lo, reciprocal_hi = F(0), F(1, 2**1000)
        correction = F(3, 2**(level + 5))
        lo = (rho_lo + correction) * lo + 3 * reciprocal_lo
        hi = (rho_hi + correction) * hi + 3 * reciprocal_hi


COEFF = 1861  # 6*304 + 18 + 18 + 1: marks 8n at 38 bits each (Delta = 2^26), plus lower-order terms


def main():
    print(f"Level | log10(K_l^17) | e_l interval | {COEFF} e_l + 1/16 | coefficient ceiling")
    for level, lo, hi in recurrence_intervals(32):
        if level not in (8, 9, 12, 16, 19, 20, 21, 22, 24, 26, 28, 32):
            continue
        with localcontext() as ctx:
            ctx.prec = 50
            decimal_exponent = Decimal(17 * exponent(level)) * Decimal(2).log10()
        print(f"{level:2} | {decimal_exponent:,.3f} | "
              f"[{float(lo):.14g}, {float(hi):.14g}] | "
              f"[{float(COEFF*lo+F(1,16)):.10f}, {float(COEFF*hi+F(1,16)):.10f}] | "
              f"[{float(F(15,16)/hi):.8f}, {float(F(15,16)/lo):.8f}]")
        # Exact rational checks, not comparisons of the displayed decimals.
        if level == 8:
            assert F(40259, 10**6) < lo <= hi < F(40261, 10**6)
            assert COEFF * lo + F(1, 16) > 74
        if level == 20:
            assert COEFF * lo + F(1, 16) > 1
        if level == 21:
            assert COEFF * hi + F(1, 16) < 1
            # The Lean proof uses e_l <= 0.66 rho^l and rho <= 3/4 instead of the interval.
            assert COEFF * F(33, 50) * F(3, 4) / 2**10 + F(1, 16) < 1
    print("The tighter interval endpoints can round to identical displayed decimals.")
    print("Coefficient ceilings concern the displayed certificate at precision four;")
    print("they do not certify a redesigned reduction or its lower-order terms.")


if __name__ == "__main__":
    main()
