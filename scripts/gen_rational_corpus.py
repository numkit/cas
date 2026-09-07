#!/usr/bin/env python3
"""Generate the rational-integration baseline corpus (section 7).

Mirrors the C1 capstone generator (tests/integrate/ratint_test.cpp,
C1CompletenessDoD): random products of linear^m, irreducible-over-Q
quadratic^m and irreducible-over-Q cubic factors, random rational
numerator of lower degree. Output lines: id<TAB>var<TAB>expr, where
expr is num/(den) printed as plain infix text for the nkcas parser.

Deterministic: fixed seed, no dependency on dict ordering.
"""

import random
from fractions import Fraction

SEED = 20260911
TASKS = 500


def frac_str(c: Fraction) -> str:
    if c.denominator == 1:
        return str(c.numerator)
    return f"{c.numerator}/{c.denominator}"


def poly_str(cs) -> str:
    """cs: coefficients ascending; infix text, high degree first."""
    terms = []
    for k in range(len(cs) - 1, -1, -1):
        c = cs[k]
        if c == 0:
            continue
        if k == 0:
            terms.append(frac_str(c))
        elif k == 1:
            terms.append(frac_str(c) + "*x")
        else:
            terms.append(frac_str(c) + "*x^" + str(k))
    return " + ".join(terms) if terms else "0"


def pmul(a, b):
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        for j, cb in enumerate(b):
            out[i + j] += ca * cb
    return out


def ppow(a, m):
    out = [Fraction(1)]
    for _ in range(m):
        out = pmul(out, a)
    return out


def has_rational_root(cs) -> bool:
    """cs ascending, monic (or scaled monic): check small p/q roots."""
    for q in (1, 2, 3, 4):
        for p in range(-12, 13):
            r = Fraction(p, q)
            v = sum(c * r**k for k, c in enumerate(cs))
            if v == 0:
                return True
    return False


def rr(rnd, lim):
    q = rnd.randint(1, 3)
    p = rnd.randint(-lim, lim)
    return Fraction(p, q)


def gen_denominator(rnd):
    den = [Fraction(1)]
    n_lin = rnd.randrange(3)
    n_quad = rnd.randrange(2)
    n_cub = rnd.randrange(2)
    for _ in range(n_lin):
        r = rr(rnd, 5)
        while r == 0:
            r = rr(rnd, 5)
        m = rnd.randint(1, 3)
        den = pmul(den, ppow([-r, Fraction(1)], m))
    for _ in range(n_quad):
        while True:
            b = rr(rnd, 4)
            c = rr(rnd, 4)
            if not has_rational_root([c, b, Fraction(1)]):
                break
        m = rnd.randint(1, 2)
        den = pmul(den, ppow([c, b, Fraction(1)], m))
    for _ in range(n_cub):
        while True:
            b = rr(rnd, 3)
            c = rr(rnd, 3)
            if not has_rational_root([c, b, Fraction(0), Fraction(1)]):
                break
        den = pmul(den, [c, b, Fraction(0), Fraction(1)])
    return den


def main():
    rnd = random.Random(SEED)
    made = 0
    while made < TASKS:
        den = gen_denominator(rnd)
        if len(den) < 4:  # want genuinely mixed denominators (deg >= 3)
            continue
        n_deg = rnd.randrange(len(den))
        num = [rr(rnd, 5) for _ in range(n_deg + 1)]
        made += 1
        expr = f"({poly_str(num)})/({poly_str(den)})"
        print(f"r{made:04d}\tx\t{expr}")


if __name__ == "__main__":
    main()
