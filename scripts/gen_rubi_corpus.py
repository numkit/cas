#!/usr/bin/env python3
"""Generate the Rubi-slice corpus (section 7, C2 metrics).

Tasks shaped like the committed rule slices (1.1.1.1 (a+b x)^m,
1.1.1.2 (a+b x)^m (c+d x)^n, and 1.1.2.1 (a+b x^2)^p), all with
op=rubi so the corpus runner routes them through the rule engine:

  0: x^m                                (m >= 1, incl. bare x at m=1)
  1: (a + b x)^m                        (m fractional or integral != -1)
  2: 1/(a + b x)                        (log rule with RemoveContent)
  3: (a +/- b x^2)^p                    (p positive integer; cascade)
  4: 1/(a + b x^2), a,b > 0             (atan rule; Rt folding)
  5: 1/(a - b x^2), a,b > 0             (atanh rule; R1a)
  6: (a + b x^2)^(-1/2), a,b > 0        (asinh rule; R1a radical gate)
  7: (a - b x^2)^(-1/2), a > 9/4 b > 0  (asin rule; R1a radical gate)
  8: (a + b x^2)^(-3/2 | -5/2)          (half-integer reduction; R1a)
  9: ((a + b x)^-1)*((c + d x)^-1)      (1.1.1.2 two-factor log/atanh)

Deterministic: fixed seed.
"""

import random
from fractions import Fraction

SEED = 20261005
TASKS = 300


def main():
    rnd = random.Random(SEED)
    made = 0
    while made < TASKS:
        kind = rnd.randrange(10)
        a = rnd.randint(1, 6)
        b = rnd.randint(1, 6)
        if kind == 0:
            m = rnd.randint(1, 9)
            expr = "x" if m == 1 else f"x^{m}"
        elif kind == 1:
            m = Fraction(rnd.randint(-4, 5), rnd.randint(2, 3))
            if m.denominator == 1 and m.numerator in (0, -1, 1):
                continue
            expr = f"({a} + {b}*x)^({m.numerator}/{m.denominator})"
        elif kind == 2:
            expr = f"1/({a} + {b}*x)"
        elif kind == 3:
            p = rnd.randint(1, 4)
            sign = "+" if rnd.randrange(2) == 0 else "-"
            expr = f"({a} {sign} {b}*x^2)^{p}"
        elif kind == 4:
            expr = f"1/({a} + {b}*x^2)"
        elif kind == 5:
            expr = f"1/({a} - {b}*x^2)"
        elif kind == 6:
            expr = f"({a} + {b}*x^2)^(-1/2)"
        elif kind == 7:
            b_small = rnd.randint(1, 3)
            a_safe = 3 * b_small + rnd.randint(1, 5)
            expr = f"({a_safe} - {b_small}*x^2)^(-1/2)"
        elif kind == 8:
            num = -3 if rnd.randrange(2) == 0 else -5
            expr = f"({a} + {b}*x^2)^({num}/2)"
        else:
            c_coef = rnd.randint(1, 6)
            d_coef = rnd.randint(1, 6)
            if a * d_coef == b * c_coef:
                c_coef += 1
            sign = "+" if rnd.randrange(2) == 0 else "-"
            expr = f"1/(({a} + {b}*x)*({c_coef} {sign} {d_coef}*x))"
        made += 1
        print(f"rs{made:04d}\tx\trubi\t{expr}")


if __name__ == "__main__":
    main()
