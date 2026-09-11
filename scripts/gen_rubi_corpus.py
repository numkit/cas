#!/usr/bin/env python3
"""Generate the Rubi-slice corpus (section 7, C2 metrics).

Tasks shaped EXACTLY like the committed rule slices (1.1.1.1
(a+b x)^m and 1.1.2.1 (a+b x^2)^p), all with op=rubi so the corpus
runner routes them through the rule engine:

  x^m                       (x_^m_. rule, m != -1, 0)
  (a + b x)^m               (m fractional or integral != -1)
  1/(a + b x)               (log rule with RemoveContent)
  (a + b x^2)^p             (p positive integer; monomial/sq rules)
  1/(a + b x^2), a,b > 0    (the atan rule; Rt folding)

Deterministic: fixed seed.
"""

import random
from fractions import Fraction

SEED = 20261005
TASKS = 120


def main():
    rnd = random.Random(SEED)
    made = 0
    while made < TASKS:
        kind = rnd.randrange(5)
        a = rnd.randint(1, 6)
        b = rnd.randint(1, 6)
        if kind == 0:
            m = rnd.randint(2, 9)
            if m == 0:
                continue
            expr = f"x^{m}"
        elif kind == 1:
            m = Fraction(rnd.randint(-4, 5), rnd.randint(2, 3))
            if m.denominator == 1 and m.numerator in (0, -1, 1):
                continue
            e = f"({a} + {b}*x)^({m.numerator}/{m.denominator})"
            expr = e
        elif kind == 2:
            expr = f"1/({a} + {b}*x)"
        elif kind == 3:
            p = rnd.randint(1, 4)
            expr = f"({a} + {b}*x^2)^{p}"
        else:
            expr = f"1/({a} + {b}*x^2)"
        made += 1
        print(f"rs{made:04d}\tx\trubi\t{expr}")


if __name__ == "__main__":
    main()
