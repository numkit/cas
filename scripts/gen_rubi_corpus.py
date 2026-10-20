#!/usr/bin/env python3
"""Generate the Rubi-slice corpus (section 7, C2 metrics, Stage R1b+R2).

Tasks shaped across the full 1.1 Binomial products section (33 rule files,
1365 rules: 1.1.1 Linear, 1.1.2 Quadratic, 1.1.3 General, 1.1.4 Improper),
all with op=rubi so the corpus runner routes them through the rule engine:

  0: x^m                                (1.1.1.1 bare power)
  1: (a + b x)^m                        (1.1.1.1 fractional/integer power)
  2: 1/(a + b x)                        (1.1.1.1 log rule with RemoveContent)
  3: (a +/- b x^2)^p                    (1.1.2.1 positive integer cascade)
  4: 1/(a + b x^2), a,b > 0             (1.1.2.1 atan rule; Rt folding)
  5: 1/(a - b x^2), a,b > 0             (1.1.2.1 atanh rule; R1a)
  6: (a + b x^2)^(-1/2), a,b > 0        (1.1.2.1 asinh rule; R1a)
  7: (a - b x^2)^(-1/2), a > 9/4 b > 0  (1.1.2.1 asin rule; R1a)
  8: (a + b x^2)^(-3/2 | -5/2)          (1.1.2.1 half-integer reduction; R1a)
  9: 1/((a + b x)*(c +/- d x))          (1.1.1.2 two-factor log/atanh)
 10: 1/(sqrt(a + x)*sqrt(c + x))        (1.1.1.2 Subst + radical norm; R1b)
 11: 3-factor linear binomials          (1.1.1.3 1/((a+x)(c+x)(d+x)) & ExpandIntegrand)
 12: x^m*(a + b*x^2)^(1/2)              (1.1.2.2 Subst + ExpandIntegrand; R2)
 13: 2-factor quadratic & mixed         (1.1.2.3 & 1.1.2.7; R2)
 14: P(x)/(a + b*x^2)                   (1.1.2.10 P(x) ExpandIntegrand; R2)
 15: General & improper binomials       (1.1.3.1, 1.1.3.2, 1.1.4.1; R2)

Deterministic: fixed seed.
"""

import os
import random
import subprocess
from fractions import Fraction

SEED = 20261005
TASKS = 500


def query_reference_antiderivatives(exprs):
    nkcas_bin = os.environ.get(
        "NKCAS_BIN",
        os.path.join("build", "msvc", "apps", "Release", "nkcas.exe"),
    )
    if not os.path.exists(nkcas_bin):
        nkcas_bin = os.path.join("build", "apps", "nkcas")
    stdin_payload = "".join(f"rubi {e} x\n" for e in exprs) + "quit\n"
    proc = subprocess.run(
        [nkcas_bin],
        input=stdin_payload,
        capture_output=True,
        text=True,
        check=True,
    )
    lines = [ln.strip() for ln in proc.stdout.splitlines() if ln.strip()]
    refs = []
    i = 0
    for expr in exprs:
        if i + 1 >= len(lines) or lines[i + 1] != "[certificate: PROVED_SYMBOLIC]":
            raise RuntimeError(f"failed to certify reference for {expr}: {lines[i:i+2]}")
        refs.append(lines[i])
        i += 2
    return refs


def main():
    rnd = random.Random(SEED)
    exprs = []
    while len(exprs) < TASKS:
        kind = rnd.randrange(16)
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
        elif kind == 9:
            c_coef = rnd.randint(1, 6)
            d_coef = rnd.randint(1, 6)
            if a * d_coef == b * c_coef:
                c_coef += 1
            sign = "+" if rnd.randrange(2) == 0 else "-"
            expr = f"1/(({a} + {b}*x)*({c_coef} {sign} {d_coef}*x))"
        elif kind == 10:
            c_coef = a + rnd.randint(1, 5)
            p1 = "-1/2" if rnd.randrange(2) == 0 else "-3/2"
            expr = f"({a} + x)^({p1})*({c_coef} + x)^(-1/2)"
        elif kind == 11:
            c_coef = a + rnd.randint(1, 3)
            d_coef = c_coef + rnd.randint(1, 3)
            if rnd.randrange(2) == 0:
                expr = f"1/(({a} + x)*({c_coef} + x)*({d_coef} + x))"
            else:
                expr = f"({a} + x)^2*({c_coef} + x)*({d_coef} + x)"
        elif kind == 12:
            m = 1 if rnd.randrange(2) == 0 else 3
            expr = f"x^{m}*({a} + {b}*x^2)^(1/2)"
        elif kind == 13:
            c_coef = a + rnd.randint(1, 4)
            if rnd.randrange(2) == 0:
                expr = f"1/(({a} + x^2)*({c_coef} + x^2))"
            else:
                expr = f"({a} + {b}*x)/({c_coef} + x^2)"
        elif kind == 14:
            c_coef = rnd.randint(1, 5)
            expr = f"({a} + {b}*x + {c_coef}*x^2)/({a} + {b}*x^2)"
        else:
            sub = rnd.randrange(3)
            if sub == 0:
                a4 = a ** 4
                expr = f"1/({a4} - x^4)"
            elif sub == 1:
                n = 3 if rnd.randrange(2) == 0 else 4
                expr = f"x^{n - 1}*({a} + {b}*x^{n})^(-1/2)"
            else:
                expr = f"(x^2 + {b}*x^4)^(1/2)"
        exprs.append(expr)

    # Stage R3-R5 (tasks 501..600): trinomials, exponentials, logarithms,
    # trigonometry, inverse trig, hyperbolics, and inverse hyperbolics.
    while len(exprs) < 600:
        kind = rnd.randrange(16, 24)
        a = rnd.randint(1, 5)
        b = rnd.randint(1, 5)
        c_coef = rnd.randint(1, 5)
        if kind == 16:
            sub = rnd.randrange(3)
            if sub == 0:
                expr = f"({a + b} + {b}*x + {a}*x^2)^-1"
            elif sub == 1:
                expr = f"({a} + {b}*x + {c_coef}*x^2)^(-1/2)"
            else:
                expr = f"({a} + {b}*x)*({a + c_coef} + {b}*x + {c_coef}*x^2)^-1"
        elif kind == 17:
            sub = rnd.randrange(3)
            if sub == 0:
                m = rnd.randint(1, 2)
                expr = f"x^{m}*exp({a} + {b}*x)" if m > 1 else f"x*exp({a} + {b}*x)"
            elif sub == 1:
                expr = f"({a} + {b}*exp({c_coef}*x))^-1"
            else:
                expr = f"exp(x)*({a} + {b}*exp(2*x))^-1"
        elif kind == 18:
            sub = rnd.randrange(3)
            if sub == 0:
                p = rnd.randint(1, 2)
                expr = f"x^{a}*log({b}*x)" if p == 1 else f"x^{a}*log({b}*x)^2"
            elif sub == 1:
                p = rnd.randint(1, 3)
                expr = f"x^-1*log({b}*x)^{p}" if p > 1 else f"x^-1*log({b}*x)"
            else:
                expr = f"x^-1*({a} + log({b}*x))^-1"
        elif kind == 19:
            sub = rnd.randrange(4)
            if sub == 0:
                n = rnd.randint(1, 4)
                fn = "sin" if rnd.randrange(2) == 0 else "cos"
                expr = f"{fn}({a} + {b}*x)^{n}" if n > 1 else f"{fn}({a} + {b}*x)"
            elif sub == 1:
                n = rnd.randint(1, 3)
                expr = f"tan({a} + {b}*x)^{n}" if n > 1 else f"tan({a} + {b}*x)"
            elif sub == 2:
                n = rnd.randint(1, 3)
                expr = f"sec({a} + {b}*x)^{n}" if n > 1 else f"sec({a} + {b}*x)"
            else:
                expr = f"cos({b}*x)*({a + 1} + sin({b}*x))^-1"
        elif kind == 20:
            sub = rnd.randrange(2)
            fn = "sin" if rnd.randrange(2) == 0 else "cos"
            if sub == 0:
                m = rnd.randint(1, 2)
                expr = f"x^{m}*{fn}({b}*x)" if m > 1 else f"({a} + {b}*x)*{fn}({c_coef}*x)"
            else:
                expr = f"exp({a}*x)*{fn}({b}*x)"
        elif kind == 21:
            sub = rnd.randrange(4)
            if sub == 0:
                expr = f"asin({a}*x)"
            elif sub == 1:
                expr = f"x*asin({a}*x)"
            elif sub == 2:
                expr = f"atan({a}*x)"
            else:
                m = rnd.randint(1, 2)
                expr = f"x^{m}*atan({a}*x)" if m > 1 else f"x*atan({a}*x)"
        elif kind == 22:
            sub = rnd.randrange(3)
            fn = "sinh" if rnd.randrange(2) == 0 else "cosh"
            if sub == 0:
                n = rnd.randint(1, 3)
                expr = f"{fn}({a} + {b}*x)^{n}" if n > 1 else f"{fn}({a} + {b}*x)"
            elif sub == 1:
                expr = f"x*{fn}({b}*x)"
            else:
                expr = f"sech({a} + {b}*x)^2"
        else:
            sub = rnd.randrange(3)
            if sub == 0:
                expr = f"asinh({a}*x)" if rnd.randrange(2) == 0 else f"x*asinh({a}*x)"
            elif sub == 1:
                expr = f"acosh({a}*x)"
            else:
                expr = f"atanh({a}*x)" if rnd.randrange(2) == 0 else f"x*atanh({a}*x)"
        exprs.append(expr)

    refs = query_reference_antiderivatives(exprs)
    for idx, (expr, ref) in enumerate(zip(exprs, refs), start=1):
        print(f"rs{idx:04d}\tx\trubi\t{expr}\t{ref}")


if __name__ == "__main__":
    main()
