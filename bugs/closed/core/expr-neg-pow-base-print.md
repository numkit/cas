# expr-neg-pow-base-print

Kind: bug
Status: ✅ FIXED (6a3d85e)
Area: core

## Description

`Ctx::toString` prints a `Pow` whose base is a NEGATIVE Number without
parentheses: `pow(-9, -1/2)` prints as `-9^(-1/2)`. Under the
MATLAB-style precedence the parser implements (unary minus looser than
`^`), that string means `-(9^(-1/2))` — a DIFFERENT node, and for
fractional exponents a genuinely different principal branch of the
power. The printed form therefore does not round-trip to the node it
came from.

## Repro

```
Ctx c;
Expr e = c.pow(c.number(std::int64_t{-9}), c.number(Rational(BigInt(-1), BigInt(2))));
c.toString(e)        // actual:   "-9^(-1/2)"
                     // expected: "(-9)^(-1/2)"
parseExpr(c, "-9^(-1/2)") == e   // actual: false — parses as -(9^(-1/2))
```

Found by the new `ParserProperty.PrintParseRoundTripSameNode`
(generated `pow(-9, -1/2)` inside a bigger tree); the print side is
stable, so the CLI masked nothing — the string simply re-parses to a
different, also-canonical node.

## Root cause

`printPrec` renders the Pow base with parent precedence 61; a Number
(positive or negative, integer or fraction) has printing precedence
100/55, both >= 61, so a negative base never gets parentheses. The
precedence ladder encodes magnitude only, not the sign interaction
with the unary minus of the grammar.

## Fix

In the Pow branch of `printPrec`: when the base is a Number with a
negative value, wrap it in parentheses explicitly (printed with
parent precedence 0 inside the manual parens). Exponents are
unaffected — `x^-2` is unambiguous because the exponent position
parses a unary expression by grammar.

## Guard

`ExprTest.NegativePowBaseKeepsParens` (fixed vector) and
`ParserProperty.PrintParseRoundTripSameNode` (the property that
caught it; the generator emits negative bases with fractional
exponents).
