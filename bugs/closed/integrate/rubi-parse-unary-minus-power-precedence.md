# rubi-parse-unary-minus-power-precedence

Kind: bug
Status: ✅ FIXED (Item 40)
Area: integrate

## Description

In `tools/rubi_parse.py`, unary negation (`-`) was handled inside `_parse_atom_base` (tighter than `parse_power`) instead of inside `parse_power` (looser than `^`). As a result, Mathematica replacement expressions of the form `-(c + d*x)^m` were parsed as `(-(c + d*x))^m` instead of `-((c + d*x)^m)`.

## Repro

For `Int[x^2*sin(x), x]` matching rule 1 of `4.1.10 (c+d x)^m (a+b sin)^n.m`:
- Replacement: `-(c + d*x)^m*Cos[e + f*x]/f + d*m/f*Int[(c + d*x)^(m - 1)*Cos[e + f*x], x]`
- With `c = 0, d = 1, m = 2, e = 0, f = 1`:
  - Expected leading term: `-x^2*cos(x)`
  - Actual leading term before fix: `(-x)^2*cos(x) = +x^2*cos(x)` (rejected by `certificateHolds`).

## Root cause

`_parse_atom_base` consumed leading `-` before `parse_power` checked for `^`, giving unary `-` higher precedence than exponentiation `^`.

## Fix

Moved unary `-` handling to the entry of `parse_power` (`return {"op": "neg", "args": [self.parse_power()]}`), so `^` binds tighter than unary `-` while still permitting negative exponents `u^-k`.

## Guard

`RubiApply.R5TrigInverseTrigHyperbolic` (`x^2*sin(x)`, `x^2*cos(x)`).
