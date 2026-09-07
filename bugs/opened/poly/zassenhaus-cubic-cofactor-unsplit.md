# zassenhaus-cubic-cofactor-unsplit

Kind: bug
Status: PARTIALLY FIXED (see below)
Area: poly

## Original case — FIXED

27x^4-54x^3-144x^2-16x+320 now splits into three factors. Root cause
(found and fixed in the same session): the mod-p leading coefficient
was absorbed into ONE lifted factor; corrections have degree below
their factor, so the product's leading coefficient was FROZEN mod p^k
and the congruence f = prod g_i mod p^k was structurally impossible
for k >= 3 (27 - 2 = 25 is not 0 mod 125). Fix: lift the MONIC
associate of f with monic factors (never absorb lc), and during
reconstruction try every positive divisor D of the current leading
coefficient against each subset product, reducing D*G mod p^k into
the symmetric range BEFORE content normalization (normalization
otherwise strips the scale factor and the rational-root-sized
divisors are never seen).

Guard: ZassenhausFixed.QuarticCubicSplit (enabled, green).

## Remaining case — OPEN

f = 12x^5 + 106x^4 + 316x^3 + 380x^2 + 230x + 100
  = 2 * (x^2+5x+5)(2x^2+x+1)(3x+10)
The planted factor 2x^2+x+1 (discriminant -7) is not returned.
Notable: disc(2x^2+x+1) = -7 = 0 mod 7 — p=7 is rejected by the
squarefree check, p=3 divides lc, p=5 makes x^2+5x+5 collide; the
accepted prime forces a specific 5-way split whose reconstruction
still misses one divisor. Guard:
ZassenhausProperty.DISABLED_AssembleFromKnownFactors.

## Impact

factorOverQ can drop factors on rare inputs; must not feed Trager
until closed.
