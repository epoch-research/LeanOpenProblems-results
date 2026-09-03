# Height ceilings for affine-digit parabola lifts

This continuation does NOT settle Erdos 773. Spec.lean is unchanged, with
its sole admission for 0<epsilon<=1/3. The results below concern specified
modular construction families, not arbitrary square-Sidon sets.

## Modular lines in the floor-parabola graph

FloorParabolaLineBound.lean proves that for p>0 and arbitrary a,c in ZMod p,
if every b in B satisfies 0<=b<p and

    floor(b^2/p) = a*b+c modulo p,

then

    |B|^2 <= p*(5+2*log p).

For a fixed positive gap d, all digit differences along that gap are equal
as integers, not merely congruent: each is in [0,p). Comparing floor errors
then bounds the diameter of gap starts by p/d. Thus there are at most p/d+1
pairs of that gap. Summing all positive gaps with a harmonic bound proves
the result. The finite variable-gap pair-sum inequality is also formalized.

## General affine high-digit condition

AffineDigitLiftBound.lean defines

    AffineDigits p a c A :=
      for all n in A, floor(n^2/p) = a*n+c modulo p.

For n=b+p*t, its exact integer square quotient is

    floor(n^2/p) = floor(b^2/p)+2*b*t+p*t^2.

The fixed-quotient remainder layer therefore lies on the floor-parabola
line with slope a-2*t and intercept c. If n<=N for all n in A, finite
Cauchy--Schwarz across all quotient layers gives

    |A|^2 <= (floor(N/p)+1)^2 * p*(5+2*log p).

If reduction modulo p is also injective and 0<p<=N, then

    |A|^3 <= N^2*(20+8*log p).

Theorem eventual_power_bound is uniform in p<=N, a,c, and A: for every
epsilon>0, eventually all such A satisfy |A|<=N^(2/3+epsilon).

The same bound holds if residue injectivity is replaced by square-pair
matching modulo p^2. The affine digit condition makes the square residue
modulo p^2 a function of the root residue modulo p. Pair matching applied
to repeated pairs then forces residue injectivity. No primality or unit
hypothesis is needed for this implication.

## Connection to the actual canonical lift

parabola_affine_digits proves the existing roots ParabolaSquareLift.root
satisfy AffineDigits p 1 0. Its earlier highDigit_congruence and the exact
quotient decomposition discharge this step. Residue injectivity follows
from root_mod. Thus arbitrary short-root truncations of the existing lift
satisfy the general cubic bound, without needing the half-band restriction.

## Sharper slope-one count

SharpCanonicalParabolaBound.lean improves the bound for this exact lift to

    |B|^3 <= N^2.

This has no logarithm and no p<=N hypothesis. More generally it applies to
any residue-injective A with AffineDigits p 1 0, nonzero root residues, and
all roots <=N.

At quotient t, a nonzero label 0<b<p obeys

    floor(b^2/p)+2*b*t = b modulo p.

At t=0 this is impossible since floor(b^2/p)<b. At t>=1 put

    F_t(b)=floor(b^2/p)+(2*t-1)*b.

This is strictly increasing, is divisible by p at every valid label, and
lies strictly between 0 and 2*t*p. Dividing by p injects the layer into
{1,...,2*t-1}. Summing gives at most T^2 roots through quotient T. Combining
|A|<=floor(N/p)^2 with |A|<=p gives |A|^3<=N^2.

This rules out near-linear short-root truncations of the canonical
slope-one parabola lift. It does not bound all modular Sidon constructions.
In particular, changing the high square digit by a quadratic function of
the root residue is outside the proved general affine condition.

## Verification

All three modules compile cleanly, with built oleans. Their 18 printed
audits use only propext, Classical.choice, and Quot.sound. They import clean
auxiliary modules, not the admitted Spec theorem.

Logs:

    /tmp/floor-parabola-line.log
    /tmp/affine-digit-lift-bound.log
    /tmp/sharp-canonical-parabola.log

No proof of the original conjecture or its negation has been submitted.

The retained combined audit source is AffineDigitLiftAudit.lean; its clean
18-result log is /tmp/affine-digit-combined-audit.log. The final main-file
check is /tmp/spec-affine-digit-check.log and still reports the expected
sorry. Spec SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.

The checksum-lift review produced no uniform construction. The finite
q=3 and q=5 witnesses and the already proved failures of the uniform cubic
rule and unrestricted concatenation do not provide an asymptotic lower
bound. No new impossibility result for arbitrary checksums is claimed.
