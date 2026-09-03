# Primitive collisions with growing binary digit moments

This is NOT a settlement of Erdos 773. Spec.lean is unchanged with its sole
admission for 0<epsilon<=1/3. No actual Sidon lower exponent or fixed-power
upper bound has improved.

## New verified result

`PrimitiveGrowingMoments.lean`, namespace `Erdos773.PrimitiveGrowingMoments`,
proves `matching_moment_collision_quartic_log`:

For every k>=1 there is a word length

    0 < L <= 1280*k^4*(k.log2+1)^2

and four odd binary words P,Q,R,S of length at most L, such that

* 0<P(2)<R(2)<S(2)<Q(2);
* P(2)^2+Q(2)^2=R(2)^2+S(2)^2;
* their first k positional binary digit moments agree;
* their evaluated roots have common gcd ONE.

The precise common-gcd condition is that every natural g dividing all four
integer evaluations is one. This is NOT pairwise coprimality, and the roots
are NOT asserted prime. `PrimitiveMomentCollision.not_sidon` explicitly
extracts the non-Sidon conclusion.

This improves the scope, not the length, of the earlier construction. The
old O(k^2 log k) collision words are common multiples of (3,11,7,9). The new
O(k^4 log^2 k) words are primitive. In particular a blanket sufficient criterion
using primitivity together with any fixed polylogarithmic number of positional
moments is still obstructed. This last asymptotic rephrasing is an explanatory
consequence of the polynomial length bound, not an additional Lean theorem.
It does NOT show that every moment class is bad, and does NOT rule out a
larger, more expensive growing collection of constraints.

## Exact arithmetic family

Use positive even u<v and put

    a = 1 + 3u + 3v + uv,
    b = 1 + 7u + 7v + 41uv,
    c = 1 + 7u + 3v + 29uv,
    d = 1 + 3u + 7v + 29uv.

Lean verifies

    a^2+b^2=c^2+d^2,
    29c+29d-a-41b=16,
    0<a<c<d<b.

All four roots are odd. Their common divisor divides 16 by the linear identity,
and therefore is one. Algebraically the norm identity comes from multiplying
1+(5+2i)u and 1+(5+2i)v, and then conjugating the first factor. The constant
term is a common UNIT; there is no common evaluated multiplier of all roots.

## Two-level signed-block encoding

`SignedBlockMoments.lean` now additionally exports the clean public theorem
`exists_block_encoder`. From a signed polynomial with leading coefficient one,
degree D, and k vanishing jets at one, and a block length B, it supplies a
positive multiplier M and a common operator E on odd B-bit words. Each E(P)
is binary, has length at most B(D+1), and evaluates to M*P(2). Every difference
E(P)-E(Q) has k vanishing jets at one. This follows from the existing explicit
borrow calculation; it does not introduce an axiom.

Apply this first at block length 4. Put u=16*M1. The two low words representing
1+3u and 1+7u have k matching jets and length H=4(D+2). Their common added
constant bit is separate from the shifted block output. A binary word bound
shows u<2^H.

Set the second block length B=H+6. The four positive odd integers

    3+u, 7+41u, 3+29u, 7+29u

are all less than 2^B, so they have odd B-bit word encodings. Apply the same
signed polynomial at block length B to those words. Put v=2^B*M2; then v is
even and v>u. Append the second encoded block after the low word of length B.
There is no overlap and therefore no unaccounted carry between the low word
and the shifted second block. The four evaluations are exactly a,b,c,d above.
Their jet differences are sums of two terms each divisible by (X-1)^k.

The total word length is

    (4(D+2)+6)*(D+2).

Taking D<16*k^2*(k.log2+1) from `SmallSignJets` gives the advertised constant
1280. The construction does not need two coprime efficient signed multipliers:
shared small factors of u and v leave all four roots congruent to the unit 1.
Thus it avoids, rather than contradicts, the old multiplier coprimality barrier.

## Verification

Logs:

    /tmp/signed-block-encoder.log
    /tmp/primitive-growing-moments.log
    /tmp/primitive-growing-moments-final.log
    /tmp/growing-moment-after-encoder.log

Build:

    .lake/build/lib/lean/Submission/PrimitiveGrowingMoments.olean

All new public theorem audits report only

    propext, Classical.choice, Quot.sound.

The new module and the extended signed-block module compile without warnings
or admissions. The older growing-moment theorem also recompiles cleanly.
Neither module imports the admitted Spec theorem. The main file's check is
`/tmp/spec-primitive-growing-check.log` and still reports its expected sorry.
No proof submission has been made.
