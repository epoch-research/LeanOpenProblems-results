# Small representatives of the carry-aware parabola lift

This continuation does NOT settle Erdos 773. Spec.lean is unchanged, with
its sole sorry for 0<epsilon<1/3. The eventual lower bound M(N)>=N^(2/3)
remains the strongest proved exponent for the original maximum.

## New verified modules

* ParabolaSmallRepresentatives.lean imports the clean ParabolaSquareLift.
* ParabolaMirrorRepresentatives.lean imports the preceding new module.

Both build without warnings or admissions, with oleans. Their eight
principal axiom audits use only propext, Classical.choice, and Quot.sound.
Logs:

    /tmp/parabola-small-representatives.log
    /tmp/parabola-mirror-representatives.log

## The specific lift

For an odd prime p and 0<b<p, the existing lift is

    a_p(b) = ((b-floor(b^2/p))/(2b) in ZMod p).val,
    r_p(b) = b+p*a_p(b).

It has r_p(b)^2 congruent to (b^2 mod p)+p*b modulo p^2. Selecting labels
in a common low-digit half-band makes the lifted squares modular Sidon.
The new bounds do not require the half-band or Sidon condition.

## Original representatives

highDigit_pos proves a_p(b)>0. The carry equation makes

    T_a(b) = floor(b^2/p)+(2a-1)*b

positive and divisible by p on the labels with high digit a. It is strictly
increasing in b and less than 2*a*p. Thus T_a(b)/p injects that level into
{1,...,2a-1}. level_card proves its cardinality is at most 2a-1 (zero at a=0).

Summing levels gives bounded_highDigit_card:

    if a_p(b)<=H for all b in B, then |B|<=H^2.

If all r_p(b)<=N, take H=floor(N/p). Also |B|<=p. Therefore

    |B|^3 <= p^2*H^2 <= N^2.

height_card_ceiling states this directly for the image of lifted roots.
This bounds every truncated subfamily of these particular representatives,
not just a full fiber or a Sidon subfamily.

## Complementary representatives and independent sign choices

highDigit_complement proves the exact identity

    a_p(b)+a_p(p-b)=p.

Consequently mirror_add proves

    (p^2-r_p(b))+p = r_p(p-b).

This controls the other canonical square root without assuming it follows
the original high-digit bound at the same label. bounded_mirror_card gives

    |B| <= (floor(N/p)+1)^2

when all complementary roots p^2-r_p(b) have height at most N.

chosenRoot selects r_p(b) or p^2-r_p(b) according to an arbitrary Boolean
function of b. Partition the labels by that function. At H=floor(N/p)>=1,
the total label count is at most H^2+(H+1)^2<=5H^2, and is also at most p.
The cases H=0 and N=0 are separately covered. signed_height_card_ceiling
proves the unconditional finite bound

    |image(chosenRoot,B)|^3 <= 5*N^2.

Thus allowing the sign to vary with every label still does not yield a
near-linear construction by taking small representatives of THIS lift.

## Scope

These are construction-specific height/cardinality ceilings. They are not
upper bounds for arbitrary Sidon subsets of the first N squares and are
not a disproof of the original conjecture. They do not assert a ceiling
for other modular Sidon sets, other affine target parametrizations, arbitrary
root translations, or arbitrary sparse unions of residue fibers.

No new exponent for the original maximum was established. No incomplete
proof was submitted. Spec.lean remains at SHA-256
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940.
