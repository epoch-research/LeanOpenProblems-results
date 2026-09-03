# Color defects and a bounded-sum counterexample to Sidon extraction

## Original task

The conjecture remains unresolved. Spec.lean is unchanged, including its
original sorry. None of the following results is its negation.

## Verified production files

* SidonGridExplore.lean
* SidonColorDefectExplore.lean
* SidonColorDefectWitnessExplore.lean

All compile with current oleans. SidonGridAudit.log and
SidonColorDefectAudit.log audit eleven principal declarations and report
only propext, Classical.choice, and Quot.sound.

## Bounded sum counts do not bound Sidon coloring number

`exists_cap_four_not_sidon_colored` proves that for EVERY natural m there
is a finite S subset Nat such that

    r_S(n) <= 4 for every natural n,

but no coloring of S into m colors has unique positive differences within
each color. Hence no such coloring has Sidon color classes either.

The construction is a no-carry integer Cartesian product X+M Y of two
finite Sidon sets. The proof checks the natural modular and quotient
identities explicitly. They give r_(X+MY)(n)<=r_X(n mod M)r_Y(n/M)<=4.

Two pigeonhole steps force a monochromatic rectangle when there are more
rows than colors and more columns than (rows)^2*(colors). The four corners
have a nontrivial equal sum, or equivalently a repeated positive difference.
This is incompatible with the claimed coloring.

The finite Sidon sets are obtained using the existing verified extraction
theorem. No density-optimality claim is made for the resulting grids.

This rules out a bound on Sidon coloring number depending ONLY on the sum
representation cap, even when that cap is the constant four. It does not
rule out an extraction theorem with additional all-scale hypotheses.

## Quantitative defect budget

For a coloring col into m colors and a block width u, take the forward
same-color pairs whose two endpoints lie in the same u-block. Map each
such pair to (color, positive difference). Define E to be the number of
pairs minus the cardinality of this image. Thus E counts repetitions
beyond one per occupied (color,difference) fiber.

Without ANY Sidon assumption, the checked block estimate is

    sum_(b in B) occupancy(b)^2 <= m|S| + 2m^2 u + 2m E

for any selected block set B. Applying it to the annuli [4^j,4^(j+1)),
J<=j<2J, gives

    a^2 4^J J^2 <= 3m|S| + 6m^2 4^J + 6m E,

provided each annulus has squared mass at least a^2 4^j J.
If |S|<=b 4^J J and m<=min(1,a^2/(6b+12))J, then

    a^2 4^J J^2 <= 12m E.

## Necessary condition for a hypothetical witness

`witness_requires_color_defects` combines the preceding finite inequality
with the already checked Tauberian counting profile. It produces positive
constants delta, eta and a threshold K such that, for every J>=K and EVERY
coloring of A intersect [0,4^(2J)) into m<=delta J colors,

    eta 4^J J^2 <= m E,

where E is the width-4^J defect defined above. The coloring may be chosen
afresh for each prefix.

## Remaining issue

A small upper bound on r_A does not by itself give a small repeated-
difference defect, and the finite grid theorem shows that a universal
bounded-Sidon-color extraction cannot be inserted in its place. No upper
bound on the defects for arbitrary logarithmic witnesses is proved.
Thus the new necessary condition is not a contradiction and does not
settle Spec.lean.
