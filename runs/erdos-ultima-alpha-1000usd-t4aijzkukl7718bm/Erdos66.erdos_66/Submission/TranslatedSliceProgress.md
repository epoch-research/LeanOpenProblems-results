# Positive finite translation averaging with a prescribed old slice

## Original task status

Erdos66.erdos_66 remains unproved and undisproved. Submission/Spec.lean is
unchanged with its original sorry. No final proof has been submitted.
The results below concern finite product groups, not the original limit
on natural numbers.

## New unconditional endpoint

Let G be any finite abelian group and A any nonempty finite subset of G.
For every c>0, epsilon>0, and lower bound N0, there are M>N0, M>1, and
B subset ZMod M x G such that:

* (0,a) belongs to B if and only if a belongs to A;
* for EVERY a in G, some z!=0 has (z,a) in B;
* at EVERY target w in ZMod M x G,

      |r_B(w)/log(|G| M)-c| < epsilon.

The old set is prescribed BEFORE the new set is chosen. No self-flatness,
mixed-flatness, polynomial description, or counting profile is assumed
for A. The second condition is full old-residue projection OUTSIDE the
retained slice, not merely projection of the old slice itself.

Main theorem:

    Erdos66LogarithmicTranslatedSlice.exists_logarithmic_translated_slice

## Exact averaging identity

For A,B subset G and any z in G, with T_a A=a+A,

    sum_(a,b in G) r_(T_a A,T_b B)(z) = |G| |A| |B|.

In particular, the uniform color-kernel mean of all translates of A is
|A|^2/|G|, independent of z. The old representation profile is averaged,
not assumed flat.

The existing universal kernel theorem now has an explicit specialization
that chooses one palette BEFORE every later old set A. Its main term is
h^2 |A|^2/|G|, with the same numerical color-cost hypothesis as before.
This is `exists_universal_translate_averaging` in
Erdos66TranslateKernelAveraging.

## Actual finite sets and exact slice replacement

Use disjoint fine palettes P_i indexed by G and form the actual union

    C = union_(i in G) P_i x (i+A).

The fine palettes are disjoint, so the exact mixed-count assembly formula
applies even though the old translates overlap. If all fine mixed counts
are delta-flat about mu, then

    |r_C(z,q)-mu |G| |A|^2| <= delta mu |G| |A|^2.

Replace C on {0} x G by {0} x A. This retains exactly the prescribed old
membership and changes every product-group representation count by at
most 2|G|. Outside that slice nothing changes.

Each fine color has a nonzero point: its positive self count at a nonzero
fine target forces this. Since all translates of nonempty A cover G,
every old residue is reached away from the replaced slice.

## Logarithmic tuning

Let D=|G| |A|^2. The existing disjoint cyclic palette is tuned at coefficient
c/D. Choose its accuracy and mean-tuning tolerance first, then take its
modulus M sufficiently large to absorb:

* the additive replacement cost 2|G|/log(|G| M);
* the change from log M to log(|G| M).

Thus the output coefficient is the prescribed c, not a coefficient
multiplied by the size of the old set. No bound is asserted on how close
the new modulus is to the old group size.

## Verification

Production files, all compiled without warnings and with current oleans:

* TranslateKernelAveragingExplore.lean
* TranslatedSliceLiftExplore.lean
* LogarithmicTranslatedSliceExplore.lean

They contain 329 lines and no placeholders. TranslatedSliceAudit.lean and
TranslatedSliceAudit.log audit fourteen declarations using only propext,
Classical.choice, and Quot.sound.

## Remaining gap and scope cautions

This is a positive finite extension, not a new universal obstruction. It
removes an old-set flatness requirement and does not permanently retain
an old residue restriction.

However, the preserved object is a SLICE in a finite PRODUCT GROUP.
Product-group representation counts at that slice are NOT preserved:
new opposite fine coordinates can contribute to them. Nor is the radix
bijection with ordinary integers additive; the corresponding carry must
be handled explicitly. No natural-number representation bound is silently
inferred from the product-group conclusion.

Even a finite radix transfer would still leave the main issue: every
intermediate natural scale must have the right density and lower counts
while the old prefix remains fixed. The result gives neither that
transition nor cutoff-independent simultaneous finite-prefix feasibility.
It cannot be substituted for the theorem in Spec.lean.

The accompanying review did not find a thinning scheme that escapes the
fixed-coefficient tail budget. External reference lookup again failed at
DNS resolution. No claim of an external solution was obtained.
