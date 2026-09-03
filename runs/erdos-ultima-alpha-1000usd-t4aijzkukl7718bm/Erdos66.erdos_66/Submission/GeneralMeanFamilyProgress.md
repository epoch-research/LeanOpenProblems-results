# Arbitrary-mean family budgets and distinct equal-size flat templates

## Original conjecture status

Spec.lean is unchanged with its original sorry. The conjecture is still
unproved and undisproved. No proof has been submitted.

## Production sources

* GeneralMeanFamilyBudgetExplore.lean
* EqualCardinalityMixedFamilyExplore.lean

Both compile with current oleans. GeneralMeanFamilyAudit.lean audits fourteen
declarations; its log reports only propext, Classical.choice, and Quot.sound.
No production sorry or new axiom occurs.

## 1. The family obstruction at arbitrary common mean

The unit-mean approximate-complementarity theorem was already available in
ApproximateComplementarityExplore.lean. The new result does NOT repeat that
special case; it keeps the growing common mean explicitly.

Let G have cardinal M. Let q nonempty-indexed sets B_i each have cardinal k,
with actual common mean mu=k^2/M. Suppose every self count is at most C and
every distinct-pair centered energy is at most M E. Then:

    q (k-mu)^2 <= (M-1) [mu(C-mu)+(q-1)E].

Its normalized form is:

    (1-k/M)^2 <= (1-1/M)[(C-mu)/q+(1-1/q) E/mu].

The proof uses the common autocorrelation spike at zero, expands the squared
sum of centered correlations, and separates the self and mixed energies.
It does not assume exact complementarity or pointwise mixed flatness.

If pointwise relative mixed error is at most epsilon, the substitution is
E=(epsilon mu)^2. In particular E/mu=epsilon^2 mu, NOT epsilon^2.

For a growing sparse family with M,q tending to infinity, k/M tending to
zero, and (C-mu)/q tending to zero, any limiting common bound E/mu is at
least one. This is proved both as a scalar limiting theorem and for actual
varying finite groups and families.

At logarithmic mean, this is a square-root-log RMS scale. It does not
contradict sublogarithmic pointwise errors which are larger than that scale.
It would be invalid to apply the unit-mean error floor unchanged after
renormalizing a logarithmic mean.

## 2. Arbitrarily many DISTINCT jointly flat equal-size templates

The existing phase-complete palettes already give joint mixed estimates
under all translations. The new step verifies enough DISTINCT translates,
without assuming that the base set has trivial translation stabilizer.

For nonempty B in ZMod M, let P be its finite orbit of distinct translates.
Every member has cardinal |B|, and their union is the full group. Hence:

    M <= |P| |B|.

The existing fitting palette theorem permits q|B|<=M before choosing the
modulus. Combining these inequalities gives |P|>=q.

The endpoint exists_large_equal_cardinality_family states: for every c>0,
mean-tuning tolerance tau>0, accuracy 0<eta<=1, requested family size q, and
lower modulus bound N0, there are M>N0, a positive k, and a family P of at
least q DISTINCT k-element sets such that

    |(k^2/M)/log M-c|<tau,

and EVERY pair, including equal members, has:

    |r_(B,C)(z)-k^2/M| <= eta k^2/M,
    |prefixCount(B,C,z,u)-(u/M)k^2/M| <= eta k^2/M,  u<=M.

All pairs share the same actual mean. The endpoint-prefix error is absolute
relative to the FULL mixed mean, not relative to the short interval's own
mean. The family need not be disjoint or nested.

## 3. Consequence for the proposed amplification route

A bound on the number of approximately flat fine templates is not a valid
universal obstruction. Arbitrarily large distinct families already exist
at any requested finite precision.

But the ordinary carry/color operators still transfer the convolution of
INTEGER coarse multiplicities. Joint fine flatness does not manufacture a
fractional coarse harmonic profile. The finite same-modulus family also
provides no changing-modulus prefix compatibility. The first transition
window and the fixed-coefficient Boolean selection problem remain unresolved.

These results neither yield a cutoff-independent family of finite natural
prefixes nor contradict arbitrary witnesses of the original conjecture.
