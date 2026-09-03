# Joint mixed counts for one finite monotone-profile rounding operator

## Original conjecture status

The conjecture in Submission/Spec.lean remains unresolved. Spec.lean is
unchanged with its original sorry. No proof has been submitted.

## New unconditional theorem

JointMonotoneProfileOperatorExplore.lean proves

    Erdos66JointMonotoneProfileOperator.exists_joint_bounded_monotone_rounding_operator.

For fixed c,delta>0 and W>=1, arbitrarily large M admit ONE map Phi from
real sequences to finite subsets of [0,M), selected before any profile.
The map preserves agreement of input prefixes exactly, both in membership
and in representation counts below the cutoff.

For EVERY pair f,g which are antitone on [0,M) and take values in [1,W],
for EVERY natural target n, the same map satisfies

    |pairs(Phi(f),Phi(g),n)/log M - c normMixedConv(M,f,g,n)| <= delta,

where

    normMixedConv(M,f,g,n)
      = (1/M) sum_{0<=x<M, x<=n, n-x<M} f(x) g(n-x).

The profiles need not agree, have the same interval partition, or be chosen
in advance. This includes the previous self-count result by setting f=g.

## Direct mixed proof -- no polarization assumption

MixedPaletteAssemblyExplore.lean proves the actual mixed count estimate
for TWO independent disjoint spatial arrangements of the same fixed height
palette. With nominal mean mu, height weights w_i, cardinality factor R,
and mixed endpoint-prefix tolerance eta,

    |pairs(A_1,A_2,n)-mu mixedProfile(n)|
      <= [(1+2 eta)R^2-1] mu (sum_i w_i)^2.

Each pair of interval pieces uses the already checked integer slice formula
and the JOINT mixed-prefix hypothesis for its two palette members. Separate
self-flatness is not substituted for that hypothesis.

MixedStepBridgeExplore.lean identifies mixedProfile exactly with
normMixedConv of the two step functions, including every carry and empty
interval case.

MixedProfileQuantizationExplore.lean proves the two-profile inequality

    |normMixedConv(F,G)-normMixedConv(f,g)| <= (R^2-1)W^2

when 0<=f,g<=W, f<=F<=Rf, and g<=G<=Rg.

UniversalMixedHeightExplore.lean chooses one list of palette members that
works for every pair of later spatial arrangements. The final theorem uses
the same fixed height grid as the preceding monotone-operator construction,
decomposes each profile into its own interval fibers, and adds the spatial
and height-quantization errors.

## Verification

All five new production files compile and have built oleans:

* MixedPaletteAssemblyExplore.lean
* MixedStepBridgeExplore.lean
* MixedProfileQuantizationExplore.lean
* UniversalMixedHeightExplore.lean
* JointMonotoneProfileOperatorExplore.lean

JointMonotoneOperatorAudit.lean checks the principal declarations. Only
propext, Classical.choice, and Quot.sound occur. The production files contain
no sorries or new axioms.

## Remaining infinite issue

This is joint compatibility for DIFFERENT PROFILES of the SAME finite
operator and modulus. It is not compatibility between different operators
or moduli. The height range W is still fixed before the modulus, with a
threshold depending on W and the precision.

Consequently the theorem does not control mixed counts when one natural
prefix is retained and the construction moves to a different modulus. Nor
does it supply the growing height range needed to approximate the harmonic
fractional profile uniformly down to a fixed natural cutoff. The finite-prefix
compactness condition for the original conjecture is still missing.
