# Approximate complementary-family energy budget

## Status

The original conjecture is unresolved; Spec.lean is unchanged. These are
finite-family restrictions, not a disproof of the existential conjecture.

## Checked files and audit

* ApproximateComplementarityExplore.lean
* ComplementarityErrorFloorExplore.lean

Both compile with built oleans. ApproximateComplementarityAudit.lean audits
nine principal declarations; its log reports only propext, Classical.choice,
and Quot.sound.

## Finite inequality

Let q sets B_i each have k elements in a finite additive group of order k^2.
Suppose all self-representation counts are at most C and every distinct-pair
centered convolution has squared L2 norm at most k^2 E. Then

    q(k-1) <= (k+1)[C-1+(q-1)E].

Here E bounds mean SQUARED error about the unit mean, not root-mean-square
error. The proof sums the centered autocorrelation vectors. Their sum has
mean zero and coordinate q(k-1) at the identity. The zero-mean coordinate
inequality and the exact mixed energy identity imply

    k^2[q(k-1)]^2 <= (k^2-1) sum_(i,j) centeredEnergy(B_i,B_j).

The self cap bounds a diagonal energy by k^2(C-1); the assumed mixed bound
controls the other terms. E=0 recovers the exact-complementarity restriction.

## Growing-family consequence

If q,k tend to infinity, C/q tends to zero, and a common distinct-pair
mean-square upper bound E tends to e, then 1<=e. This is checked both as a
scalar limit theorem and for actual varying finite groups and color types.

## What it does not prove

It does not rule out aggregate averaging of many mixed pairs: individual
pair errors may be order one while their combined error is smaller than
the combined mean. It supplies neither an infinite compatible palette
construction nor a universal logarithmic fluctuation lower bound.
