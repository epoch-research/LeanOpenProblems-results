# Rotation-carrier continuation: no settlement

The original conjecture remains unresolved. No Lean source was changed in
this review, no new exponent was obtained, and no incomplete proof was
submitted. Spec.lean retains its sole admission for 0 < epsilon < 1/3;
the completed endpoint is eventual M(N) >= N^(2/3).

## Bounded rotations

The existing SmallRotationLifting theorem needs its explicit digit bound
3*Q*H < B. Its denominator Q is not a harmless normalized real coefficient:
dividing a rotation row by its denominator does not preserve the integer
hypothesis of signed_zero. The Gaussian-factor restrictions and the
common-residue lower cutoff were not found to control the remaining
large-parameter collisions with a power saving. No bound for their count
in an arithmetically selected near-linear carrier was proved.

## Modular target variants

The affine carry-target construction is already covered uniformly in its
slope and intercept by AffineParabolaHeightBound. Varying those parameters
is not an unexamined escape from its cubic height/cardinality ceiling.
QuadraticCarryParabola is a genuinely broader positive finite criterion,
but still requires many small representatives. No parameters producing
such a family were found here, and the affine ceiling was not applied to
this broader criterion without proof.

Finite checksum examples remain finite examples, not a uniform rule in
the radix or a valid concatenation theorem.

## Full allowed-alphabet permutation carrier

Rechecked the actual statement of AllowedAlphabetSwapRigidity.
Its generic theorem identifies equal positive square differences when BOTH
root pairs have a one-transposition shape. Its application to permutations
is complete, but does not decompose an arbitrary equal square difference
into such a pair of shapes. A general permutation pair may change many
positions. Cancelling a digit transposition is not known to preserve the
original norm equation, so it does not currently give an induction proving
Sidonness of the full family.

No arbitrary-permutation rigidity proof or collision certificate was
obtained. The old restricted affine-repair UNSAT and timeout results were
not treated as completeness results, and no blind numerical search was
launched. The conditional theorem
AllowedAlphabetCandidate.near_linear_of_eventually_sidon remains unusable
without its explicit Sidon hypothesis.

## Scope

These are unsuccessful reviews, not impossibility theorems for all
rotation-based, modular, or permutation constructions. There is still no
actual Sidon exponent above two thirds, near-linear selector, or fixed-power
upper bound for the unrestricted maximum. Nothing here proves the negation
of the original quantified conjecture.

Main-file SHA-256 remains:

    257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940

Original theorem: line 17276. Sole admission: line 17287.
Sole import unchanged: import FormalConjecturesUtil.
