# Joint two-thickness palettes and endpoint prefixes

## Status

The original conjecture remains unresolved. Spec.lean is unchanged and still
contains its original sorry. No proof submission has been made.

Four production files compile, with current oleans:

1. PeriodicPatternComparisonExplore.lean
2. JointCoprimeThicknessExplore.lean
3. UniformJointCoprimeThicknessExplore.lean
4. JointThicknessPrefixExplore.lean

JointCoprimeThicknessAudit.lean audits 16 principal declarations. Each depends
only on propext, Classical.choice, and Quot.sound. The production files contain
no placeholders or new axioms. JointThicknessChecks.lean is a scratch file
with failed name checks, not a production dependency.

## Exact comparison of periodic descriptions

`Erdos66PeriodicPatternComparison.periodic_mixed_count_comparison`:

For positive M,N,a,b, assume M*a=N*b. If B,C in ZMod M and D,E in ZMod N
have the same natural-index membership patterns, then for every natural n,

    a * cyclicCount(M,B,C,n) = b * cyclicCount(N,D,E,n).

The proof lifts both pairs to the common period and uses the existing exact
outer-lift count identity. Equality is about the full membership patterns,
not just agreement on a short initial interval.

## Vertical rescaling and self-type counts

`verticalPreimage_fiber_card` proves that an invertible vertical coordinate
rescaling preserves every plane mixed fiber, with the target rescaled too.
It works for arbitrary positive p and a unit in ZMod p; primality is not needed.

Write M=p*(p*(K*L)), and assume p,K,L positive, p coprime to K*L, and K coprime
to L. The previous natural-index thickening identifications now give exact
count comparisons:

    K * r(left(B),left(C)) = L * r(old K-thickening of rescaled B,C),
    L * r(right(B),right(C)) = K * r(old L-thickening of rescaled B,C).

These are `left_count_comparison` and `right_count_comparison`. The old cyclic
moduli are (p*K)^2 and (p*L)^2 respectively. The common-multiple identities
are ring equalities, so there is no silent transport of incompatible ZMod
instances.

If every plane mixed fiber of B,C has mean mu and error E, then:

    left/left:   |r - KL mu| <= KL E + 2L(mu+E),
    right/right: |r - KL mu| <= KL E + 2K(mu+E),
    left/right:  |r - KL mu| <= KL E + min(K,L)(mu+E).

The last estimate is the previously checked mixed-thickness theorem. New
commutativity lemmas cover right/left. The self-type results are for arbitrary
B,C, not just B=C.

`twoSet` indexes left/right by a Boolean. `twoSet_error` packages all four
pair types with the common error

    KL E + 2 max(K,L)(mu+E).

All side choices have cardinality KL |B|. Their actual mixed mean is exactly

    KL |B| |C| / p^2,

independent of the side choices (`twoSet_actualMean`).

## Unconditional uniform joint family

`every_prime_joint_coprime_thickness_family` fixes eta in (0,1] and a finite
level bound H, and then chooses D,K0. For every prime p above

    max(8*(D*H)+2, 2*(D*H)^2),

it selects one nested plane family B_i BEFORE K,L. For all later positive
admissible thicknesses with

    K0 <= min(K,L),

all i,j<=H, all four side pairs, and every target in ZMod M satisfy

    |r - 4D^2 KL i j| <= eta * (4D^2 KL i j).

Both thicknesses must be large in this joint theorem. Do not substitute the
weaker max(K,L) condition from the earlier cross-type-only theorem.

## Endpoint prefixes after a common outer lift

`outerTwoSet` repeats the common-period sets R times, in ZMod(M*R). Its
cardinality is RKL|B|.

`outerTwoSet_prefix_error` applies the generic outer-prefix engine to all
four pair types. If their common cyclic mean is mu, relative error sigma,
sigma<=eta/4, and 2<=eta R, then every endpoint prefix has error at most
eta R mu about its length fraction of R mu.

`every_prime_joint_prefix_family` combines this with the unconditional joint
family. The plane family is chosen before K,L,R. For every later admissible
choice it supplies both full mixed-count estimates and endpoint-prefix
estimates about

    4 D^2 R K L i j.

This is a finite-period statement. Prefix error is relative to the FULL
mixed mean, not to the mean inside a short prefix. This distinction remains
important for growing-height or fixed-initial-cutoff arguments.

## Remaining gap

This continuation removes the missing self-type estimates from the earlier
same-prime compatibility result and supplies its endpoint-prefix transfer.
It does not compare different primes, produce a single infinite set, or
establish finite-prefix feasibility with one coefficient and thresholds
chosen independently of the final cutoff.

Further consideration of changing primes, field towers, and correction
methods supplied no proof of that missing step. In particular, separate
field-template flatness and same-prime mixed flatness cannot be silently
combined into cross-prime short-interval control. No universal obstruction
to the original existential conjecture has been obtained either.
