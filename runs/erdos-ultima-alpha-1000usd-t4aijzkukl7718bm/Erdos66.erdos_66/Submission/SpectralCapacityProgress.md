# Scalar multiscale energy and a conditional capacity test

## Original task status

Erdos66.erdos_66 remains unproved and undisproved. Submission/Spec.lean is
unchanged with its original sorry. No final proof was submitted.

## Checked production files

* DyadicPrefixEnergyExplore.lean
* SpectralCapacityExplore.lean

Both compile without warnings and have current oleans. The two files contain
167 lines and no placeholders. SpectralCapacityAudit.lean audits all twelve
definition/lemma/theorem declarations. Its log uses only propext,
Classical.choice, and Quot.sound.

## Scalar estimate

For x : Nat -> Real define

    running(x,0) = x(0),
    running(x,n+1) = x(n+1) + running(x,n)/2.

The finite estimate is

    sum_(j<N) running(x,j)^2 <= 4 sum_(j<N) x(j)^2.

A stronger induction retains the final squared term as a potential. Hence
square summability of x implies square summability of running(x).

Writing S(n)=sum_(j<=n) y(j), if

    y(n)^2 <= 4^n E(n)

and E is summable, then S(n)^2/4^n is summable. In particular it cannot be
bounded below by c/(n+1) at every sufficiently late n for any c>0.

## Conditional capacity consequence

Suppose the same block-energy assumptions hold and an additional sequence q
satisfies, eventually,

    4^n <= q(n) S(n).

Then for every C>0 and every N there exists n>=N such that

    q(n)^2 > C 4^n (n+1).

The finite form says that imposing q(n)^2<=C 4^n(n+1) at all n<L forces

    sum_(n<L) 1/[C(n+1)] <= 4 sum_(n<L) E(n).

Thus this particular finite-energy mechanism has a harmonic-in-resolution
cost at the critical capacity scale.

## Application status and caution

The motivation was a proposed shrinking-neighborhood construction from a
single singular measure with sufficiently regular self-convolution. These
new files prove ONLY the scalar statements above. No Fourier expansion,
measure-support estimate, or measure-theoretic instantiation is formalized
here. In particular, no theorem about all singular measures is being claimed
as a checked consequence in this development.

More importantly, no sequences satisfying these hypotheses were extracted
from the original hypothetical natural-number witness. Natural prefix
agreement does not by itself give a compatible spectral tower, and taking
rapidly separated subsequences changes the scale budget. This conditional
criterion is therefore not a disproof of the conjecture.

The translation-window review also did not produce the missing uniform
short-interval or changing-period estimate. The existing expected-mass
rotation discrepancy theorem was located in RotationMassProgress.md; it
already addresses narrow rotation windows, but does not construct the
required sparse windows or their mixed convolutions.
