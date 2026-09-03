# Review of overlapping periodic palettes

The original conjecture remains unresolved. This review adds no theorem and
makes no change to Spec.lean.

## Proposed use of marginal balance

One might compare an old periodic template with a new geometric pattern by
making the latter's residue fibers uniform. Complete fibers give an exact
mixed-count identity, and sufficiently many outer repetitions can reduce
endpoint errors. The obstacle is the simultaneous sparse-density and
resolution requirement, not the complete-fiber identity itself.

A positive relatively self-flat cyclic template of modulus M cannot have
arbitrarily small self-mean. If its error is strictly less than its positive
mean, every integer count is positive and its mean is at least one. Hence
its density d satisfies d^2 M >= 1. At a logarithmic natural scale n, the
required d^2 n is of order log n, so M must be at least of order n/log n.

A new nonempty exactly equal-fiber pattern over all M old residues needs
at least M points. In a period L no larger than the target scale, this
requires d L >= M. Combining this with the preceding density requirements
leads to n = O((log n)^3), which fails at large n. This is the same scalar
resolution issue already addressed by PeriodicMixResolutionExplore, not a
new impossibility theorem for all transition methods.

In particular, choosing old residue sets of size about sqrt(log n) while
using an old modulus about sqrt n silently abandons the self-flat old
palette hypothesis: their cyclic self-mean tends to zero. Such row sets
could conceivably be used in a different collective construction, but the
old palette estimates would no longer apply.

## Nearby primes

MixedPrimeIntervalExplore handles two parameter intervals in ONE prime
field. It does not compare integer curves with different prime moduli.
NearbyPrimeCarryExplore explicitly retains a quotient depending on the
curve variable when moduli differ. A bounded number of high-digit carry
classes does not eliminate that quotient. No uniform logarithmic-scale
mixed estimate has been derived from these identities.

## Other possibilities reviewed, not proved

Splitting old templates into colors and distributing colors among new
blocks would avoid literal copies only if the resulting weighted
color-pair counts can be controlled. Demanding uniformity of the entire
color-pair matrix is stronger than necessary and introduces another coarse
representation problem. No tailored weighted estimate was established.

A finer new period alone does not solve the infinite transition: retaining
an old prefix makes its mixed contributions substantial at targets
comparable to the cut. Small-prefix perturbation estimates apply far above
the cut, leaving that transition window uncovered.

No compatible changing-source chain, uniform quadratic rounding, or
universal contradiction was obtained in this review.
