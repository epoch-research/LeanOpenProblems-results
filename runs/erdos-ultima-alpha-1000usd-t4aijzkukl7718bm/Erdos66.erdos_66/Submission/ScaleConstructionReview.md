# Further scale-construction review

## Status

No proof or disproof of the original conjecture was obtained in this review.
`Submission/Spec.lean` remains unchanged with its original `sorry`.

## Small-step thinning

The checked mixed-thinning theorem concerns a selected set D against fixed
unthinned sets. It must not be read as a self-count estimate for D. At a
retention probability theta, the mixed scale is theta*mu whereas the
self-count scale is approximately theta^2*mu. The former can be well above
logarithmic size while the latter remains at the critical logarithmic size.

Splitting a large thinning into many small steps has not resolved this.
Errors in successive stages cannot simply be discarded or assumed to
contract. No martingale or deterministic selection theorem controlling the
entire sequence to vanishing relative self-count error has been proved.

## Digit and rotation constructions

Compatible digit systems, low-discrepancy rotations, and refinements of
finite-field graph templates were reconsidered. None supplied an estimate
for the integer mixed counts across scales. Equidistribution on a continuous
circle does not by itself give the required short-orbit count, and finite
field addition does not identify with integer addition without carry control.

A field tower with fixed old parameter sets still has the wrong intermediate
prefix density. Allowing parameter sets to vary within a tower might change
that density, but the needed restricted-fiber convolution estimates remain
unproved. No finite or infinite construction from this proposal is claimed.

## Analytic scope

The strengthened fluctuation theorem gives arbitrarily large deviations
above every a*sqrt(log n) with a^2<c. It does not force deviations comparable
to log n. No bootstrap from the original relative limit to a forbidden
square-root error estimate has been established.

## Packet repair revisited

A finite flat packet could cover a whole target interval at a small mean,
so its self-count upper bound alone is not the main obstacle. The missing
estimate is its mixed convolution with the accumulated set, uniformly over
all other targets. Translating a fixed packet only translates that mixed
convolution and does not reduce its maximum. Choosing many random shifts
therefore does not automatically eliminate a large reflected-template peak.

It is also not enough to cover an arbitrary exceptional target set cheaply:
no theorem has been proved giving both the required coverage and a uniform
o(log n) bound on all collateral counts. No packet-repair construction
settling the conjecture follows from the existing finite flatness or sparse
completion theorems.

These observations are limitations of the reviewed methods, not a universal
nonexistence theorem.
