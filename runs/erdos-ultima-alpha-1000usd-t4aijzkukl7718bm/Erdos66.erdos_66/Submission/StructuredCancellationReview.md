# Review of structured cancellation routes

## Status

This review produced no new verified theorem settling Erdős 66. Spec.lean
is unchanged with its original sorry. No proof or disproof was submitted.
The observations below are diagnostics, not Lean-verified new results.

## Exact target already available in Lean

For the exact fractional harmonic profile p, let e=1_A-p. The checked
RoundingExplore.lean identity is

    r_A(n)=H_(n+1)+2(e*p)(n)+(e*e)(n).

Bounded prefix discrepancy (or the checked weaker o(log n) discrepancy)
makes the mixed term negligible after division by log n. The missing
existence theorem still concerns one actual Boolean rounding for which
(e*e)(n)/log n tends to zero at every sufficiently large target.

The existing moving-window estimates are signed averages. They do not
bound pointwise quadratic error. BoundedDiscrepancyPeaksExplore.lean
already supplies actual roundings with unbounded normalized peaks, so a
universal deduction from prefix discrepancy is unavailable.

## Complementary signs / sparse flat-polynomial idea

Complementary autocorrelation identities do not directly control the
self-convolution here. Replacing a reversed factor by the original factor
is invalid. Moreover, a freely selected signed sequence is not the same
as a Boolean rounding error: each coordinate must be either -p_n or 1-p_n.
No sparse complementary construction satisfying those restrictions and
the needed self-convolution estimate was obtained.

The canonical floor rounding was also reconsidered geometrically through
inverse cumulative locations. Local near-arithmetic-progressions suggest
square-root-logarithmic resonances, but no uniform lattice-count estimate
at logarithmic mean was proved. These heuristics neither establish nor
refute the canonical rounding's desired limit.

## Colored density-preserving lifts

A possible fiber lift uses q-point affine lines in a q-by-q field plane:
distinct directions have mixed count one, while a line's self-count has
peaks of size q. It is insufficient to average all same-color coarse pairs
without tracking their individual fine targets. Conversely, suppressing
every same-color term requires an actual simultaneous coloring theorem;
random coloring at logarithmic mean does not automatically give it.

The earlier ComplementaryFamilyBarrierProgress.md and SidonColorProgress.md
already contain relevant checked tradeoffs. No new coloring satisfying
all target budgets, no Boolean infinite lift, and no integer carry/prefix
compatibility theorem was derived in this review.

## Repair review

Shared-point incidence identities already cover unrestricted reuse, but
they do not construct the concentration of repair incidences needed for
the actual exceptional sets. Two-sided local resets also do not provide
a cumulative sublogarithmic error estimate. The checked counterexample
in HostResetAbsorptionProgress.md warns against exchanging a growing-target
limit with coordinatewise convergence.

## Unresolved

There is still no justified passage from these finite identities or
averaged estimates to the existential limit in Spec.lean. In particular,
none of these reviews supplies a proof of its negation either.
