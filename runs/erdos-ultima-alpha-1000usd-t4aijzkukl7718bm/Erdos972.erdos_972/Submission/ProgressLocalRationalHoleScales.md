# Common-scale local rational exclusions — conjecture still unresolved

The original Spec.lean remains unchanged with its sorry. No sufficient
prime-pair lower bound, lower-tail moment upper bound, or irrational
counterexample is proved. An attempted submission of the unchanged file
was rejected; it is not a completed proof and should not be resubmitted.

## New variable-radius packing

LocalWeightedRationalArcs.lean, namespace
Erdos972LocalWeightedRationalArcs, compiles and audits with only the allowed
axioms. For a finite set of rationals with reduced denominators d<=L,
the open intervals of radius 1/(2Ld) are pairwise disjoint. This follows
from rational separation 1/(d e) and d+e<=2L.

The resulting local estimate, simultaneously for ALL denominators D<=d<=L,
is

    volume.real ((a,b) intersect union rationalArc(Q,r))
       <= (2L/Q)(b-a) + 4L/(Q^2 D) + 2/(Q D).

Both endpoint terms are retained. No dyadic band decomposition is needed.
This is stronger than the earlier fixed-band estimate for the application.

## Actual exceptional sets and low-denominator exclusion

LocalWideBadSlopes.lean compiles and audits. It constructs the finite
reduced-rational center set underlying wideBadSlopes and proves the
original, possibly unreduced boxes are contained in the corresponding
reduced rational arcs.

If |alpha-r|<=epsilon, r.den>D, and

    (epsilon+h) D + 1/Q < 1/r.den,

then (alpha-h,alpha) is disjoint from every arc with reduced denominator
at most D. Combining this with the variable-radius packing gives the same
local measure bound for the ACTUAL wideBadSlopes(A,L,Q).

## A genuine common-scale half-hole theorem

LocalRationalHoleScales.lean compiles and audits. Its principal theorem is

    exists_half_hole_scale

For each prescribed irrational alpha>1, A, and lower bound B, it selects
v>B, v>=2 such that, with N=v^40, L=v^24, Q=v^28,

    volume.real ((alpha-1/(2N),alpha) intersect wideBadSlopes(A,L,Q))
       <= 1/(4N).

There is NO unproved geometric or distribution hypothesis. Selection uses
an actual good rational approximant with denominator q, and v a power of
two such that

    v^26 <= q < 2^26 v^26.

Take D=v^13. The low-denominator separation budget, after multiplication
by q, is bounded by

    1/v^13 + 2^26/(2v) + 2^26/v^2 -> 0.

The local high-denominator measure bound, multiplied by N, is

    1/v^4 + 4/v^5 + 2/v -> 0.

All eventual thresholds are chosen before the one approximant is selected.
No intersection of independently selected existential scale sets occurs.

## Application to the actual lower-tail moment

RationalExcludedDeficit.lean compiles and audits. The theorem

    finite_primeSet_forces_excluded_deficit

proves: if primeSet(alpha) is finite, a<alpha<b, alpha>1 irrational, then
there is ONE B such that for every V there is v>V, v>=2, v>=A, with

    deficitMoment A B (v^40) a b (wideBadSlopes A (v^24) (v^28))
       >= (v^40)^3 / 262144.

Thus the earlier half-hole hypothesis is now fully discharged for the
actual rational exclusions on common metric scales. This is still only a
lower-tail obstruction. A sufficient arithmetic upper bound (for example,
o(N^3) for this deficit moment with these exclusions) is STILL MISSING.
The fixed-interval first moments, upper sieve bounds, and almost-everywhere
results do not supply such a bound.

## Weaker zero-count coverage target

RationalExcludedCoverage.lean now compiles and its principal declarations
audit with only propext, Classical.choice, and Quot.sound.

`finite_primeSet_forces_excluded_missing` proves, under finiteness at the
prescribed irrational alpha, that ONE B works at arbitrarily large common
scales N=v^40:

    volume.real ((a,b) \ (narrowTail B N union wideBadSlopes(A,v^24,v^28)))
       >= 1/(4N).

This concerns absence of ANY half-window prime pair, not failure to have a
linear number of pairs. The generic measure proof retains the half-hole
loss explicitly.

`infinite_of_eventually_small_excluded_missing` proves the corresponding
conditional implication from a strict upper bound <1/(4N), eventually in
v for every fixed B. That upper bound is NOT proved. Merely having it at
arbitrarily large independent scales would not justify intersecting those
scales with the geometric selector.

The weaker coverage target avoids demanding a linear prime-pair count,
but still needs a quantitative arithmetic rate at scale 1/N. Almost-everywhere
coverage and the existing fixed-interval first moments provide no such rate.
No new sufficient arithmetic estimate or irrational counterexample was found.
Spec.lean remains unchanged and unresolved; it has not been resubmitted.
