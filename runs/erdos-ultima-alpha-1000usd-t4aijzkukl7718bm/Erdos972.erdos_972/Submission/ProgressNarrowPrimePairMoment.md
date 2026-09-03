# Genuine-prime lower-tail moment — original conjecture unresolved

Spec.lean remains unchanged with its original sorry. No prime-pair lower bound
or irrational counterexample has been proved, and no incomplete proof has
been submitted.

## New verified file

`Submission/NarrowPrimePairMoment.lean`, namespace
`Erdos972NarrowPrimePairMoment`.

`narrowPairs A B N beta` is the finite sum of log(p)log(q) over genuine primes
with B<p<=N and 0<q<=A*p, using the strict half-window

    q < beta*p < q+1/2.

The file proves positivity, an explicit finite uniform bound, measurability,
global integrability of the count, and vanishing off `narrowTail B N`.
All powers of its centered absolute deviation are proved integrable on
bounded intervals after removal of an arbitrary set. There is no remaining
integrability hypothesis when the earlier hole lemma is applied to this
actual count.

## Actual fourth-moment obstruction

`fourthMoment` integrates |narrowPairs-N/2|^4 over (a,b)\E.
`fourthMoment_lower_of_half_hole` proves the lower bound N^3/64 if the
original slope alpha has no pairs beyond B and E removes at most 1/(4N)
from the one-sided interval (alpha-1/(2N),alpha).

`finite_primeSet_forces_fourth_moment` selects ONE B from finiteness and
proves this at every sufficiently large N, uniformly over all measurable E
satisfying the local loss bound.

## Weaker, one-sided target

A sharp full centered-moment upper estimate is unnecessary. Define

    deficitMoment = integral_(beta in (a,b)\E)
      max(N/16 - narrowPairs A B N beta, 0)^4.

This ignores counts above the low threshold N/16. Its integrability is
proved by the constant envelope (N/16)^4. The exact identity

    |min(x,t)-t| = max(t-x,0)

allows application of the verified moment obstruction to the capped count.

`deficitMoment_lower_of_half_hole` proves

    N^3/262144 <= deficitMoment

under the same finiteness cutoff and half-hole assumptions.
`finite_primeSet_forces_deficit_moment` again chooses one B and retains
ALL sufficiently large N and ALL admissible measurable E.

An arithmetic upper estimate o(N^3) for this lower-tail moment on suitable
common scales would suffice; it is NOT proved or assumed as a theorem here.

## A checked limitation on the proposed upper estimate

`global_deficit_cubic_lower` proves, unconditionally, for every A and N>0,

    N^3/262144 <= deficitMoment A 0 N 1 3 empty.

It uses the integer slope two, whose original prime-pair set is empty.
Consequently rational neighborhoods cannot simply be omitted from a proposed
global o(N^3) moment estimate. This is not a disproof of Erdos 972, which
requires irrational slopes.

## Verification and remaining work

The complete file compiles. All printed principal axiom audits contain only
propext, Classical.choice, and Quot.sound.

No sufficient moment upper bound or quantitative lower-tail coverage estimate
was obtained. The existing fixed-interval first moments and sieve upper
bounds do not provide it. The local rational-band estimate in
LocalRationalArcMeasure.lean has not yet been assembled into an all-denominator,
common-scale half-hole theorem for the actual exceptional sets. Neither that
geometric step nor the new actual-count obstruction settles the conjecture.
