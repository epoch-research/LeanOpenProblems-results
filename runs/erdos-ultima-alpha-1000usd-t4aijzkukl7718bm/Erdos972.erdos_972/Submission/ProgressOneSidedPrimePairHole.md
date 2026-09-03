# One-sided metric obstruction — original conjecture still unresolved

Spec.lean is unchanged and retains its original sorry. No proof or irrational
counterexample has been found, and no incomplete proof has been submitted.

## New verified file

`Submission/OneSidedPrimePairHole.lean`, namespace
`Erdos972OneSidedPrimePairHole`.

Define `narrowTail B N` using genuine primes p,q with

    B < p <= N,   q < beta*p < q+1/2.

`transfer_from_left` proves that a narrow pair at beta transfers to an original
floor-prime pair at alpha whenever

    alpha - 1/(2N) < beta < alpha.

The proof keeps both strict endpoints and the upper input cutoff p<=N.
It needs neither irrationality nor a positivity assumption on alpha: the prime
q and the inequalities already imply the nonnegativity needed for the floor.

`left_interval_subset_compl` therefore proves that if every original pair at
alpha has input at most B, the ENTIRE interval

    (alpha - 1/(2N), alpha)

is disjoint from `narrowTail B N`, at every positive N.

`missing_measure_lower` turns this into an exact lower bound 1/(2N) for the
missing half-window pairs in any ambient interval containing that hole.
`finite_primeSet_forces_missing_measure` chooses ONE B from finiteness and
proves the bound at EVERY sufficiently large N in each fixed interval
(a,b) with a<alpha<b. No endpoint separation or Diophantine-type assumption
is used. This is a finite-scale missing-set bound, not a positive measure
claim about slopes that fail infinitude.

`moment_lower_outside` retains an arbitrary excluded set E. If the WHOLE hole
is outside E and a real function F vanishes off `narrowTail B N`, then, for
c>=0 and any natural k, assuming the displayed moment is integrable,

    integral_(beta in (a,b)\E) |F(beta)-c*N|^k
        >= (c*N)^k/(2N).

This is a genuine lower obstruction under finiteness, not a moment upper
bound. The hypotheses concerning E and integrability are explicit.

All four printed principal axiom audits contain only propext,
Classical.choice, and Quot.sound. The complete file compiles with no sorry.

## What remains missing

The existing metric proofs give first-moment mass on FIXED slope intervals
and a sieve upper bound outside small rational neighborhoods. They give no
upper bound o(1/N) for the finite-scale missing set, and no moment upper bound
o(N^(k-1)) outside excluded sets that avoid the whole one-sided hole.

A global such moment bound cannot simply be expected: integer slopes already
have no prime pairs and generate holes of this size. Any proposed quantitative
metric upgrade must handle rational resonances and choose its good scales
for the prescribed irrational alpha. No adequate arithmetic estimate was
proved in this continuation. The new hole theorem is not a settlement.

## Follow-up: partial holes and local rational arcs

Two additional lemmas in `OneSidedPrimePairHole.lean` now compile:

- `moment_lower_remaining` only uses the part of the hole outside a measurable
  excluded set E. Its lower bound is

      volume.real(hole \\ E) * (c*N)^k.

- `moment_lower_of_half_hole` assumes the LOCAL loss

      volume.real(hole intersect E) <= 1/(4N)

  and concludes a moment lower bound `(c*N)^k/(4N)`. Complete disjointness
  between the hole and E is no longer necessary. No local loss estimate is
  asserted for the actual full rational exceptional set in this lemma.

New file `LocalRationalArcMeasure.lean`, namespace
`Erdos972LocalRationalArcMeasure`, supplies geometric estimates:

- `spaced_card_bound`: delta-separated points in [a,b] number at most
  `(b-a)/delta+1`. Proved by disjoint interval packing and Lebesgue measure.
- `rational_separation`: distinct rationals r,s are separated by at least
  `1/(r.den*s.den)`.
- `rational_band_local_measure`: for any finite rational set S whose reduced
  denominators lie in [D,2D], D,Q>0, the arcs of radius `1/(Q*r.den)` satisfy

      volume.real((a,b) intersect union_(r in S) arc(Q,r))
        <= (8D/Q)*(b-a) + 16/Q^2 + 2/(D*Q).

The local bound retains both endpoint terms. The proof filters to centers
that can meet the interval, uses separation `1/(4D^2)`, and does not assume
that a qualitative global small-measure estimate controls a shrinking hole.

These added declarations compile and audit with only the permitted axioms.
No combined all-denominator local bound, common-scale half-hole theorem for
the actual exceptional sets, or sufficient arithmetic moment UPPER bound
was proved. The original conjecture is still unresolved.
