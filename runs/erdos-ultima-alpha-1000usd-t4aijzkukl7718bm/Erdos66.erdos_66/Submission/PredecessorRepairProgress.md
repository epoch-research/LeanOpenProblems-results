# Finite count-preserving predecessor repair

## Status

The original theorem in `Spec.lean` is unchanged and unresolved. This
continuation proves a finite one-target repair and verifies its candidate
bounds. It does not produce an infinite set with the requested limit.

## Checked production files

1. `PredecessorCellExplore.lean`
2. `BoundedFiberSelectionExplore.lean`
3. `CellSidonSelectionExplore.lean`
4. `NaturalSymmetricPacketExplore.lean`
5. `PredecessorPacketRepairExplore.lean`
6. `PredecessorCandidateDegreeExplore.lean`
7. `IntervalPredecessorRepairExplore.lean`
8. `PredecessorRepairParametersExplore.lean`

All compile and have current oleans. The preceding `ProfileLowerGapExplore.lean`
has also now been explicitly audited. `PredecessorRepairFullAxiomCheck.lean`
checks the principal declarations; only propext, Classical.choice, and
Quot.sound occur. No placeholders or new axioms occur in the production files.

## Geometry

`predecessor A u = Nat.findGreatest (fun a => a in A) u`.

If an old point exists through u, the predecessor is in A. There is no old
point strictly between the predecessor and u. Distinct predecessor cells
are ordered and disjoint. For a finite set F of new points, if predecessor
is injective on F, removing its image D and inserting F gives

    -1 <= count(new,N) - count(A,N) <= 0

for every N, regardless of |F|. Both supports have equal cardinality.

The exact fractional-profile square lower bound from the prior continuation
implies that bounded-prefix-discrepancy roundings have an old point in the
last H positions through u whenever

    H <= u+1,   2D sqrt(u+1) < H.

Thus predecessor distance is less than H and each predecessor fiber has at
most H candidate integer points. These conclusions require old-point
existence; the default value 0 of findGreatest is not treated as an old point.

## Selection

`bounded_fiber_indicator_bound` permits up to H bad values of one coordinate
and bounds the uniform event probability by H/q. The finite selection
criterion sums separate fiber costs for separate forbidden events.

`exists_cell_sidon_avoid_and_hits` combines:

* Sidon selection (including injectivity);
* avoidance of a forbidden choice set B;
* distinct cells for all chosen endpoints;
* simultaneous bounds on hit counts at a finite family T.

For k choices, b endpoint types, q possible values, and cell fibers at most H,
the criterion is

    (k^4 + k^2 b^2 H + k |B|)/q
      + |T| exp(k exp(t) K/q - t R) < 1.

Within each individual choice the endpoint cells must already be distinct.
The theorem enforces all cross-choice cell distinctions.

## Symmetric-packet accounting

The natural-number packet is E union (n-E), with E strictly below n/2.
If E is Sidon, it has |F|=2|E|, r_F(n)=|F|, and r_F(z)<=6 for z!=n.
A packet disjoint from old A has no new/old mixed representations at n.
If deleted D is a subset of A and pairs(D,A,n)=0, then

    r_((A\D) union F)(n) = r_A(n) + |F|.

This differs from the previous anchored-insertion formula: here the central
representations are all new/new, not new/old.

## Finite repair theorem

`exists_predecessor_packet_repair` uses choices x(a), n-x(a), deletes both
predecessors, and returns D,F with

* D subset A, F disjoint from A;
* |D|=|F|=2m;
* prefix difference in [-1,0] at every cutoff;
* exact central gain 2m;
* r_F(z)<=6 for every z!=n;
* |r_new(z)-r_A(z)| < 4R+6 at every tested z!=n.

Its forbidden choices include inserted points already in A and predecessor
points having an old partner at n. Its hit choices include both inserted/old
and deleted/old partners. Both endpoints are tested.

## Candidate degrees

`predecessor_candidate_degrees` avoids the long-range difference-count issue
in the earlier reflection-candidate route.

If both endpoint maps are injective and lie in windows of width W, every
such old-point window has cardinality at most U, and predecessor fibers have
size at most H, then

    |badChoices| <= 2U + 2H r_A(n),
    |swapHits(z)| <= 2U + 2H r_A(z).

The deleted-point estimate maps choices to

    {r in A : r<=z and z-r in A},

whose cardinality is exactly r_A(z). It does NOT assume an unrestricted
difference-correlation bound.

`natural_window_bound` proves U <= sqrt(2WV) under the uniform finite
representation envelope r_A(z)<=V.

`exists_interval_predecessor_repair` specializes to x(i)=L+i, i:Fin W, with

    W>0,  2(L+W)+H<=n,

and old-predecessor membership and gap <H in the two endpoint windows. Its
sole sampling inequality uses

    K0 = K = 2 sqrt(2WV) + 2HV

and cell-collision cost 4m^2H. It gives the full finite repair conclusions
above. The gap/membership hypotheses are local to the endpoint windows; a
finite set is not erroneously assumed to approximate the divergent profile
at every prefix.

## Asymptotic parameter check

`eventually_predecessor_selection_small` proves that for

    q >= N/24, m <= D log N, H <= G sqrt N,
    K0,K <= B sqrt N log N, |T| <= N^h+1,

one can take the same fixed tilt t=32(h+1)/epsilon and R=epsilon log N/16 as
in the existing one-target repair parameter lemma. The extra collision cost
4m^2H is absorbed into the coefficient B+4DG of sqrt(N) log(N).

This is a checked parameter theorem, not yet an all-natural-target repair
of an infinite old set. The cutoff-transfer and far-target estimates for
that stronger corollary have not been written here.

## Main unresolved issues

The finite repair and its asymptotic feasibility do not eliminate the known
exceptional sets. At small fixed tolerances their known counting exponents
can be arbitrarily close to one, whereas the existing completion schedules
need sub-square-root exception counts and the exact asymptotic upper
coefficient. Repeating one-target repairs also needs a proof controlling
all accumulated signed collateral and the prefix profile.

No new exception-count exponent, compatible all-target schedule, or universal
contradiction has been obtained. Do not insert any of these auxiliary
lemmas into Spec.lean as if they proved the original existential assertion.

## Lean notes

Specializing predicates to finite types frequently changes Decidable
instances. Displayed-identical Finset.filter expressions may fail exact or
rw. `convert ... using 1; congr 2` (or congr 3 through casts) often resolves
these proof-independent instance differences. When predicates differ,
prove Finset equality by extensionality. Expanding card_filter alone does
not remove the corresponding if-decidability differences.

For Sets.MapsTo into a concrete interval, explicitly `change ... in Ico ...`
before `Finset.mem_Ico.mpr`; otherwise metavariables can be instantiated by
omega with an unrelated available interval inequality.

## Subsequent update: separated infinite iteration completed

`SeparatedPredecessorRepairProgress.md` records the now-checked all-target
infinite-host one-target theorem and a separated infinite signed iteration.
They resolve the cutoff-transfer, far-target, and nonaccumulating prefix
bookkeeping for that sparse schedule. They still do not handle the denser
exceptional sets needed for the original conjecture.
