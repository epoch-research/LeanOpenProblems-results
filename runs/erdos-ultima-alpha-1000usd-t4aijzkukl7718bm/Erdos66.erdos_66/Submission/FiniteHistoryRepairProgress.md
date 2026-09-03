# Finite-history stability and bracket-only restoration

## Original task status

The conjecture in `Submission/Spec.lean` remains unresolved. Its import,
statement, and original `sorry` are unchanged. No valid proof or disproof
submission is available.

## Verified sources

1. FiniteHistoryIncidenceExplore.lean
2. BoundaryMarginAllowanceExplore.lean
3. FiniteHistoryBatchClippingExplore.lean
4. BracketWindowOccupancyExplore.lean
5. BracketOnlyRestorationExplore.lean
6. CenterCapBatchClippingExplore.lean
7. FiniteHistoryRepresentationExplore.lean
8. QuarticHistoryBatchClippingExplore.lean

All eight compile without warnings and have current oleans.
`FiniteHistoryRepairAudit.lean` audits all 19 theorem/lemma declarations;
each uses only propext, Classical.choice, and Quot.sound.

## 1. Finite history changes remote incidences by a constant

Let A satisfy exact harmonic brackets, and let B agree with A at every
coordinate at least U. No brackets are needed for B in this estimate.
If U<=N and U*profile(N)<=1/2, then:

* fiber(B,N,n,z) <= fiber(A,N,n,z)+2 for every n,z;
* boundary(B,d,n) <= boundary(A,d,n)+2 if d>=2 and n>=2N;
* |r_B(n)-r_A(n)| <= 4 if n>=2N.

For the triple statement, the first two coordinates are at least N and
therefore unchanged. Any new triple has its third coordinate below U.
Its first coordinate lies in one reflected length-U interval, whose start
is clipped to be at least N. Exact brackets give occupancy <=2+U*profile(N),
which is at most 2.5, and thus at most TWO by integrality.

The boundary and representation estimates similarly inject changed
contributions into one short window of old tail points. These bounds depend
on the history support, not on its cardinality or number of stages.

Uniformly for U<=W, the mass hypothesis holds for every N>=W^3, eventually
in W. This follows from

    W*profile(W^3) <= 6 log(W)/sqrt(W) -> 0.

The earlier, looser W^32 versions remain available unchanged.

## 2. Brackets alone bound short candidate windows

For ANY exact harmonic-bracket host A and ANY interval start a,

    count(A intersect [a,a+w)) <= 2 + prefixSum(profile,w).

Using the checked square-prefix estimate and w=ceil(log(N)^8), this gives

    count(A intersect [a,a+w)) <= 6 log(N)^5

for N>=3, log(N)>=1, and w<=N. The bound also holds for any subset of A,
including all finite cutoffs.

This removes the need for a global representation envelope in rank
restoration: the old envelope was used only to bound these candidate-window
occupancies. Intervals near zero are included; they are bounded using the
whole initial profile prefix rather than a false uniform density estimate.

## 3. Bracket-only global restoration

`Erdos66BracketOnlyRestoration.uniformly_eventually_rank_restoration`
applies to EVERY exact harmonic-bracket host, even one with unbounded
normalized representation peaks. Any prescribed D subset A in [2N,5N]
with |D|<=M log(N)^2 admits one equal-size reinsertion F such that:

* all edits are in [N,6N];
* every original exact bracket survives;
* at every natural z,

      0 <= r_((A\D) union F)(z)-r_(A\D)(z) <= epsilon log(z+2).

The comparison is with the DELETED CORE. No assertion of small deletion
loss is made. One common insertion potential and the separate far-tail
argument still control all z.

## 4. Only a centerwise representation cap is needed for batch clipping

`Erdos66CenterCapBatchClipping.uniformly_eventually_batch_downward_clipping`
replaces the global logarithmic envelope by

    r_A(n) <= M log(N) for n in the requested center set T.

All earlier explicit center-count, triple, boundary, and support conditions
remain. The centerwise cap bounds total deletion demand; candidate windows
are now bounded from brackets alone.

## 5. Fourth-power waiting bound, uniform over histories

Main endpoint:

    Erdos66QuarticHistoryBatchClipping.exists_host_with_quartic_history_batches

There is ONE exact-bracket host A with all reciprocal-integer power-cost
rows. For every c>0 and epsilon>0, there are rho>0 and J>=2 such that, for
EVERY U,N with

    max(U,J)^4 <= N,

and EVERY B satisfying the original exact brackets and agreeing with A
above U, EVERY center set T subset [4N,5N] with

    |T| <= rho log(N)

has a single simultaneous finite clipping swap. The output preserves the
original brackets, is supported in [N,6N], and satisfies:

    min(r_B(n),floor(c log(n))-1) <= r_new(n)+epsilon log(n+2),
    r_new(n) <= floor(c log(n))+epsilon log(n+2)       for every n in T;

    |r_new(z)-r_B(z)| <= epsilon log(z+2)             for every z outside T.

One may take

    rho = min(1, epsilon/[4(tripleCap(34)+3)]).

Neither rho nor J depends on U or on B. The triple cap is always compared
back to the original base and inflated by only TWO, not by two per stage.
The far representation cap differs from the base by at most FOUR, avoiding
a history-dependent global-envelope constant K+2U in the repair budget.

The fourth power absorbs the fixed boundary-cutoff factor into the cubic
incidence waiting bound. It also guarantees U<N, so previous membership
below U is untouched. Above 6N the result again agrees with the base, giving
a usable finite-history class for subsequent sufficiently separated steps.

## Scope and remaining gap

This proves a uniform finite-history extension theorem, not an unrestricted
infinite correction. It supports separated iterations: the next scale can
be chosen after the previous support. It does NOT allow consecutive dense
batches at comparable scales or show that the produced sets retain the
original triple bounds immediately next to their edits.

The batch capacity is still logarithmic. Available shrinking-tolerance
exception estimates do not establish such sparse batches. The new theorem
also clips downward rather than filling deficits. No all-target finite
prefix feasibility, pointwise sublogarithmic Boolean quadratic error, or
contradiction to a hypothetical witness has been established.

Consequently the original conjecture is still unproved and undisproved.
