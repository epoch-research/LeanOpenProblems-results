# Aggregate near-square-root rank restoration

## Original task status

The conjecture in `Submission/Spec.lean` remains unresolved. Its import,
statement, and original `sorry` are unchanged. No proof or disproof of the
existential limit is being submitted.

## Checked sources

1. RowAdaptiveHitSelectionExplore.lean
2. EqualWidthRowPackingExplore.lean
3. AntitoneFiniteMassExplore.lean
4. IntervalRowSingletonSelectionExplore.lean
5. DisjointWindowMassExplore.lean
6. AggregatedRankRestorationSelectionExplore.lean
7. WideRankCellBudgetExplore.lean
8. WideRankRestorationBudgetExplore.lean
9. WideBracketOnlyRestorationExplore.lean

All nine compile without warnings and have current oleans. The 17 theorem
and lemma declarations are audited in `WideRankRestorationAudit.lean`; all
use only `propext`, `Classical.choice`, and `Quot.sound`.

## 1. Row-dependent conditional potential

`exists_row_adaptive_small_hits` permits degree and rate budgets K(k,z),
b(k,z) depending on the insertion step. Its potential uses the difference
between the total rate prefix and the already-spent prefix. Its initial
budget is

    sum_z exp(sum_(k<m) b(k,z) - t R(z)) < 1.

The state, choices, and hit sets can still depend on the entire history.

## 2. Constant new/new degree for equal-width rows

Any width-w window contains at most TWO selected points from a partial
transversal of disjoint width-w rows. The proof uses three hypothetical
points and their distinct row labels. It includes arbitrary row ordering.

Consequently, reflected partner choices from previously selected points
contribute at most two at every insertion step. The diagonal contributes
at most one. `exists_interval_singletons` therefore has degree K(k,z)+3,
not the former K(z)+m+1. It retains exactly one selected point in every row.

## 3. Aggregate old-point degree

For antitone p, any finite S satisfies

    sum_(a in S) p(a) <= sum_(i<|S|) p(i).

For nonnegative p and an exact-bracket host, disjoint intervals with total
length at most mw therefore have summed occupancy at most

    2m + sum_(i<mw) p(i).

The reflected rows are the ACTUAL truncated intervals

    [z+1-(L_k+w), z+1-L_k).

Their lengths are at most w and they remain disjoint, including truncation
at zero. Padding every truncated interval back to length w would lose this
property and is deliberately not used.

For old-point partner degrees, summing over all rows gives the bound above.
Combining with the two new/new hits and the diagonal leaves a total rate
budget

    exp(t) * [sum_(i<mw) p(i) + 5m] / q.

## 4. Wide rank-cell windows

The chosen width is

    w(N) = ceil(sqrt(N)/(16 log N)).

Eventually it is positive, at most N, and satisfies

    sqrt(N)/(16 log N) <= w(N) <= sqrt(N)/(8 log N),
    w(N)*profile(N) <= 1/4.

Thus the existing prescribed-rank cell lemma supplies a whole width-w
window for each old point in [2N,5N]. Different old ranks force the windows
to be disjoint. Every candidate window starts at least N, so exact brackets
bound its old occupancy by 3; a global representation envelope is not used.

The compressed profile prefix obeys

    [sum_(i<mw) p(i)]/w <= sqrt(12(m+1) log(N)/w)

when m,w<=N. The aggregate mean tends to zero whenever

    S(N) log(N)^2 / sqrt(N) -> 0.

The extra +1 in the majorant handles m=0 safely. A fixed exponential tilt
then controls the full polynomial horizon N^33, and the previous short-
support estimate controls every farther target.

## 5. Main endpoint

`Erdos66WideBracketOnlyRestoration.uniformly_eventually_rank_restoration`:
For S eventually nonnegative satisfying the preceding decay and epsilon>0,
eventually N, uniformly over EVERY exact harmonic-bracket host A and every
prescribed D subset A in [2N,5N] with |D|<=S(N), there is F such that:

* |F|=|D| and F is disjoint from A;
* all edits lie in [N,6N];
* every original exact bracket survives;
* at EVERY natural z,

      0 <= r_((A\D) union F)(z)-r_(A\D)(z)
        <= epsilon log(z+2).

`eventually_power_rank_restoration` specializes this to every fixed demand
N^a with a<1/2.

The insertion cost is measured against the DELETED CORE. No small deletion
loss is asserted. This strengthens the former O(log(N)^2) arbitrary-rank
restoration but does not establish the conjecture. Available shrinking-
tolerance exception bounds still do not give this demand scale or small
aggregate deletion incidence. Dense consecutive repairs and all-target
finite-prefix feasibility remain unproved.
