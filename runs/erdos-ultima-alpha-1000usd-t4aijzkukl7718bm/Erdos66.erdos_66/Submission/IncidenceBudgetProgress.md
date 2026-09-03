# Cubic collision budgets instead of excluding every triple

## Original conjecture status

Erdos66.erdos_66 remains unproved and undisproved. Spec.lean is unchanged
with its original import, statement, and sorry. Its SHA256 is still
32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0.
The previous unchanged submission failed verification. No new valid main
proof or exact-negation theorem has been obtained.

## New finite-field endpoint

Let p=|F|, h=|U|>0, characteristic not two, and U+U contained in S.
Assume 2h^2<p. One translation a yields an actual anchored graph B and a
nonnegative integer function D on the target plane such that

    (x,0) in B iff x in U,
    |r_B(z)-h^2| <= sqrt(16 |S| h^2)+24h+D(z),
    p D(z)^3 <= 6912 h^9                    for EVERY target z.

The same translation is used for all targets. D(z) is the positive part
of the exact collision correction minus 24h, transported through the
anchoring translation. The endpoint is exists_budget_anchored_graph in
Erdos66BudgetInterceptFlat.

A sufficient relative-error version gives |r_B(z)-h^2|<=3 epsilon h^2
under the additional real inequalities

    24 <= epsilon h,
    16 |S| <= epsilon^2 h^2,
    6912 h^3 <= p epsilon^3,
    epsilon >= 0.

Thus the useful incidence regime improves from roughly p>>h^7 to p>>h^3.
The existing natural encoding still preserves the literal prefix below p.
It does not identify full plane-group counts with ordinary natural counts
above p.

## Incidence budget and counting argument

properEdges(U) contains the nondegenerate ordered pairs in U x U. A valid
ordered triple consists of three distinct UNORDERED pairs. Each unordered
class has at most two orientations. For any finite edge set R,

    validTripleCount(R) >= (|R|-4)^3,

where subtraction is natural truncated subtraction.

For fixed w and a, budgetAt(U,a,w) counts valid triples of proper edges
whose degree-at-most-eight concurrency polynomial vanishes at a. Its
nonvanishing on valid triples was proved in the preceding general-position
branch. Consequently

    sum_a budgetAt(U,a,w) <= 8h^6,
    sum_a budget(U,a) <= 8h^7,
    budget(U,a) = sum_(w in U) budgetAt(U,a,w).

For a fixed reflected curve, let R be its active collision edges. Every
collision point is in an active edge's point set, and every edge has at
most two points. Every valid active triple is counted in budgetAt. Therefore

    collisionCurveCount <= 2|R| <= 8+2(|R|-4),
    (|R|-4)^3 <= budgetAt.

Chebyshev's power-sum inequality, already available in Mathlib as the
ROOT-NAMESPACE lemma pow_sum_le_card_mul_sum_pow, gives

    (sum_w (|R_w|-4))^3 <= h^2 budget(U,a).

Combining with the exact set-level collision correction gives

    max(correction(z)-24h,0)^3 <= 216 h^2 budget(U,a).

No pointwise bound was inferred merely from a total-deficit estimate.

## Simultaneous selection

Only oppositeForbidden(U), of size at most h^2, is excluded. For h>0 use

    f(a) = translatedEnergy(U,a)/(4h^2)
           +p budget(U,a)/(8h^7).

Its sum over a is at most 2p. The existing outside-set minimum selector
supplies one a outside oppositeForbidden with f(a)<=4, hence

    translatedEnergy <=16h^2,
    p budget(U,a)<=32h^7.

This proves the displayed uniform cubic correction and actual graph bound.
All zero and opposite-label hypotheses used in the root formula are retained.

## Checked limitation

BudgetInterceptScaleExplore also proves that a hypothetical witness has,
eventually, NOT 2 count(A,N)^2<N. The prime-prefix version substitutes
prefixParameters and the actual ZMod cardinality. Thus even the weakened
opposite-exclusion certificate eventually fails for full old prefixes.

This is failure of a SUFFICIENT certificate, not failure of all translations
and not a disproof of the original conjecture. Pruning opposite labels might
remove this particular certificate, but the cubic correction itself remains
too large at h^2 comparable with p log p. Nor does the finite endpoint solve
natural carry, tapering, or all-scale prefix compatibility.

## Files and verification

Five production files compile without warnings and have current oleans:

* EdgeTripleBudgetExplore.lean
* InterceptIncidenceBudgetExplore.lean
* InterceptBudgetPointwiseExplore.lean
* BudgetInterceptFlatExplore.lean
* BudgetInterceptScaleExplore.lean

IncidenceBudgetBuild.log records the rebuild. IncidenceBudgetAudit.lean/.log
audits 35 definitions and theorems; only propext, Classical.choice, and
Quot.sound occur. None of these production files has a placeholder or new
axiom. CollisionBudgetChecks2.lean and BudgetScaleChecks.lean are scratch
API searches, not production dependencies.

No all-scale Boolean witness, completion input with the required weighted
lower-exception cost, or universal logarithmic fluctuation contradiction
was proved. The original task is still unresolved.
