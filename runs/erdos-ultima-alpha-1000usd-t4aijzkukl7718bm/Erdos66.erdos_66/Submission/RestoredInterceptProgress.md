# Opposite pruning and exact row-zero restoration

## Original task status

Erdos66.erdos_66 remains unproved and undisproved. Spec.lean is unchanged,
including its original import, statement, and sorry. The unchanged earlier
submission failed verification. No new valid main proof has been submitted.
The new results are finite-field constructions and explicit scope checks.

## New finite endpoint: no field-size exclusion assumption

Let F be any odd finite field, p=|F|, h=|U|>0, and U+U contained in S.
There is an actual set B in F^2, constructed from one translation a, and
nonnegative integer r and D(z), with

    (x,0) in B iff x in U,
    p r <= 3h^2,
    |r_B(z)-h^2| <= sqrt(12 |S| h^2)+24h+(4h+2)r+D(z),
    p D(z)^3 <= 5184 h^9                       for EVERY target z.

Main declaration:

    Erdos66RestoredInterceptPrefix.exists_restored_graph

Unlike the preceding incidence-budget selector, this theorem has NO
hypothesis 2h^2<p, or any other lower bound on p in terms of h. The bounds
may of course be uninformative in dense regimes. It is not an assertion
that the displayed error is always small.

The ordinary encoding has exact prefix membership and sumRep preservation
below p, proved by encoded_restored_prefix and encoded_restored_counts_below.
No full-field count is identified with an ordinary count above that prefix.

## Selection without a forbidden set

Define oppositeCount(U,a) as the number of ordered pairs (u,v) in U^2 with

    a=-(u+v)/2.

For each pair there is exactly one such a, so

    sum_a oppositeCount(U,a)=h^2.

Normalize three costs:

    translatedEnergy/(4h^2)
      +p budget/(8h^7)
      +p oppositeCount/h^2.

Their sum is at most 3p. Taking a minimum over the WHOLE field, not outside
a forbidden set, supplies one a with all three costs at most 3. Hence

    translatedEnergy<=12h^2,
    p budget<=24h^7,
    p oppositeCount<=3h^2.

## Pruning and restoration

pruned(U,a) removes every u for which some v in U satisfies the opposite
condition. This removes both members of a nonzero opposite pair, and any
zero translated label. If V=pruned(U,a), then

    V subset U,
    |U|-|V| <= oppositeCount(U,a),
    translated(V,a) has no zero or opposite pair.

The original incidence budget is monotone under taking V subset U, so the
same selected budget controls the cubic correction for V.

Deleting bounded signed pair weights costs at most the number of deleted
ordered pairs in the L1 norm of their fibers. In this application,

    sum_s |crossCharFiber(V,V,s)|
      <= sum_s |crossCharFiber(U,U,s)| + (h^2-|V|^2),
    h^2-|V|^2 <= 2h oppositeCount(U,a).

These statements are applied to the translated sets. There is no claim
that the signed energy itself is monotone under deletion. The energy of
U controls its L1 fiber norm; the checked L1 deletion inequality transfers
that bound to V. Retuning the mean from |V|^2 to h^2 costs another 2hr.

Anchor the actual curve union for V and adjoin only

    {(u,0): u in U minus V}.

This restores row zero exactly. Adding E to a finite group set changes
every ordered self-count by at most 2|E|, proved by covering every newly
counted first endpoint by E or its reflection. Thus the restoration costs
at most 2r, giving the total (4h+2)r term above.

## Checked asymptotic scope

RestoredInterceptScaleExplore proves:

1. From p r<=3h^2, p,h>0,

       (4h+2)r/h^2 <= (12h+6)/p.

2. A hypothetical witness has count(A,N)/N->0. Consequently any selected
   pruning counts with N r_N<=3 count(A,N)^2 have normalized pruning cost
   tending to zero. The old opposite-exclusion obstruction is genuinely
   removed by this construction; it should not be cited as an unresolved
   assumption of exists_restored_graph.

3. A hypothetical witness also has

       count(A,N)^3/N -> infinity.

   Hence, for EVERY fixed epsilon, eventually the sufficient inequality

       5184 count(A,N)^3 <= N epsilon^3

   fails. This is the condition that would turn the cubic upper certificate
   into D<=epsilon h^2. It is only failure of an upper-bound certificate,
   NOT a lower bound on the actual collision correction and NOT a disproof.

The cubic incidence estimate remains too weak at full-prefix density.
Even improving it would not automatically resolve the different problem
of density-correct tapering and all ordinary natural transition windows.

## Verification

Five production files compile without warnings, with current oleans:

* InterceptOppositePruningExplore.lean
* FinitePruningErrorExplore.lean
* PrunedInterceptBoundsExplore.lean
* RestoredInterceptPrefixExplore.lean
* RestoredInterceptScaleExplore.lean

RestoredInterceptBuild.log records the rebuild. RestoredInterceptAudit.lean
and its saved log audit 38 definitions and theorems. Only propext,
Classical.choice, and Quot.sound occur. No production placeholder or new
axiom was added. PruningChecks.lean and RestoredScaleChecks.lean are API
scratch files, not production dependencies.

There is still no complete proof or exact-negation theorem for Spec.lean.
