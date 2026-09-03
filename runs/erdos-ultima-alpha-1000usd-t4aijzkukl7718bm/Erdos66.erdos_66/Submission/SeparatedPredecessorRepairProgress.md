# Infinite separated count-preserving repairs

## Original task status

The conjecture in `Submission/Spec.lean` is still unresolved. Its original
import, statement, and `sorry` are unchanged. No proof/disproof was submitted.
SHA256:

    32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0

## Production files and verification

1. LocatedPredecessorPacketExplore.lean
2. LocatedIntervalPredecessorExplore.lean
3. PredecessorCutoffTransferExplore.lean
4. PredecessorScaleBudgetExplore.lean
5. GlobalPredecessorRepairExplore.lean
6. SeparatedPredecessorStateExplore.lean
7. SeparatedPredecessorSpikesExplore.lean
8. CountPreservingPowerSpikesExplore.lean

All eight compile and have current oleans. `SeparatedPredecessorAudit.lean`
audits 52 declarations; its saved log contains only `propext`,
`Classical.choice`, and `Quot.sound`. No production placeholders or new
axioms occur. There are two harmless linter warnings in the early pipeline.
The `PredecessorTransferChecks` and `PredecessorGlobalChecks` files are API
scratch files and intentionally contain failed checks.

## Support information retained

The located finite selector retains the facts discarded by the earlier
endpoint theorem:

    E = image(predecessor A,F),
    every inserted endpoint has the selected symmetric-packet form.

The interval corollary therefore locates every modified point u by

    L <= u+H,  u <= n-L.

The earlier one-target theorem remains unchanged. Its proof is reused with
these additional output fields, not strengthened by an unproved assumption.

## One-target repair of an infinite host: ALL natural targets tested

`Erdos66GlobalPredecessorRepair.eventually_global_predecessor_repair` assumes

    |count(A,X)-P(X)| <= D,
    r_A(z) <= K+C log(z+2),  D,K,C>=0.

For every M>=0 and epsilon>0, eventually in N, every natural
m<=M log N admits finite E,F with:

* E subset A; F disjoint from A;
* |E|=|F|=2m;
* all modified points lie in [3N,12N];
* every prefix count changes by an amount in [-1,0];
* r_((A\E) union F)(16N)=r_A(16N)+2m;
* for EVERY z!=16N,

      |r_new(z)-r_A(z)| <= epsilon log(z+2).

The centers in this theorem are 16N, not arbitrary n.

### Cutoff and far-target argument

Use candidate interval [4N,5N), its reflection about 16N, and

    H=ceil(12(D+1)sqrt N).

Eventually H<=N; the existing harmonic gap lemma applies to all endpoints.
Truncate the old set at X=N^h+1, with h>=2 and epsilon*h>=4M. Its finite
representation envelope is bounded by

    [K+C(h+6)+1] log N.

The candidate-degree bound is at most B sqrt(N) log N, so the prior
predecessor sampling criterion controls every z<X. For z<3N, no modified
point can occur in a representation, so the change is exactly zero. For
z>=X, the generic edit bound is

    |r_new(z)-r_A(z)| <= 2 max(|E|,|F|)=4m,

which is at most epsilon log(z+2) by the choice of h. Thus the all-target
claim does NOT extrapolate a polynomial-horizon sampling bound without
checking its remaining tail.

## Infinite separated iteration with no prefix-error accumulation

`Erdos66SeparatedPredecessorSpikes.exists_count_preserving_sparse_spikes`
applies to any Host with the displayed prefix and global representation
bounds. It constructs B and a strictly increasing center sequence t such
that:

    (k+1)^4 <= t(k),
    -1 <= count(B,N)-count(A,N) <= 0       for every N,
    r_B(n) <= K+(C+9)log(n+2)             for every n,
    r_B(t(k))/log(t(k)) >= 2              for every k,

and, for every epsilon>0, eventually n outside range(t),

    |r_B(n)/log n-r_A(n)/log n| < epsilon.

The centers are selected adaptively, arbitrarily far beyond the previous
frozen cutoff. They are NOT a prescribed list of dense exceptional targets.

A state agrees with the original host in both membership and cumulative
count beyond its cutoff. A new equal-cardinality repair occurs beyond that
cutoff. Inside the new repair region, the old cumulative count is therefore
exactly the original host's, rather than a count already shifted by previous
repairs. This keeps the cumulative difference in [-1,0] for the entire
iteration.

At stage k, use collateral allowance 2^(-k-1). The finite telescoping estimate
between stages j and l, away from their centers, is

    |r_l(z)-r_j(z)| <= (2^(-j)-2^(-l))log(z+2).

Membership stabilizes pointwise and the frozen central counts survive.
Compare the final set with stage j, then let j grow; each fixed stage differs
from the base on only finitely many coordinates. This proves uniform
normalized o(1) change off the centers, not merely convergence at the moving
repair target. Strictly increasing centers imply there is at most one
central contribution at any z; that contribution is bounded by 8log(z+2),
which explains the upper coefficient C+9.

## New joint auxiliary counterexample

`Erdos66CountPreservingPowerSpikes.exists_balanced_power_exceptions_no_limit`
constructs ONE set B and K>=0 with:

    |count(B,N)-P(N)| <= 2                   for all N,
    r_B(n) <= K+43log(n+2)                   for all n,

and, for each epsilon>0, some 0<alpha<1 for which

    sum_{|r_B(n)/log n-1|>=epsilon} (n+2)^(-1+alpha)

converges. Nevertheless r_B(n)/log n has NO finite real limit.

Start with the balanced harmonic power-potential witness, extract its
coefficient-34 global envelope, and apply the separated construction.
For any fixed tolerance, the new bad set is eventually contained in the
union of the old half-tolerance bad set and the chosen centers. The latter
have summable reciprocal power weight for alpha<=1/2 because t(k)>=(k+1)^4.
A finite hypothetical limit would have to be 1, by the summable-exception
argument. The retained peaks at least 2 contradict that limit.

This improves the earlier power-exceptions/no-limit example by retaining a
uniform harmonic prefix-discrepancy bound. It does NOT assert exact original
floor/ceiling brackets, preservation of the numerical power potentials, or
local difference control for the resulting B. Those additional properties
must not be silently added.

## What this does NOT solve

The sparse signed iteration is now complete, so that particular iteration
and far-target bookkeeping are no longer gaps. The application to the
conjecture remains missing:

* the construction only treats well-separated adaptively selected centers;
* it does not correct the much denser exceptional sets currently known;
* it gives positive spikes, not a sharp all-target upper coefficient;
* the power-saving exponent has not been improved past the repair-capacity
  threshold;
* it does not provide mixed-period compatibility or shrinking-tolerance
  finite-prefix feasibility.

The new no-limit set is only an auxiliary counterexample to the sufficiency
of several invariants. It is NOT the negation of the existential statement
in Spec.lean and must not be submitted as an `erdos_66.disproof` theorem.
