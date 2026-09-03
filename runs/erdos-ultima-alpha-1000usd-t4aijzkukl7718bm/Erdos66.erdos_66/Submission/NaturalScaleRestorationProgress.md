# Natural-counting-scale restoration and active aggregate clipping

## Original task status

The conjecture in `Submission/Spec.lean` remains unproved and undisproved.
Its original import, statement, and `sorry` are unchanged. No new valid
submission is available.

SHA256:
32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0

## Verified production files

1. ExactClippingDemandExplore.lean
2. AggregateIncidenceBatchClippingExplore.lean
3. NaturalScaleRankWindowExplore.lean
4. NaturalScaleRankBudgetExplore.lean
5. NaturalScaleBracketRestorationExplore.lean
6. NaturalScaleBatchClippingExplore.lean
7. ActiveCenterBatchClippingExplore.lean

All seven compile without warnings and have current oleans. The 17 theorem
and lemma declarations pass `NaturalScaleRestorationAudit.lean`; its saved
log lists only propext, Classical.choice, and Quot.sound. The earlier four-
declaration aggregate-demand audit is retained as well.

## 1. Exact clipping demand, without a midpoint margin

Define

    clipDemand(r,q) = floor(((r-q)_+ + 1)/2).

This is exactly the ceiling of half the positive excess, and is zero iff
r<=q. It is at most r.

`exists_central_clipping_exact` chooses exactly this many upper endpoints,
provided d>=2 and

    q >= 2*boundary(A,d,n).card + 2.

The remaining count lies between min(r_A(n),q-1) and q. No harmonic-bracket
hypothesis is needed for this cardinal selection. Because reinsertion is
allowed a small error at the clipped center itself, the former excluded
midpoint margin is unnecessary. Its boundary allowance +6 is reduced to +2.

## 2. Correct natural-scale window and normalized mean

The sharp profile estimate is

    sqrt(N)*profile(N) <= 2 sqrt(log N).

Use

    densityWindow(N) = ceil(sqrt(N)/(16 sqrt(log N))).

Eventually it is positive, at most N, and

    sqrt(N)/(16 sqrt(log N)) <= w <= sqrt(N)/(8 sqrt(log N)),
    w*profile(N) <= 1/4.

The preceding disjoint-row selector remains applicable. The normalized
compressed-prefix estimate is

    [sum_(i<mw) profile(i)]/[w log N]
      <= sqrt(12(m+1)/[w log N]).

Since w log N >= sqrt(N log N)/16, the entire insertion mean divided by
log N is bounded by

    2 exp(t) [sqrt(192 delta_N) + 80 delta_N],
    delta_N = (S(N)+1)/sqrt(N log N).

It therefore tends to zero under the NATURAL counting-scale hypothesis

    S(N)/sqrt(N log N) -> 0.

The tilt is 40(h+1)/epsilon. This leaves enough logarithmic exponential
margin for the polynomial horizon, even though the unnormalized mean need
not tend to zero. The old far-target support argument is unchanged.

## 3. Main global finite restoration endpoint

`Erdos66NaturalScaleBracketRestoration.uniformly_eventually_rank_restoration`:
For every eventually nonnegative S with S(N)/sqrt(N log N)->0, and every
fixed epsilon>0, eventually N, uniformly over every exact harmonic-bracket
host A and every prescribed D subset A in [2N,5N] with |D|<=S(N), there is F
such that:

* |F|=|D| and F is disjoint from A;
* all edits lie in [N,6N];
* all original exact brackets are preserved;
* at EVERY natural z,

      0 <= r_((A\D) union F)(z)-r_(A\D)(z)
        <= epsilon log(z+2).

No representation envelope or incidence hypothesis on A is assumed.
The comparison is with the DELETED CORE, not the original A. Deletion
collateral is still separate.

`eventually_sqrt_rank_restoration` explicitly includes demand M sqrt(N)
for every fixed M>=0. This goes beyond all fixed powers strictly below 1/2,
and beyond the previous S log(N)^2/sqrt(N)->0 condition.

## 4. Aggregate clipping at the natural scale

`Erdos66NaturalScaleBatchClipping.uniformly_eventually_batch_downward_clipping`
uses the preceding restoration theorem. There is NO explicit center-count
bound and NO global or centerwise representation envelope. Instead it asks:

    sum_(n in T) clipDemand(r_A(n),q(n)) <= S(N),

and, for every z<=N^33,

    2 sum_(n in T\{z}) fiber(A,n/d(n)^2,n,z).card
      <= (epsilon/2) log N.

Active centers must lie in [4N,5N], d(n)>=2, and q must satisfy the +2
boundary margin. The final swap preserves brackets, clips each requested
center into the usual epsilon-log enlargement of [min(r_A,q-1),q], and
changes every other representation count by at most epsilon log(z+2).

The earlier `AggregateIncidenceBatchClippingExplore.lean` retains the same
finite argument with the previous, stronger demand-decay hypothesis.

## 5. Only actually active centers are charged

Define

    activeCenters(A,T,q) = {n in T : q(n)<r_A(n)}.

`active_demand` proves that restricting the demand sum to these centers
changes nothing.

`Erdos66ActiveCenterBatchClipping.uniformly_eventually_active_clipping`
requires the aggregate cross-incidence, location, and boundary hypotheses
ONLY on activeCenters. It still gives the requested clipping inequalities
at EVERY n in T. Outside activeCenters, including inactive requested
centers, all counts stay within epsilon log(z+2) of their old values.

## 6. Check against the existing host estimates

The available power-cost rows yield a positive power saving for the number
of fixed-tolerance exceptions. That saving depends on the tolerance and
can be much smaller than 1/2. Multiplying such an exceptional-count upper
bound by a logarithmic representation envelope does not give negligible
half-excess demand at scale sqrt(N log N). Using exact half-excess instead
of the full count sharpens the certificate but does not prove that missing
estimate.

Likewise, the checked per-center triple cap gives an aggregate bound
proportional to the number of active centers. No small aggregate bound for
the actual dense exceptional sets has been proved. The new theorem assumes
that bound explicitly; it does not infer it from separate triple caps.

These are limitations of the available certificates, not lower bounds on
every possible host and not a disproof of the conjecture. Shared-point
selection could reduce actual union deletion size, and more structured
hosts could have different exceptional geometry, but neither improvement
has been established here at all tolerances.

No unrestricted all-target finite-prefix construction, compatible infinite
correction, pointwise sublogarithmic quadratic Boolean rounding theorem,
or universal contradiction has been obtained. In particular, arbitrary
negligible deletions across infinitely many adjacent scales have NOT been
restored by an infinite theorem: finite restoration bounds cannot simply
be summed without a new cumulative argument.
