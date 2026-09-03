# Matching-based repair and superquadratic sparse completion

## Original task status

`Spec.lean` remains unchanged, with its original `sorry`. The conjecture has
not been proved or disproved. No appropriate base set is constructed below.
No proof submission has been made.

## New checked conclusions

### Summably prescribed spikes

`Erdos66SummableMatchingSpikes.asymptotic_prescribed_spikes`:
for any base A with r_A(z)<=K+C log(z+2), any repeated center list n_i
satisfying

    sum_i sqrt(log(n_i+2))/sqrt(n_i+1) < infinity,

and stabilized multiplicities m(z), there is B containing A with, eventually,

    r_A(z)+2m(z) <= r_B(z) <= r_A(z)+2m(z)+o(log z).

The upper statement is uniform over all sufficiently large z, not just the
prescribed centers. The lower statement omits at most a finite initial set
of targets, because a finite initial coordinate segment is discarded.

### Weighted sparse-exception completion

`Erdos66WeightedSparseCompletion.summable_exception_completion`:
if an injective exceptional sequence n_k satisfies

    sum_k log(n_k+2)*sqrt(log(n_k+2))/sqrt(n_k+1) < infinity,

then an O(log)-bounded base with asymptotic upper coefficient at most c>0,
and lower coefficient at least c outside range(n), has a superset B with
r_B(z)/log z -> c.

### Every fixed exponent greater than two

`Erdos66SuperquadraticCompletion.superquadratic_exception_completion`:
the weighted condition holds if, for some real p>2,

    (k+1)^p <= n_k eventually.

This strengthens the previously checked exponent-twelve criterion. The new
criterion requires injectivity, not monotonicity, of the center sequence.
`cubic_exception_completion` specializes to the natural-number inequality
(k+1)^3<=n_k.

## Why matching replaces Sidon uniqueness

The old joint engine forbade every collision between two unintended sums.
This gave at most two unintended ordered pairs at each target, but imposed
a fourth-power coordinate cost. That much uniqueness is unnecessary.

For one fixed target z, assume all packet labels denote distinct points.
Each coordinate has two labels. Each label can have at most one partner
summing to z. Thus at most FOUR realized ordered pairs touch a given
coordinate. Each pair has at most two coordinates, so its conflict
neighborhood contains at most EIGHT realized pairs. A greedy argument
extracts a coordinate-disjoint subfamily of size at least one eighth of
the total unintended ordered-pair count.

For supports E_e and binary event functions f_e, define the matching
partition function

    Z_t(omega) = sum_{M pairwise support-disjoint}
                    product_{e in M} (exp(t)-1) f_e(omega).

For a realized matching M, its subsets contribute exp(t*|M|). Uniform
independent-coordinate averages factor on support-disjoint events. Thus,
if E[f_e]<=p_e,

    E[Z_t] <= product_e (1+(exp(t)-1)p_e)
           <= exp((exp(t)-1) sum_e p_e).

A non-designated sum equation has at most one solution in either occurring
coordinate. Charging the larger choice space bounds its event probability
by 1/sqrt(q_i*q_j). Summing over all ordered labelled pairs gives at most
4 S^2, where S=sum_i 1/sqrt(q_i).

Consequently, with the MGF set to zero on noninjective selections,

    E[1_injective exp(t * unintended_pair_count(z))]
        <= exp((exp(8t)-1)*4 S^2).

Point-collision avoidance also costs at most 4 S^2. After discarding a
finite coordinate segment this cost is small. The old-set avoidance mass
is summable under the displayed weighted condition. Mixed-hit MGFs use
the previous local window bound B sqrt(log(z+2)).

At tilt t=4/epsilon and threshold epsilon log(z+2), both the mixed and
self test potentials are summable in z. Accuracy-level tail thresholds
are chosen BEFORE the finite coordinate prefix. Product compactness then
produces one infinite selection with both counts uniformly o(log z).
Exact packet decomposition and finite-stage attainment of each union
representation count transfer the result to natural-number sets.

## Checked files

1. `DisjointMeanExplore.lean`: uniform-mean factorization on disjoint
   coordinate supports.
2. `BoundedConflictExplore.lean`: large disjoint subfamily under a bounded
   conflict-neighborhood cardinality.
3. `MatchingPartitionExplore.lean`: matching partition function, its mean
   bound, and the contribution of all subsets of a realized matching.
4. `PacketMatchingExplore.lean`: sum-equation fibers, four-incidence/eight-
   conflict bounds, and pointwise exponential domination.
5. `PacketMatchingMassExplore.lean`: reciprocal geometric-mean costs and
   the uniform restricted MGF bound.
6. `MatchingPacketSelectionExplore.lean`: joint finite selection with
   injectivity, old-point avoidance, and self/mixed tests.
7. `MatchingPotentialExplore.lean`: summable combined potentials and
   uniform finite-test tail thresholds.
8. `InfiniteMatchingSelectionExplore.lean`: restriction-monotone pair
   counts and compactness across coordinate prefixes and accuracy levels.
9. `PacketDecompositionExplore.lean`: exact designated/unintended split.
10. `MatchingInfiniteRepairExplore.lean`: infinite natural-set transfer
    under small square-root-mass and old-avoidance costs.
11. `SummableMatchingSpikesExplore.lean`: discard finitely many coordinates;
    weighted summability also implies unweighted square-root summability.
12. `WeightedSparseCompletionExplore.lean`: clipped deficit multiplicities
    and weighted sparse-exception completion.
13. `SuperquadraticCostsExplore.lean`: logarithmic powers are dominated by
    every positive real power; compare costs with a convergent p-series.
14. `SuperquadraticCompletionExplore.lean`: p>2 and cubic specializations.

All fourteen files compile and have built oleans. The audit files
`MatchingRepairAxiomCheck.lean` and `SuperquadraticCompletionAxiomCheck.lean`
report only propext, Classical.choice, and Quot.sound.

## Remaining gap and caution

No base with these lower-bound exceptions is known in the checked work.
Independent random selection at fixed mean c log N has lower-deviation
tails roughly N^(-O(c epsilon^2)); as epsilon tends to zero, those exceptions
are much denser than N^(1/p) for every fixed p>2. Thus the new theorem does
not turn the existing random construction into a witness.

The finite power-annulus constructions still leave uncontrolled dense
transition intervals. Their mixed-period gluing has not been justified.
No necessary condition derived so far contradicts the conjectured limit.

The natural remaining directions are a genuinely structured base with
sharper pointwise behavior, an efficient repair method that reuses points
across far denser deficits, or a valid mixed-period transition construction.
Further optimization of logarithmic factors in the sparse-repair cost would
not by itself remove this gap.


## Subsequent transition-budget check

`TransitionBudgetExplore.lean` now formally quantifies a limitation of using
negligible additions to bridge dense transition gaps. See
`TransitionBudgetProgress.md` for the exact linear first-window equation
and cardinality lower bound. This does not construct the missing base and
does not negate the original conjecture.
