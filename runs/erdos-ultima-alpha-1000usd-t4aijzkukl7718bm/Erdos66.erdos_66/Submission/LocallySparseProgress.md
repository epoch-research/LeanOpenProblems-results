# Local difference control alongside the harmonic rounding

## Original task status

The original conjecture is not proved or disproved. `Submission/Spec.lean`
is unchanged and still has its original `sorry`. No main proof is submitted.
SHA256:

    32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0

## New unconditional infinite construction

`Erdos66LocallySparsePowerProfile.exists_locally_sparse_power_potentials`
constructs ONE set A and cutoff N0 with:

1. |prefixSum(indicator A - profile)(n)| <= 1 for every n;
2. for every N>=N0 and positive d,

       #{a : N<=a, a+d<2N, a in A, a+d in A} <= 24 log(N+2);

3. all the earlier reciprocal-integer two-sided power-tilted representation
   potentials for coefficient c=1 are summable.

`exists_locally_sparse_power_exceptions` extracts the corresponding positive
power saving in each fixed-tolerance exceptional set. As before, the saving
may shrink with tolerance. The same potential witness also supports the
previous density-one and constant-width envelope extraction lemmas.

The difference estimate is genuinely local: it counts pairs with BOTH
endpoints in [N,2N). It does not assert that the infinite difference function
is finite at a fixed shift.

## Why this was investigated

A count-preserving reflected patch would select some old points a and insert
n-a, replacing nearby points. Its mixed collateral is controlled by local
DIFFERENCE correlations, not solely by the old SUM representation envelope.
The previous candidate did not have such local difference control. This pass
supplies that missing structural bound, but does not construct the patches or
prove that they eliminate the exceptional targets.

## Finite selection engine

`CombinedPipageExplore.lean`:

* `exists_ordered_rounding_for_cost`: an abstract ordered-rounding induction
  using pair-average and final single-coordinate-average inequalities.
* `poly_single_average`: exact affinity of a multilinear polynomial in a
  single rounded coordinate.
* `exists_compensated_rounding_with_poly`: adds any nonnegative multilinear
  polynomial to the compensated two-sided representation cost.

`PositiveBinaryExpansionExplore.lean`:

* Products of Boolean monomials reduce to the monomial on their support union,
  even if those supports overlap.
* `multilinearExp` is the multilinear Bernoulli expectation of the exponential
  of a weighted monomial sum.
* For nonnegative tilt and monomial weights, its coefficients are nonnegative.
* `exists_combined_selection` is the Boolean-set version of the combined rule.

`MixedExponentialSelectionExplore.lean`:

* `exists_mixed_exponential_selection` handles a finite family of arbitrary
  positive exponential monomial costs jointly with the two-sided sumRep costs.
  Prefix brackets remain intact; only the latter pay exp(2|t|) compensation.

## Difference matching decomposition and tail budget

`DifferenceMatchingExplore.lean` defines edges (a,a+d) with a>=N and a+d<2N.
Color an edge by floor(a/d) modulo 2. Each color is a matching when d>0.
The checked disjointness proof uses the identity

    floor((a+d)/d) = floor(a/d)+1.

Each matching has at most N edges. If the coordinate probabilities in the
window are bounded by v, its mean is at most N v^2. The positive MGF obeys

    E exp(X/2) <= exp(mean).

`LocalDifferencePotentialExplore.lean` connects these matching counts to the
actual natural-number `localDiff` cardinality and proves, for the harmonic
profile,

    mean <= H_(N+1),
    exp(-6 log(N+2)) * E exp(X/2) <= exp(1)/(N+2)^5.

Summing over both colors and all 1<=d<N is bounded by the summable sequence

    2 N exp(1)/(N+2)^5.

`FiniteLocalDifferenceSelectionExplore.lean` supplies a uniform N0 before the
finite cutoff. Any finite compensated representation-potential budget <=1/2
can be imposed jointly with all the local difference bounds. Each matching
is bounded by 12 log(N+2), so their sum is bounded by 24 log(N+2).

## Infinite passage

`LocalDifferenceCompactnessExplore.lean` defines `encodedDiff`, proves its
continuity and exact relationship to `localDiff`, and retains these closed
constraints alongside prefix discrepancy and summable representation costs.

`LocallySparseCostsExplore.lean` adapts the exponential-cost selection theorem
to this setting. Finite constraints indexed up to L use coordinates through
2L, so all windows [N,2N) with N<=L are covered. All row thresholds and the
local-difference cutoff are fixed before L.

`LocallySparsePowerProfileExplore.lean` applies that theorem to the existing
power-tilted deviation costs. No new concentration assumption is made.

## Verification

All nine new production files compile and have current oleans:

1. CombinedPipageExplore.lean
2. PositiveBinaryExpansionExplore.lean
3. MixedExponentialSelectionExplore.lean
4. DifferenceMatchingExplore.lean
5. LocalDifferencePotentialExplore.lean
6. FiniteLocalDifferenceSelectionExplore.lean
7. LocalDifferenceCompactnessExplore.lean
8. LocallySparseCostsExplore.lean
9. LocallySparsePowerProfileExplore.lean

`LocallySparsePowerProfileAxiomCheck.lean` audits the main declarations. Only
propext, Classical.choice, and Quot.sound occur. No placeholders or new axioms
occur in these production files.

## Remaining gap and next possible work

A count-preserving local reflection/replacement lemma could now use the
local-difference envelope to bound mixed collateral when selecting a small
number of points from a much larger window population. It would still need:

* an exact prefix-discrepancy-preserving replacement map;
* simultaneous bounds for all unintended new/new, new/old, and deleted/old
  effects, not merely an expected count;
* compatibility over infinitely many patches;
* a way to handle the actual exceptional sets from the construction.

The last point is essential: the known exceptions need not be sub-square-root
sparse at small tolerances. Local difference control does not itself improve
that exponent or give the exact all-target upper coefficient. There is still
no all-target o(log n) error estimate and no universal contradiction.

The mixed-modulus review in this continuation did not find an alternative
valid gluing argument. The existing same-field root formulas still cannot be
used after changing the modulus without handling the quotient/carry terms.
