# Simultaneous infinite sparse rank restoration

## Original conjecture status

The original conjecture is still neither proved nor disproved.
`Submission/Spec.lean` is unchanged and retains its original `sorry`.
Its SHA256 remains
`32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0`.
No auxiliary result below is being substituted for the conjecture.

## Main new theorem

Namespace: `Erdos66SimultaneousRankRestoration`.

`exists_simultaneous_sparse_restoration` proves:

If A has all exact harmonic-profile prefix brackets, D is a subset of A,
and

    count(D,N) / sqrt(N log N) -> 0,

then there is B containing A\D such that:

* B has every original exact harmonic-profile prefix bracket;
* [r_B(n)-r_(A\D)(n)] / log n -> 0.

The difference is nonnegative because A\D is contained in B.
It is measured from the DELETED CORE, not from A. The theorem does not
claim that deletion itself has negligible representation effect.

One set B works for all targets and all shrinking tolerances. This is
not an iteration that adds per-batch epsilon-log error allowances.
There is no summability-rate assumption on the deletion-density decay.
No representation envelope, boundary certificate, or triple cap is assumed
on A beyond its exact prefix brackets.

## Construction and analytic estimate

For every sufficiently large deleted point d, the rank-cell window theorem
supplies an interval near d, all of whose sites have rank cell count(A,d).
The window width is densityWindow(floor(d/2)), of order sqrt(d/log d).
Deleting old A-sites from this interval leaves at least half the sites.
Uniform candidate mass therefore totals one per row, the filled row mass
is at most two, and the row probability is bounded pointwise by
256 times the harmonic profile. Rows corresponding to distinct old points
are ordered and disjoint. Every row site i satisfies d <= 2i and i <= 2d.

The logarithmically sharp lower bound

    log(n+1) <= 4(2n+1) profile(n)^2

is essential to the universal pointwise majorant.

The actual insertion matching pattern has Boolean value

    r_(A union F)(n)-r_A(n).

Its fractional mean is at most

    2(q * indicator(A))(n) + (q*q)(n) + 1.

The mixed convolution is NOT controlled merely from negligible q-prefix
mass. The proof uses constant-height interval rows in the middle and
truncated Abel comparisons at the boundaries.

At cutoff m=floor(n/d^2), the two boundary portions are bounded by constant
multiples of boundaryMean(d,n), plus a fixed bracket-error allowance.
The middle uses the actual row total mass and row total height.
If R(n)=count(D,2(n+1)+1), the full fractional insertion mean is bounded by

    (4C+2C^2) boundaryMean(d,n)
       + 16C+1 + (4+6C) profile(m) R(n),

with C=256 (and with the treated tail of D in place of D when needed).
For each fixed d, profile(m) R(n)/log(n+2) tends to zero. The boundary term
has normalized upper bound O(1/d). Taking d arbitrarily large proves the
actual mean is o(log n).

Countable positive-pattern rounding then selects one F with exact brackets
for q, no selected zero-probability sites, and sublogarithmic actual
representation increment. Integer q-mass at every row boundary forces
exactly one selected point per row. The rank assignment maps F bijectively
to the treated tail of D.

An infinite-rank-swap lemma transfers finite rank swaps to each prefix,
using i <= 2d to choose a large enough finite truncation. The finite initial
portion of D is left in B; its representation contribution is uniformly
bounded and therefore disappears after division by log n.

## Verification

Thirteen production files were rebuilt in dependency order, with no warnings:

1. InsertionMatchingPatternExplore.lean
2. TruncatedProfileComparisonExplore.lean
3. TruncatedConvolutionAlgebraExplore.lean
4. SparseRowConvolutionBoundsExplore.lean
5. SparseRowMeanDecayExplore.lean
6. InfiniteRowProbabilityExplore.lean
7. InfiniteIntervalRowsExplore.lean
8. SparseRowCountingScaleExplore.lean
9. InfiniteRankSwapExplore.lean
10. SimultaneousIntervalRowSelectionExplore.lean
11. InfiniteRankWindowExplore.lean
12. InsertionIncrementComparisonExplore.lean
13. SimultaneousRankRestorationExplore.lean

`SimultaneousRankRestorationAudit.lean` audits all 57 theorem/lemma
declarations in these files. Its saved log reports only propext,
Classical.choice, and Quot.sound. The current oleans are built.

The four preceding profile/pattern-rounding files are independently audited
in `PatternSublogRoundingAudit.lean` and its saved log (12 declarations).
`InsertionMatchingPatternAudit.lean` also records its eight declarations.

## Remaining original-conjecture gap

The available host has exact brackets, a global O(log n) envelope,
density-one coefficient-one convergence, and power-saving exceptions at
each fixed tolerance. The power savings may be much smaller than 1/2 as
the tolerance shrinks. These facts do NOT establish a negligible deletion
set clipping all upper exceptions, nor a simultaneous upward repair of all
lower exceptions. The aggregate incidence and clipping-demand requirements
from the previous finite pipeline remain unverified for such dense target
sets.

The new theorem solves the infinite sparse RESTORATION problem, not the
problem of producing suitable sparse corrections to the original host.
It must not be used as if it changed r_A by o(log n), or as if any collection
of exceptional targets automatically had negligible endpoint demand.

A subsequent review of the already documented alternatives did not supply
a new all-prefix construction or universal obstruction. In particular,
finite cyclic flatness, fixed-field palette transfer, and good annuli are
still not a compatible changing-scale integer construction. The existing
higher-moment lower bounds remain at square-root-logarithmic scale; the
checked finite/annular counterexamples prevent silently assuming a uniform
Gaussian growing-moment amplification from Boolean convolution alone.
