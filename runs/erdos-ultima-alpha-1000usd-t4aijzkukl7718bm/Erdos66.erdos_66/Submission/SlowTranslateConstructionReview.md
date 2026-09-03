# Slowly growing translate families: endpoint review

## Status

This is a mathematical review, not a new Lean theorem or a solution.
Spec.lean remains unchanged with its original sorry. No proof was submitted.

## Candidate mechanism

One could try A=B+C, where B has counting scale sqrt(N), while C has about
sqrt(log N) active translations (for example, a sufficiently sparse sequence
whose logarithms grow quadratically). If overlaps were negligible and the
translations were mostly small relative to N, this suggests the desired
sqrt(N log N) counting scale.

For a FINITE translation family, if every element of B+C has a unique
B+C decomposition, its indicator equals the convolution of the indicators
of B and C. The ordered representation function is then the convolution
of the two individual ordered representation functions. This identity
requires uniqueness; a union with overlaps is not a multiset convolution.
No new Lean declaration for this identity was added in this review.

Counting scale alone does not establish a pointwise asymptotic. The actual
missing estimate is uniform accuracy of the increasingly long, sparse
translate average of r_B, simultaneously at every sufficiently large target.
An average over unrelated finite cyclic translations is not this estimate.

## Issues that cannot be discarded

* Every retained translate of B passes its representation peaks to A.
  Averaging is nonnegative and cannot erase such inherited peaks. A candidate
  base therefore needs an adequate pointwise upper bound of its own.
* The number of active translates and their truncation near the target
  matter. Infinite formal convolution identities require targetwise locality
  and cannot silently replace a varying finite sum by a fixed one.
* Negligible counting overlap alone is not a uniform o(log n) bound on the
  representation error caused by treating overlaps as multiplicities.
* Random sampling at total mean proportional to log n still supplies only
  the existing fixed-relative-error tail certificate. No new estimate was
  obtained that makes its all-target tolerance shrink at fixed coefficient.
* TranslateKernelAveragingExplore already averages an arbitrary old set
  exactly over a finite group and has a universal finite palette version.
  Its group/color-size cost and its later cyclic extension do not establish
  the sparse natural translate average required here.

Thus this mechanism remains conditional, and has not produced a new host
meeting the clipping/completion budgets or the compactness criterion. The
latest new compiled result remains PowerLogEndpointExplore.lean, which only
excludes a different weighted pointwise-transfer route.
