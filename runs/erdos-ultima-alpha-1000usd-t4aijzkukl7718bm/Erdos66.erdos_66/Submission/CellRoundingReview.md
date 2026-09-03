# Review of one-point-per-cell rounding and smoothing

## Status

No new verified proof, disproof, or construction was obtained in this review.
Spec.lean is unchanged with its original sorry. No proof was submitted.

## Candidate selection space

Partitioning a cumulative fractional profile into roughly unit-mass cells
and choosing one integer per cell provides a natural count-balanced choice
space. Boundary-cell masses must be handled explicitly; arbitrary uniform
choices in integer cells do not automatically have the exact desired
marginals. The ordered dependent-rounding infrastructure already supplies
actual Boolean roundings with every prefix bracket retained.

The missing theorem is still a joint selection of positions with uniformly
sublogarithmic quadratic self-error. Count balance alone does not supply it;
the checked bounded-discrepancy peak examples remain relevant.

The available exponential-tail certificates for selecting many constraints
still impose a fixed coefficient-versus-tolerance budget at logarithmic mean.
Rephrasing the coordinates as cell positions does not by itself prove a
stronger certificate. No lower bound showing that EVERY cell-based selection
must fail was proved or claimed here.

## Repair and local optimization

The existing finite local-move identities and cell-preserving replacement
lemmas remain valid. Distinct-cell packet capacity, however, does not cover
dense exception families at shrinking tolerances. Allowing repeated use of
points requires a genuinely joint signed or shared-point argument. None was
obtained from the existing per-target collateral estimates.

A local minimum of aggregate squared error is not a proof of uniformly small
maximum error. Likewise, reducing a selected moving target does not preserve
all earlier lower bounds without a cumulative footprint estimate. No such
new estimate was established.

## Smoothing review

Thickening each sparse coarse point by a short interval would convolve its
representation sequence with a triangular kernel, provided the intervals
are disjoint. The cardinality and convolution coefficient grow as well;
they cannot be ignored while claiming density-preserving averaging.

A fixed smoothing width does not give the growing-window estimates needed
to infer pointwise accuracy. Increasing the width requires new control of
local mass, integer carries, overlaps, and compatibility across scales.
The existing repeated-pattern restrictions also continue to apply whenever
literal long progressions are introduced. No infinite smoothing operator
meeting all of these requirements was constructed.

## Remaining issue

There is still no Boolean rounding with the required uniform quadratic
estimate, no compatible changing-palette chain, no global repair satisfying
the completion criterion, and no universal logarithmic-scale contradiction.
This review does not strengthen any necessary condition into a negation of
the original existential conjecture.
