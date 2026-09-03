# Checking the unrestricted-incidence criterion against the existing base

## Status

No proof or disproof of the original conjecture was obtained in this review.
Spec.lean is unchanged. No new mathematical theorem is asserted here.

## The hypothesis actually needed

The new unrestricted repair criterion uses

    degree(cutoff(B,N), T_N, x)
      = #{b<N : b in B and x+b in T_N},

where B is the hypothetical COMPLETED set and x is a newly added point.
Persistent delta log N deficits, together with negligible normalized added
count, force this degree to exceed every fixed multiple of

    |T_N| sqrt(log N)/sqrt(N)

at some new point along arbitrarily large scales.

To deduce an obstruction, a uniform upper bound on those degrees would be
needed. None has been established for the current base and all possible
completions.

## Why the existing structural results do not imply it

* Local difference sparsity bounds pairs already in the base in one dyadic
  interval. It does not bound how a translate meets the entire exceptional
  target set.
* Central triple sparsity bounds each separate target correction's effect at
  another target. Summing those bounds over all exceptional centers can lose
  the entire saving. No uniform bound on that sum has been proved.
* The final-set degree includes new/new incidences. Even a hypothetical
  bound involving only the base would not automatically control those.
* Power-saving exceptional COUNT upper bounds do not control additive
  structure or degrees into those targets. They also are not lower bounds
  showing that a necessary capacity inequality is violated.

## Construction alternatives reviewed

Grouping exceptional targets into short intervals would change repair costs,
but no theorem localizes the current exceptions into intervals with the
required geometry. The mixed-period transition errors likewise have not been
shown to occupy only such short intervals.

The exact fractional harmonic profile and bounded prefix discrepancy still
leave its quadratic rounding-error convolution uncontrolled pointwise. No
new estimate eliminating that term was obtained.

Thus neither an unrestricted-sharing completion nor a contradiction for all
candidate sets follows from this application check.
