# All-cutoff fixed-damping means — the conjecture remains unresolved

Spec.lean is unchanged with its original sorry. No prime-pair lower bound,
sufficient signed four-factor gap, or irrational counterexample has been
proved. No incomplete proof was submitted.

## OrdinaryRotationMean.lean

Namespace Erdos972OrdinaryRotationMean.

Reuses the existing finite weighted Fejer discrepancy inequality with weights
identically one. Every nonzero integer multiple of an irrational theta is
irrational, so its phase differs from one. A geometric-sum bound gives

    |sum_(n<K) exp(2 pi i h theta n)| <= 2/|exp(2 pi i h theta)-1|.

For a fixed finite frequency cutoff H, the sum of these bounds is a finite
constant independent of K and the starting phase. First choose the arc
smoothing margin, then H, then let K tend to infinity.

Verified:
- ordinary_arc_mean: every fixed interval strictly inside (0,1) has its
  expected mean, at every fixed starting phase.
- fract_shift_arc: exact translation of an initial fractional-part arc to
  such an interior interval, including its half-open endpoint convention.
- rotationInterval_mean: for irrational theta and 0<t<1,

      #{n<K : fract(theta*n)<t}/K -> t

  along ALL natural K.

## OrdinaryDivisorMean.lean

Namespace Erdos972OrdinaryDivisorMean.

- divisorRow_mean: for alpha>=0 irrational and fixed d,e>0,

      #{k<K : e divides floor(alpha*d*k)}/K -> 1/e.

  The e=1 case is handled separately.
- divisorPairs_mean: using the exact progression-count correction,

      #{0<n<=N : d|n and e|floor(alpha*n)}/N -> 1/(d e).

  These are all-N means, not merely common good-scale estimates.
- truncated_correlation_mean: for a fixed D, the normalized finite-divisor
  damped correlation tends to divisorMean(D,a_t)^2.

## OrdinaryDampedCorrelation.lean

Namespace Erdos972OrdinaryDampedCorrelation.

Combines the all-N finite-divisor means with the previously proved tail
approximation uniform in N for each FIXED t>0. For alpha>=1 irrational:

    fullExpCorrelation(t,alpha,N)/N -> m(t)^2,
    smoothCorrelation(t,alpha,N)/N -> (m(t)/t)^2,
    m(t)=sum'_d mu(d) exp(-t log d)/d=1/zeta(1+t).

Both limits now hold along ALL natural N; the selected-scale restriction
from FixedDampedCorrelation.lean is no longer needed at fixed positive t.
The n=1 correction is retained in the transfer to smoothMangoldt.

The outer scalar limit (m(t)/t)^2 ->1 as t->0+ is also recorded.

## Remaining gap

These statements are ITERATED limits: fix t>0 first and take N->infinity.
Their convergence thresholds can depend on t. They do not provide a lower
bound at the prime-comparison parameters t_N with t_N log(N)^2->0.

The previous L1 noncommutation theorem and the damping-factor incompatibility
still apply. Neither pointwise convergence nor all-N fixed-t convergence
justifies exchanging these limits. The full prime-detecting signed estimate
remains unproved.

AuditOrdinaryDampedCorrelation.lean compiles. All eight audited declarations
use only propext, Classical.choice, and Quot.sound.
