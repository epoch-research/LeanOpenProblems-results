# Review of density-adapted spatial resolution

## Status

This review produced no new verified construction or disproof of Erdős 66.
Spec.lean is unchanged with its original sorry. No proof was submitted.
The observations below diagnose a proposed construction; they are not new
Lean-verified impossibility theorems for arbitrary sets.

## Proposed construction

Use a small period for dense early pieces and a larger period for sparse
later pieces. Each period would be small relative to its eventual spatial
location. The aim was to make endpoint-prefix errors local rather than
measured against a much larger full-period mean.

The existing mixed prefix engine has absolute error relative to the full
mixed mean. It does not automatically give relative accuracy in a short
prefix. The fixed-height monotone operator therefore still cannot be used
with an increasing inverse-square-root height range and a fixed initial
natural cutoff.

## Common-source clipping

ClippedTwoPeriodExplore already permits different members of one common
source palette in its mixed-count comparisons. Retuning the members can
change density. Exact short-prefix agreement, however, was proved for the
SAME source member. It cannot be reused after changing members.

An actual piecewise assembly could keep the old part and use the new member
later, provided that the old member belongs to the same selected source.
The remaining problem is selecting a new common source after a previous
natural prefix or template has already been prescribed. This review found
no such extension theorem. Choosing an unrelated common source separately
for each pair of scales does not give an infinite compatible chain.

## Equal-fiber route

A simple exact cross-count mechanism is worth distinguishing from a
solution. In a product G x H, let the old set be B x H, and suppose a new
set has exactly k points over EVERY residue of G. Their mixed count is
then k|B| at every target, independently of the internal new fibers.

For nonempty integer fibers, k>=1. If |G|=M and |H|=R, fitting this to
logarithmic density at an ambient scale comparable to MR requires,
heuristically, R log(MR) to be at least of order M. On the other hand,
retaining a complete old cylinder multiplies its self-count mean by R;
a logarithmic cap only allows R times the old mean to be O(log(MR)).
These are the same competing scale costs already reflected in the checked
common-period and repeated-pattern results.

This does not exclude nonuniform fibers, sparse high-block selections,
clipped patterns, or constructions without a complete old cylinder. No
extension using those alternatives was obtained.

## Other reviews

* Separate self-flatness still cannot supply the missing mixed estimate:
  a reflected copy turns a mixed sum into an autocorrelation, which can
  have a large peak even if both self-sum profiles are flat.
* Independent partial refresh retains the checked logarithmic tail-budget
  obstruction; breaking the change into small steps alone does not prove
  cumulative o(log n) error.
* The fixed-additive-cap obstruction from SharpCapRoundingProgress.md does
  not apply to unbounded sublogarithmic slack. No rounding rule achieving
  that weaker, still sufficient accuracy was constructed here.
* A renewed request to https://www.erdosproblems.com/66 failed DNS
  resolution. No new external theorem or claimed solution was obtained.

## Still missing

There is no compatible density-changing palette chain, Boolean rounding
with uniform sublogarithmic quadratic error, globally controlled repair,
or universal contradiction on the logarithmic error scale. In particular,
none of this review changes the unresolved status of the original theorem.
