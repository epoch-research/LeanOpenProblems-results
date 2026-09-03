# Actual bounded-discrepancy roundings can have unbounded peaks

Status: all six production files compile; principal statements axiom-audited.
This is an auxiliary obstruction, NOT a solution or disproof of Erdős 66.

## Files

- `ReflectionRoundingPatchExplore.lean`: count-preserving finite reflected patches.
- `FlatProfileWindowsExplore.lean`: suitable flat windows of the harmonic profile.
- `SetIntervalReplacementExplore.lean`: exact replacement count identities.
- `LargeReflectionPatchExplore.lean`: arbitrarily late large normalized peaks.
- `ReflectionStateExplore.lean`: extension with a fixed discrepancy bound of 11.
- `BoundedDiscrepancyPeaksExplore.lean`: stabilized infinite set.
- `BoundedDiscrepancyPeaksAxiomCheck.lean`: audits (only propext, choice, Quot.sound).

## Main result

`Erdos66BoundedDiscrepancyPeaks.exists_bounded_discrepancy_unbounded_peaks`:
There exists a set A with

    |count A N - cumulative profile N| <= 11 for every N,

and for every natural M,N there is n>=N with

    M <= sumRep A n / log n.

Consequently its normalized representation sequence has no finite limit.
`badRounding_error_prefix` expresses the discrepancy as the prefix sum of
`indicator A - profile`, so this is genuinely an actual 0/1 rounding example,
not an arbitrary signed error sequence.
`badRounding_quadratic_error_not_zero` verifies directly that this actual
rounding does not satisfy the missing quadratic-error limit.

## Mechanism

Choose k large, W=k^20, and one of k^12 adjacent windows of width 2W between
k^32 and 3k^32. Telescoping and the bound k^15 p(k^32)<=1 give at least one
window of integrated oscillation <=1. The profile lower bound supplies
W*p(L+2W)>=k^2/2. Each half of the canonical rounding therefore has at least
k^2/2-2 points.

Reflect left-half points into the right half, trimming/extending to the
original right-half cardinality. The replacement has prefix count change
at most 10 and creates at least k^2-4 representations at 2L+2W-1. This target
is <=6k^32, so the normalized peak can be made arbitrarily large.

Each patch preserves its total count exactly. A state agrees with canonical
rounding in both membership and counts beyond a cutoff; a new patch is placed
after that cutoff. Thus discrepancy remains <=11 without accumulation.
Freezing the entire new reflection target after each step yields pointwise
stabilization of membership. All count bounds and all previously created peaks
pass to the stabilized infinite set directly, without compactness.

## Scope

This rules out the universal assertion that bounded prefix discrepancy from
the harmonic fractional profile implies a logarithmic pointwise representation
limit. It does not settle the canonical floor rounding, a specially chosen
rounding, or the original existential conjecture.

`Submission/Spec.lean` remains unchanged with its original sorry.
