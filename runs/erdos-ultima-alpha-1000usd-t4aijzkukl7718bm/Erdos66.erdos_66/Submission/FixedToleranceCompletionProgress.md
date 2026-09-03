# Fixed-tolerance and count-only completion criteria

## Original task status

The conjecture in `Submission/Spec.lean` remains unresolved. Its original
statement, import, and sorry are unchanged. No proof was submitted.

## Exact reformulation of the weighted-deficit condition

Write L(n)=log(n+2) and

    W(n) = L(n) sqrt(L(n)) / sqrt(n+1).

`FixedToleranceCompletionExplore.lean` proves, for c>=0, the equivalence of:

1. There exists d(n)>=0 with d(n)/L(n)->0 such that

       sum_n max(0,cL(n)-d(n)-r_A(n)) sqrt(L(n))/sqrt(n+1)

   converges.
2. For every fixed epsilon>0,

       sum_{r_A(n)<=(c-epsilon)L(n)} W(n)

   converges.

Main theorem:
`Erdos66FixedToleranceCompletion.allowance_iff_fixed_tolerance_costs`.

For 2=>1, apply weighted exceptional-set diagonalization to
max(0,c-r_A(n)/L(n)), with weight W. On the resulting exceptional set E
choose d=0; off E choose the full nonnegative deficit. Then d/L->0 and
the remaining weighted deficit is at most c times the W-weight of E.
For 1=>2, eventually d<epsilon L/2, so a fixed epsilon-shortfall contributes
at least epsilon L/2 to the actual deficit.

The existing actual-deficit completion theorem now gives
`completion_of_fixed_tolerance_costs`: in the presence of the all-target
asymptotic upper bound c, condition 2 yields a superset B with
r_B(n)/log n -> c.

## Tolerance-dependent power exponents

`completion_of_tolerance_dependent_power_costs` assumes, separately for
each epsilon>0, some alpha(epsilon) in (1/2,1) for which

    sum_{r_A(n)<=(c-epsilon)L(n)} (n+2)^(-1+alpha(epsilon))

converges. Each such power eventually dominates W(n), up to a constant,
since alpha-1/2 is positive and absorbs the logarithmic factor.

**No common alpha>1/2 is required.** The alpha values can approach 1/2 as
epsilon shrinks. Diagonalization happens with the common repair weight W,
after the separate comparisons, not with a common power weight.

## Count-only endpoint

`CountingPowerCompletionExplore.lean` proves
`Erdos66CountingPowerCompletion.completion_of_tolerance_dependent_count_bounds`.

Assume the same all-target asymptotic upper bound c. For every epsilon>0,
suppose there are K(epsilon)>0 and 0<theta(epsilon)<1/2 such that eventually

    count({n: r_A(n)<=(c-epsilon)L(n)},N)
      <= K(epsilon)*(N+2)^theta(epsilon).

Then a superset B satisfies r_B(n)/log n -> c.

The generic supporting lemma `power_summable_of_count_bound` proves that a
set of count O(N^theta) has summable reciprocal s-power weight whenever
s>theta>0. For an infinite E, use its increasing enumeration a_k, the
bound k<=count(E,a_k), and comparison with the convergent k^(-s/theta)
series. Finite E is handled separately. Choose theta<s<1/2 and alpha=1-s.
The exponents theta may approach 1/2; they need not have a common margin.

## Verification and remaining gap

Both production files compile and have built oleans. Their principal
theorems pass `FixedToleranceCompletionAxiomCheck.lean` and
`CountingPowerCompletionAxiomCheck.lean`, using only propext,
Classical.choice, Quot.sound. Neither production file contains sorry or a
new axiom.

This corrects an overly strong possible reading of earlier progress notes:
a UNIFORM power saving beyond the square-root boundary is not necessary.
What is still missing is a sub-square-root lower-exception count at EACH
fixed tolerance, plus the correct all-target upper coefficient. The checked
positive construction supplies only an unspecified positive power saving,
which can be much less than 1/2, and only a wider O(log n) upper envelope.
No implication supplying the two missing hypotheses has been established.

A review of scale gluing did not supply a mixed-period compatibility lemma.
Common-modulus flatness, outer carry smoothing, and dense-palette completion
do not by themselves control all intermediate natural-number scales.
