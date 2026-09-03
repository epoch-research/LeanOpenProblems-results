# Expected-mass-sensitive rotation discrepancy and ordinary carries

## Original task status

Erdos66.erdos_66 remains unproved and undisproved. Submission/Spec.lean is
unchanged with its original import, statement, and sorry. No main proof or
exact-negation theorem has been submitted.

## New rotation estimate

Write

    rotationSum(alpha,x,rho,N)
      = sum_(k<N) [floor(x+k alpha)-floor(x+k alpha-rho)].

Assume Q^2 |alpha-sqrt(2)| <= 1, N<=Q, and rho>=0. The new theorem proves

    |rotationSum-N rho| <= 30+50 log(N rho+1).

The previous bound was 25 log(N+1). Both remain available; the new bound is
useful for narrow windows, and is not claimed to dominate the old bound
for every parameter choice.

For 0<=rho<=1, the exact complementary-window identity gives the stronger

    |rotationSum-N rho| <= 30+50 log(N min(rho,1-rho)+1).

The complementary count starts at x-rho, not at x. That shift is retained.

## Proof

The existing approximation lemma supplies a block d with

    0<d<=N, N+1<=5d,
    |rotationSum(alpha,x,rho,d)-d rho|<=5 for every x,rho.

If N rho<=1, positivity and monotonicity of rotationSum compare the count
with five full d-blocks. Their total is at most 5d rho+25<=30. Thus the
absolute discrepancy is at most 30, independently of N.

Otherwise remove one d-block. For R=N-d, one has R<=4N/5 and N rho>1, hence

    R rho+1 <= (9/10)(N rho+1).

The inequality log(9/10)<=-1/10 pays for the block error five with a factor
50 in front of the logarithm. Strong induction stops in the small-mass
case instead of continuing down to orbit length zero.

## Same explicit finite phase and a uniform relative endpoint

For every positive M retain the old phase

    b = floor(M sqrt(2)) mod M.

For Q^2<=M, t<M, u<=Q, and every starting phase a, put

    rho=(t+1)/M, N=u-l (natural truncated subtraction).

The exact finite endpoint count over [l,u) has error at most
30+50 log(N rho+1). A balanced version gives an IntervalBound with
30+50 log(Q min(rho,1-rho)+1).

`exists_uniform_relative_mass_threshold` proves that for every epsilon>0
there is ONE T>0, before all M,Q,t,l,u,a, such that N rho>=T implies
absolute discrepancy <=epsilon N rho under the preceding horizon bounds.
It uses the checked limit

    (30+50 log(X+1))/X -> 0.

Thus expected hits tending to infinity suffice for vanishing relative
error, even when the width tends to zero. The horizon Q^2<=M is still
explicit and has not been removed.

## Actual ordinary carry endpoint

For antitone row sets C_k, the same phased rows b*k+C_k retain row zero.
With q>0, t<M and (q+1)^2<=M, let phaseMass and halfMass be the existing
exact coarse quantities, and rho=(t+1)/M. The new theorem gives

    |r(qM+t)-rho phaseMass(q,t)-(1-rho)phaseMass(q-1,t)|
      <= [60+100 log((q+1)rho+1)]
           [halfMass(q,t)+halfMass(q-1,t)].

The balanced endpoint replaces rho INSIDE THE ERROR LOGARITHM by
min(rho,1-rho). It does not change the mean, drop the upper carry, or equate
the two different coarse targets. No phase is selected separately for a
target.

## Verification

All three production files compile without warnings and have current oleans:

* RotationMassLogBoundExplore.lean
* DiscreteRotationMassExplore.lean
* MassSensitivePhaseCarryExplore.lean

RotationMassAudit.lean audits 16 declarations. Its saved log reports only
propext, Classical.choice, and Quot.sound. There are no production sorries
or new axioms. RotationMassChecks.lean and RotationComplementChecks.lean
are scratch API checks, not production dependencies.

## Remaining main gap

This removes an avoidable orbit-length loss in narrow-window discrepancy.
It does not create the accurate unsigned coarse convolution, remove the
halfMass factor, reset a sparse palette minimum, or make two changing
moduli compatible. The full-lift mass mismatch and the original infinite
finite-feasibility quantifiers remain unresolved. No conclusion settling
Spec.lean follows from these estimates alone.
