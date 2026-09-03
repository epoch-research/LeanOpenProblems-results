# Explicit greedy trajectories and numerical envelope verification

**Historical note:** The missing concrete-guard, integrated-variance, failure,
and square-transfer work described below is now completed for every fixed
normalized horizon, and the growing-horizon argument is now completed as
well. See GreedySquareGainResearchNotes.md and GreedyLogGainResearchNotes.md.
The strongest actual lower bound is now (1/10000000)*N^(2/3), with no
logarithmic loss. The original conjecture nevertheless remains unsettled.

This is NOT a settlement of Erdős 773. Spec.lean is unchanged, with its sole
admission for 0<epsilon<=1/3. No actual Sidon exponent or endpoint improved.
The strongest actual lower bound remains (5/4)N/(N log N)^(1/3).

## New verified modules

Nine modules, 1482 lines, 43 printed audits:

* GreedyProfileDrift.lean: 184 lines, 8 audits.
* GreedyProfileVariance.lean: 154 lines, 4 audits.
* GreedyTrajectoryCalculus.lean: 283 lines, 8 audits.
* GreedyEnvelopeCalculus.lean: 152 lines, 6 audits.
* GreedyScaledTrajectory.lean: 110 lines, 4 audits.
* GreedyDriftBudget.lean: 86 lines, 2 audits.
* GreedyOneStepProfiles.lean: 94 lines, 1 audit.
* GreedyPhysicalStep.lean: 190 lines, 6 audits.
* GreedyUniformHorizon.lean: 229 lines, 4 audits.

All are built without warnings or admissions and use only propext,
Classical.choice and Quot.sound. None imports admitted Spec.lean.
The nine-module audit is /tmp/greedy-numerical-trajectory-final-audit.log.
Combined with the preceding eleven modules, there are 118 checks:

    /tmp/greedy-concentration-trajectory-combined-audit.log

The temporary CheckTrajectoryAPI.lean was deleted.

## Drift errors from profile boxes

`GreedyProfileDrift` first proves the unavailable-vertex simplifications:
its incident sets and safe choices are empty and its survival drift is zero.
It also proves that incident size j>r is empty if original edge sizes are <=r.
For an available u in a linear hypergraph,

    |safeChoices(u)| = Q-1-d_2(u).

The following estimates use actual survival drifts R_j, not unconditional
updates of already dead vertices. Suppose all available d_2 values satisfy
|d_2-f_2|<=e_2 and the tracked d_j,d_{j+1} values have the indicated errors.
The deterministic f_2 and e_2 are nonnegative. Common-neighbor counts are <=C.

For two-degrees:

    |R_2-(2*f_3-f_2^2)|
      <= 2*e_3+f_2*e_2+(e_2+1+C)*(f_2+e_2).

For j>=3:

    |R_j-(j*f_next-(j-1)*f_2*f_j)|
      <= j*e_next+(j-1)*f_2*e_j
         +((j-1)*(e_2+1)+choose(j,2)*C)*(f_j+e_j).

Direct-loss and common-neighbor terms are retained. If actual Q is within
E_Q of a deterministic q and d_2(u) is within e_2 of f_2, then

    ||safeChoices(u)|-q| <= E_Q+1+f_2+e_2.

The generic numerator inequality is

    |R-S*slope| <= D+|M-q*slope|+E*|slope|

when |R-M|<=D and |S-q|<=E. Finally, if this error is <=s_min*growth,
S>=s_min, and growth>=0, then

    R-S*(slope+growth) <= 0,
    -(R-S*(slope-growth)) <= 0.

Thus growing envelopes can provide global guarded supermartingale signs,
without needing a critical-region hypothesis. Critical excursions remain
available, but are not necessary for this proposed instantiation.

## Explicit conditional variance controls

`GreedyProfileVariance` converts uniform caps into deterministic raw
second-moment numerators, including when u is unavailable:

    Vraw_2 = (C+1)*(2*U_3+U_2^2),
    Vraw_j = (U_2+1)*(j*U_next+(j-1)*(U_2+1)*U_j), j>=3.

The raw increment caps are C+1 at j=2 and U_2+1 at higher sizes. If Q>=q_min>0,
the recorded error second moment is <=

    2*Vraw_j/q_min + 2*(Delta f)^2.

`two_moment_control` and `higher_moment_control` build actual MomentControl
instances for any guard implying the supplied degree/common-neighbor/Q
caps and Valid. They keep the total increment cap b and all guard bounds
explicit. These are not yet time-integrated variance estimates.

## Checked normalized trajectory calculus

Define

    q(t)=exp(-t^3),
    a_2(t)=3*t^2*q(t),
    a_3(t)=3*t*q(t)^2,
    a_4(t)=q(t)^3.

All first and second derivatives are checked in Lean:

    q'=-a_2,
    a_2'=(6*t-9*t^4)*q,
    a_3'=(3-18*t^3)*q^2,
    a_4'=-9*t^2*q^3,
    a_2''=(6-54*t^3+27*t^6)*q,
    a_3''=(-72*t^2+108*t^5)*q^2,
    a_4''=(-18*t+81*t^4)*q^3.

The exact mean-field identities are

    q*a_2'=2*a_3-a_2^2,
    q*a_3'=3*a_4-2*a_2*a_3,
    q*a_4'=-3*a_2*a_4.

`first_order_remainder` proves from a second-derivative bound C that the
first-order remainder on [a,b] is <=C*(b-a)^2. The harmless constant 1 avoids
Taylor integration. It uses two finite mean-value bounds, not an assumed
series expansion.

On 0<=t<=tau, all |a_j''|<=200*(1+tau)^6. The first derivatives have coarse
bound 30*(1+tau)^4, and weighted versions retain q(t)^(j-1). On a step
0<=h<=1 the checked local increment bounds are

    |a_j(t+h)-a_j(t)|
      <= 750*(1+t^2)^2*q(t)^(j-1)*h.

The q powers are essential; discarding them would destroy the planned drift
balance at logarithmic time. Availability has the separate remainder

    |q(t+h)-q(t)+a_2(t)*h| <=30*(1+tau)^4*h^2.

## Physical scaling and one-step remainders

For original degree d^3 and V vertices, the normalized step is delta=d/V.
Define

    F_2=d*a_2, F_3=d^2*a_3, F_4=d^3*a_4, Qprofile=V*q.

Write M_2=2*F_3-F_2^2, M_3=3*F_4-2*F_2*F_3,
M_4=-3*F_2*F_4. With t+delta<=tau, the checked residual bounds are

    |M_j-Qprofile(t)*(F_j(t+delta)-F_j(t))|
      <=200*(1+tau)^6*(d^(j+1)/V)*q(t), j=2,3,4.

The physical availability remainder is <=30*(1+tau)^4*d^2/V. It does not
silently include the additional -1 for the chosen vertex. Physical slope
bounds are

    |Delta F_j|<=750*(1+t^2)^2*(d^j/V)*q(t)^(j-1).

## Growing errors with matched q powers

For K and r define

    growth(K,r,t)=exp((K-r)*t^3+K*t),
    budgetWeight(K,t)=growth(K,0,t)/(1+t^2).

The r values 0,1,2 correspond to residual sizes 2,3,4. Consecutive growth
weights differ exactly by q. For K>=3 and r<=2, the finite increment satisfies

    Delta growth(K,r,t)
      >= K*(1+t^2)*growth(K,r,t)*delta.

The derivative of budgetWeight is >=(K-1)*growth(K,0,t); for K>=1 its finite
increment has the same lower bound times delta.

For a relative error parameter rho>=0, define

    E_2=d*rho*growth(K,0,t),
    E_3=d^2*rho*growth(K,1,t),
    E_4=d^3*rho*growth(K,2,t),
    E_Q=V*rho*budgetWeight(K,t).

Then E_3=(d*q)*E_2 and E_4=(d*q)^2*E_2, exactly. For a physical step,

    Delta E_j >= delta*K*(1+t^2)*E_j,
    Delta E_Q >= (K-1)*E_2.

The division by 1+t^2 is why E_Q can absorb accumulated E_2 errors without
introducing an unmanageable extra power of time in the drift numerator.

## Numerical absorption, not merely formal ODE identities

Let A=d*q, e=E_2, and s=1+t^2. Then the ideal profiles and errors are

    F_2=3*A*t^2, F_3=3*A^2*t, F_4=A^3,
    E_2=e, E_3=A*e, E_4=A^2*e.

If 0<=e<=A and C+1<=e, all three explicit drift errors above are bounded by

    40*s*A^k*e, k=1,2,3.

`GreedyDriftBudget.absorb` checks the full scalar calculation. Assume
Q*delta=A, E_Q*delta*s=e, S>=Q/2, |S-Q|<=2*E_Q, K>=4000, and:

    |R-M| <= 40*s*A^k*e,
    |M-Q*slope| <= A^k*e,
    |slope| <=750*s^2*delta*A^k,
    growth >=delta*K*s*A^(k-1)*e.

The numerator error is <=1541*s*A^k*e, while S*growth is at least
(K/2)*s*A^k*e. Both signed drift inequalities follow. No limiting or
approximation step is omitted.

`GreedyOneStepProfiles.three_drift_signs` applies this to an actual linear
hypergraph with edge sizes <=4. It verifies all six signs, including dead
vertices. The j=4 promotion term is zero because no residual size-five edge
exists. The safe count lower bound follows from E_Q<=Q/4 and
1+F_2+E_2<=E_Q, not from incorrectly replacing safe count by Q.

## Physical one-step conditions and Q propagation

`GreedyPhysicalStep.Conditions V d rho K t C` requires:

* V,d>0, rho>=0, K>=4000, t>=0, delta=d/V<=1;
* E_2<=d*q and C+1<=E_2;
* E_Q<=Qprofile/4 and 1+F_2+E_2<=E_Q;
* each of the three displayed Taylor remainder bounds (with tau=t+1)
  is <=(d*q)^k*E_2.

`signed_drifts` proves all six actual profile-plus/minus-error signs under
these numerical conditions and the current degree/common-neighbor/Q box.
It instantiates the analytic slope, growth and curvature estimates rather
than leaving a derivative approximation as a hypothesis.

`availability_remainder` shows that the two-degree curvature condition also
bounds the Q remainder by E_2. `availability_growth` proves
Delta E_Q>=2*E_2+1. Consequently `availability_box_step` proves that every
genuine choice from a state with |Qactual-Qprofile|<=E_Q and the local
E_2 degree bound still has the Q box after the step. This is deterministic.

## Uniform horizon validation

`GreedyUniformHorizon.Bounds` reduces all Conditions throughout [0,tau] to:

    V>0, d>=1, rho>=0, K>=4000, tau>=0, d<=V,
    rho*growth(K,0,tau) <= q(tau)/4,
    C+1 <= d*rho,
    5*d*(1+tau)^4 <= V*rho,
    200*(2+tau)^6*d <= V*rho*q(tau)^2.

`conditions` proves these imply Conditions at every real t in [0,tau].

These uniform assumptions are now proved nonvacuous. `polynomial_parameters`
takes d=m^4, rho=1/m and V>=m^12. For m>=17, C<=16*m, K>=4000, tau>=0, it
suffices that

    4*growth(K,0,tau) <= m*q(tau),
    5*(1+tau)^4 <= m,
    200*(2+tau)^6 <= m*q(tau)^2.

`eventually_bounds` verifies these eventually for natural m at every fixed
finite K,tau. More strongly, `exponential_threshold` proves explicitly, at
K=4000, that

    m >= exp(10000*(1+tau)^3), V>=m^12, C<=16*m, tau>=0

suffice. This permits normalized horizons of order (log m)^(1/3). It is an
actual checked uniform scalar estimate, not only a proposed profile.

## What was still missing at the time of this note

Despite the analytic progress, no unconditional long greedy run has been
proved. In particular, the following work has NOT yet been done:

1. Construct and validate the concrete profile guard with the actual process,
   regular initial degrees, and the six signed recorded tests per vertex.
2. Prove its Q box at every reachable running state using the new physical
   availability_box_step (the earlier abstract Reach method is a template).
3. Establish uniform upper bounds on Delta E_j and on the conditional moment
   budgets, sum them to T, and bound each actual crossing probability.
4. Combine these with the all-subset common-neighbor tail, including its
   vertex-pair union, and prove total failure probability <1.
5. Prove that good states imply the guard and readiness, then invoke the
   already-verified path and independent-set extraction.
6. Transfer any resulting independent-set bound through square linearization
   and regularization with the actual losses tracked.

For a convenient next parameterization, d=m^4, original degree=m^12,
rho=1/m and C=16*m match the common-neighbor witness threshold with packing
parameter m. The initial error levels are m^3,m^7,m^11. With V polynomial
in m, expected integrated variance scales (up to horizon factors) are
m^5,m^12,m^16, giving potentially strong crossing tails. THESE INTEGRATED
VARIANCE AND TAIL ESTIMATES ARE NOT YET PROVED.

One can first work at a fixed arbitrary tau, where all exponential and
polynomial horizon factors are constants, before attempting a growing tau.
A prospective V<=m^400 bound would accommodate the intended square
regularization sizes, but no such specialization has been carried out.

Even a completed logarithmic-gain generic extraction remains at the 2/3
square-Sidon exponent scale. A square-specific near-linear construction or
a fixed-power upper bound is still required to settle the original problem.
No such arithmetic breakthrough was obtained in this continuation.

## Main file and logs

Main check: /tmp/spec-numerical-trajectory-check.log. It reports the expected
admission and pre-existing linter warnings, with no errors. The original
conjecture statement and import remain unchanged. The sole sorry is at
line 2031; Spec.lean SHA-256 is still

    917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.

No proof or disproof has been submitted.
