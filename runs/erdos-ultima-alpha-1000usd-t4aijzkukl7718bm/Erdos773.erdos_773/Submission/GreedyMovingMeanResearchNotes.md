# Moving means, survivor bias, and stationary centered energy

## Main problem remains UNSETTLED

Spec.lean is unchanged. The sole admission remains at line 2031 for
0<epsilon<=1/3. The strongest completed actual square-Sidon lower bound
remains M(N)>=N^(2/3)/500 eventually. No coefficient-one endpoint, exponent
improvement, or disproof has been obtained. No proof has been submitted.

Spec SHA-256:
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14

Read GreedySurvivalTargetResearchNotes.md for the already completed finite
hazard certificate, killed-kernel comparison, backward density profile,
capped target laws, and duplicate/common-neighbor survival tails. Those
results are not rederived here.

## Eight new clean modules

1. FiniteMovingMean.lean
2. GreedyAvailableMeanDrift.lean
3. FiniteKernelSizeBias.lean
4. GreedySurvivorBiasedKernel.lean
5. GreedyMeanCovarianceExample.lean
6. FiniteCenteredPowerDeaths.lean
7. FiniteCenteredStationarity.lean
8. GreedyCenteredEnergyDrift.lean

All have built oleans and compile without warnings, errors, or admissions.
All 42 printed main axiom audits use only propext, Classical.choice,
Quot.sound. No file imports admitted Spec.lean.

Independent fresh audit groups:

    /tmp/greedy-moving-mean-audit-1.log
    /tmp/greedy-moving-mean-audit-2.log
    /tmp/greedy-moving-mean-audit-3.log

Combined audit:

    /tmp/greedy-moving-mean-final-audit.log

## 1. Means on a changing available set

FiniteMovingMean defines mean(S,f)=sum_S f/|S|. Its exact cardinality-times-
mean identity includes empty sets. For current S, next T, old f and new g:

    |T|*(mean(T,g)-mean(S,f))
      =sum_T g-sum_S f-mean(S,f)*(|T|-|S|).

weighted_survivor_drift sums this identity through a finite survivor
relation T(v) subset S. Its right side is the sum of surviving local
increments, minus the death-weighted CURRENT CENTERED old values.

This is a NEXT-cardinality-weighted mean drift, not an ordinary conditional
mean. The distinction remains explicit.

reweighting_error proves, for |Q-w(v)|<=B:

    |Q*sum z(v)-sum w(v)*z(v)| <= B*sum |z(v)|.

average_upper_of_weighted deduces, for Q>0, B>=0, sum w*z<=D and sum|z|<=V:

    sum z/Q <= (D+B*V)/Q^2.

Thus conversion to uniform drift pays the actual absolute mean variation;
it does not silently equate the two drift notions.

## 2. Exact drift of actual mean degrees

Namespace Erdos773.GreedyAvailableMeanDrift.

Let Q=|available(H,I)|, D_j(u)=incident degree, f_j=the actual available-
vertex mean, R_j(u)=the existing survivalDrift, and

    Cov(j,k)=sum_{u available}(D_j(u)-f_j)*(D_k(u)-f_k).

For a legal choice v, write Q'_v for the next available cardinality.
weighted_mean_drift proves:

    sum_v Q'_v*(f'_j-f_j)
      =sum_u R_j(u)-Cov(j,2)+sum_u duplicateExcess(u)*(D_j(u)-f_j).

Combining with the existing exact neighbor-operator identities yields:

    sum_v Q'_v*(f'_2-f_2)
      =Q*(2f_3-f_2^2)-2*Cov(2,2)
       +sum_u c_2(u)+sum_u duplicateExcess(u)*(D_2(u)-f_2),

and, for j>=1,

    sum_v Q'_v*(f'_j-f_j)
      =Q*(j*f_(j+1)-(j-1)*f_j*f_2)-j*Cov(j,2)
       +sum_u c_j(u)+sum_u duplicateExcess(u)*(D_j(u)-f_j).

The c_j are the previously defined explicit nonlinear corrections. The
coefficient on mixed covariance is j, not j-1: vertex deaths supply another
copy. In the two-degree formula BOTH covariance copies are negative
variance. All empty-next-state cases are included correctly.

uniform_two_mean_upper converts the two-degree identity to the actual
uniform conditional drift, retaining -2*Cov(2,2) AND the B*V/Q^2 reweighting
error. The correction and variation bounds are explicit hypotheses.

## 3. An explicitly DIFFERENT survivor-biased greedy law

FiniteKernelSizeBias.tilt(K,f) uses weights K(x,y)*f(y)/K.avg(f,x) when the
normalizer is positive; when it is zero, it falls back to K. f is required
nonnegative everywhere. The theorem avg_tilt gives the exact tilted average,
and support_tilt characterizes support at a positive normalizer.

The general finite identity is

    tilted_mean(f)=ordinary_mean(f)+variance(f)/ordinary_mean(f).

No independence assumption is used. avg_tilt_le compares nonnegative
observables when f has a supported upper bound.

GreedySurvivorBiasedKernel applies this with f(J)=|available(H,J)| to the
existing stopped greedy kernel. In a ready state with positive

    Z=sum_{v available} Q'_v,

it chooses v with probability Q'_v/Z. Thus it is a legal greedy process,
but NOT the old uniform process. support_original proves that every
transition remains in the original legal support, including the zero-
normalizer fallback.

The exact conditional mean-degree drifts are the weighted identities in
section 2 divided by Z. No reweighting error is needed for this changed law.

Let b(v)=1+|closes(v)|, bbar=mean_S b, Var_b=mean_S (b-bbar)^2. Then

    ordinary normalizer=Q-bbar,
    biased E[Q'-Q]=-bbar+Var_b/(Q-bbar).

The last identity is availability_drift. Its variance term is favorable,
but this does NOT prove global stochastic domination, a longer run, or
control of the higher means. The old uniform and killed-uniform tail laws
have NOT been transferred to this biased process.

## 4. Verified sign obstruction for higher mixed covariance

GreedyMeanCovarianceExample is a METHOD CHECK, not a conjecture disproof.
On Fin 8 take

    H={{0,1,2,3},{4,5,6,7}}, I={0,1}.

The file verifies:
- four-uniformity;
- exact initial regular degree 1;
- disjoint distinct original edges;
- legal selections of 0 then 1, and independence of I;
- available={2,3,4,5,6,7};
- D2 is 1 on {2,3}, zero elsewhere;
- D4 is 1 on {4,5,6,7}, zero elsewhere;
- f2=1/3, f4=2/3, Cov(4,2)=-4/3.

Consequently -4*Cov(4,2) is POSITIVE. It cannot be dropped with the sign of
-2*Cov(2,2), even under exact initial regularity and complete linearity.
The example does not assert that the FULL higher mean drift is positive.
Finite checks use decide +kernel, not native_decide.

## 5. Optimized power energy with ALL death mass retained

FiniteCenteredPowerDeaths extends the earlier optimized-center lemma.
Let c minimize E_p(S,f)=sum_S |f-c|^p. For T subset S and any next comparison
center a:

    E_p(T,g)-E_p(S,f)
      <=sum_{u in T} (|g(u)-a|^p-|f(u)-c|^p)
        -sum_{u in S\T}|f(u)-c|^p.

survivor_taylor supplies the previously proved variance-sensitive remainder
for even p=n+2, allowing a per-vertex increment cap B(u). death_sum double-
counts the second sum across choices, giving the exact death multiplicity
of every old coordinate. No death mass is silently frozen or dropped.

## 6. Stationarity removes artificial center-shift costs

Namespace Erdos773.FiniteCenteredStationarity.

For even p=n+2 and the optimally chosen center c:

    sum_{u in S}(f(u)-c)^(p-1)=0.

This is proved by differentiating the finite scalar objective in its CENTER
ARGUMENT and applying Fermat's theorem at its global minimum. It is NOT
an assumption about, or a differentiation of, the stochastic sequence of
centers across transitions. It also includes empty S.

constant_cancel proves for every common scalar F:

    sum (f-c)^(p-1)*(R(u)-F)=sum (f-c)^(p-1)*R(u).

This matters: the Taylor upper comparison can keep the old center UNMOVED,
while the desired common mean-field profile is subtracted in the first-
order pairing by stationarity. Thus there is no need to pay a large μ^2
variance term just to cancel that profile.

## 7. A genuine conditional optimized-energy drift theorem

Namespace Erdos773.GreedyCenteredEnergyDrift, for the UNIFORM greedy kernel.

Define c_j=the p-power minimizing center of the actual available D_j,
e(u)=D_j(u)-c_j, E_p=sum|e|^p. A general common proposed shift μ has

    shiftedVariance(u)=sum_{v safe(u)}(Delta D_j(u)-μ)^2.

shiftedVariance_le proves

    shiftedVariance(u)<=2*raw_second_moment(u)+2*Q*μ^2.

profile_shift retains the exact missing-safe-choice correction when
μ=F/Q. These are available if a genuinely shifted comparison is needed.

sum_drift and uniform_drift prove the full one-step bound, including
survivalDrift-|safeChoices(u)|*μ, the variance-sensitive Taylor term, and

    -sum_u (1+|closes(u)|)*|e(u)|^p.

uniform_drift_stationary uses section 6 to choose μ=0 while subtracting ANY
common profile F in the signed drift. It has no center-shift variance cost.

The convenient final API is uniform_drift_bound. Given:

    |Delta D_j(u)|<=B(u) on safe choices, B(u)>=0,
    sum_u e(u)^(p-1)*(R_j(u)-F)<=D,
    sum_{v safe(u)}(Delta D_j(u))^2<=V(u),
    1+|closes(u)|>=l,

it proves the ACTUAL uniform conditional bound

    E[E'_p-E_p]
      <= [p*D+c_(p-2)*sum_u(|e(u)|^(p-2)+B(u)^(p-2))*V(u)-l*E_p]/Q,

where c_n=(n+2)^2*2^n is the proved Taylor coefficient. The energy at the
next state is optimized there; it is not a frozen record. Raw increment and
second-moment bounds already exist in GreedyCodegreeVariance and can now be
used directly. D is a signed operator budget, not an absolute-drift bound.

This is a real one-step stochastic estimate. It is still NOT an integrated
concentration or long-run extraction theorem.

## Remaining mathematical gaps and cautions

1. The shrinking scale A=d*q remains unresolved. The O(1+t) coupled budget
   controls absolute errors in x2=D2-c2, x3=(D3-c3)/A, x4=(D4-c4)/A^2.
   An energy bound relative to (rho*A)^p introduces additional normalization
   drift. The newly retained death term helps but no proof supplies all
   the required p-dependent restoring strength. Do not claim that fixed
   higher moments or stationarity alone removes this problem.
2. No signless spectral gap has been proved for the actual residual two-
   graph. The arbitrary symmetric-weight budget supplies nonnegative
   dissipation, not a positive multiple of f2*energy. Near-bipartite modes
   make an unjustified gap assertion particularly dangerous.
3. Actual available means and normalized ratios still require quantitative
   control of higher mixed covariances. Their signs cannot be presumed,
   as section 4 verifies. The favorable two-degree variance alone does
   not close the higher system.
4. The survivor-biased kernel is an alternative process, not a completed
   replacement extraction theorem. It would need its own profile/guard
   estimates and compatible selection tails. Do not reuse unrestricted
   uniform-carrier tail equalities for it.
5. The finite survival-target/backward-density certificates are already
   complete. Their actual long-time numerical hypotheses, promotion-tail
   transfer, target-cap budget, readiness, and bootstrap are not.
6. Even a sharp coefficient-one N^(2/3) theorem leaves all 0<epsilon<1/3
   open. Nothing here gives the square-specific exponent improvement or
   fixed-power upper bound needed to settle the original conjecture.

## Practical Lean details from this continuation

- IsLocalMin.hasDerivAt_eq_zero works for the stationary-center proof.
  HasDerivAt.sum yields a sum of FUNCTIONS; use sum_apply, Pi.pow_apply,
  Pi.sub_apply to compare with the pointwise sum.
- Finset.sum_sdiff h has order sum_{S\T}+sum_T=sum_S.
  Finset.sum_sdiff_eq_sub h is the corresponding subtraction identity.
- A single rw [sum_sub_distrib] may rewrite the left side of an inequality
  first; simp only [sum_sub_distrib] before transposing a right-side double
  sum avoids that trap.
- For finite examples, unfold Independent before decide +kernel.
  Rewrite available_eq BEFORE expanding H and I in active/incident filters.
- No temporary checking file remains.
