# Survival-aware targets: completed finite certificates and remaining gap

## Main conjecture is NOT settled

Spec.lean remains unchanged, with its sole admission at line 2031 for
0<epsilon<=1/3. The strongest completed actual square-Sidon lower bound is
still M(N)>=N^(2/3)/500 eventually. No coefficient-one endpoint, exponent
above 2/3, or disproof has been obtained. Nothing has been submitted.

Spec SHA-256:
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14

This note supersedes the previously unformalized target-hazard proposal in
GreedyEnergyTrackingResearchNotes.md. The earlier nonlinear extraction and
iterated short-overlap cube reductions are already completed; do not redo
them or mistake them for a near-linear square-Sidon construction.

## Later continuation

GreedyMovingMeanResearchNotes.md now records completed actual moving-mean
drift identities, a survivor-biased alternative kernel, a verified negative
mixed-covariance example, retained death-energy Taylor bounds, stationary
center cancellation, and an actual conditional optimized-energy drift
certificate. The shrinking-scale and exponent gaps remain unresolved.

## Newly completed modules

All eight compile cleanly, have built oleans, and their 31 printed main
axiom audits use only propext, Classical.choice, Quot.sound:

1. GreedyTargetHazard.lean
2. FiniteKilledKernel.lean
3. GreedySurvivalTargets.lean
4. GreedyBackwardDensity.lean
5. FiniteWitnessCrossing.lean
6. GreedySurvivalWitnesses.lean
7. GreedySurvivalLocalTails.lean
8. FiniteCenteredPower.lean

The previously completed GreedyHighMomentBudget.lean and
FinitePowerTaylor.lean were independently re-audited as well. All 43 audits:

    /tmp/greedy-survival-audit-1.log
    /tmp/greedy-survival-audit-2.log
    /tmp/greedy-survival-audit-3.log

No new file imports admitted Spec.lean.

## 1. Exact one-step hazard certificate

Namespace Erdos773.GreedyTargetHazard.

For a target set U and selected carrier I, put B=U\I and

    value(H,U,I,r) = if B subset available(H,I) then r^|B| else 0.

A selected target costs no factor; a killed unselected target makes the
potential zero permanently along legal greedy steps. Completed targets have
value one. viable_predecessor proves that viability cannot be regained.

Define hazard(H,I,B) as the union of the closure neighborhoods of B.
Suppose k=|B|, Q=|available|, r>=0, every target closure has size >=l, and
pairwise distinct target closure intersections have size <=C. Then
step_hazard_bound proves

    sum_{v available} value(H,U,I+v,r)
      <= k*r^(k-1) + [Q-k*l+choose(k,2)*C]*r^k.

This handles target/closure overlaps: the target-choice term is safely
overcounted, never silently assumed disjoint from the hazard. l may be real.
The complement count is bounded using the existing exact Bonferroni lemma.

power_tangent derives finite convexity from natural-power Young:

    s^k+k*s^(k-1)*(r-s) <= r^k,  r,s>=0.

scalar_supersolution proves that for k<=K a sufficient condition is

    1 <= Q*(r-s) + [l-(K-1)*C/2]*s.

There is NO monotonicity requirement between r and s. k=0 is included.
average_le_value combines these into the actual uniform-choice conditional
potential bound. Dead states are covered explicitly.

## 2. Killing AFTER guard failure, preserving the first bad state

Namespace Erdos773.FiniteKilledKernel.

kill(K,G) acts on Option sigma. At some x with G x true, it uses K's actual
transition law and goes to some y. If G x is false, its NEXT transition goes
to none. none is absorbing. A first bad destination reached from a good
state is therefore not discarded.

liftEvent gives false at none; liftValue gives zero there.

- avg_some gives the exact guarded original average or cemetery value.
- support_some and support_death characterize the actual support.
- hit_none is zero for every lifted event.
- hit_le_original: killing cannot increase an arbitrary event's first hit.
- hit_eq_original: if P includes every guard failure through T, its lifted
  first-hit probability under kill(K,G) equals its ORIGINAL first-hit
  probability, through that finite horizon.
- hit_le_guarded_potential: a nonnegative potential with drift hypotheses
  ONLY at G-good states has the usual finite Ville bound in the killed
  kernel. Its domination hypothesis still includes the first bad state.

This is the required comparison mechanism for later guard bootstrapping.
It does not give an unrestricted sharp selected-carrier inclusion law.

## 3. Arbitrary finite memory and an actual target first-hit theorem

Namespace Erdos773.GreedySurvivalTargets.

UniformOnGuard H K G carrier T requires, at every guarded state before T:
- available is nonempty;
- every projected carrier observable has exactly the uniform greedy-step
  average. No independence or special memory update is assumed.

HazardProfile H G carrier T K r l C requires:
- r(n)>=0 through T;
- guarded lower closure bounds and pair-overlap upper bounds;
- the scalar supersolution condition with the maximum target size K.

hit_target bounds the inclusive first-hitting probability of U being
selected in the killed process by value(H,U,carrier(x),r(n)), whenever
|U|<=K and n+h<=T.

hit_target_from_empty gives r(0)^|U| from an empty selected carrier, including
initially unavailable targets (which only lower the probability).

uniform_lifted instantiates the interface for the existing finite-memory
greedy kernel, provided its new killing guard implies Ready and its
supported updates have the previously required correct carrier projection.

## 4. A discrete backward profile WITHOUT a terminal 1/q cost

Namespace Erdos773.GreedyBackwardDensity.

For positive consecutive reference volumes w,v, a>=0 and remaining time
B>=0, set r=a(B+1)/w and s=aB/v. exact_cancellation proves

    w*(r-s)+(w-v)*s = a.

Let actual Q satisfy |Q-w|<=eta*w, with eta>=0 and v<=w. Let the effective
closure hazard l satisfy l>=w-v-b. Then scalar_step proves the supersolution
condition from the EXPLICIT error budget

    a*[eta*(1+B*(w-v)/v)+b*B/v] <= a-1.

The deficit b need not be nonnegative; the theorem does not need that
extra restriction. scalar_step_two uses a=2 and the bracket budget <=1/2.

For a reference sequence w(n)>0 through T, define

    parameter(T,w,n) = 2*(T-n)/w(n).

hazardProfile_of_density constructs a full HazardProfile from:
- w nonincreasing;
- the above finite error budget at every n<T, with B=T-(n+1);
- guarded relative Q errors;
- lower effective hazard l-(K-1)C/2 >= w(n)-w(n+1)-b(n);
- guarded individual closure and pair-overlap bounds.

Combining with hit_target_from_empty costs (2*T/w(0))^|U|. This removes the
terminal minimum-density factor at the LEVEL OF AN EXPLICIT CONDITIONAL
CERTIFICATE. No actual long-run numerical profile is instantiated yet.

## 5. First-crossing witness packing, with a target-size cap

FiniteWitnessCrossing provides finite-horizon hit_mono, indexed witness
union bounds, and configuration tails. Its generic configuration_tail has
an explicit eligible-state predicate; the cemetery is not accidentally
counted as containing the empty target.

GreedySurvivalWitnesses defines TargetLaw for a kernel on Option sigma:

    for every |U|<=cap,
    hit(selected U by horizon) <= p^|U|.

law_of_hazard supplies this law in the killed process. witness_bound covers
arbitrary time-dependent recorded events with indexed selected targets.
packing_tail and packing_exponential_tail give

    hit( more than r*M*k selected configurations )
      <= choose(|S|,k+1)*p^(s*(k+1))
      <= [3*|S|*p^s/(k+1)]^(k+1),

when supports are nonempty, their sizes lie in [s,r], each vertex belongs
to at most M indexed supports, and crucially

    r*(k+1) <= cap.

Repeated witness supports remain indexed with their multiplicity. No
selection independence is asserted.

## 6. Actual local witness tails transferred

Namespace Erdos773.GreedySurvivalLocalTails.

For a four-uniform hypergraph with distinct-edge intersections <=2,
degree at u <=D and pair-codegree <=P, a TargetLaw with p in [0,1] and
cap>=4*(k+1) implies:

    hit(prefix duplicate excess at u >16*P^2*k)
      <= [9*D*P*p^4/(k+1)]^(k+1),

    hit(prefix common degree of distinct u,v >16*P^2*k)
      <= [9*D*P*p^3/(k+1)]^(k+1).

These use the existing exact witness constructions and monotonicity of
witness costs under selected-carrier inclusion. They are first-crossing
bounds and retain all-subset prefix witnesses. They do not apply the old
unrestricted terminal expectation theorem to the killed law.

Promotion heavy/light tails have NOT yet been transferred.

## 7. Optimally centered energy: avoiding derivatives of the center

Namespace Erdos773.FiniteCenteredPower.

    powerSum(S,f,p,c) = sum_{u in S} |f(u)-c|^p.

exists_minimizer proves global attainment, including empty data and p=0.
It minimizes first on [-M,M], M=sum|f(u)|, and shows outside centers cannot
improve the value. center chooses a minimizer; energy is its value.
No equivariance of the chosen center is assumed.

- energy_le evaluates against any proposed center.
- point_power_le controls every individual deviation by the global energy.
- point_lt_of_energy_lt gives uniform pointwise control from energy<R^p.
- energy_translate proves translation invariance of the MINIMUM value.
- survivor_step: if T subset S, any next center a gives

    energy(T,g,p)-energy(S,f,p)
      <= sum_{u in T} (|g(u)-a|^p-|f(u)-center(S,f,p)|^p).

- survivor_taylor supplies the variance-sensitive natural-power remainder
  for even p=n+2, using the actual squared centered increment. It permits
  any proposed next center (hence one depending on the selected action).

This is a useful alternative to differentiating a changing arithmetic mean.
It does NOT yet instantiate the normalized greedy-process energy drift.

## Important new scope check: absolute energy versus a shrinking scale

The proved high-moment budget has growth O(1+t) for normalized components

    x2=D2-c2, x3=(D3-c3)/A, x4=(D4-c4)/A^2,  A=d*q.

It bounds ABSOLUTE energy in these x variables. The intended uniform local
error threshold is rho*A, which shrinks with q. Dividing the energy by A^p
introduces a potentially leading positive p*t^2 term. Therefore the
O(1+t) operator bound plus high moments does NOT by itself justify tracking
to q near d^-1. Optimizing the center does not remove this normalization
problem.

A rough diagnostic, not a theorem about the actual process: if accumulated
absolute noise is on the scale sqrt(B*d), an envelope rho*d*q cannot be
closed when q is much smaller than sqrt(B/d)/rho. Fixed higher moments
handle the number of vertices, but do not cure this scale mismatch.

The two-degree signless dissipation has no supplied spectral gap. For an
arbitrary symmetric nonnegative matrix, near-bipartite modes can have weak
damping. Do NOT silently replace the proved nonnegative dissipation by a
positive multiple of f2*energy. Vertex-death terms were dropped in the
survivor upper bound; they could be retained, but no proof that they alone
supply the needed p-dependent damping has been given.

Possible directions requiring real new work, not claimed results:
- retain or strengthen dissipative information in the ACTUAL coupled
  residual hypergraph, rather than arbitrary independent neighbor matrices;
- use the favorable negative two-degree variance term in mean drift, so
  loss of pointwise regularity need not automatically mean a short run;
- derive actual normalized energy and mean/invariant estimates with all
  denominator and survivor corrections accounted for.

## Remaining program

1. Supply an actual quantitative density/hazard profile; the discrete scalar
   certificate itself is finished and should not be rederived.
2. Transfer promotion tails and quantify all guard costs with cap large
   enough for their packed targets. The cap times common-neighbor correction
   may constrain the smallest permitted d*q.
3. Close a genuinely adequate stochastic energy/normalization argument.
   This is NOT just supplying a Taylor lemma: that lemma is finished, and
   the shrinking-scale issue above must be resolved.
4. Prove the guard bootstrap/readiness and extract a new long actual run.
5. Handle average degree, trimming, regularization, sampling, and constants
   in any square application. The sharp collision coefficient 41/500 is
   only slightly below 1/12 and does not itself imply a unit endpoint.
6. Even a coefficient-one N^(2/3) endpoint leaves every 0<epsilon<1/3
   unresolved. A genuinely square-specific exponent construction or a
   fixed-power upper bound is still needed to settle Spec.lean.
