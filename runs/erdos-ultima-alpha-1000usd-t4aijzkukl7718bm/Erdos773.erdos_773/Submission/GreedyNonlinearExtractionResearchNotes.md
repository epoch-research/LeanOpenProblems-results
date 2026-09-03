# Nonlinear extraction and the improved square-Sidon coefficient

## Status: main task NOT settled

The strongest completed square-Sidon lower bound is now

    M(N) >= N^(2/3)/500 eventually.

This improves the previous 1/1200 coefficient. It still does NOT prove
M(N)>=N^(2/3), and it supplies no exponent above 2/3. The unresolved range
of the unchanged conjecture remains 0<epsilon<=1/3.

Submission/Spec.lean is unchanged, still has its sole sorry at line 2031,
and has SHA-256

    917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14

No completed proof/disproof has been submitted. All new work is in helper
files, not consolidated into Spec. The main theorem's only import remains
`import FormalConjecturesUtil`.

## Completed milestone

The four unfinished nonlinear tracking obligations listed in
GreedyHigherPromotionResearchNotes.md are now discharged:

1. Weighted two-degree loss and drift.
2. Nonlinear tracked increments and second moments.
3. Nonlinear profile guards, drift signs, availability propagation, and
   uniform concentration bounds.
4. A numerical growing-horizon family, actual full independent runs,
   regularization, arbitrary finite carriers, and application to squares.

Unlike the earlier controlled_run guard certificate, the NEW growing
extraction theorem has NO early-stop alternative. Its parameter conditions
are proved, not merely hypotheses that some trajectory is good.

The general theorem is still a logarithmic improvement at the generic
four-uniform independence scale V/D^(1/3). This is not near-linear
square-Sidon selection.

## New modules and audits

- GreedyCodegreeTwoDrift.lean: 181 lines, 7 printed audits.
- GreedyCodegreeVariance.lean: 192 lines, 8 printed audits.
- GreedyCodegreeMomentControl.lean: 157 lines, 4 printed audits.
- GreedyCodegreeProfileDrift.lean: 131 lines, 4 printed audits.
- GreedyCodegreeOneStepProfiles.lean: 133 lines, 2 printed audits.
- GreedyCodegreePhysicalStep.lean: 133 lines, 3 printed audits.
- GreedyNonlinearGuardTails.lean: 144 lines, 4 printed audits.
- GreedyCodegreeProfileGuard.lean: 95 lines, 3 printed audits.
- GreedyCodegreeGuardControls.lean: 129 lines, 3 printed audits.
- GreedyCodegreeExtraction.lean: 101 lines, 3 printed audits.
- GreedyCodegreeUniformCosts.lean: 140 lines, 7 printed audits.
- GreedyCodegreeScales.lean: 139 lines, 5 printed audits.
- GreedyCodegreeGrowing.lean: 146 lines, 3 printed audits.
- GreedyCodegreeGrowingExtraction.lean: 158 lines, 4 printed audits.
- GreedyCodegreeSquareCertificate.lean: 79 lines, 2 printed audits.
- GreedyCodegreeSquareScales.lean: 166 lines, 6 printed audits.
- GreedyCodegreeSquareLower.lean: 77 lines, 1 printed audits.

All files compile cleanly. Their printed audits use only propext,
Classical.choice, and Quot.sound. Built .olean files exist.

Combined fresh audit:

    /tmp/greedy-nonlinear-final-audit.log

Four independent audit groups:

    /tmp/greedy-nonlinear-final-audit-1.log
    /tmp/greedy-nonlinear-final-audit-2.log
    /tmp/greedy-nonlinear-final-audit-3.log
    /tmp/greedy-nonlinear-final-audit-4.log

## 1. Weighted two-degree identities

`GreedyCodegreeTwoDrift.weighted_closure_swap` proves, for any available
choice set S and nonnegative integer weights a(x),

    sum_{w in S} sum_{x in closes(u) intersect closes(w)} a(x)
      = sum_{x in closes(u)} a(x)*|closes(x) intersect S|.

Consequently:

    sum_safe lostDuplicate(u,w)
      = sum_{x in closes(u)} (pairReps(u,x).card-1)
                            *restrictedClosure(u,x).card
      <= h*duplicateExcess(u)

when the neighboring closure degrees are <=h. In particular the forbidden
E*|available| bound is never used.

A stronger identity preserves all multiplicities as weights:

    sum_safe localLost_2(u,w)
      = sum_{x in closes(u)} pairReps(u,x).card
                            *restrictedClosure(u,x).card.

For a closure neighbor x, the exact omitted-choice balance is

    restrictedClosure(u,x).card + 1 + commonDegree(u,x)
      = closes(x).card.

Thus, if neighboring incident two-degrees are in [l,h], duplicate excess
is <=E, and common degrees are <=C:

    (l-E-1-C)*d2(u) <= sum_safe localLost_2(u,w) <= (h-1)*d2(u),

    2*d3(u)-P2(u)-(h-1)*d2(u)
      <= survivalDrift_2(u)
      <= 2*d3(u)-P2(u)-(l-E-1-C)*d2(u).

No duplicate penalty at u, multiplied by the available cardinality, is
present. These identities do not assume original-edge linearity.

## 2. Nonlinear moments and drift envelopes

The small two-degree increment cap is k+C+E, where k bounds pair codegrees.
Higher-degree safe increments are bounded by k*(h+1). Total local variation
bounds second moments, rather than charging B^2 on every available choice.
The two-edge loss sum remains <=h*d2(u), without a factor k.

`GreedyCodegreeMomentControl` supplies actual MomentControl instances for
the generic frozen-clock tracked kernel. The old linear stochastic moment
instantiations are NOT reused.

With mean profiles f2,f3 and errors e2,e3:

    |R2-(2*f3-f2^2)|
      <= 2*e3+f2*e2+(e2+E+1+C)*(f2+e2)+P2_bound.

For j>=3:

    |Rj-(j*fn-(j-1)*f2*fj)|
      <= j*en+(j-1)*f2*ej
         +((j-1)*(e2+E+1)+choose(j,2)*C)*(fj+ej)+Pj_bound.

The original 40*(1+t^2)*A^j*e numerical drift budget still absorbs all
these terms when E<=e, C+1<=e, P2<=A*e, and P3<=A^2*e. Here A=d*q.
There is no residual size five in a four-uniform original hypergraph, so
P4=0. The existing analytic growth constant 4000 therefore suffices.

Availability now has its exact duplicate correction. Its deterministic
error propagation costs 3*E2+1 per step, instead of 2*E2+1. The verified
availability envelope growth absorbs this cost. Readiness is derived from
past guarded steps, not assumed from a successful future.

## 3. Guard tails and finite certificate

`GreedyNonlinearGuardTails.cost` is the sum of all-prefix duplicate,
common-neighbor, P2, and P3 indicators. `auxiliaryBad` means cost>=1.
The cost is monotone in the selected carrier and antitone in its thresholds.
The carrier law is unchanged by record freezing. The previously verified
witness estimates give first-hit probability <=8/m^2 on the tracked kernel.

`GreedyCodegreeExtraction.independent_of_certificate` combines these
with six recorded profile crossings at each vertex. It leaves only finite
numerical horizon, promotion, cap, and failure inequalities. It concludes
an actual independent set of exactly T vertices.

`GreedyCodegreeUniformCosts` bounds the new raw caps and variances by
(k+2) times the old purely analytic scalar expressions. This is a
conservative comparison between numerical expressions, NOT an application
of a linear hypergraph concentration theorem. The common profile cost is

    6*exp(-d*rho^2/(4*(k+2)*penalty(tau)*(C+1))).

## 4. Fully instantiated growing-horizon theorem

Parameters:

    original degree D=m^300,
    d=m^100,
    rho=1/m^25,
    pair codegrees <=m^3,
    C=16*m^21,
    B2=288*m^133,
    B3=54*m^274,
    horizonBudget(tau)=exp(10000*(1+tau)^3)<=m.

The volume lies between m^300 and m^A in the regular theorem. The stopped
sampling ratio T/L is proved <=m^-97. The promotion thresholds are below
the actual profile margins at every step, using the uniform inequalities

    288/q(tau)<=horizonBudget(tau),
    54/q(tau)^2<=horizonBudget(tau).

The total failure is bounded uniformly over allowed tau by

    8/m^2 + 6*m^A*exp(-m/204),

which tends to zero for fixed A. All floor-rounding is handled.

Main API:

    GreedyCodegreeGrowing.eventually_independent

It gives |I|>=V*tau/(2*m^100), with no early stopping, for regular
four-uniform hypergraphs whose distinct edges intersect in at most two.

`GreedyCodegreeGrowingExtraction.eventually_independent` removes exact
regularity using the existing prime regularization. It preserves pair
codegree and intersection bounds and transfers independent-set density
without loss. The regularized volume exponent is A+303.

`GreedyCodegreeGrowingExtraction.eventually_selection` transports this to
arbitrary finite carriers. Both intersection and pair-codegree subtype
transport are proved explicitly.

## 5. Actual application to squares

`trim_at_threshold` keeps at least

    |A|-4*|edges(A)|/D

vertices with degree<=D. No additional random thinning/linearization is
performed.

The square certificate requires AP-free square values, pair codegree<=m^3,
D<=m^300, and polynomial volume. It proves

    tau*(|A|-4*|edges(A)|/D)/(2*m^100) <= M(N).

Use the existing logarithmic sampler with delta=1/1000:

    |A| >= (999/1000)*N/log N,
    |edges(A)| <= (83/1000)*N^2/(log N)^3.

Choose

    D=(4/3)*N/(log N)^2,
    m=ceil(D^(1/300)),
    tau=(log N)^(1/3)/160.

The exact trimming surplus is >=(3/4)*N/log N. For m>=10001:

    m^300*(log N)^2 <= (8/5)*N.

Volume N<=m^301 holds once (log N)^2<=N^(1/301). The old divisor-based
codegree estimate at exponent 1/301 then bounds pair codegrees by m,
hence by m^3. The horizon budget is checked exactly when log N>=10^12.

The final cubic comparison uses (75/64)^3>=8/5 and yields

    M(N) >= N^(2/3)/500 eventually.

API:

    Erdos773.GreedyCodegreeSquareLower.eventual_power_lower

## What remains

The original conjecture is NOT proved or disproved. Removing linearity is
now complete and should not be redone. Further small coefficient changes
in this generic argument do not raise the exponent above 2/3.

To settle the task one still needs either:

* a genuinely square-specific N^(1-o(1)) construction/extraction, or
* a fixed positive exponent loss in an upper bound on an unbounded sequence.

Even the epsilon=1/3 endpoint still needs substantially sharper independence
constants and average-degree handling. The presently conservative profile
growth and horizon constant are far from proving a unit lower coefficient.
All previously recorded digit-carry, moment, modular, and sparse-fiber
obstacles remain relevant; none is a disproof of the conjecture.

Technical observations:

* `field_simp` alone closes several high-power ratio identities; a following
  `ring` can fail with "No goals to be solved".
* For m^200*m^100, use `simpa only [← pow_add] using hV` rather than a deep
  `convert` followed by `ring`, which can exceed recursion depth.
* Some namespaces shadow `add_le_add_right`; using `add_le_add h le_rfl`
  avoids selecting a reversed-addition variant.
* For exact rational surplus identities, a short `calc` with `ring` and
  `sub_le_sub` is more robust than `linarith` over unreduced divisions.
* maxRecDepth 4096 is needed for some natural powers 300/301; exponentiation
  threshold 1024 suppresses default numeric-exponent warnings.
