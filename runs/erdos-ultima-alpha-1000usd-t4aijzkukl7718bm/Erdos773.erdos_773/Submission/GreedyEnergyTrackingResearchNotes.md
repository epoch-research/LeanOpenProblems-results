# Symmetric energy tracking: completed identities and unfinished program

## Main task is NOT settled

Spec.lean is unchanged. Its sole admission is still at line 2031 for
0<epsilon<=1/3. The strongest completed actual lower bound remains

    M(N) >= N^(2/3)/500 eventually.

Nothing below establishes the coefficient-one endpoint, any exponent above
2/3, or a negation of the original conjecture. No proof was submitted.
Spec SHA-256:
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14

The iterated short-shift cube extraction proposed earlier is already fully
completed; see IteratedShortTranslatedIntersectionResearchNotes.md. Do not
redo it or treat it as a square-collision theorem.

## Later completed work — read the newer note before continuing

The higher-moment extension and variance-sensitive Taylor estimate listed
as unfinished below have now been completed in GreedyHighMomentBudget.lean
and FinitePowerTaylor.lean. A further continuation completed the finite
survival-hazard certificate, killed-kernel first-crossing comparison,
backward density profile, capped witness packing, duplicate/common-neighbor
survival tails, and optimized-center energy lemmas.

See **GreedySurvivalTargetResearchNotes.md** for the current APIs, audit
logs, and remaining gaps. In particular, that note records a new scope
check: O(1+t) growth of absolute energy does not itself control errors
relative to the shrinking scale A=d*q. No near-terminal stochastic tracking
or improvement of the actual lower bound has been claimed.

## Why this continuation changed direction

The review of residue lifting found no new compatible partial-fiber
construction. Existing full-fiber and private-modulus ceilings still apply
to their sufficient selectors, not to arbitrary Sidon subsets. No new
square-specific exponent argument was found.

The active narrower target became the coefficient-one endpoint M(N)>=N^(2/3),
by improving actual random-greedy tracking rather than optimizing the old
1/500 numerical constant. Even reaching that endpoint would leave all
0<epsilon<1/3 unresolved. The existing sharp collision coefficient makes
this a plausible target, NOT an established consequence of a generic
independence theorem.

## Nine new verified modules

All compile without warnings, errors, or admissions, and all have built
oleans. Their 50 printed axiom audits contain only propext, Classical.choice,
Quot.sound. No admitted Spec theorem is imported.

1. GreedyCodegreeSelfCorrection.lean
2. GreedyWeightedRecords.lean
3. GreedyWeightedDissipation.lean
4. GreedyTwoDegreeEnergy.lean
5. GreedyHigherPairWeights.lean
6. GreedyHigherDegreeEnergy.lean
7. GreedySurvivalTotalDrift.lean
8. GreedyNormalizedEnergyBudget.lean
9. GreedyPowerYoung.lean

Fresh independent audit groups:

    /tmp/greedy-energy-audit-1.log
    /tmp/greedy-energy-audit-2.log
    /tmp/greedy-energy-audit-3.log

These are not yet an instantiated new stochastic concentration theorem.

## 1. Retaining the scalar restoring drift

GreedyCodegreeSelfCorrection.two_damped and higher_damped retain the signed
local error, rather than counting it as an absolute positive error. Write
D_j(u)=incident degree, R_j(u)=survivalDrift, and f_j for supplied centers.

    |R2-(2f3-f2^2)+f2(D2-f2)|
      <=2e3+(e2+E+1+C)D2+P2,

    |Rj-(j fn-(j-1)f2 fj)+(j-1)f2(Dj-fj)|
      <=j en+((j-1)(e2+E+1)+choose(j,2)C)Dj+Pj.

The two_critical and higher_critical theorems save f2*c and (j-1)f2*c,
respectively, in BOTH signs when the local error is at least distance c
from the center. Duplicate and promotion errors are not omitted.

Scalar self-correction alone does not solve the endpoint: worst-case
neighbor errors and deterministic availability errors can still produce
exp(const*t^3) inflation. The symmetric identities below are the more
substantial new ingredient.

## 2. Clock-weighted recorded observables

GreedyWeightedRecords defines

    weightedError(w,f,s,j,u)=w(clock_u)*stored_degree_j(u)-f(clock_u),
    offset=(w(n+1)-w(n))*D_j(u)-(f(n+1)-f(n)).

On a safe update its exact increment is

    w(n+1)*(new_D_j-D_j)+offset.

On a death or bookkeeping freeze, the ENTIRE weighted record freezes; the
weight does not continue advancing at a dead vertex. Exact conditional mean:

    [w(n+1)*R_j(u)+|safeChoices(u)|*offset]/|available|.

The safe-choice factor multiplies BOTH deterministic changes. The exact
second moment is the safe-choice average of the displayed increment squared.
A raw nonlinear second-moment numerator V gives the bound

    2*w(n+1)^2*V/|available|+2*offset^2.

The file proves active and frozen drift, exact second moment and variance
transfer. It does NOT yet provide a weighted CriticalControl, a complete
high-moment observable, or a long-time numerical instance.

## 3. Symmetric signless dissipation

GreedyWeightedDissipation.symmetrize proves for a finite set S, symmetric
weights W(u,v), any error vector e and any test function phi:

    sum_u phi(eu) [(sum_v Wuv)*eu+sum_v Wuv*ev]
      = (1/2) sum_uv Wuv [phi(eu)+phi(ev)] [eu+ev].

If W>=0 and phi is odd and monotone, this is nonnegative. The proof uses
that phi(a)+phi(b) has the same weak sign as a+b. odd_power_nonnegative
specializes to phi(x)=x^p for ANY odd natural p. Quadratic specialization:

    sum_u eu [d_u*eu+sum_v Wuv*ev]
      = (1/2) sum_uv Wuv(eu+ev)^2 >=0.

No expansion, neighbor independence, or spectral-gap assumption is used.
The same file proves a weighted Young bound from symmetric row bounds B:

    2t sum_uv Wuv f_u g_v <= B[t^2 sum f_u^2+sum g_u^2].

## 4. Exact two-degree operator

GreedyTwoDegreeEnergy uses

    W2(u,v)=|pairReps(H,I,u,v)|.

It is symmetric and its available-vertex row sum is D2(u). All original-edge
multiplicities are retained. Define the explicit correction

    c2(u)=sum_v W2(u,v)(duplicateExcess(v)+1+commonDegree(u,v))-P2(u).

Then weighted_drift proves EXACTLY

    R2(u)=2D3(u)-sum_v W2(u,v)D2(v)+c2(u).

For e2(u)=D2(u)-f2 and e3(u)=D3(u)-f3,

    R2(u)-(2f3-f2^2)=2e3(u)-f2 e2(u)-sum_v W2(u,v)e2(v)+c2(u).

Combining the row-sum identity with signless dissipation gives
energy_identity:

    sum_u e2(u)[R2(u)-(2f3-f2^2)]
      =2 sum_u e2(u)e3(u)
       -(1/2)sum_uv W2(u,v)(e2(u)+e2(v))^2
       +sum_u e2(u)^3+sum_u e2(u)c2(u).

Thus the leading neighbor term is FAVORABLE after summing. test_identity
and test_drift_bound give the corresponding result for arbitrary odd
monotone tests, retaining phi(e2)*e2^2 as the nonlinear remainder.

If f2 is the actual available-vertex mean, mean_drift proves

    sum_u R2(u)=2 sum_u D3(u)-Q*f2^2-sum_u e2(u)^2+sum_u c2(u).

WARNING: this is the SUM OF SURVIVAL-CONDITIONED DRIFTS, not the drift of
the moving available-vertex average. The death correction is handled below.

## 5. Higher-degree pair weights and covariance

GreedyHigherPairWeights defines Wj(u,v) as the number of ORIGINAL active
j-residual edges containing distinct u,v. These weights are symmetric and

    sum_v Wj(u,v)=(j-1)Dj(u).

weighted_sum identifies the operator with the incident-edge/other-residual-
vertex sum. In particular neighborWeight is Wj applied to simple closure
degrees. sum_weighted proves its exact column-sum identity.

GreedyHigherDegreeEnergy defines c_j by explicit duplicate, neighbor-loss,
and promotion counts and proves

    Rj(u)=j D_(j+1)(u)-sum_v Wj(u,v)D2(v)+c_j(u).

For j>=3 and the existing guards:

    -(j-1)Dj(u)-Pj <= c_j(u)
      <= [(j-1)(E+1)+choose(j,2)C] Dj(u).

Its centered identity retains BOTH the self damping and the neighbor error.
When f2,fj are the actual scalar means, its summed drift has covariance
correction

    sum_u Rj(u)
      =j sum_u D_(j+1)(u)-(j-1)Q fj f2
       -(j-1)sum_u (Dj(u)-fj)(D2(u)-f2)+sum_u c_j(u).

Again, this is not silently equated with a moving-average process drift.

## 6. Vertex deaths and actual total-degree drift

GreedySurvivalTotalDrift first proves generic finite survivor bookkeeping.
Let totalDegree_j(I)=sum_{u available(I)} Dj(u). Its exact theorem is

    sum_{v available(I)} [totalDegree_j(I+v)-totalDegree_j(I)]
      =sum_u Rj(u)-sum_u (1+|closes(u)|)Dj(u).

Equivalently, the subtracted death cost is

    totalDegree_j + sum_u D2(u)Dj(u)-sum_u duplicateExcess(u)Dj(u).

No linearity assumption is needed. This removes a potentially serious gap
in moving from frozen local records to actual averages.

## 7. Coupled normalized quadratic budget

GreedyNormalizedEnergyBudget.coupled_budget is a COMPLETE deterministic
operator inequality. Let W2,W3,W4 be symmetric nonnegative matrices, with
row bounds

    row(W3)<=A(6t+2), row(W4)<=6A, A,t>=0.

The row sum of W2 is used in its signless self term. Define linearized
normalized drifts

    L2=2A*x3 - [row(W2)*x2+W2*x2],
    L3=3A*x4 - 3A*t^2*x3 - W3*x2,
    L4=       - 3A*t^2*x4 - W4*x2.

Then

    sum x2*L2 + sum x3*L3 + sum x4*L4
      <= A(8+4t) [sum x2^2+sum x3^2+sum x4^2].

For W3 the scaled Young parameter t+1 makes its leading 3A*t^2 term
cancel against restoring drift, leaving growth O(A(1+t)). The proof is
fully algebraic. This is NOT yet a theorem for an actual normalized greedy
process: changing means, normalization increments, nonlinear remainders,
and second moments must all be supplied.

## 8. Fixed high moments

GreedyPowerYoung.power_young proves by a polynomial recurrence

    (n+1)a^n b <= n a^(n+1)+b^(n+1), a,b>=0.

weighted_young and scaled_weighted_young prove

    (n+1)t^n sum_uv Wuv |f_u|^n |g_v|
      <= B[n t^(n+1) sum_u |f_u|^(n+1)+sum_u |g_u|^(n+1)]

for symmetric nonnegative weights of row sum <=B and t>=0.
This is meant to extend the deterministic coupled budget to fixed even
moments large enough for simultaneous control of polynomially many vertices.
That extension has NOT yet been written.

## Unfinished mathematical program — NOT routine scalar cleanup

A plausible next route is to center local degrees at their ACTUAL available-
vertex means, rather than at deterministic q(t)-profiles. This avoids treating
a global availability fluctuation as an independent worst-case neighbor error.
Symmetry makes the change in the mean of the neighbor interaction a quadratic
covariance, instead of a new leading linear error.

Necessary work, NONE of which is asserted completed:

1. Extend coupled_budget to arbitrary fixed even moments using the proved
   odd-test dissipation and weighted Young inequality. The expected constant
   may depend exponentially on the fixed moment; that is acceptable for a
   t=O((log D)^(1/3)) horizon if the growth is exp(C_p(t+t^2)), not exp(C_p t^3).
2. Prove a bounded-increment natural-power Taylor/conditional-moment bound,
   charging the quadratic variation rather than B^2 at every choice.
3. Instantiate the actual centered, normalized observables. Handle means,
   denominators, vertex deaths and normalization increments exactly or with
   proved remainders. A global L2 bound alone does NOT give simultaneous
   per-vertex control at polynomial volume; higher moments are needed.
4. Prove a much sharper witness-selection bound. The old T/L domination is
   inadequate near the desired horizon: if Q~Vq and T~Vt/d, it gives t/(dq),
   rather than t/d. Reusing the old m^-97 hypothesis at q near d^-1 would
   be invalid. See the possible hazard argument below.
5. Rebuild common-neighbor, duplicate and promotion guard tails with the
   sharper selection bound, close the bootstrap, prove readiness, and only
   then extract an actual long independent run.
6. Even a sharp four-uniform theorem would first need a correct application
   with regularization, trimming, density and constants. No coefficient-one
   endpoint follows merely from these local calculations.

### Possible survival-aware witness argument (mathematics only)

For a fixed target set U with l currently unchosen vertices all still open,
the chance of selecting one is l/Q, whereas the chance of killing a target
is approximately l*D2/Q. Common-neighbor guards bound simultaneous deaths.
If t is scaled time, q(t)=exp(-t^3), d=D^(1/3), the backward one-target
success profile is

    r(t)=(tau-t)/(d*q(t)),
    r'(t)=-1/(d*q(t))+3t^2*r(t).

The prospective potential is r(t)^l when all remaining targets are open,
zero if one is killed, and one if all are selected. The selection and death
terms should cancel the derivative, up to explicitly controlled errors.
This would aim at (C*tau/d)^|U|, avoiding the terminal 1/q loss. A finite-step
supersolution, target-selection/closure overlaps, and the stopped process
comparison all need actual proofs. No such probability estimate is claimed.

### Two cautions

* Simple independent absolute envelopes still lose the symmetric cancellation.
  Merely lowering the old numerical constant 4000 is not this new argument.
* The coefficient-one endpoint, even if eventually obtained, is not a proof
  of the original conjecture for 0<epsilon<1/3. A genuinely new square-specific
  exponent argument or a fixed-power upper bound would still be needed.
