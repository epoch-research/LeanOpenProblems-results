# Joint rough-smooth comparison — original conjecture still unresolved

`Submission/Spec.lean` remains unchanged and contains its original `sorry`.
No complete proof or irrational counterexample has been found. The new
auxiliary theorems below are NOT a substitute for the requested settlement.

## RoughSmoothLowerBound.lean (completed in the previous context)

For every irrational alpha>1 there are arbitrarily large actual scales u
such that, with Z=fastRoot(u), all 0<tau<=1/2 simultaneously satisfy

    roughSmoothCoefficient(tau) * u^6
      <= mixedPrimeSmooth(tau/log Z, alpha, u^6).

The coefficient is (tau/2)^49153/(8195*tau*roughConstant), and roughConstant
is fixed and positive. The output factor bound 49153 is NOT primality.

## RoughSmoothComparison.lean (new, verified)

Define

    J = layerCount(u),
    t = layerParameter(alpha,u)
      = 1/[(1+log(floor(alpha*u^6)))*(J+1)^2],
    layerTau(alpha,u) = t*log(fastRoot u),
    D = 2^49153 * 8195 * roughConstant,
    c = 1/(49155^49152 * D).

For alpha>=1, Z=fastRoot(u)>=2 and alpha<=Z, the file proves:

    1/[49155*(J+1)^2] <= layerTau <= 1/(J+1)^2.

When J>=1, layerTau is in the admissible range (0,1/2]. Also
roughParameter(layerTau,u)=layerParameter(alpha,u), exactly.

The coefficient cancellation is proved without evaluating huge constants:

    roughSmoothCoefficient(tau) = tau^49152 / D  (tau>0).

The main coefficient comparison is

    c/(J+1)^98304
      <= roughSmoothCoefficient(layerTau(alpha,u))
      <= 1/(J+1)^98304.

`layer_lower_envelope_lt_error_budget` proves the strict inequality

    roughSmoothCoefficient(layerTau)*u^6 < 100000*u^6/(J+1).

This compares two proven envelopes. It does not give a lower bound for the
ACTUAL error, nor an upper bound for the ACTUAL smoothed correlation.
It shows that subtracting the available error budget from the new lower
envelope cannot certify positive genuine prime correlation.

`exists_layerParameter_rough_lower` obtains arbitrarily large actual scales
with J also arbitrarily large and

    c*u^6/(J+1)^98304 <= mixedPrimeSmooth(layerParameter,alpha,u^6).

This theorem alone does not assert the least-factor moment bound at the
selected rough-output scale.

## CommonRoughMomentScale.lean (new, verified)

The common-scale issue is now resolved explicitly, not assumed away.

`exists_common_rough_moment_scale` combines all eventual cutoff and budget
conditions BEFORE choosing a direct rational approximant r to alpha. With
u=sqrt(sqrt(r.den)), it supplies at the SAME arbitrarily large scale:

    coprimePrimeWeight(alpha,(fastRoot u)!,u^6)
      >= u^6/[roughConstant*(1+log(u+1))],

    primeLeastFactorMoment(alpha,u^6)
      <= 100000*u^6*(J+1).

Both fastRoot(u) and J can exceed any prescribed bound.

`rough_weight_to_smooth` exposes the finite transfer from the actual rough
weight lower bound, allowing the smoothing parameter to be chosen after u.

`exists_common_layer_estimates` gives, at the same scale and parameter,

    c*u^6/(J+1)^98304 <= mixedPrimeSmooth(t,alpha,u^6),

    |mixedPrimeSmooth(t,alpha,u^6)-mixedPrimeMangoldt(alpha,u^6)|
      <= 100000*u^6/(J+1).

Thus separate existential selections are no longer a gap in this specific
comparison. The numerical loss is still decisive: the lower envelope is
smaller than the error budget, and no prime-pair lower bound follows.

## Verification and implementation notes

Both new files compile to .olean files under .lake/build/lib/lean/Submission.
The six principal new declarations were axiom-audited; they use only
propext, Classical.choice, and Quot.sound. Neither new file contains sorry.

Avoid `positivity` on fully expanded layerCount expressions: it can exceed
millions of heartbeats. Instead explicitly use Nat.cast_nonneg and
add_pos_of_nonneg_of_pos. Avoid `ring` on concrete exponents 98304 or on the
huge fixed constants: it can try to expand the entire binomial and exhaust
memory. Use generic-exponent scalar identities, or the exact rewrite
`div_mul_eq_mul_div` for final rearrangements.

## Remaining task

A genuine two-prime lower bound, a sufficient signed four-factor lower gap,
or an actual irrational counterexample is still required. These new
comparison theorems do not settle Erdos 972. No final proof was submitted.
