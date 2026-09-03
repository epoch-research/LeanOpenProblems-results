# Complete common-scale recentering transfer — conjecture still unresolved

`Submission/Spec.lean` is unchanged and retains the original `sorry`.
No prime-pair infinitude proof or irrational counterexample has been found.
No incomplete proof was submitted.

## Verified additions

* `RecenterCovarianceBounds.lean`
* `RecenterCovarianceScales.lean`
* `RecenterFourFactorReduction.lean`

The principal declarations compile and audit using only `propext`,
`Classical.choice`, and `Quot.sound`.

## Finite recentering estimate

Write

    A = typeIPart(W,W), B = typeIPart(1,W), s = Lambda_{<=W},
    R = typeIIPart(W,W), m = reciprocalMoebius(W).

The exact recentered remainder is R + m*(B-s). Under W>0,
W^2<=v<=N, L>=1, log N,log(floor(alpha*N))<=L-1, |m|<=1,
and the five actual covariance bounds

    |Cov(B,Lambda_output)| <= E_left,
    |Cov(Lambda,B_output)| <= E_right,
    |Cov(B,A_output)|, |Cov(A,B_output)| <= 32*N*|m| + E,
    |Cov(B,B_output)| <= 32*N + E,

`mean_recenter_covariance_bound` proves

    |meanCenteredFourFactor - centeredFourFactor|
        <= E_left + E_right + 96*N*m^2 + 3*E + 210*v^2*L^2.

All mixed and small-cutoff terms are retained. The small-cutoff estimate
uses total |s| and total |s_output| <= 7v, and an L1 covariance perturbation.

## One actual common scale

`exists_common_recenter_covariance_scale` chooses all eventual budget
thresholds FIRST, with error epsilon/8, together with |m(W)|<=1 and W>B.
It then invokes `exists_two_sided_prime_divisor_scale` ONCE.

At the resulting

    N=scaleCutoff(alpha,u), v=root64(u), W=growingCutoff(u),
    L=1+log(alpha*N),

it obtains simultaneously:

* the original Type-I/prime covariance <= epsilon*N;
* the dual prime/Type-I covariance <= epsilon*N;
* the joint Type-I covariance <= epsilon*N;
* the COMPLETE recentering correction <= epsilon*N;
* the existing OutputPrimeScale hypothesis.

The same original, dual and joint rows apply to cutoff pairs (W,W) and
(1,W). The elementary identity m(1)=1 turns the three mixed joint main
terms into 32*N*|m|, 32*N*|m|, and 32*N.

For

    E=100*(118*v*u^4+1)*v^2*L^5,
    D=32*N*m^2+E,

the small-cutoff term satisfies 210*v^2*L^2<=3E. The finite correction
is therefore at most E_left+E_right+6D <= epsilon*N. This uses only
qualitative m(W)->0, not any unproved logarithmic Mertens rate.

## Recentered finiteness obstruction

`finite_primeSet_forces_negative_recentered_fourFactor` proves that a
finite prime-pair set forces, at arbitrarily large common scales,

    |meanCenteredFourFactor(alpha,N,W,W,W,W)/N + 1| <= epsilon.

The argument combines all FOUR simultaneous errors with the existing
prime covariance obstruction; no independently selected good-scale sets
are intersected.

`infinite_primeSet_of_recentered_fourFactor_gap` proves that an eventual
strict lower bound

    meanCenteredFourFactor >= -(1-delta)*N, delta>0,

on these OutputPrimeScale scales would imply the conjecture at alpha.
That lower bound remains an EXPLICIT UNPROVED HYPOTHESIS.

## Remaining gap

This completes the arithmetic recentering step proposed in
ProgressCenteredLowMellin.md. It does NOT turn the explicit low-frequency
Mellin integral there into a representation of the full floor-strip sum,
and does NOT bound the signed high-frequency contribution.

A genuine sufficient lower bound on the full correlation, or an actual
irrational counterexample, is still required. The requested universal
conjecture is not settled.
