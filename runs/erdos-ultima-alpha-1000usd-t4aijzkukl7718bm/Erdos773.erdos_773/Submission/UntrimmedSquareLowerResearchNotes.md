# Actual square-Sidon lower bound N^(2/3)/36 without degree trimming

The original conjecture is NOT settled. Spec.lean is unchanged, with its
sole admission for 0<epsilon<=1/3. Nothing has been submitted.

## Strongest actual lower bound

UntrimmedSquareLower.eventual_power_lower proves

    eventually M(N) >= N^(2/3)/36.

This improves the former 1/75 coefficient. It is an actual lower bound for
the unrestricted maxSidonSubsetCard of the first N positive squares, not a
conditional, fractional, or restricted-family result. All sampling and
extraction hypotheses are instantiated. It is still not the coefficient-one
endpoint, and gives no exponent greater than two thirds.

## New arithmetic and sampling inputs

UniformSquareSamplingResearchNotes.md documents the completed proof that,
for every fixed 0<delta<1, eventually there is a progression-free root set
A subset [1,N] with

    |A| >= (1-delta)*N/log N,
    degree(edges A,a) < (1999/6000)*N/(log N)^2 for all a in [1,N].

There is no maximum-degree trimming and no linearizing polynomial thinning.
The Gaussian incident count has finite leading coefficient 83/250 and
uniform eventual coefficient 333/1000. The finite high-moment sampling
argument controls every link simultaneously. Its 40-declaration combined
audit is GaussianSamplingAudit.lean, with log
/tmp/gaussian-sampling-combined-audit.log.

## Untrimmed extraction certificate

GreedyUntrimmedSquareCertificate.eventually_certificate applies the existing
GreedyRelaxedExtraction directly to the entire supplied AP-free carrier A.
The hypotheses supply degree<=m^300 and pair codegree<=m^3. It concludes

    M(N) >= tau*|A| / ((100/99)*m^100),

under the existing polynomial-volume and relaxed horizon-budget hypotheses.
There is no term 4*E/D. This is not a new stochastic tracking theorem: the
already proved relaxed growing-horizon theorem is reused unchanged.

## Scalar conversion

UntrimmedSquareScales defines

    root(X,L) = degreeRoot(X/4,L)
              = ceil((X/(3L^2))^(1/300)).

It proves:

- X/(3L^2) <= root^300;
- if 3L^2<=X^(1/301), then X<=root^301;
- once root>=1000001, root^300*L^2 <= (667/2000)*X.

The volume proof is direct, so the exponent is still 301 rather than 302.
The logarithmic condition follows from log X <= (1/2)*X^(1/602) eventually.
The unchanged horizon tau=(log N)^(1/3)/50 obeys
horizonBudget(tau)<=m^25 via the already proved long_horizon_budget.

Use delta=1/1000. The exact degree denominator bound is

    (100000/98901)*m^100*L <= (18/25)*(X*L)^(1/3).

The cube comparison uses 667/2000 <= (890109/1250000)^3.
Together with the 999/1000 retained density and the 99/100 floor factor,
this gives 1/(50*(18/25))=1/36. The final real-power cancellation is checked.

The old uniform pair-codegree estimate at exponent 1/301 gives codegrees
<=m, hence <=m^3. The sample degree cap is below X/(3L^2), hence <=m^300.
The sample has size <=N by containment; no upper N/log N estimate is assumed.

## Files and verification

- GreedyUntrimmedSquareCertificate.lean
- UntrimmedSquareScales.lean
- UntrimmedSquareLower.lean

All compile without warnings/admissions and have built oleans. Their axiom
checks contain only propext, Classical.choice, Quot.sound. The combined
UntrimmedSquareLowerAudit.lean checks 13 declarations; all are clean.

Logs:

    /tmp/greedy-untrimmed-square-cert.log
    /tmp/untrimmed-square-scales.log
    /tmp/untrimmed-square-lower.log
    /tmp/untrimmed-square-lower-combined-audit.log

Spec.lean still has its only sorry at line 2031. SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
The latest main-file compilation is /tmp/spec-gaussian-sampling-check.log.
No new proof has been consolidated into Spec.lean.

## Remaining work and scope

Uniform sampled maximum-degree control and the trimming loss are now
resolved. The dominant remaining coefficient loss is the conservative
long-time greedy envelope, not rounding, sampling density, or regularization.
The previous survival-target, moving-mean, and centered-energy certificates
remain conditional at the sharper shrinking scales; their outstanding
bootstrap and signed-covariance issues have not been solved here.

Even the coefficient-one endpoint would leave every 0<epsilon<1/3 open.
A near-linear integer square-Sidon selector or a fixed-power upper bound for
arbitrary square-Sidon subsets is still missing. No such result follows from
any of the completed generic extraction or construction-specific ceilings.
