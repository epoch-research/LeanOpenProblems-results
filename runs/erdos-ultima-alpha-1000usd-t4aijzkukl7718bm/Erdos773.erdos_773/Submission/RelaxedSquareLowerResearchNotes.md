# Relaxed nonlinear horizon: actual N^(2/3)/75 lower bound

The main conjecture is NOT settled. Spec.lean remains unchanged, with its
sole sorry for 0<epsilon<=1/3. This continuation improves an actual lower
bound, not merely a conditional or construction-specific theorem.

## New strongest completed lower bound

RelaxedSquareLower.eventual_power_lower proves

    eventually M(N) >= N^(2/3)/75.

This improves the earlier coefficient 1/500 by a factor of 20/3. An
intermediate RefinedSquareLower.eventual_power_lower proves 1/424 using
only tighter ceiling and horizon constants. Neither result proves the
coefficient-one endpoint, much less the original near-linear conjecture.

## Relaxation and proof obligations

The original nonlinear scales have

    d=m^100, rho=m^-25, C=16*m^21,
    degree <=m^300, pair codegree <=m^3.

Previously the growing-horizon interface required

    horizonBudget(tau)=exp(10000*(1+tau)^3) <= m.

The new interface allows horizonBudget(tau)<=m^25. This is NOT a change to
the old theorem's statement: new theorems discharge the relaxed numerical
conditions independently.

GreedyRelaxedBudget proves exp(50*(1+tau)^3)<=m by comparing twenty-fifth
powers. The already established penalty and speed bounds, plus explicit
bounds for 4/q, 4*tau/q, 288/q and 54/q^2, are therefore each <=m. Thus the
old small-factor bounds needed for witness tails and concentration are
retained, even though the envelope budget itself is now much larger.

GreedyRelaxedScales applies the old analytic exponential_threshold at
parameter m^25 (where it only needs this relaxed budget). It verifies the
promotion thresholds 288*m^133 and 54*m^274 and retains the actual profile
failure bound 6*exp(-m/204), including the pair-codegree factor.

GreedyRelaxedGrowing rechecks the full numerical data, availability,
short-run inequality, selection ratio <=m^-97, promotion bounds, and
vanishing total failure probability. It proves actual full independent
runs, with no early-stop alternative or unproved trajectory hypothesis.

The floor loss is also reduced from 1/2 to 99/100. The run length before
rounding is >=100 from V>=m^300 and m>=36, so floor(x)>=.99*x. The old
factor two came from floor rounding, NOT from regularization. The verified
regularization transfer preserves independent-set density exactly.

GreedyRelaxedExtraction transfers to arbitrary finite carriers, and
GreedyRelaxedSquareCertificate transfers to square Sidon sets with the
same explicit maximum-degree trimming loss as before.

## Square scale

Use the same degree threshold D=(4/3)*N/(log N)^2 and degree root
m=ceil(D^(1/300)). RefinedSquareLower proves, once m>=1000001,

    m^300*(log N)^2 <= (667/500)*N.

The retained size after degree trimming is >=(3/4)*N/log N.
The new horizon is tau=(log N)^(1/3)/50. Its relaxed budget is <=m^25,
using N<=m^301. All constants, floor/ceiling bounds, and real-power
identities are explicitly checked. These give the rational coefficient
1/75.

## Modules and audits

New modules:

- RefinedSquareLower.lean (intermediate actual 1/424 bound)
- GreedyRelaxedBudget.lean
- GreedyRelaxedScales.lean
- GreedyRelaxedGrowing.lean
- GreedyRelaxedExtraction.lean
- GreedyRelaxedSquareCertificate.lean
- RelaxedSquareLower.lean

All compile, have built oleans, and have clean printed axiom audits using
only propext, Classical.choice, Quot.sound. None imports Spec.lean.

Logs: /tmp/refined-square-lower.log, /tmp/greedy-relaxed-budget.log,
/tmp/greedy-relaxed-scales.log, /tmp/greedy-relaxed-growing.log,
/tmp/greedy-relaxed-extraction.log, /tmp/greedy-relaxed-square-cert.log,
/tmp/relaxed-square-lower.log.

## Remaining issue

These results still give only exponent 2/3 with a constant below one.
The larger horizon is within the verified generic logarithmic-gain regime,
not a new exponent or a near-linear construction. Maximum-degree trimming
and the non-sharp envelope growth still lose constants. No original proof
or disproof has been submitted.

The retained combined audit is RelaxedSquareLowerAudit.lean, with 14 clean
checks in /tmp/relaxed-square-lower-combined-audit.log.

## Exploratory next direction (NOT yet a theorem)

Research/SquareIncidentProfile.cpp computes exact incident four-support
counts by sorting unordered square sums. It is exploratory and is not
trusted by any Lean theorem. The runs at N=2000 and N=8000 have maximum
degrees 3732 and 18393, respectively; the normalized maxima are about
.2455 and .2558. These finite counts do not prove an asymptotic bound.

A possible route is to encode each collision through a fixed root by a
small primitive Gaussian factor and the partner's residue class. A factor
of norm at most sqrt(2)*N would lead to a sum of N/q+1 over primitive
opposite-parity Gaussian directions with norm q<=sqrt(2)*N. Its expected
leading coefficient is 1/pi<1/3. A periodic sieve excluding shared factors
3,5,7 together with opposite parity has density 18432/44100, small enough
that a sufficiently accurate rational radial integral bound could also
make the coefficient less than 1/3. The encoding, its multiplicities, and
the analytic bound are NOT proved yet. No endpoint conclusion follows.

The small Gaussian-factor step has subsequently been proved in
GaussianCollisionFactorization.lean. Its precise scope and remaining
normalization/counting obligations are in GaussianIncidentDegreeResearchNotes.md.
It does not yet yield an incident-degree bound.

Final main-file check: /tmp/spec-relaxed-lower-check.log. The file remains
unchanged with its expected sorry and SHA-256
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
