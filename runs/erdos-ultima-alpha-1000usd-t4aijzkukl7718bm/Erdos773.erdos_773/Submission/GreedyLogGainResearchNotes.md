# Growing horizons and a square-Sidon N^(2/3) lower bound

**Later coefficient update:** GreedyTightSquareLower.eventual_power_lower now
proves M(N)>=(1/8192)*N^(2/3) eventually. See
GreedyTightCoefficientResearchNotes.md. The newer proof tightens rounding
and the horizon without changing the concentration machinery. The combined
audit now has 199 clean checks across 43 modules. The conjecture remains
unsettled, including the unit-coefficient epsilon=1/3 endpoint.

This is NOT a settlement of Erdős 773. The conjecture in Spec.lean is unchanged
and still has its sole admission for 0<epsilon<=1/3. This continuation DOES
remove the logarithmic loss from the actual square-Sidon lower bound.

## Strongest current actual theorem

File: GreedySquarePowerLower.lean
Namespace: Erdos773.GreedySquarePowerLower

`eventual_power_lower` proves

    eventually M(N) >= c0*N^(2/3),
    c0 = 1/(32768*15360000^(1/3)) > 0.

`eventual_rational_power_lower` gives the convenient weaker statement

    eventually M(N) >= (1/10000000)*N^(2/3).

M(N) is the ACTUAL maximum Sidon-subset cardinality of the first N positive
squares, not a relaxed hypergraph parameter. The real cube root is Mathlib's
Real.rpow with exponent 1/3; all identities involving it are proved.

This is stronger than both the old fixed 5/4 logarithmic-loss bound and the
intermediate unbounded-multiplier logarithmic-loss bound. It does NOT give
an exponent greater than 2/3. Its constant is below one, so it does not even
prove the exact original epsilon=1/3 assertion M(N)>=N^(2/3). No original
proof or disproof has been submitted.

## Verification

Six additional clean built modules, 741 lines, 18 permitted-axiom checks:

* GreedyHorizonFactors: explicit exponential bounds on all horizon factors.
* GreedyGrowingFailure: uniform growing-horizon concentration and extraction.
* GreedyGrowingExtraction: regularization and finite-carrier transfer.
* GreedyGrowingSquareCertificate: growing-horizon square extraction certificate.
* GreedyGrowingSquareScales: twenty-fourth-root rounding and logarithmic time.
* GreedySquarePowerLower: actual square-Sidon power-scale lower bounds.

No warnings, admissions, native evaluation, or extra axioms occur in them.
None imports admitted Spec.lean.

New audit: /tmp/greedy-growing-final-audit.log (18 checks).
Combined audit:

    /tmp/greedy-square-power-combined-audit.log

contains 191 clean checks across 41 modules. The twenty-one concrete-guard,
extraction, and square-transfer modules total 2791 lines with 73 checks;
the earlier concentration/trajectory foundation supplies the other 118.
Audit sources GreedyCombinedAudit.lean and GreedyGrowingAudit.lean are retained.

## Explicit horizon dependence

Set B=1+tau, q=exp(-tau^3), S=16030*B^4. The six-test penalty from the
fixed-horizon proof is

    P = ((1200*B^6+2*S^2)/q)*B + 5*B^2 + S + 2.

The new analytic estimates prove, for tau>=0,

    P <= 10^9*B^9*exp(tau^3) <= exp(50*B^3),
    S <= exp(20*B^3),
    576*tau^3/q^3 <= exp(20*B^3).

The numerical exponential bounds use 2^k<=exp(k), proved from exp(1)>=2;
no transcendental numerical oracle is used. In particular exp(32)>=10^9.

Define

    horizonBudget(tau)=exp(10000*(1+tau)^3).

This bounds P, S, the auxiliary numerator, 4/q, and 4*tau/q, and is at least
17 and tau. It is also exactly the already verified scalar trajectory
threshold, so no additional unproved analytic condition is introduced.

## Uniform concentration in a growing horizon

Specialize the previous polynomial parameter m to n^2. Thus

    d=n^8, original degree D=n^24, rho=1/n^2, C=16*n^2.

Assume tau>=1 and horizonBudget(tau)<=n. The old profile cost exponent
m/(68*P) is then at least n/68. The auxiliary numerator is at most n, and

    n/(n^2+1) <= 1/2

follows from (n-1)^2>=0. Also (1/2)^(n^2+1)<=(1/2)^(n+1).

For regular volume n^24<=V<=n^(2*A), the total failure probability is bounded
UNIFORMLY in tau by

    uniformBound(A,n)
      = n^(4*A)*(1/2)^(n+1) + 6*n^(2*A)*exp(-n/68).

This tends to zero. Consequently the threshold in n depends only on A, not
on tau. `eventually_uniform_data` proves every finite numerical obligation,
including L>0, T<=L, all profile controls, failure<1, and the rounded size
lower bound, simultaneously for every allowed tau.

`GreedyGrowingFailure.eventually_independent` gives independent sets of size

    V*tau/(2*n^8)

in every linear regular degree-n^24 four-uniform hypergraph in that volume
interval, for all sufficiently large n and all allowed tau.

## Bounded degrees and arbitrary finite carriers

`GreedyGrowingExtraction.eventually_independent` permits maximum degree n^24
and volume <=n^A. Regularization uses <=8*n^24 copies; for n>=2 its volume is
<=n^(A+27)<=n^(2*(A+27)). The lower volume requirement follows from the prime
regularization degree when the original carrier is nonempty. Empty carriers
are handled explicitly. The density transfer has no additional loss.

Its `eventually_selection` transfers this statement to arbitrary ambient
finite sets, reusing the exact degree, intersection, and independence lifts.
All thresholds remain uniform over tau. The fixed-multiplier theorem from
the preceding continuation is not mistakenly applied with a varying multiplier.

## Square transfer and rounding

Reuse logarithmic AP-free sampling, pair codegree <=N^(1/16), and the earlier
finite penalized linearization and degree trimming. With X=N,L=log N,

    r=X^(1/4), p=1/r, mu=L^2/(16*r), D=128*r/L^2,
    n=ceil(D^(1/24)).

Both deletion/penalty costs are <=p|A|/4. The trimmed AP-free linear carrier
has size >=p|A|/4 and maximum degree <=D<=n^24. The new square certificate
therefore gives

    M(N) >= tau*p*|A|/(8*n^8).

The twenty-fourth-root ceiling is essential: reusing the twelfth-root
ceiling with the n^24 degree theorem would lose a power of N. The exact
rounding bounds are

    D<=n^24<=16777216*D,
    n^24*L^2 <=2147483648*r,
    X<=n^192.

The volume bound follows eventually from L^2<=X^(1/8), while the lower size
bound for A is X/(2*L). Cubing a denominator verifies

    16*r*L*n^8 <=32768*(X*L)^(1/3).

Consequently

    M(N) >= tau*X/(32768*(X*L)^(1/3)).

## A genuinely logarithmic horizon

Take

    tau=(L/15360000)^(1/3).

Eventually L>=15360000, so tau>=1. Then

    10000*(1+tau)^3 <=80000*tau^3 = L/192.

As X<=n^192,

    horizonBudget(tau) <=exp(log X/192)=X^(1/192)<=n.

Thus this growing tau satisfies the actual uniform extraction hypotheses at
every sufficiently large N. A final exact real-power identity cancels L:

    tau*X/(32768*(X*L)^(1/3))
      = X^(2/3)/(32768*15360000^(1/3)).

Since 15360000^(1/3)<=256, the coefficient is >=1/10000000.
This completes the claimed actual power-scale lower bound.

## Remaining task

The old integrated-variance, fixed-horizon, and growing-horizon probability
gaps are now all closed. The generic logarithmic gain has also been
transferred through the square-specific machinery with every loss included.
It still leaves the central arithmetic exponent gap: a generic sparse
four-uniform argument only reaches the 2/3 scale here.

No near-linear square-specific selection theorem, no bootstrap improving
that exponent, and no fixed-power upper bound disproving the conjecture has
been found. Merely replacing the small explicit constant by a better one
would not settle the range epsilon<1/3. No such improvement is claimed.

The new results remain in clean scratch modules, not consolidated into the
single final submission file. Spec.lean has its same sole import, unchanged
statement, and sole sorry at line 2031. Latest main check:

    /tmp/spec-greedy-power-lower-check.log

It shows only the expected admission and the old harmless linter warnings.
SHA-256 remains

    917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
