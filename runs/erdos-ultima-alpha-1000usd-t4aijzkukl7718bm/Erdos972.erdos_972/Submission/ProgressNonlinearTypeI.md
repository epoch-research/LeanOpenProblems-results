# Nonlinear Type-I weights: a verified signed one-prime covariance estimate

The original conjecture remains UNSOLVED. Spec.lean is unchanged and retains
its original sorry. No prime-pair lower bound or irrational counterexample
has been proved. No final proof was submitted.

## New analytic tool: LipschitzLogWeights.lean

Namespace Erdos972LipschitzLogWeights.
For a real L-Lipschitz function Phi of the logarithm, finite partial
summation proves:

- `logarithmic_weighted_prefix_bound`: a uniform prefix error E costs
  (|Phi(log N)|+L log N) E, with no monotonicity assumption on Phi.
- `centeredLogWeight_bound`: if X(0)=0, then

    |sum_{n=1}^N Phi(log n) [X(n)-X(n-1)-X(N)/N]|
      <= L * centeredMeanBudget(X,c,N),

  where the budget is

    sum_{n=1}^N |X(n)/n-c| + N |X(N)/N-c|.

  Constants in Phi cancel, so Phi(0) is unrestricted.
- `centeredMeanBudget_div_tendsto`: X(N)/N -> c implies budget/N -> 0.
  No logarithmic rate is inserted into this qualitative convergence.

## Finite pattern inversion and weighted rows

GcdProfileExpansion.lean, namespace Erdos972GcdProfileExpansion:
For F>0 and f on naturals, Mobius inversion gives

    f(gcd(n,F)) = sum_{d|F, d|n} profileCoeff(f,d).

The signed divisor density sum profileCoeff(f,d)/d equals the average of
f(gcd(n,F)) over n=1,...,F. Thus the average profile keeps the original
Lipschitz constant, without a loss in the number of patterns.

The coefficient costs remain explicit:

    |profileCoeff(f,d)| <= tau(d) H,
    profileCost(F) = sum_{d|F} tau(d).

GcdWeightedRows.lean, namespace Erdos972GcdWeightedRows:
Assume all divisors d|F satisfy, for j<=N,

    |sum_{n<=j,d|n} a(n) - X(j)/d| <= E,   X(0)=0.

For profiles Phi_r with Lipschitz constant L and endpoint bound H,
`weighted_gcd_row_error` gives the actual finite comparison error

    <= profileCost(F) * (H+L log N) * E.

The comparison is with the averaged profile weighted by X(n)-X(n-1).

GcdProfileCovariance.lean, namespace Erdos972GcdProfileCovariance:
If also |X(N)/N|<=C, `gcd_covariance_bound` proves

    |Cov_N(Phi_{gcd(n,F)}(log n), a(n))|
      <= L * centeredMeanBudget(X,c,N)
         + (H+L log N) [profileCost(F)(E+C)+E].

Ordinary divisibility counts have prefix error <=1. The main centering
budget has NO profileCost factor; the cost occurs only in the row errors.

## Application to the actual positive Vaughan remainder

PrimeGcdRows.lean, namespace Erdos972PrimeGcdRows:
The existing prime-output arc rows imply input-indexed divisibility rows
with common prefix X(j)=rowMean(alpha,j)=psi(alpha*j)/alpha:

    |sum_{n<=j,d|n} Lambda(floor(alpha*n)) - X(j)/d|
      <= E+2 log(alpha*N),   j<=N.

Short prefixes j<d are included. A direct Chebyshev endpoint comparison
avoids any assumed rate for psi(x)/x -> 1.

PositiveRemainderPrimeCovariance.lean:
Namespace Erdos972PositiveRemainderPrimeCovariance.
Let R be the actual Vaughan remainder, R_+=max(R,0), D=UV and F=D!.
For U>=1, V>0, D<=N, the finite row hypotheses above give

    |Cov_N(R_+(n), Lambda(floor(alpha*n)))|
      <= D * centeredMeanBudget(rowMean(alpha),1,N)
         +100 D [profileCost(F)+1]
              [1+log(alpha*N)]^2 [E+1].

This is a SIGNED covariance estimate, not an unsigned energy bound.
The n<=V correction is proved, with L1 cost <=7V and covariance cost
<=14 V log(alpha*N), then absorbed into the displayed coarse budget.
A sharper finite statement retains that correction separately.

## Fixed-cutoff and diagonal good scales

PositiveRemainderPrimeScales.lean:
Namespace Erdos972PositiveRemainderPrimeScales.

- `positiveCovarianceBudget_div_tendsto`: for each FIXED U,V and alpha>=1,
  the displayed budget, using the established polynomial row error on
  N=scaleCutoff(alpha,u), divided by N tends to zero.
- `eventually_positive_remainder_prime_covariance`: for alpha>1 irrational,
  every sufficiently large good OutputPrimeScale satisfies the epsilon-N
  bound for each fixed positive U,V.
- `exists_growing_positive_remainder_prime_scale`: for every B and epsilon>0,
  there are W>B, u>B and N=scaleCutoff(alpha,u), with (W^2)!<=root64(u),
  the actual good prime rows, and

    |Cov_N(R_{W,W,+}, Lambda_output)| <= epsilon N.

  The proof chooses W=B+1 FIRST, then chooses a sufficiently large good
  scale. It does NOT assert this for W=growingCutoff(u), the previous
  power-growing cutoff, nor supply a quantitative rate for W versus N.

## Remaining mathematical gap

This advances the nonlinear positive-part approach past a mere structural
identity: one genuine signed mixed covariance is now controlled on suitable
scales. It does not estimate the full signed two-remainder correlation.
In particular it cannot be substituted for the strict centered four-factor
gap in FourFactorReduction.lean. The main power-growing cutoffs have a
factorial pattern modulus outside the proved row range.

No dual positive-remainder covariance, two-positive-remainder correlation,
sufficient negative-remainder lower bound, or prime-pair lower bound was
asserted as a consequence. Nonnegativity of a majorant residual alone leaves
its mean product and centering correction, which must not be discarded.

All seven new development files compile. AuditNonlinearTypeI.lean checks
fifteen principal declarations with only propext, Classical.choice,
and Quot.sound. The original Spec.lean and its sole import are untouched.

## Positivity follow-up: the actual fixed-cutoff majorant mean diverges

PositiveTypeIMajorantMean.lean now verifies, for each FIXED U>=1 and any V,

    total_N max(typeIPart(U,V),0) / N -> +infinity.

This is divergence of the ACTUAL mean, not an upper error budget. The proof
is elementary: for F=(max U V)!, every integer F*k+1 is coprime to F, so the
rough-support identity gives

    max(A_UV(F*k+1),0) = log(F*k+1).

The intermediate finite theorem `progression_log_mean_lower` proves, for
any nonnegative f with f(F*k+1)>=log k and N>=2F,

    log(floor(N/(2F))) / (4F) <= total_N f / N.

An injective progression block inside [1,N] supplies the count. The final
limit uses only logarithmic growth and division by the fixed positive F.
No PNT, prime-pair lower bound, or irrationality is needed.

This checks a concrete limitation of converting the newly proved fixed-
cutoff mixed covariance into a lower bound using the positive Type-I
majorant. The product of the majorant means cannot be discarded. In the
idealized normalized main terms, the elementary majorant-product lower
bound is M+L-ML; small mixed covariance does not make this positive when
both majorant means are large. The new divergence theorem does not claim
the same conclusion for arbitrary N-dependent cutoffs.

AuditPositiveTypeIMajorantMean.lean compiles and checks its three principal
declarations with only propext, Classical.choice and Quot.sound.

Further review of prime-ratio approximation, translation, and topological
routes did not yield a new sufficient estimate or an irrational
counterexample. The original conjecture is still unresolved, Spec.lean is
unchanged, and no final proof was submitted.
