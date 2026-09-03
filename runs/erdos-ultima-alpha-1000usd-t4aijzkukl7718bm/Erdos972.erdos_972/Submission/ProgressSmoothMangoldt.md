# Exponential-divisor proxy: verified comparison, still no settlement

Spec.lean is unchanged and still contains the original sorry. No proof or
disproof of the conjecture has been found. No submission has been made.

## New definitions and verified results

SmoothMangoldt.lean, namespace Erdos972SmoothMangoldt:

    F(t,n) = expDivisorSum t n
           = sum_{d|n} mu(d) exp(-t log d)
    S(t,n) = smoothMangoldt t n = [F(t,n)-F(0,n)]/t.

The subtraction is essential at n=1. F(0,n) is the arithmetic-function unit,
so S(t,1)=0 rather than 1/t. The convention at n=0 also gives S(t,0)=0.

- `hasDerivAt_expDivisorSum`: derivative at t=0 is Lambda(n).
- `smoothMangoldt_tendsto`: S(t,n) -> Lambda(n) as t->0+ for fixed n.
- `smoothMangoldt_error_bound`: for t>0 and t log n<=1,

      |S(t,n)-Lambda(n)| <= t * card(divisors n) * (log n)^2.

- `finite_smooth_correlation_tendsto`: convergence of the correlation on
  each FIXED finite window. This cannot silently be used with N=N(t).

SmoothMangoldtPositive.lean, namespace Erdos972SmoothMangoldtPositive:

- `expDivisorSum_product`, for n!=0:

      F(t,n) = product_{p|n, p prime} [1-exp(-t log p)].

  The proof establishes multiplicativity and evaluates every prime power;
  it is not restricted to squarefree n.
- `smoothMangoldt_nonneg`: 0<=S(t,n) for t>0, all n.
- `smoothMangoldt_le_log`: S(t,n)<=log n for t>0, all n.

SmoothCorrelationApprox.lean, namespace Erdos972SmoothCorrelationApprox:

    smoothCorrelation t alpha N = sum_{0<n<=N} S(t,n) S(t,floor(alpha*n)).

- The elementary first-moment bound sum_{n<=N} tau(n)<=N(1+log N).
- The corresponding output divisor bound, using injectivity of floor(alpha*n)
  for alpha>=1.
- `smoothCorrelation_error_bound`: for alpha>=1, t>0,
  M=floor(alpha*N), t log M<=1,

      |smoothCorrelation t alpha N - mangoldtCorrelation alpha N|
        <= t*(N+M)*(1+log M)^4.

  This uses the mean divisor bound, not a worst-case divisor estimate. The
  positivity and log bound for S keep the product error linear in tau.

SmoothCorrelationScale.lean, namespace Erdos972SmoothCorrelationScale:

    smoothingParameter alpha N = 1/(1+log(floor(alpha*N)))^5.

- `normalized_error_bound`: for N>=1, the error divided by N is at most
  (1+alpha)/(1+log N).
- `variable_smoothing_error_tendsto`: at this parameter, the difference
  between smoothed and Mangoldt correlations divided by N tends to zero,
  for every fixed alpha>=1, over ALL natural cutoffs.
- `polynomial_cutoff_damping_tendsto_one`: for every fixed real delta,

      exp(-delta * smoothingParameter(alpha,N) * log N) -> 1.

  For N>0 this is the damping D^(-t_N) at D=N^delta. Thus one cannot claim
  this factor tends to zero at polynomial divisor cutoffs in the same
  parameter regime. This is a check on a proposed truncation estimate,
  not an impossibility theorem for all approaches using the proxy.

## Remaining analytic gap

No lower bound for the variable-parameter smoothed correlation has been
proved. In particular the preceding o(N) comparison does not prove that
its mean, or the Mangoldt correlation mean, approaches a positive number.

A possible fixed-t mean-value approach was reconsidered. Even an asymptotic
for every separately fixed t>0 would not justify substituting t=t_N and
interchanging the smoothing and cutoff limits. No such interchange has been
proved. No fixed-t correlation asymptotic was added as an assumed theorem.

The existing small-divisor covariance estimates apply to truncated finite
divisor polynomials. Their use for this full divisor sum requires a proved
uniform tail estimate in the vanishing-parameter regime, which is missing.
The long-divisor part cannot be discarded merely from the product formula
or positivity of the full sum.

All nine principal declarations in AuditSmoothMangoldt.lean compile with
only propext, Classical.choice, and Quot.sound. The original conjecture and
its import have not been changed.

## Subsequent uniformity review

No new sufficient correlation estimate was obtained. The original conjecture
is still unresolved.

- Reconsidered proving fixed-positive-t mean values by finite divisor
  approximation and mean-square tail control. No result uniform as t tends
  to zero was obtained, and no fixed-t asymptotic has been inserted as an
  assumption into the development.
- Such a fixed-t theorem would not by itself justify the diagonal parameter
  t_N used in SmoothCorrelationScale.lean. The already verified polynomial
  damping limit remains one at that parameter.
- Positivity of the full Euler product does not imply positivity of its
  signed truncated-divisor remainder. Discarding that remainder would be an
  unjustified lower-bound step.
- Reconsidered a less aggressive parameter on the order of 1/log N. The
  existing error comparison is not sufficient in that range, and no sharper
  mixed prime/composite correlation bound was proved to replace it.

No final theorem, import, or axiom declaration in Spec.lean was changed.
