# Explicit divisor-tail estimates: verified, conjecture unresolved

Spec.lean is unchanged with its original sorry. No prime-pair lower bound
or irrational counterexample has been obtained. No submission was made.

## SmoothDivisorTail.lean

Namespace Erdos972SmoothDivisorTail. With

    a_t(d) = mu(d) exp(-t log d),
    P(t,D,n) = sum_{d|n, d<=D} a_t(d),
    R(t,D,n) = expDivisorSum(t,n) - P(t,D,n),
    rho(t,D) = exp(-t log D),

for t>=0 the file proves:

- `abs_expTail_le`: |R(t,D,n)| <= rho(t,D) tau(n).
- `expTail_energy_bound`:

      sum_{0<n<=N} R(t,D,n)^2
        <= rho(t,D)^2 N (1+log N)^3.

  No sign is assigned to the tail.

Let M=floor(alpha*N), L=1+log M, alpha>=1. Define

    divisorTailBudget = (N+M) [rho L + (rho^2/2) L^3].

- `full_truncated_correlation_error`: the difference of the correlations
  of F(t,n) and P(t,D,n) is at most divisorTailBudget in absolute value.
  Uses 0<=F<=1, the actual signed-tail absolute bound, and divisor first
  and second moments. Output moments use injectivity of floor(alpha*n).
- `full_exp_correlation_error`: if every joint divisor row d,e<=D has
  discrepancy <=B, B>=0, the full F correlation differs from

      N * (sum_{d<=D} mu(d) exp(-t log d)/d)^2

  by at most divisorTailBudget+B D^2. The row estimate is an explicit
  hypothesis, available on the separately proved irrational good scales.
- `full_minus_scaled_smooth`: the difference between the F correlation
  and t^2 times the corrected smoothMangoldt correlation is <=1. The
  exceptional n=1 term is included, not omitted.
- `smooth_correlation_divisor_error`: for t>0 the normalized proxy satisfies

      |smoothCorrelation(t,alpha,N)
          - N*(divisorMean(D,a_t)/t)^2|
        <= [1 + divisorTailBudget + B D^2]/t^2.

This is a quantitative estimate, not a claimed prime-correlation lower bound.

## SmoothTailScales.lean

Namespace Erdos972SmoothTailScales.

    slowParameter u = 1/sqrt(1+log u).

- `slow_damping_bound`: at D=root64(u), for u>=1,

      rho(slowParameter(u),D)
        <= exp(1) exp(-sqrt(1+log u)/65).

- `slow_damping_weight_tendsto`: for every fixed k,

      rho(slowParameter(u),root64(u)) (1+log u)^k
        / slowParameter(u)^2 -> 0.

This gives an actual slowly vanishing parameter range where the explicit
long-divisor damping controls all fixed logarithmic losses. It does not
assert an asymptotic for the truncated scalar mean or a prime-pair result.

For the much smaller earlier comparison parameter

    t_N = smoothingParameter(alpha,N)
        = 1/(1+log(floor(alpha*N)))^5,

and ANY natural cutoff D(N)<=N eventually:

- `comparison_damping_tendsto_one`: rho(t_N,D(N))->1.
- `comparison_tail_budget_tendsto_atTop`:

      divisorTailBudget(t_N,alpha,D(N),N)/(t_N^2 N) -> +infinity.

IMPORTANT: the last theorem concerns the particular UPPER ERROR BUDGET.
It is not a lower bound on the actual tail or actual correlation error.
For example a full cutoff can make a particular tail exactly zero while
this crude upper bound is large. No impossibility theorem for stronger
signed tail estimates is claimed.

## What remains missing

The previous o(N) comparison with Mangoldt correlation and the successful
slow-parameter damping result have different parameter regimes. They cannot
be combined by substituting one parameter for the other without a new bound.
No stronger signed-tail estimate, mixed prime/composite estimate, or genuine
prime-pair lower bound was proved in this phase.

All eight principal declarations in AuditSmoothDivisorTail.lean compile
using only propext, Classical.choice, and Quot.sound. Spec.lean and its sole
import remain unchanged.

## Balanced-cutoff check: an actual error lower bound

New file BalancedSmoothCutoff.lean, namespace Erdos972BalancedSmoothCutoff.
Define

    balancedTruncation(t,D,n) = [P(t,D,n)-P(0,D,n)]/t.

This tests the idea of subtracting the truncated t=0 value rather than
subtracting the arithmetic-function unit after truncation.

Verified results:

- `balancedTruncation_prime`: this function is ZERO at every prime p>D,
  for every t. The prime contribution is entirely in its error.
- `smoothMangoldt_prime_lower`: if t>0 and t log p<=1/4, then
  S(t,p)>=log p/2.
- `balanced_error_energy_lower`: if x>=2, D<=x, t>0,
  t log(2x)<=1/4, and the available dyadic prime count lower bound holds,

      sum_{0<n<=2x} [S(t,n)-balancedTruncation(t,D,n)]^2
        >= x log x / 16.

- `comparison_parameter_quarter`: the earlier comparison parameter t_N
  satisfies t_N log(floor(alpha*N))<=1/4.
- `balanced_error_energy_tendsto_atTop`: for alpha>=1 and any D(x)<=x
  eventually, using t=smoothingParameter(alpha,2x), the actual error
  energy divided by 2x tends to +infinity. The proof uses the verified
  qualitative PNT dyadic prime count, not a prime-pair assumption.

Unlike `comparison_tail_budget_tendsto_atTop`, this last theorem is about
ACTUAL ERROR ENERGY, not merely a diverging upper bound. It rules out the
particular o(N) mean-square approximation proposed for this balanced cutoff.
It does not estimate a signed cross-correlation and does not disprove the
original conjecture.

A cofactor-weighted truncation was also reconsidered mathematically. Its
small-parameter limit is the already studied truncated Mobius-log Type-I
expression; the exact rough-semiprime values in RemainderSemiprimes.lean
prevent treating its residual as an automatically small or nonnegative
error. No new cofactor-weighted theorem or sufficient signed estimate was
asserted in this review.

AuditBalancedSmoothCutoff.lean compiles; all five printed declarations use
only propext, Classical.choice, and Quot.sound. Spec.lean is still unchanged
and unresolved.
