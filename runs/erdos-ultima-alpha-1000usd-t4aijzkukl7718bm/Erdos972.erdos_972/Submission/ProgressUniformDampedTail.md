# Uniform fixed-parameter tails and actual mean values

The original conjecture is STILL UNSOLVED. Spec.lean is unchanged with its
original sorry. No irrational counterexample or sufficient prime-pair lower
bound has been proved. Do not submit these results as a settlement.

## DampedDivisorKernel.lean

Namespace Erdos972DampedDivisorKernel. Defines

    w(t,n) = exp(-t log n)/n,
    K(t,d,e) = gcd(d,e) w(t,d) w(t,e),
    kernelMass(t) = sum'_(d,e) K(t,d,e).

For every fixed t>0, proves summability of w and K. The gcd decomposition
(d,e) -> (g,d/g,e/g) is injective, even when a coordinate is zero. It bounds
the nonnegative K series by a product of three convergent reciprocal-power
series. For d,e>0,

    K(t,d,e) = exp(-t log d) exp(-t log e) / lcm(d,e).

No explicit small-t growth estimate for kernelMass is asserted.

## UniformDampedTail.lean

Namespace Erdos972UniformDampedTail. Let

    Pplus(t,n) = sum_(d|n) exp(-t log d).

Proves the exact lcm expansion of its finite second moment and

    sum_(n<=N) Pplus(t,n)^2 <= N kernelMass(t),       t>0.

For the actual signed divisor tail R(t,D,n)=F(t,n)-P(t,D,n), proves

    |R(t,D,n)| <= D^(-t/2) Pplus(t/2,n),
    sum_(n<=N) R(t,D,n)^2 <= N D^(-t) kernelMass(t/2).

Here D^(-t) is implemented as exp(-t log D), including D=0. For every
fixed t>0 and epsilon>0, one D makes the normalized energy <=epsilon for
ALL N. Unlike the earlier bound, no log N loss occurs.

## UniformSmoothCorrelationTail.lean

Namespace Erdos972UniformSmoothCorrelationTail. Uses injectivity of
floor(alpha*n), alpha>=1, to transfer the uniform second moment to output
indices. An elementary quadratic perturbation inequality yields

    for fixed alpha>=1,t>0,epsilon>0,
    exists D, forall N,
    |fullExpCorrelation(t,alpha,N)-truncatedExpCorrelation(t,alpha,D,N)|
      <= epsilon N.

## FixedDampedCorrelation.lean

Namespace Erdos972FixedDampedCorrelation.

- Strengthens the preceding cutoff statements to EVENTUALLY ALL D.
- Defines m(t)=sum'_d mu(d) exp(-t log d)/d and proves absolute
  summability and divisorMean(D,a_t)->m(t) for t>0.
- DivisorScale(alpha,u) is precisely the existing joint-divisor row
  property on N=floor(u^6/alpha), with row error 118 root64(u) u^4.
- For fixed D, the normalized total row error is bounded eventually by
  236 alpha D^2/u and hence tends to zero.
- eventually_fixed_full_error: for fixed alpha>=1,t>0,epsilon>0,
  eventually all good u satisfy

      |fullExpCorrelation(t,alpha,N)-N m(t)^2| <= epsilon N.

- exists_fixed_damped_scale_sequence: for alpha>1 irrational, there is a
  SINGLE u(k)->infinity, independent of t, such that for EVERY FIXED t>0,

      fullExpCorrelation(t,alpha,N_k)/N_k -> m(t)^2,
      N_k=floor(u(k)^6/alpha).

- fixed_smooth_mean_on_scales transfers to the corrected smoothMangoldt
  correlation, using the proved n=1 correction of size at most one:

      smoothCorrelation(t,alpha,N_k)/N_k -> (m(t)/t)^2.

The convergence thresholds are allowed to depend on t.

## DampedMeanZeta.lean

Namespace Erdos972DampedMeanZeta.

- Identifies the complex embedding of m(t) with L(mu,1+t).
- For t>0, proves zeta(1+t) m(t)=1.
- Identifies m(t)/t with the inverse regularized zeta at 1+t.
- Uses the proved zeta residue and continuity to prove

      m(t)/t -> 1 as t -> 0+.

Thus the ITERATED normalized smooth correlation limit is one: first
k->infinity at fixed t>0, then t->0+. This is NOT the opposite order and
NOT a joint-limit theorem with t depending on k.

## Audit and remaining gap

AuditUniformDampedTail.lean prints the axioms for twelve principal results.
All compile using only propext, Classical.choice, and Quot.sound.

The actual prime/Mangoldt comparison requires much smaller damping at a
given N. None of the new results is uniform enough near t=0 to make that
substitution. For fixed positive t the weights also detect composites;
as t decreases, their contributing mass can move to larger n. An iterated
limit and pointwise convergence cannot justify exchanging the limits.
No prime-pair lower bound or signed four-factor lower gap was obtained.
