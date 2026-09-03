# Exact full-smoothing L1 discrepancy; conjecture remains unresolved

Spec.lean is unchanged with its original sorry. No sufficient signed
prime-pair estimate or irrational counterexample has been proved. No proof
submission was made.

## DampedSingleMean.lean

Namespace Erdos972DampedSingleMean.

Proves a general absolutely convergent divisor-mean theorem:

    Summable (a(d)/d) implies
    (1/N) sum_(0<n<=N) sum_(d|n) a(d) -> sum'_d a(d)/d.

The proof expands the divisor sum, bounds each normalized floor-count term
by |a(d)/d|, proves floor(N/d)/N -> 1/d for each fixed d, and applies
summable dominated convergence. In the real-valued setting, the assumed
summability implies absolute summability.

Applied to a_t(d)=mu(d) exp(-t log d), t>0, this gives the ALL-N mean of the
full exponential-divisor function and its corrected smoothMangoldt proxy:

    mean F(t,n) -> m(t),
    mean S(t,n) -> m(t)/t,
    m(t)=1/zeta(1+t).

The n=1 correction is included exactly.

## FullSmoothL1Obstruction.lean

Namespace Erdos972FullSmoothL1Obstruction.

Defines

    overlap(t,N)=sum_(n<=N) min(S(t,n),Lambda(n)),
    error(t,N)=sum_(n<=N) |S(t,n)-Lambda(n)|.

Verified:

- 0<=S(t,n)<=1/t for t>0.
- pi(N)/N -> 0, from Mathlib's Chebyshev prime-counting bound.
- overlap(t,N) <= pi(N)/t + psi(N)-theta(N).
- overlap(t,N)/N -> 0 for each fixed t>0.
- The exact L1 identity

    error(t,N)=sum_(n<=N) S(t,n)+psi(N)-2 overlap(t,N).

- Consequently, for EVERY FIXED t>0,

    error(t,N)/N -> 1+m(t)/t = 1+1/[t zeta(1+t)].

- This limiting value tends to TWO as t->0+.
- For EVERY FIXED N, error(t,N)->0 as t->0+, by the already proved
  pointwise smoothMangoldt convergence and finite summation.
- For every t>0 and every B, some N>B has error(t,N)>N/2.
- Explicitly negates the claim

    forall epsilon>0, exists delta>0, forall 0<t<delta,
      forall N, error(t,N)<=epsilon N.

These are actual full-function error statements, unlike the earlier
estimate about a diverging upper bound. The relevant iterated limits
really do differ (two versus zero after normalization at fixed N).

## Meaning and limitations

The fixed-t mean theorem cannot be transferred to the Mangoldt mean by an
L1 approximation uniform over ALL input cutoffs N. That approximation is
false, even in one variable.

This does NOT rule out an L1 approximation in a prescribed joint regime
with t=t_N tending to zero fast enough; earlier small-parameter estimates
already prove such approximations. It also does NOT control the signed
cross-correlation error along floor(alpha*n), and does NOT disprove Erdos
972. A new signed prime-detecting estimate or an actual counterexample is
still needed.

AuditFullSmoothL1.lean compiles and audits all nine principal declarations
with only propext, Classical.choice, and Quot.sound.
