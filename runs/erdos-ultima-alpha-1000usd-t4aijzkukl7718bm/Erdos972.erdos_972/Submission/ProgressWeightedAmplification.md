# Weighted divisor amplification — conjecture remains unresolved

New verified file: `WeightedDivisorAmplification.lean`.
Namespace: `Erdos972WeightedDivisorAmplification`.
The file imports only FormalConjecturesUtil and compiles.

Let S be a finite input set, P a finite set of primes, a(n) a nonnegative
weight, and

    row(d) = sum_{n in S, d|n} a(n),
    K(n) = sum_{p in P} 1_{p|n},
    H = sum_{p in P} 1/p.

Assume X,E >= 0 and absolute row error at most E relative to X/d at d=1,
at every p in P, and at every lcm(p,q) for p,q in P.

## Verified estimates

- `centeredPair_rows`: exact expansion of each centered indicator product
  using these four divisor rows.
- `centeredPair_error`: each centered pair differs from its local main
  term by at most 4E.
- `weighted_variance`:

      sum a(n) (K(n)-H)^2 <= X*H + 4E*|P|^2.

- `amplification_sq`, for |b(n)|<=1, is weighted Cauchy--Schwarz:

      [H sum a(n)b(n) - sum a(n)b(n)K(n)]^2
        <= [sum a(n)] [sum a(n)(K(n)-H)^2].

- `open_amplifier` rewrites the amplified term as the actual sum of
  signed divisor rows.
- `amplification_rows_sq` combines them:

      [H sum a(n)b(n) - sum_{p in P} row_{ab}(p)]^2
        <= (X+E) [X*H + 4E*|P|^2].

- `output_moebius_amplification` specializes this to the actual functions
  a(n)=Lambda(floor(alpha*n)) and b(n)=mu(n), on 1<=n<=N. The row hypotheses
  remain explicit in its statement.

The weight enters linearly in the variance; no estimate for sum a(n)^2 is
used. This addresses the initial weighted replacement step, NOT the later
signed amplified correlation. In particular, no cancellation of that
amplified sum, no sufficient prime-pair lower bound, and no irrational
counterexample is supplied by these lemmas.

All five printed principal axiom audits contain only propext,
Classical.choice, and Quot.sound. Spec.lean is unchanged with its original
sorry. No incomplete final proof was resubmitted.

## Actual good-scale application

`PrimeOutputAmplificationScales.lean` now compiles. It imports the finite
amplification file, the existing one-prime divisor-row theorem, and the existing
common-scale budget infrastructure.

Verified:

- `exists_large_prime_harmonicMass`: finite prime sets have arbitrarily large
  reciprocal mass, using Mathlib's divergence theorem.
- `exists_small_output_rows`: for every fixed irrational alpha>1, finite divisor
  cutoff M, tolerance eta>0, and lower scale bound B, there are N>B and X,E with
  0<=X<=7N, 0<=E<=eta*N, and all actual output-Mangoldt divisor rows through M
  within E of X/d. The existing irrational good scales supply these rows; this
  theorem has no unproved row-distribution hypothesis.
- `amplification_numeric`: the explicit conversion of the squared error budget
  to an epsilon*N bound.
- `exists_prime_amplifier_comparison`: for each fixed irrational alpha>1 and
  epsilon>0, there is a FIXED finite prime set P, H=sum_{p in P}1/p>0, such that
  for every B there is N>B where, simultaneously for every |b(n)|<=1,

      |sum_{n<=N} Lambda(floor(alpha*n)) b(n)
       - (1/H) sum_{p in P} sum_{n<=N,p|n} Lambda(floor(alpha*n)) b(n)|
          <= epsilon*N.

The two principal scale theorems audit with only propext, Classical.choice,
and Quot.sound. The amplifier is fixed before the scale is selected; no
prescribed P(N) growth rate is asserted.

This is still a replacement estimate. It neither estimates the amplified
signed sum nor makes the unbounded source Mangoldt weight a bounded source
coefficient. It therefore does not imply the original prime-pair conjecture.
Spec.lean remains unchanged and incomplete, and was not resubmitted.
