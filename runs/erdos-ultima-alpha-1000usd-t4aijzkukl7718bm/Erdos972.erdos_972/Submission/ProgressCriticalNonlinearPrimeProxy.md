# Critical nonlinear detector — composite error fully controlled

The conjecture in `Submission/Spec.lean` remains unproved and undisproved.
Its statement, import, and `sorry` are unchanged. No incomplete proof was
submitted as a settlement.

## New verified files

1. `Submission/PrimePairKernelSummability.lean`
   Namespace `Erdos972PrimePairKernelSummability`.
2. `Submission/CriticalNonlinearPrimeProxy.lean`
   Namespace `Erdos972CriticalNonlinearPrimeProxy`.

Both compile without errors or warnings. All principal printed axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Prime-pair kernel (not a prescribed-slope prime-pair estimate)

Over all ordered pairs of primes p,q, the kernel

    1 / max(p,q)^2

is summable. The proof partitions by k=floor(log_2(max(p,q))). The k-th
block is bounded by

    pi(2^(k+1))^2 / (2^k)^2.

Chebyshev's ordinary upper bound makes this O(1/(k+1)^2), proving
summability. No primality correlation in an irrational strip is used.

Principal result: `summable_pairKernel`.

## Nonlinear proxy at parameter two

Recall

    E_t(n) = sum_{d|n} mu(d) exp(-t log d),
    P_t(n) = exp(-t log n)/(1-E_t(n)) for n>1, otherwise 0.

The earlier `NonlinearPrimeProxy` proved P_t(p)=1 at genuine primes and
summable composite error at t=4.

The new proof establishes summable composite error already at t=2:

    Summable (fun n => if n.Prime then 0 else P_2(n)).

This is over ALL natural inputs, not only the prescribed prime inputs.
The calculation that was previously only investigated informally is now
complete and verified.

### Factor separation

For n>1, put p=minFac(n), m=n/p. The Euler-product defect gives

    P_2(n) <= 1/m^2.

If n is composite and m is prime, p<=m and the assignment n -> (p,m)
is injective into prime pairs. The summable prime-pair kernel controls
this entire case, including prime squares.

If n and m are both nonprime, minimality of p and minFac(m)^2<=m give
p^3<=n. Consequently

    P_2(n) <= n^(-4/3).

This controls every remaining composite by a summable power envelope.
The exceptional n=0,1 terms are zero by definition.

## Actual floor-map consequences

For alpha>=1, let

    w_alpha(n) = P_2(floor(alpha*n)) if n prime, otherwise 0,
    i_alpha(n) = 1 if n and floor(alpha*n) prime, otherwise 0.

The file proves that w_alpha-i_alpha is nonnegative and summable.
Injectivity of floor(alpha*n) also gives the UNIVERSAL finite-set bound

    sum_{n in S} [w_alpha(n)-i_alpha(n)]
      <= sum_{q>=0, q nonprime} P_2(q).

The finite constant is independent of alpha>=1 and of S.

Thus

    Summable(w_alpha)
      iff {p : p prime and floor(alpha*p) prime} is finite.

No nonsummability or positive prime-input lower bound has been proved.

## High-moment limitation remains explicit

At every genuine prime p, the first J terms of the geometric expansion obey

    sum_{j<J} exp(-2 log p) E_2(p)^j <= J/p^2,

while the complete sum is exactly one. Capturing a fixed fraction therefore
still requires moment indices of order p^2. The earlier fixed-moment
means do not supply the needed uniform estimate.

## Main declarations

* `primeProxy_two_le_cofactor`
* `primeProxy_two_three_factor_bound`
* `summable_semiprime_proxy`
* `summable_compositeProxyTwo`
* `summable_primeInputErrorTwo`
* `primeInputErrorTwo_sum_le`
* `prime_truncated_proxy_bound_two`
* `summable_primeProxyWeightTwo_iff_finite`

## Remaining task

A genuine arithmetic lower bound proving divergence of the prime-input
proxy series (or another sufficient prime-pair bound), or an actual
irrational counterexample, is still missing. The new results control
composite error; they do not establish the original conjecture.
