# Sharper Selberg weights and a logarithmic-order almost-prime lower bound

The original conjecture is STILL UNSOLVED. Spec.lean is unchanged and retains
its original sorry. No prime-output lower bound or irrational counterexample
has been obtained, and no proof has been submitted.

## SelbergUnitWeights.lean

For the actual optimal finite weights from SelbergWeights.lean:

    |selbergWeight(R,d)| <= 1,  R>=1, all d.

This replaces the earlier coarse bound <=d. The proof establishes the exact
formula, for d>0,

    lambda_d = mu(d) * d/phi(d) * H(R/d,d) / G(R),
    H(X,d) = sum_{r<=X, gcd(r,d)=1} mu(r)^2/phi(r).

For squarefree d, an injective map (e,r) -> e*r, over e|d and the coprime
r<=R/d, gives

    [d/phi(d)] H(R/d,d) <= G(R).

Non-squarefree d have lambda_d=0. This proves the unit bound for the actual
weights, not a substituted set of coefficients.

## SelbergMajorantSize.lean

Two consequences:

- The full quadratic coefficient mass is <=R^2 instead of R^4.
- If n>0 and Omega(n)<=K, the actual squared Selberg divisor sum satisfies

      majorant(R,n) <= majorantCap(K) = (2^K)^2,

  independently of R. Only squarefree divisors contribute. Their prime-factor
  sets inject into the powerset of the prime factors of n.

## CappedLowerSieve.lean

Retains the lower-supported test (1-omega_Z)*majorant_R but treats its cap
on rough outputs separately from its coefficient mass.

For nonnegative source weights a(n), output map g, and divisor row error E
for every 0<d<=R^2 Z, if majorant(R,g(n))<=C on Z-rough outputs, then

    X*lowerMain(R,Z) - E*(Z+1)*R^2
      <= C * sum_{Z-rough outputs} a(n).

The full row-error contribution is retained. If

    R>=1, Z>=1, R^3 Z<=v, C>0,
    X>=N/2, lowerMain>=1/[2G(R)], E<=N/(16v),

then the rough weight is at least

    N/[8 C G(R)] >= N/[24 C (1+log(R+1))].

The elementary bound G(R)<=3(1+log(R+1)) follows by applying the existing
multiplicative-interval estimate with p=R+1.

## PrimeRoughLogLower.lean

The existing actual prime-input rows, with their proper-prime-power error,
now supply the capped lower theorem. The same roughness root is retained:

    Z=roughRoot(u),  Z^524288<=u,
    R=Z^1024, N=u^6.

At the selected good scales, Z>=2 and alpha<=Z. Thus every positive Z-rough
output up to floor(alpha*u^6) has at most

    K = 6291457

prime factors, with multiplicity. The cap majorantCap(K) is therefore a
FIXED constant, not a power of R or N.

Let roughConstant=24*majorantCap(K). For every irrational alpha>1 and B,
`exists_prime_rough_log_scale` gives u>B, Z>B and

    weighted prime-input / Z-rough-output count
      >= u^6/[roughConstant*(1+log(u+1))].

The corresponding actual cardinality is at least

    u^6/[6*roughConstant*(1+log(u+1))^2].

Finally, `frequently_many_prime_almostPrime_pairs` verifies the scale-free
formulation: there exists c>0 such that for every B there exists N>B with

    #{p<=N : p prime and Omega(floor(alpha*p))<=6291457}
      >= c*N/[1+log(N+1)]^2.

The proof uses c=1/[6*roughConstant], independent of alpha; scales can depend
on alpha. No assertion is made that this lower bound holds at every N.

## Remaining gap and audit

The factor bound K has NOT been reduced to one. This is a substantive
quantitative improvement to the almost-prime theorem, not a proof of prime
output. The original two-prime / signed four-factor lower gap is unchanged.

All four development files and AuditCappedSieve.lean compile. The audit checks
thirteen declarations; each depends only on propext, Classical.choice, and
Quot.sound. There are no sorry declarations or new axioms in these files.
Spec.lean and its sole import have not been modified.

Implementation note: avoid running unrestricted arithmetic tactics on the
let-bound R=Z^1024 or unfolding majorantCap(6291457). Keep R abstract after
recording its bounds and use explicit positivity lemmas for the fixed cap.

## Smaller factor bound now available

See ProgressEfficientSieve.md. The elementary bound sum_{d<=N} Lambda(d)/d
<=log N+7 reduces the required sieve power to R=Z^16 eventually. With
Z=root64(root64 u), the capped budget fits, and the same logarithmic-order
counting theorem and explicit infinitude theorem now hold with output
factor bound 49153. The original prime-output conjecture remains unresolved.
