# Two least DISTINCT prime factors — verified improvement, still no settlement

The original conjecture in Spec.lean remains UNSOLVED. That file is unchanged
and retains its original sorry. No irrational counterexample or sufficient
prime-pair lower bound has been found. No incomplete proof was submitted.

## New compiled files

1. MaskedPrimeSieve.lean
2. TwoLeastPrimeFactors.lean
3. TwoLeastSieveEnvelope.lean
4. TwoLeastFactorMoment.lean
5. PrimeTwoLeastFactorScales.lean

Their principal declarations have been compiled and axiom-audited. The audits
contain only propext, Classical.choice, and Quot.sound.

## Masked Selberg upper bound

For a designated prime p, mask the actual Selberg weights by setting lambda_d
zero whenever p divides d. Write G(R) for the existing sieveMass.

The exact local identities already established in SelbergLocalCost give

    Q_R(mask_p lambda) <= 2/G(R).

Define NoOtherSmallPrime(R,p,n) to mean that every prime q<=R dividing n is p.
This permits arbitrary repetitions of p. The masked divisor sum is exactly
one on such n. For nonnegative input weights a and map g, put

    W_p(R) = sum_{n in S, p|g(n), NoOtherSmallPrime(R,p,g(n))} a(n).

If the actual divisor rows satisfy

    |row(d)-X/d| <= E,  0<d<=p*R^2,

then the new proofs give

    W_p(R) <= 2X/[p G(R)] + E R^2,
    log R W_p(R) <= 4X/p + E R^2 log R,  R>=2.

The error is quadratic in R because the actual Selberg weights have absolute
value at most one. Every modulus p*lcm(d,e) (or its equivalent lcm form)
is within p*R^2. The row errors were not discarded.

## Actual two-least-distinct-factor cost

secondFac(n) is the minimum of primeFactors(n) with minFac(n) erased, or one
when that set is empty. Define

    twoLeastCost(n) = log(minFac(n))*log(secondFac(n)).

It is nonnegative and zero on prime powers (also on 0 and 1). On an integer
with at least two distinct prime factors it is the product of the two least
DISTINCT prime-factor logarithms, not the first two factors with multiplicity.

For every t>0 the verified pointwise comparison is

    S_t(n) <= Lambda(n) + t*twoLeastCost(n).

On prime powers S_t<=Lambda already. On other nonunits, the Euler product
retains the two least factors and bounds all remaining factors by one.

## Geometric layer summation

For R>=2, define the nonnegative envelope

    E(L,R,n) = L^2 * 1_{n coprime R!}
       + L * sum_{p<=R, p prime} log p
                  * 1_{p|n and NoOtherSmallPrime(R,p,n)}.

If secondFac(n)>R and log(secondFac(n))<=L, it majorizes twoLeastCost(n).
The masked upper bound and the elementary estimates

    sum_{p<=R} log p/p <= log R+7,
    sum_{p<=R} log p <= 7R

give, using rows only through R^3,

    sum a(n) E(2log R,R,g(n))
      <= 128X log R +18E R^3 log R.

Use R_j=2^(2^j), Z=R_J. Every nonzero cost is covered by one doubling-log
layer or the terminal envelope. Crucially,

    sum_{j<J} log R_j = log Z-log 2,

so no factor J remains. More generally, for K>=0 and
log(secondFac(g(n)))<=K log Z throughout S, the new finite theorem is

    sum a(n) twoLeastCost(g(n))
      <= (128+2K^2+60K) X log Z
          +(18+K^2+7K) E Z^3 log Z.

The required row range is d<=Z^3. The convenient specialization X<=7N,
E Z^4<=N, K=5000 gives a bound of 10^9 N log Z.

## Application to each irrational slope

The existing direct irrational row scales have N=u^6 and

    Z=layerCutoff(u),  Z^4<=root64(u),
    log(floor(alpha*N)) <=5000 log Z,
    X=psi(N)<=7N,
    E=primeRowError(u)<=N/[16 root64(u)].

These conditions imply the new theorem's entire modulus and error budget.
For every alpha>1 irrational and B, there is u>B, with layerCount(u)>B, such
that

    primeTwoLeastFactorMoment(alpha,u^6) <=10^9 u^6 log(layerCutoff(u)).

At that ONE scale, for ALL t>0 simultaneously,

    mixedPrimeSmooth(t,alpha,u^6)
       -10^9 t u^6 log(layerCutoff(u))
      <=mixedPrimeMangoldt(alpha,u^6).

This is a ONE-SIDED comparison, not a newly proved absolute-error estimate.
It removes the previous log-log loss in the direction useful for positivity.
No lower bound for mixedPrimeSmooth exceeding the new budget is asserted.

## Remaining limitation

The existing rough-output lower envelope behaves as a high power of
 tau=t log(fastRoot(u)) near zero; the new error budget is linear in t.
Removing the log-log factor does not alone make that subtraction positive.
The full signed-correlation / prime-pair lower-bound gap remains unresolved.
The auxiliary upper bound must not be presented as the requested proof or
as a disproof of the original conjecture.
