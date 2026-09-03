# Least-factor smoothing comparison — original conjecture still unresolved

`Spec.lean` is unchanged and retains its original `sorry`. No prime-pair lower
bound or irrational counterexample has been found. No proof was submitted.

## New verified results

### LeastFactorSmoothMangoldt.lean
Namespace `Erdos972LeastFactorSmoothMangoldt`.

For all t>0 and all natural n:

    |S(t,n)-Lambda(n)| <= t log(n) log(minFac(n)).

This refines the prior t log(n)^2 pointwise bound. Prime powers use the
one-factor exponential error; other positive nonunits use the least prime
factor and a distinct second prime factor in the Euler product. The zero
and unit conventions are included.

For nonnegative finite source weights a and outputs g with log(g(n))<=L:

    |sum a(n) S(t,g(n)) - sum a(n) Lambda(g(n))|
      <= t L sum a(n) log(minFac(g(n))).

### LeastFactorSieve.lean
Namespace `Erdos972LeastFactorSieve`.

The actual optimal Selberg weights give, from divisor rows with error E
through R^2,

    roughWeight(R) <= X/G(R) + E R^2,
    log(R) roughWeight(R) <= 2X + E R^2 log(R), R>=2.

Define logLevel(j)=2^(2^j). A finite layer decomposition bounds the weighted
least-factor logarithm using rough-output weights at these cutoffs and an
explicit final tail. With Z=logLevel(J), the resulting budget is

    log(2)(X+E) + 4XJ + 2XL/log(Z)
      + E Z^2 [2J log(Z)+L].

The row requirement is only d<=Z^2. The tail L is retained, not discarded.
If X<=7N, E Z^4<=N, and L<=5000 log(Z), this budget is at most
100000 N (J+1).

### LeastFactorCutoff.lean
Namespace `Erdos972LeastFactorCutoff`.

    v=root64(u)
    W=sqrt(sqrt(v))
    J=layerCount(u)=Nat.log 2 (Nat.log 2 W)
    Z=layerCutoff(u)=2^(2^J).

For W>=2, rounding is proved exactly:

    Z<=W<Z^2,
    Z^4<=v,
    u<=Z^832.

If alpha<=Z and n<=u^6, floor(alpha*n)<=Z^4993. Also J tends to infinity,
and for every u,

    J <= 2+2 log(1+log u).

### PrimeLeastFactorScales.lean
Namespace `Erdos972PrimeLeastFactorScales`.

Let primeWeight(n)=log n if n is prime, and zero otherwise. The existing
actual prime-input rows at direct rational-approximation good scales give,
for every irrational alpha>1 and every B, some u>B with J(u)>B and

    sum_{n<=u^6} primeWeight(n) log(minFac(floor(alpha*n)))
      <= 100000 u^6 (J(u)+1).

All proper-prime-power row errors are included. The proof uses the actual
available error E<=u^6/[16 root64(u)], not a new distribution assumption.
Thus the least-factor moment on prime inputs has an O(N log log N) upper
bound on these selected scales.

Define the MIXED sums

    mixedPrimeSmooth(t,alpha,N)
      = sum_{n<=N} primeWeight(n) S(t,floor(alpha*n)),
    mixedPrimeMangoldt(alpha,N)
      = sum_{n<=N} primeWeight(n) Lambda(floor(alpha*n)),

and the parameter

    layerParameter(alpha,u)
      = 1 / ([1+log(floor(alpha*u^6))] [J(u)+1]^2).

At any scale with the preceding least-factor moment bound,

    |mixedPrimeSmooth(layerParameter,alpha,u^6)
      - mixedPrimeMangoldt(alpha,u^6)|
      <= 100000 u^6/[J(u)+1].

`exists_layerParameter_small_error` supplies arbitrarily small normalized
mixed-comparison error at arbitrarily large selected scales.

Finally,

    primeCorrelation <= mixedPrimeMangoldt <= mangoldtCorrelation,

so the already proved proper-prime-power error tends to zero after dividing
by N. `exists_layerParameter_prime_comparison` therefore gives, for every
epsilon>0 and B, some u>B and J(u)>B with

    |mixedPrimeSmooth(layerParameter,alpha,u^6)
      - primeCorrelation(alpha,u^6)| <= epsilon*u^6.

The last sum counts genuine prime input/output pairs, with logarithmic
weights. No prime-pair lower bound is assumed in these comparison results.

## What is still missing

This is a MIXED prime--smooth comparison, not an upgraded all-N mean theorem
for the earlier smooth--smooth correlation. No positive lower bound for the
mixed sum at layerParameter was established. The existing fixed-positive-t
smooth--smooth formulas do not provide such a bound, and no limit exchange
is justified by the new comparison.

The new parameter still has t log(N) tending to zero. Thus the elementary
long-divisor damping mechanism does not become effective simply by using
this larger comparison parameter. This observation concerns that mechanism,
not a proof that stronger signed-tail estimates are impossible.

A sufficient signed correlation estimate or a genuine irrational
counterexample is still needed to settle Spec.lean.

## Verification

All four new development files compile. AuditLeastFactorComparison.lean
audits twelve principal declarations; they use only propext,
Classical.choice, and Quot.sound. No new axioms or sorry declarations were
added to these files, and Spec.lean was not changed.
