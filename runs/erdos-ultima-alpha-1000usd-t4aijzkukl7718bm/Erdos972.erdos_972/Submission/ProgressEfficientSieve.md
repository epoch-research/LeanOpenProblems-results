# Improved almost-prime output bound: 49153 factors

The original conjecture is STILL UNSOLVED. Spec.lean is unchanged and retains
its original sorry. No prime-output lower bound or irrational counterexample
has been proved, and no incomplete proof has been submitted.

## SharpReciprocalPrimeCost.lean

An elementary identity and Chebyshev's bound sharpen the accumulated prime
cost. No quantitative PNT rate is used; the argument does not need qualitative
PNT either.

`mangoldt_floor_sum`:

    sum_{d<=N} Lambda(d)*floor(N/d) = logMass(N).

The fractional-part error is at most psi(N)<=7N, while logMass(N)<=N log N.
Consequently `reciprocal_mangoldt_log_upper` proves the uniform estimate

    sum_{d<=N} Lambda(d)/d <= log N + 7.

With primeCost(Z)=sum_{prime p<=Z}(1+log p)/p, splitting off a fixed finite
initial segment gives

    primeCost(Z) <= (9/8) log Z + 63/8 + harmonic(P)

whenever log P>=8. Thus `eventually_primeCost_upper` gives, for all sufficiently
large Z,

    primeCost(Z) <= (5/4) log Z.

The existing exact local-cost bound then gives

    sum_{p<=Z} localMain(R,p) <= 3*primeCost(Z)/G(R)^2.

Since G(Z^16)>=8 log Z, `eventually_lowerMain_sixteen` proves

    lowerMain(Z^16,Z) >= 1/[2G(Z^16)]

at every sufficiently large Z. This replaces the previous choice Z^1024.

## EfficientSieveScale.lean

Define

    fastRoot(u)=root64(root64(u)).

Then Z<=fastRoot(u) iff Z^4096<=u. For Z=fastRoot(u), R=Z^16,

    R^3 Z = Z^49 <= Z^64 <= root64(u).

This fits the new capped lower-sieve coefficient budget. It is important that
this uses R^3 Z, not the old R^5 Z budget.

For Z>=2, u<=Z^8192. Hence, if alpha<=Z and p<=u^6,

    floor(alpha*p) <= Z^49153.

Together with Z-roughness, the existing factor-list argument bounds the
number of output prime factors, WITH MULTIPLICITY, by 49153.

## EfficientPrimeAlmostPrime.lean

Uses the actual prime-input rows at good direct-approximation scales, including
the proper-prime-power row error. The prime rows themselves have not been
extended beyond the already proved range.

All the logarithmic-order lower results from PrimeRoughLogLower.lean now hold
with the larger fastRoot and the smaller factor bound K=49153. The fixed cap is

    majorantCap(K)=(2^K)^2,
    roughConstant=24*majorantCap(K).

At arbitrarily large selected scales N=u^6:

    weighted prime-input / fastRoot-rough-output count
      >= u^6/[roughConstant*(1+log(u+1))],

and the actual cardinality is at least

    u^6/[6*roughConstant*(1+log(u+1))^2].

`frequently_many_prime_almostPrime_pairs` proves the scale-free statement:
there exists c>0 such that for every B there exists N>B with

    #{p<=N : p prime and Omega(floor(alpha*p))<=49153}
      >= c*N/[1+log(N+1)]^2.

The explicit constant is c=1/[6*roughConstant], independent of alpha. The scales
may depend on alpha. This is not a claim for every sufficiently large N.

`exists_prime_almostPrime_beyond` and `infinite_prime_almostPrime_inputs`
explicitly prove infinitude with the new factor bound. Their unboundedness
argument uses the elementary estimate

    u/(2C) <= u^6/[C*(1+log(u+1))],  u>=1, C>0,

rather than introducing any additional asymptotic estimate.

## Remaining gap and verification

K=49153 is NOT one. The sifting radius is still a small power of the input
scale and does not certify prime output. No strict signed four-factor lower
gap or other prime-pair lower bound has been obtained.

All three new development files compile, as does AuditEfficientSieve.lean.
Its ten audited declarations depend only on propext, Classical.choice,
and Quot.sound. There are no sorry declarations or added axioms in these
files. Spec.lean and its import are untouched.

Development pitfall: when changing the sieve exponent, also change the
explicit exponent passed to Nat.one_le_pow. A stale 1024 argument against
R=Z^16 can cause a very expensive failed definitional-equality check.
