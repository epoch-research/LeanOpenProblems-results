# Checkpoint: completed polynomial-roughness / almost-prime lower theorem

The original conjecture is STILL UNSOLVED. Spec.lean is unchanged and still
contains the original sorry. The following is a genuine unconditional lower
bound and an almost-prime weakening, NOT a prime-pair proof or a disproof.
Do not submit the auxiliary theorem as the original conjecture.

## Main completed results

PrimeRoughOutputs.lean, namespace Erdos972PrimeRoughOutputs:

    roughRoot u = sqrt(root64(root64(root64 u))).
    k <= roughRoot u  iff  k^524288 <= u.

For every alpha>1 irrational and every B, there exists u>B with
Z=roughRoot u>B such that

    sum_{0<p<=u^6, p prime, gcd(floor(alpha*p),Z!)=1} log p
        >= u^6/(8*root64 u).

The theorem is `exists_prime_rough_output_scale`. Unlike the earlier growing
coprime-modulus theorem, the FACTORIAL Z! is not required to fit below the
divisor level. Instead, a lower-supported Selberg test with individual
moduli bounded by R^2 Z is used. Thus Z itself grows as a fixed power of u,
rather than only logarithmically.

PrimeAlmostPrime.lean, namespace Erdos972PrimeAlmostPrime:

    exists_prime_almost_prime_beyond
    infinite_prime_almost_prime_inputs

For every alpha>1 irrational:

    {p : Nat | p.Prime and
      (floorMul alpha p).primeFactorsList.length <= 6291457}.Infinite.

The length counts prime factors WITH MULTIPLICITY. The bound is intentionally
very loose. It is not a prime-output theorem.

## New sieve infrastructure

### SelbergLocalCost.lean
Namespace Erdos972SelbergLocalCost.

    sieveAtom n = mu(n)^2 / phi(n)
    coprimeMass R p = sum_{0<r<=R, p not dividing r} sieveAtom(r)
    localMain R p = sum_{d,e<=R} lambda_d lambda_e / lcm(d,e,p),

where lambda are the actual `selbergWeight R` from SelbergWeights.lean.

`localMain_exact` proves, for p prime and R>=1:

    localMain R p =
      [coprimeMass R p - coprimeMass floor(R/p) p] / [p G(R)^2],

where G(R)=sieveMass R. This is an exact identity.

The proof uses the complementary quadratic form (masking divisors divisible
by p), upper Mobius inversion, and

    G(R)=G_p(R)+G_p(floor(R/p))/(p-1).

### SieveMassUpper.lean
Namespace Erdos972SieveMassUpper.

- `sieveAtom_le_divisors`:

      sieveAtom(n) <= (1/n) sum_{d|n} sieveAtom(d),  n>0.

- `sum_sieveAtom_div_le_three`:

      sum_{n<=R} sieveAtom(n)/n <= 3.

The latter follows from a finite Euler product, bounded by
exp(sum_{p<=R}1/[p(p-1)]) <= exp(1) < 3. All finite divisor/support issues
are proved, including squarefree support.

### SieveMassInterval.lean
Namespace Erdos972SieveMassInterval.

- A reciprocal interval bound H_b-H_floor(b/p) <= 1+log p.
- `sieveAtom_Ioc_bound`:

      sum_{R/p<n<=R} sieveAtom(n) <= 3(1+log p).

- `localMain_upper`:

      localMain R p <= 3(1+log p)/(p G(R)^2).

### SelbergLowerMain.lean
Namespace Erdos972SelbergLowerMain.

    smallPrimes Z = primes <= Z
    lowerMain R Z = 1/G(R) - sum_{p<=Z} localMain R p.

Elementary Chebyshev partial summation gives

    sum_{n<=Z} Lambda(n)/n <= 14(1+log Z),
    sum_{p<=Z}(1+log p)/p <= 42(1+log Z).

Consequently, if G(R)>=252(1+log Z), then

    lowerMain R Z >= 1/(2G(R)).

With the existing G(R)>=0.5 log(R+1), R=Z^1024 suffices for Z>=1,
log Z>=1. This is `lowerMain_power_positive`.

### SelbergLowerTest.lean
Namespace Erdos972SelbergLowerTest.

    nu_R(n) = majorant R n
    omega_Z(n) = number of distinct prime divisors of n at most Z
    lowerTest R Z n = (1-omega_Z(n))*nu_R(n).

Important: this test is NOT asserted to be <=1 on rough n. It is <=0 on
nonrough n and <=R^4 on rough n. This is sufficient for the weighted lower
bound, with the factor R^4 retained.

For an arbitrary finite source S, nonnegative weights a, output map g, and
row approximation

    |sum_{n in S, d|g(n)}a(n) - X/d| <= E

for every 0<d<=R^2 Z, the theorem `rough_weight_lower` proves

    X*lowerMain R Z - E*(Z+1)*R^4
      <= R^4 * sum_{n in S, gcd(g(n),Z!)=1}a(n).

The coefficient-mass error is fully retained; no prime output is assumed.

The finite positive version `rough_weight_positive_bound` assumes

    R>=1, Z>=1, R^5 Z<=v, X>=N/2,
    lowerMain R Z>=1/(2G(R)), E<=N/(16v),

and obtains

    sum_{rough outputs} a(n) >= N/(8R^5).

The simple upper bound G(R)<=R is proved and used here.

## Application to genuine prime inputs

PrimeRoughOutputs.lean:
- `primeWeight n = if n.Prime then log n else 0`.
- The actual prime-input divisor rows differ from the Lambda-input rows by
  at most psi(N)-theta(N). This error is proved explicitly, not omitted.
- Existing sixth-scale estimates show

      root64(u) * [scaledRowError(1,u,root64 u) + psi(u^6)-theta(u^6)] / u^6
          -> 0.

- Good rational approximants to alpha supply all the required input rows at
  the same u, by `input_divisor_row_discrepancy` with K=1.
- Z=roughRoot u, R=Z^1024 satisfy R^5 Z=Z^5121<=root64 u, since
  Z^8192<=root64 u.
- The positive lower theorem then gives N/(8R^5)>=N/(8root64 u).

PrimeAlmostPrime.lean:
- The weighted bound is unbounded and exceeds the total weight of all prime
  inputs <=B, which is <=7B, so it produces inputs beyond every B.
- For Z>=2, u<=Z^1048576, hence u^6<=Z^6291456.
- Eventually alpha<=Z, so floor(alpha*p)<=Z^6291457 for p<=u^6.
- Every prime factor of a Z-rough output exceeds Z. Taking the product of
  its prime-factor list proves length<=6291457.

## Remaining obstruction to the original problem

Roughness up to this small power does NOT imply primality. The proved
almost-prime bound 6291457 cannot be substituted for 1. The argument uses
R=Z^1024 and needs divisor moduli up to R^2 Z; setting Z near sqrt(N) would
violate the available row range by a large margin. No such extension is
asserted.

The earlier centered four-factor gap remains unproved. No new signed
prime-pair lower bound, irrational counterexample, or completed final
conjecture declaration has been obtained.

All principal declarations compile and audit with only propext,
Classical.choice, Quot.sound. Audit: AuditLowerSieve.lean.

Lean performance note: positivity/nlinarith on a let-bound R=Z^1024 can
spend millions of heartbeats unfolding huge powers. Clearing the let-value
after recording the needed hypotheses, or using a separate abstract numeric
lemma with explicit positivity arguments, avoids that problem. Do not solve
it by allowing sorry or an unverified axiom.

## Verified cutoff check

`LowerSieveCutoff.lean` now compiles against the compiled `SieveBarrier.olean`.
Its printed axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`.

- `available_level_below_primality`: if alpha>=1, u>=2, R>=1 and
  R^2 Z <= root64(u), then (Z+1)^2 <= floor(alpha*u^6).
- `not_available_square_root_sieve`: the strict size hypothesis for the
  current elementary primality certificate is therefore incompatible with
  that modulus range at the full sixth-power endpoint.
- `scaledRowError_ge_level`: for 1<=v<=u, the current absolute row-error
  expression is at least v.
- `square_prefix_exceeds_error_budget`: if also X<=v^2, that expression
  cannot be <= X/(16v). Uniformity over prefixes does not make this
  absolute error relative to the shorter prefix.

These are limitations of the specific proved estimates, not limitations of
all sieve methods, and not a disproof of Erdos 972. The final Spec.lean is
unchanged and the conjecture remains unresolved.

## Quantitative improvement: fixed cap instead of a power loss

See ProgressCappedSieve.md and AuditCappedSieve.lean. The actual Selberg
weights now satisfy |lambda_d|<=1. Their majorant is bounded by a fixed
constant on outputs with at most 6291457 factors. Applying the resulting
capped lower sieve to the same actual prime rows upgrades the almost-prime
count to c*N/[1+log(N+1)]^2 at arbitrarily large scales, with c>0 fixed.
The output factor bound is unchanged; this is still not prime output and
Spec.lean remains unresolved.
