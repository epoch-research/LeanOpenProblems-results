# Prime-output gcd determinants — structural progress, not a settlement

Spec.lean remains unchanged with its original sorry. No proof of the
conjecture or irrational counterexample has been found. No incomplete proof
was submitted.

New file: PrimeOutputGcdDeterminant.lean.
Namespace: Erdos972PrimeOutputGcdDeterminant.
All four principal declarations compile and audit with only propext,
Classical.choice, and Quot.sound.

## Exact determinant bounds

For alpha>=0, positive p,q, and

    floor(alpha*p)=d*k,  floor(alpha*q)=d*l,

the floor errors give the strict inequalities

    -q < d*(k*q-l*p) < p.

For alpha>=1, distinct PRIME inputs p,q, and d>alpha, the integer
k*q-l*p cannot be zero. Indeed, a zero determinant and coprimality of p,q
would imply p|k, hence k>=p, and therefore d<=alpha.

It follows that every common output divisor in the nonlocal range satisfies

    d>alpha => d<max(p,q).

This conclusion does not need irrationality. The strict bounds and the
exception d<=alpha are both retained.

## Large divisor rows

For d>=N and d>alpha, there is at most one prime p<=N whose output is
divisible by d. Consequently the actual prime-weight row satisfies exactly

    row(d)^2 = sum_{0<n<=N, d|floor(alpha*n)} primeWeight(n)^2.

For ANY finite block T of divisors with d>=N and d>alpha throughout T,

    sum_{d in T} row(d)^2
      <= (log N)^2 floor(alpha*N) [1+log(floor(alpha*N))].

The proof uses the existing divisor first moment and injectivity of the
Beatty map. This is an unconditional O_alpha(N log^3 N) upper bound for
that large-divisor second moment, not a prime-pair lower bound.

## Unresolved range

The intermediate range of divisors below N still permits nonzero small
determinants. No adequate estimate for their prime-weighted aggregate, or
for the centered off-diagonal dispersion from DivisorRowDispersion.lean,
was obtained. The new uniqueness statement must not be extended to that
range without proof. The universal conjecture remains unresolved.
