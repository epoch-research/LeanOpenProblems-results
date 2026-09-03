# A stronger factorial-tail criterion (verified auxiliary work)

`SubquadraticTailCriterion.lean` compiles and its olean has been built. The
three main axiom audits list only `propext`, `Classical.choice`, and
`Quot.sound`. This file does NOT settle Erdős 68.

## Close prime pairs

`prime_predecessor_pairs_square` proves, for every natural C,M, that there
are naturals a>=M and L>0 such that

    (C+1)*(L+1)^2 < a,
    a+1 and a+L+1 are prime.

The argument uses divergence of the sum of prime reciprocals. If such
pairs were absent beyond M, then for consecutive primes p<q beyond M,

    p-1 <= (C+1)*(q-p+1)^2.

Writing D=C+1, B=5D, J=4D+M+2, and P_i for the i-th prime, induction gives

    P_(J+B*n) >= D*(n+2)^2+M+1.

Indeed, once a prime reaches this lower bound, each subsequent prime gap
is at least n+1. A block of B gaps then gives the next quadratic bound.
The reciprocal-prime series along each residue class modulo B is bounded,
after a finite shift, by the convergent series sum 1/(n+2)^2. Combining
these classes contradicts divergence of prime reciprocals.

## Local irrationality criterion

`irrational_of_local_tails_and_unit_pairs` packages the previously verified
`UnitTailSeparation.no_close_unit_returns`. For integer factorial
coefficients c_n with eventual n | c_(n+1)-1, it suffices to have arbitrarily
large intervals with

    c_(a+1)=c_(a+L+1)=1,
    0 <= T_(a+i) <= H       for i<=L+1,
    a*L + (L+1)*H + 1 < a^2,

where T_n is the factorial-scaled tail. H can depend on the interval.
Under rationality, clearing the fixed rational denominator makes these
tails integers. Their recurrence and congruence then contradict the local
separation lemma.

## Explicit larger-than-linear bound

`irrational_of_sqrt_tails_prime_coefficients` proves irrationality assuming,
for all sufficiently large n,

    n | c_(n+1)-1,
    0 <= T_n <= C*n*(floor(sqrt(n))+1),

and c_p=1 at every sufficiently large prime p.

Choose the prime pair with squared-gap constant (16*(C+1))^2. For
s=floor(sqrt(a)), this ensures

    16*(C+1)*(L+1) <= s.

On the interval i<=L+1 one has a+i<=2a and
floor(sqrt(a+i))+1<=4s. Hence H=8*C*a*s bounds all the tails there.
The helper `local_sqrt_bounds` verifies

    16*a*L <= a^2,
    16*(L+1)*H <= 8*a^2,
    a*L+(L+1)*H+1 < a^2.

This proves the explicit criterion, extending the older fixed linear bound
without invoking a quantitative prime number theorem.

## Application gap remains

The original Lambert representation has the required congruences and prime
coefficients. Its scaled tails are too large: the already verified
`MovingLambertTailBarrier.moving_lambert_tail_ge_square` (in namespace
`Erdos68Development`) gives T_n^(K)>=n^2 for n>=18 and K<=floor(n/2)+1.
For every fixed C and fixed row cutoff K this eventually exceeds
C*n*(floor(sqrt(n))+1). Thus the new criterion does not apply directly to
those representations.

The rowwise floor representation has sufficiently small tails, but no
proof supplies its eventual predecessor congruences and prime-unit values.
Finite failures already prevent assuming these properties at all indices;
no assertion about their eventual truth or falsity is made here.

`Submission/Spec.lean` is unchanged with its original `sorry`. No complete
proof or disproof of the conjecture has been submitted.
