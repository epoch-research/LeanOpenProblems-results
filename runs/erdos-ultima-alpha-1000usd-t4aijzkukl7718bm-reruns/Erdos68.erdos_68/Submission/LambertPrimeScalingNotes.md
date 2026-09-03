# Prime scaling of the original Lambert coefficients

Auxiliary work only. The original theorem in Spec.lean remains unproved.

Let a_n be the exact original Lambert coefficients. Define

    U(d,k) = (dk)!/(d!)^k,
    A_n = sum_(d|n) U(d,n/d) = a_n+n!   (n>0).

LambertPrimeScaling.lean proves by Lucas's theorem and multinomial
divisibility that for every prime p and positive n,

    U(pd,k) = U(d,k) mod p,
    A_(pn) = A_n mod p,
    a_(pn) = a_n+n! mod p.

In particular a_(2p)=3 mod p. The n! correction must not be omitted
unless p<=n. A_n/n! is not a summable representation: the newly included
divisor one contributes one at each index.

CarriedTwicePrimeCriterion.lean proves that if the target sum is rational
q, then for every prime p>=max(5,q.den) such that 2p-1 is composite,

    p does NOT divide c_(2p)-3,

where c is the actual congruence-preserving carried representation.
Indeed, if r is the last prime below 2p, the rational prime-gap pattern
forces

    c_(2p) = 1+(2p-1)(2r-2p).

A congruence to 3 would imply p divides r+1, whereas p<r+1<2p.

Thus arbitrarily many successful inheritances of a_(2p)=3 mod p at such
primes suffice for irrationality. Dirichlet's theorem supplies arbitrarily
large p=2 mod 3, for which 2p-1 is composite. It does NOT supply successful
congruence inheritance.

The exact transfer condition is now verified:

    p divides c_(2p)-3  iff  p divides h_(2p).

Here h_(2p) is Lean's CongruencePreservingCarry.carry (2*p-3).
This follows from c_(2p)=a_(2p)+h_(2p)-2p*h_(2p-1). It is only a
reformulation: no infinitely-often divisibility of h_(2p) is proved.

There is a verified finite failure: c_10=55, not 3 mod 5. Consequently
inheritance is not automatic. Neither an eventual nor an infinitely-often
inheritance theorem is available.

Both Lean files compile without warnings; the main axiom audits use only
propext, Classical.choice, and Quot.sound. These results do not settle the
conjecture, and no proof or disproof has been submitted.
