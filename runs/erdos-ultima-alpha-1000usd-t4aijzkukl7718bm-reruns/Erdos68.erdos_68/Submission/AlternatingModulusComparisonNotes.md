# Quadratic rational comparison with least-prime-factor congruences

This is verified auxiliary work, NOT a proof or disproof of Erdős 68.
`Submission/Spec.lean` is unchanged and retains its original `sorry`.
No proof or disproof has been submitted.

`AlternatingModulusComparison.lean` compiles without warnings, has a built
olean, and all four printed principal axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Construction

For the original Lambert coefficients a_n, set

    m_n=2*(n-1)       when n is even,
    m_n=a_n-1        when n is odd.

Starting with t_3=1, define for n>=4

    t_n=1+(n*t_(n-1)-2) mod m_n,
    c_n=n*t_(n-1)-t_n.

The remainder and subtraction in the definition are natural-number
operations. The proof establishes n*t_(n-1)>=4, so the subtractions used
in the coefficient identities have their intended values. Modulo zero
has Lean's usual convention; in particular at odd primes a_p=1, m_p=0,
and c_p=1. Put c_n=0 for n<4.

## Verified properties

* t_n>0 and c_n>0 for n>=4.
* For even n>=4, t_n<=2*(n-1).
* For every n>=3, t_n<2*n^2.
* c_p=1 for all primes p>=5.
* c_n=1 modulo n-1 for all n>=4.
* c_n=1 modulo (minFac n)! for all n>=4.
* At every odd n>=5, a_n-1 divides c_n-1. Thus every original
  coefficient-to-one congruence passes to c_n at odd indices.
* sum_(n>=0) c_n/n! = 1/6.
* The actual factorial-scaled tails of this rational series are t_n.
* c_4=1 whereas a_4=7, so these are not the original coefficients.

The quadratic bound does not require an upper bound on odd-index moduli.
At an even index the remainder bounds the tail by its linear modulus.
At the following odd index, t_n<=n*t_(n-1)-1, giving the quadratic bound.
Summability of 2*n^2/n! and telescoping give the rational total.

## Scope

Adding the least-prime-factor factorial congruence to positivity, prime
units, predecessor congruences, and an O(n^2) tail bound does not suffice
for irrationality. The comparison does NOT preserve every prime-band
congruence at even indices, or the exact original coefficient formula.
It also does not satisfy the original carry's sharper bound t_n<n at all
composites. No claim excluding stronger criteria is made.

The older explicit `QuadraticTailComparison` also has unit coefficients
at odd indices and odd coefficients at even indices. Thus the general
warning about the least-prime-factor modulus should not be presented as
a new settlement-level phenomenon. This file verifies a recursive version
and explicitly records the full odd-index inheritance and its tail bounds.

Review of the exact carry and the combined column modulus did not produce
an infinite nonvanishing statement or a complete argument for the target.
The original conjecture remains unresolved in this workspace.
