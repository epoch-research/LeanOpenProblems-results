# Rational comparison preserving nonunit prime-square residues

Verified auxiliary work, NOT a proof or disproof of Erdős 68. The theorem in
`Submission/Spec.lean` is unchanged and still contains its original `sorry`.
No proof or disproof has been submitted.

`PolynomialModulusRational.lean` compiles without warnings, has a built olean,
and its five printed principal axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Exact construction

Let a_n be the original Lambert coefficients. Put t_3=27. For n>=4 define

    t_n = n*t_(n-1)-1                         if n is prime,
    t_n = 3*n^2 + (n*t_(n-1)-a_n-3*n^2)
                    mod (n^2*(n-1))          otherwise.

The modulus and remainder are integers, with the usual nonnegative remainder
for a positive modulus. Define c_n=0 for n<4 and

    c_n=n*t_(n-1)-t_n                         for n>=4.

The Lean index `tail r` represents t_(r+3).

## Verified properties

* t_n>=3*n^2 for every n>=3.
* At nonprime n>=4, t_n<n^2*(n+2).
* At every n>=3, t_n<n^4.
* c_n>0 for every n>=4; earlier coefficients are zero.
* c_p=1 for every prime p>=5.
* n^2*(n-1) divides c_n-a_n for every n>=4.
* In particular, n-1 divides c_n-1.
* For every odd prime p, p^2 divides c_(2p)-3.
* sum_(n>=0) c_n/n! = 9/2.
* The actual factorial-scaled tails of this rational series equal t_n.
* The coefficients are different from the target's: c_4=55, a_4=7.

The sum follows from telescoping and summability of n^4/n!. Positivity at
composite indices follows from

    n*t_(n-1)-t_n
      > 3*n*(n-1)^2 - n^2*(n+2)
      = 2*n^2*(n-4)+3*n > 0.

At a prime p>=5, its predecessor is nonprime, so the nonprime cubic bound
at p-1 gives the stated quartic bound at p. The square congruence uses the
existing verified original identity a_(2p)=3 mod p^2 and the new full
coefficient congruence, not an assumption about carrying.

## Scope and remaining gap

The earlier `LambertCongruenceComparison` preserved congruences of the form
'a_n equals one modulo m'. It did not automatically preserve the nonunit
residue a_(2p)=3 modulo p^2. The present construction preserves that residue
and keeps polynomially bounded tails, but with a larger bound than the
actual small-tail carry: cubic at composites and quartic overall.

Thus adding the prime-square residue while merely allowing a quartic tail
bound does not force irrationality. The existing criterion requiring much
smaller tails is not contradicted. This result does not assert that every
polynomial tail bound is insufficient, or that the exact original coefficient
formula can be replaced by the comparison. It is not a disproof of the
conjecture.

A linear-modulus variant was considered informally during development; the
file verifies the stronger n^2*(n-1) modulus and quartic-tail construction
above. No separate cubic-tail comparison is claimed as Lean-verified here.

No compatible sharper bound, infinite carry-congruence inheritance theorem,
or other complete argument for the original sum was obtained in this pass.
