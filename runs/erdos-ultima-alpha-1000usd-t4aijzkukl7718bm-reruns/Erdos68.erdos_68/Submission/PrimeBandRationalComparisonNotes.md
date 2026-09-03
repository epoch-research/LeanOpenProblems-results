# Rational comparison with prime-band-sized tails

Verified auxiliary work, NOT a proof or disproof of Erdos 68.
`Spec.lean` is unchanged with its original `sorry`.

`PrimeBandRationalComparison.lean` compiles without warnings and has a built
olean. It has no proof holes. All five printed principal axiom audits list
only `propext`, `Classical.choice`, and `Quot.sound`.

## Construction

Let

    M_n=product_(p prime, n/2<p<=n) p,
    L_n=lcm(n-1,M_n).

Start t_3=1. At prime n>=4 set t_n=n*t_(n-1)-1. At nonprime n>=4 set

    t_n=1+(n*t_(n-1)-2) mod L_n.

Set c_n=n*t_(n-1)-t_n for n>=4, and c_n=0 below four. The Lean recursion
uses r=n-3 and the modulus zero at prime steps, where Nat.mod x 0=x.

The file verifies all of the following for this DIFFERENT sequence:

* c_n>0 for every n>=4;
* c_p=1 for every prime p>=5;
* n-1 divides c_n-1 for every n>=4;
* M_n divides c_n-1 for every n>=4;
* 1<=t_n<=(n-1)*M_n for every n>=3;
* sum_(n>=0) c_n/n! = 1/6;
* t_n is exactly the factorial-scaled tail of that rational series.

In particular c_4=1, whereas the original Lambert coefficient is 7.
The comparison does not preserve the exact Lambert coefficients or sum.
Nor is it asserted to preserve the minFac-factorial or all the stronger
Lambert congruences.

## Growth and convergence

The elementary prime-band identity

    M_p=p*M_(p-1),  p an odd prime,

is proved by identifying the prime sets. Oddness ensures that no prime
leaves the lower edge when p is added at the upper edge. At a nonprime
step, t_n<=L_n<=(n-1)*M_n. At a prime step, the previous tail bound and the
identity give the same upper bound.

The file also proves M_n<=primorial(n)<=4^n. Hence t_n/n! is summable by
comparison with the exponential power series. The exact identity

    c_n/n! = t_(n-1)/(n-1)!-t_n/n!

telescopes to 1/6. Thus the t_n bounds concern the actual tails, not merely
an unrelated recursively defined integer sequence.

Principal declarations:

* band_at_prime
* tail_upper
* sum_coeff
* scaled_tail_identity
* comparison_properties

## Scope

This supplies a limitation on using the predecessor and prime-band
congruences together with exponential tail bounds: positivity, prime
unit coefficients, both congruences, and even the bound (n-1)*M_n are
compatible with a rational total.

It does not rule out a sharper compatible bound, additional exact
arithmetic structure, or a different argument for the original series.
No such application or complete informal proof of the conjecture was
obtained in this continuation. This file is not an `erdos_68.disproof`.

No numerical search or submission check was run. No computation or
compilation is pending, and Spec.lean remains unproved.
