# A rational comparison preserving all Lambert coefficient-to-one congruences

This is verified auxiliary work, NOT a proof or disproof of Erdős 68.
Spec.lean is unchanged and still contains its original sorry. No complete
proof or disproof has been obtained or submitted.

## Exact recursive comparison

Let a_n be the original Lambert coefficients

    a_n=sum_(d|n,d>=2) n!/(d!)^(n/d).

Set t_3=1. For n>=4 recursively define natural numbers

    t_n=1+(n*t_(n-1)-2) mod (a_n-1),
    c_n=n*t_(n-1)-t_n,

and put c_n=0 for n<4. The modulo-zero convention is the usual Nat.mod:
x mod 0=x. Thus when a_n=1 the formula gives

    t_n=n*t_(n-1)-1, c_n=1.

The Lean definition tail(r) is t_(r+3); coeffRow(r) is c_(r+4).

## Verified properties

`LambertCongruenceComparison.lean` proves:

* every t_n is a positive integer;
* every c_n for n>=4 is a positive integer;
* c_n=1+(a_n-1)*floor((n*t_(n-1)-2)/(a_n-1));
* a_n-1 divides c_n-1 for every n>=4 (`full_congruence`);
* c_p=1 at every prime p>=5;
* every congruence a_n=1 modulo m passes to c_n=1 modulo m
  (`inherited_congruence`);
* in particular the predecessor, minFac-factorial, and prime-band-product
  congruences all hold for c_n;
* sum_(n>=0) c_n/n! = 1/6;
* the actual factorial-scaled tails of this rational series equal t_n.

The coefficients are genuinely different: c_4=1 whereas a_4=7.

## Convergence and rational sum

At a nonunit index a_n>=2, the modulo formula gives t_n<=a_n. For every
even n>=4, the earlier Lambert lower bound gives a_n>=2. At an odd index,
use t_n<=n*t_(n-1) and the even predecessor. Consequently, for n>=5,

    t_n <= a_n+n*a_(n-1),
    t_n/n! <= a_n/n!+a_(n-1)/(n-1)!.

The two series on the right are summable by the verified Lambert identity.
Thus the normalized tails are summable and tend to zero. Telescoping

    c_n/n! = t_(n-1)/(n-1)!-t_n/n!

then gives t_3/3!=1/6, including the exact finite-prefix and scaled-tail
identities.

## Scope

This comparison preserves all the known coefficient-to-one congruences
simultaneously, not just one smaller modulus. It shows that those congruences,
prime unit values, positivity, and summability alone are insufficient.

It does NOT give small polynomial tail bounds satisfying the existing
irrationality criteria. It does NOT preserve the exact original coefficient
formula, the original sum, or the original pole structure. It cannot be used
as a disproof of the conjecture. A successful application still needs a
compatible stronger analytic bound or additional exact arithmetic structure.

The file compiles without warnings, has a built olean, contains no proof
holes, and all printed principal axiom audits list only propext,
Classical.choice, and Quot.sound. No external computation is trusted.
