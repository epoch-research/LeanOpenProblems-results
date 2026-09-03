# Narrow top-of-base digits: verified obstruction

## Original problem remains unresolved

This is NOT a disproof of Erdős 773. Spec.lean has not been edited. Its sole
admission still covers 0 < epsilon <= 1/3. No actual lower exponent or upper
exponent for the original maximum has improved. The strongest established
actual lower bound remains eventual M(N) >= N^(2/3)/36.

An earlier incomplete submission was rejected. No incomplete proof has been
resubmitted in this continuation.

## New clean module

Submission/NarrowDigitCollision.lean imports only FormalConjecturesUtil.
It builds without warnings or admissions. Its seven printed axiom audits use
only propext, Classical.choice, and Quot.sound.

Namespace: Erdos773.NarrowDigitCollision
Principal API: arbitrarily_narrow

For every real delta > 0 and natural lower base bound L, this theorem supplies
an explicit parameter t, with base B > L, and four 16-digit words such that:

* every digit is positive and lies in [(1-delta) B, B);
* all four leading digits and all four constant digits equal (t+3)^2;
* the four words have identical complete digit histograms;
* their evaluated natural roots are positive and pairwise distinct;
* their square values have a nontrivial equal-pair-sum relation.

Thus restricting every position to an arbitrarily narrow relative band near
the top of the base does not suffice, even with fixed end digits and a common
histogram. This is a failure of a proposed sufficient digit condition, not a
bound on the largest Sidon subclass of these words or of all squares.

## Exact parameters and digit table

Write k=t+3. The base is

    B=t^2+9t+20=(k+1)(k+2).

The six digit labels 0,...,5 stand for

    k^2, k^2-k, k^2+k, k^2-2k-1, k^2+2k-1, k^2+1.

The four words, constant coefficient first, are

    [0,1,2,0,1,3,5,1,2,5,4,2,0,1,2,0]
    [0,2,1,0,2,4,5,2,1,5,3,1,0,2,1,0]
    [0,2,1,0,1,5,3,1,2,4,5,2,0,2,1,0]
    [0,1,2,0,2,5,4,2,1,3,5,1,0,1,2,0].

The Lean definitions expand the six digits as nonnegative natural
polynomials in t, avoiding truncated-subtraction assumptions.

Every digit is at least B-(5t+18) and less than B. The sufficient quantitative
condition for the relative band is 10/delta <= t+3. The common digit sum is
16k^2, and the common squared-digit sum is 4(2k^2+1)^2.

## Algebraic source

Let

    A=k(1+X+X^2+X^3),   B0=X-X^2,
    C=k(1+X^4+X^8+X^12), D=X^4-X^8.

The four root polynomials are

    AC-B0*D-A*D-B0*C,
    AC-B0*D+A*D+B0*C,
    AC+B0*D-A*D+B0*C,
    AC+B0*D+A*D-B0*C.

Comparing (1+i)(A+iB0)(C+iD) and (1+i)(A-iB0)(C+iD) gives the
square-sum identity. The Lean collision theorem directly checks the expanded
identity with ring for every natural evaluation base, not merely the chosen
base. This is a formal polynomial identity, not a carry-only collision.

The common histogram comes from swapping positions 1 and 2 within each block,
and swapping blocks 1 and 2. Injectivity of the actual evaluations is proved
using canonical-digit injectivity and the distinguishing digits at positions
1 and 4. No numerical search is trusted.

## Explicit limitations

* The bases are composite; no prime-base assertion is made.
* The leading coefficient is k^2, not one.
* These are NOT Gaussian-Eisenstein admissible words. There is no
  contradiction with FormalGaussianSidon.formal_sidon.
* The common digit energy is a square, not prime.
* No primitive-gcd, pairwise-coprimality, or positional-moment assertion is made.
* A bad family does not show every large class or every base is bad.

## Verification

Build/axiom log: /tmp/narrow-digit-collision.log
Olean: .lake/build/lib/lean/Submission/NarrowDigitCollision.olean

Main-file SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.

No proof or disproof of the original conjecture is supplied by this module.
