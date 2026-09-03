# A positivity ansatz for the polynomial kernels (unresolved)

These are mathematical research notes, NOT a new Lean theorem and NOT a
solution of Erdős 68. No complete construction with small errors has been
obtained.

The previously verified index-dependent kernel identity uses

    q_j(n) = n^j H_j(n-1)-H_j(n),
    P(n,t) = A-(1-t)*sum_(j=1)^J q_j(n)*t^(j-1),

and yields

    sum_(n>=2) P(n,1/n!)/(n!-1) = A*alpha-sum_j H_j(1).

A possible way to ensure nonvanishing, rather than relying only on a
homogeneous lattice argument, is to seek a rational polynomial R(n,t) with
2*deg_t(R)<=J-1 and impose

    q_j(n) = A - [t^(j-1)] R(n,t)^2,    j=1,...,J.

These identities would give exactly

    P(n,t) = A*t^J + (1-t)*R(n,t)^2.

For A>0 and 0<t<1, this is strictly positive. Clearing rational polynomial
coefficients would make A and the boundary integer while retaining the
positive identity (the multiplier need not be a square; it can multiply
both terms). The remaining essential task would be to construct a family
whose total positive error tends to zero after that clearing.

Unlike exact row zeros, strict positivity of this form does not itself
force n!-1 to divide A. It does not by itself bound A, the polynomial
coefficients, the boundary denominator, or the error.

## Elementary consistency checks

For J=1, take A=1, R(n,t)=n-1, and H_1(n)=-n. Then

    n H_1(n-1)-H_1(n) = 1-(n-1)^2.

The form is alpha+1, which is positive but not small. More generally every
J=1 form of the ansatz has a positive contribution at row n=2 of at least
A/2, so it cannot provide small integer forms with positive integral A.

For J=3, the highest-column condition alone has the explicit solution

    R_1(n)=2n^2+2n-1,
    H_3(n)=-4n-12,
    A=13,

because

    n^3 H_3(n-1)-H_3(n) = 13-R_1(n)^2.

Here R=R_0+R_1*t would still have to satisfy the two lower-column conditions
for H_1 and H_2. No claim is made that these checks produce a complete J=3
kernel, much less an asymptotic family. Even a complete positive kernel at
one degree would not settle the target.

## Status

No family with controlled integer heights and errors tending to zero has
been found. The original conjecture and its `sorry` in Spec.lean are unchanged.

## Exact J=3 specialization checked later

Set A=1, R_1(n)=1, H_3=0, and R=R_0+t. The second column forces

    R_0(n)=(1-[n^2 H_2(n-1)-H_2(n)])/2.

The first-column polynomial equation has a solution iff

    sum_k [n^k](R_0(n)^2) * Bell(k) = 1.

For H_2(n)=a*n+b this becomes the rational conic

    96a^2+60ab+12b^2-4a-2b-3=0.

Sage/PARI finds a local obstruction at 5. This obstruction is now also
Lean-verified as `PositiveKernelObstruction.no_rational_point` in
`Submission/PositiveKernelObstruction.lean`. The proof shows that any
integer homogeneous solution has all three coordinates divisible by 5,
then descends on the absolute value of its nonzero final coordinate.
Clearing rational denominators proves the displayed conic has no rational
point. The axiom audit lists only propext, Classical.choice, and Quot.sound.
The derivation of this conic from the polynomial-kernel ansatz is still
mathematical reasoning here, not a Lean theorem about arbitrary kernels.

Degree two does have a rational solution:

    H_2(n)=(-2n^2+13n-10)/16,
    R_0(n)=(2n^4-17n^3+23n^2+13n+6)/32,
    H_1(n)=(-4n^7+36n^6-45n^5-220n^4+99n^3
             +248n^2-409n-988)/1024.

Exact polynomial arithmetic verifies the three column identities. Here

    H_1(1)+H_2(1)=-1219/1024.

Clearing the coefficients by 1024 gives the positive integer form

    1024*alpha+1219,

which is not small. The universal row-two lower bound alone is 1024/8=128.
The particular exact rational points produced in degrees 3 through 6 have
still larger coefficient-clearing factors and give no useful small form.
These finite computations neither rule out other positive kernels nor
construct a controlled infinite family. No proof of Erdős 68 results.

Development script: /tmp/positive_kernel_quadratic.sage (exact arithmetic).

## Later distinct physical-domain ansatz

See PhysicalPositiveKernelsNotes.md for a quadratic-t construction with
P=[a+(1-t)R]^2+(1-t)^2(S-R^2), where S>=R^2 is required only at physical
indices x>=2. A rational Gram block weighted by x-2 allows this condition
without imposing it at x=0,1. An exact A=4,B=5,J=2 certificate is now verified
in PhysicalPositiveKernelExample.lean and escapes the earlier fixed-column
baseline. There is still no growing family with controlled integral heights
and errors tending to zero, so the original conjecture remains unsettled.
