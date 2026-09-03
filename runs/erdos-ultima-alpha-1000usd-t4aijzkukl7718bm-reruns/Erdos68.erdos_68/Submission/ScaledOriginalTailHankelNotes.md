# Factorial-scaled original-tail Hankel polynomials

This is an external exact construction test, NOT a Lean theorem and NOT a
settlement of Erdős 68. Spec.lean is unchanged with its original sorry.
No proof or disproof of the conjecture has been obtained or submitted.

## Construction

Let S_h=sum_(k=2)^h 1/(k!-1), with S_1=0, and form

    D_(h,m)(X)=det_(0<=i,j<m) [(h+i+j)!*(X-S_(h+i+j))].

Unlike the previous original-tail Hankel experiment, these entries include
a factorial factor. The X coefficient matrix is not rank one. The degree
is m and its leading coefficient is

    product_(i=0)^(m-1) i!*(h+i)!.

The experiment constructs this rational polynomial by interpolation at
X=0,...,m, checks the displayed leading coefficient, and checks one extra
value X=m+1. It then clears the common coefficient denominator and divides
the gcd of all resulting integer coefficients. The resulting primitive
integer polynomial P has positive leading coefficient.

The error tested is P(alpha) for the FULL original series alpha. No tail
is dropped. The diagnostic quantity log2(|P(alpha)|)/m reflects the
necessary degree-relative rational-denominator bound. Plain smallness of
the raw rational determinant would not suffice.

## Parameters and exact classifications

    m=2,...,8;
    h in {1,2,m,2m,m^2}, with duplicates removed.

There are 33 cases. The exact construction reports:

* 26 values greater than 1;
* 5 values less than -1;
* 2 values in (0,1), both with m=2 and h=1 or h=2;
* no ambiguous classifications.

Thus all tested m>=3 have primitive integer polynomial values of absolute
value greater than one. This is a finite result, not an asymptotic
impossibility theorem. It excludes no untested parameters or other matrix
constructions. It supplies no irrationality proof.

## Exact interval and independent audit

The interval uses N=10000, W=N!, and

    L=sum_(k=2)^N floor(W/(k!-1)),
    L/W < alpha < (L+N+2)/W.

Rational interval Horner evaluation bounds P(alpha). All signs and
comparisons with one use exact integer/rational operations. The original
logarithm diagnostic overflowed; this affected no comparisons. The audit
recomputes that diagnostic from leading integer bits.

The independent audit uses Python Fraction rather than Sage matrix or
polynomial algorithms. It reconstructs partial sums and determinants by
rational Gaussian elimination, checks the polynomial at m+1 distinct
points, verifies primitive coefficients and every stored interval endpoint,
and checks every classification again on the separate N=10017 grid.

All 33 cases passed the independent audit, including the second-grid
classifications. Both processes have completed; no computation is pending.
For example, (h,m)=(64,8) has maximum coefficient bit length 92,853 and
diagnostic log2(|P(alpha)|)/8 approximately 11,243.76. These diagnostics are
not used as proof premises; the classifications are exact.

Artifacts:

* /tmp/scaled_original_tail_hankel.py
* /tmp/scaled_original_tail_hankel.log
* /tmp/scaled_original_tail_hankel.json
* /tmp/scaled_original_tail_hankel_audit.py
* /tmp/scaled_original_tail_hankel_audit.log

The separate Lean file PositiveMatrixCriterion.lean verifies a general
integer-matrix irrationality criterion and its dimension-dependent scaling.
It does not assert that these rational Hankel matrices meet that criterion.
