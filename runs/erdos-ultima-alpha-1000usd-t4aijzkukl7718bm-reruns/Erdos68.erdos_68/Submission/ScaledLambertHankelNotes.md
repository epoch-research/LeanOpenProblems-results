# Factorial-scaled Lambert-prefix Hankel polynomials

This is an external exact construction test, NOT a Lean-verified settlement
of Erdos 68. `Submission/Spec.lean` is unchanged with its original `sorry`.
No proof or disproof has been obtained or submitted.

## Construction and distinction from earlier tests

Write

    a_n = sum_(d|n,d>=2) n!/(d!)^(n/d),
    B_n = n! * sum_(k=0)^n a_k/k!,
    D_(h,m)(X) = det_(0<=i,j<m) ((h+i+j)!*X-B_(h+i+j)).

The integers B_n satisfy B_0=0 and B_n=n*B_(n-1)+a_n. The exact
finite-geometric-row expression is

    B_n/n! = sum_(d=2)^n sum_(j=1)^floor(n/d) 1/(d!)^j.

Thus D is an INTEGER polynomial without any entrywise denominator clearing.
This differs from both the earlier unscaled Lambert Hankel determinants
(which are affine) and the factorial-scaled ORIGINAL-prefix determinants
(which have rational entries and need coefficient denominator clearing).
The degree is m and the leading coefficient is

    product_(i=0)^(m-1) i!*(h+i)!.

The test divides D by the positive GCD of its integer coefficients before
evaluating it. This gives the primitive integer polynomial P. Dividing by
this content is valid for the integer-polynomial criterion; no claim is made
that P itself retains the displayed integer-matrix-pencil representation.

## Completed exact test

Parameters:

    m=2,...,12,
    h in {0,1,2,m}, with duplicates removed.

All 43 cases completed. For the full target alpha=sum_(n>=2)1/(n!-1):

* 1 primitive polynomial value lies in (0,1);
* 19 values exceed 1;
* 23 values are below -1;
* no classification is ambiguous.

The only small case is (h,m)=(0,2), with

    P(X)=X^2-X.

In particular every tested m>=3 gives |P(alpha)|>1. This is a finite failure,
not an asymptotic impossibility theorem. No positivity or nonvanishing
claim for arbitrary h,m follows from these cases.

Some initial primitive polynomials are:

    (h,m)=(1,2): 2X^2-1,
    (h,m)=(2,2): 12X^2-22X+7,
    (h,m)=(0,3): 4X^3-15X^2+9X+1.

The last polynomial has unit constant coefficient, but its value has
absolute value greater than one. The one small determinant does not give
arbitrarily small degree-normalized errors. Its powers keep the same
positive degree-normalized absolute value.

## Exact certificates and independent audit

Artifacts:

* `/tmp/scaled_lambert_hankel.py`
* `/tmp/scaled_lambert_hankel.json`
* `/tmp/scaled_lambert_hankel.log`
* `/tmp/scaled_lambert_hankel_audit.py`
* `/tmp/scaled_lambert_hankel_audit.log`

The generator interpolates at X=0,...,m, checks integrality, degree, leading
coefficient, and an additional node X=m+1. It computes B_n by the integer
recurrence and cross-checks the closed finite-geometric formula.

Evaluation uses the full-series factorial-grid enclosure

    N=1500, W=N!,
    L=sum_(k=2)^N floor(W/(k!-1)),
    L/W < alpha < (L+N+2)/W.

Every interval comparison is exact. Displayed logarithms use leading
integer bits and are diagnostics, not proof premises.

The independent audit uses only Python integers and fractions, not Sage
matrix or polynomial algorithms. It reconstructs B_n by explicitly summing
all finite geometric row terms, checks determinants by fraction-free
Bareiss elimination, and verifies each stored polynomial at m+1 nodes.
It checks primitive content, leading coefficients, every interval endpoint,
and repeats classification with the distinct grid N=1517. All 43 audits
passed. Both computations have finished.

## Other review in this continuation

Changing the representative interval in the congruence-preserving carry
has not supplied a bound for the residual immediately before prime indices.
The existing prime-unit and predecessor congruences still coexist only with
the known quadratic prime-tail bound, not with the stronger bounds needed
by the verified irrationality criteria. No new infinite distribution or
nonvanishing theorem was proved in this review.

There is no complete informal proof awaiting formalization. The original
conjecture remains unproved and undisproved in this workspace.
