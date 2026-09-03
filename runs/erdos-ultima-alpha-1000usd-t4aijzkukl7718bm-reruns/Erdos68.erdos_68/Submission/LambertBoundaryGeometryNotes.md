# Extended exact boundary-lattice geometry tests

This is an external finite construction test, NOT a Lean theorem and NOT
an irrationality proof. Spec.lean is unchanged with its original sorry.

## Construction and indexing

The experiment retains the earlier linear-window construction:

    Q_K(E)=product_(d=2)^K(d! E^d-1),
    A_K=Q_K(1),
    H=K,...,3K,    D=2K+1,
    B_H=Q_K(E)S_H,
    C=lcm of the reduced denominators of B_H,
    b_H=C*B_H.

The integral-boundary lattice is

    Lambda={w in Z^D: C divides sum w_H*b_H}.

Its pair map is

    w -> (s,b)=(sum w_H, sum w_H*B_H),

and the actual integer form is A_K*s*alpha-b.
The symbol K here is the largest cancelled row, whereas the new Lean
operator bounds use K for the number of cancelled rows.

## Exact results

All six selected cases completed. Each basis has D-2 zero-pair rows and
exactly two nonzero-pair rows. The latter have determinant +1 or -1 in
(s,b) coordinates. Every displayed error bound concerns the UNREDUCED
integer form, not a divided pair.

    K   C bits  zero-pair rows  max weight bits  two absolute error bounds
   24    1830        47                41        <2^-44,  <2^-43
   28    2499        55                50        <2^-53,  <2^-53
   32    3279        63                60        <2^-64,  <2^-63
   36    4175        71                70        <2^-73,  <2^-74
   40    5187        79                81        <2^-83,  <2^-84
   48    7569        95               103        <2^-106, <2^-108

All twelve errors have interval-certified nonzero sign. The bounds in the
last column were checked by exact rational multiplication by the indicated
power of two; floating-point logarithms are only diagnostics.

In each case gcd(b_H-b_K)=1. The image is therefore all of Z^2. The full
D-row weight matrix has absolute determinant C, so it is a basis of Lambda.
Since the two nonzero images form a basis of Z^2, the remaining D-2 rows
are a saturated basis of the exact zero-pair kernel.

The exact Gram determinant of that kernel basis agrees with

    D*sum b_H^2 - (sum b_H)^2,

the squared covolume formula when the boundary-difference gcd is one.
These are finite integer equalities, not a newly formalized general theorem.

## Geometry and its limitation

The zero-pair basis is numerically fairly balanced in these cases. For
example, at K=48 its Euclidean row norms have base-two logs between about
80.095 and 80.745, while its covolume per dimension has log about 77.508.
The two useful rows require appreciably larger weights (up to 103 bits).
Thus an assumption that all final minima stay near C^(1/D) is not justified
by these results; the useful and zero-pair directions are already separating.

A uniform upper bound on the needed useful minima, or an appropriate
controlled-lift/nonvanishing theorem, remains missing. Full image, a small
kernel covolume, and finite balanced bases do not themselves give such a
bound. Rational limiting examples can have large tangential lift costs.
No asymptotic assertion is inferred from these six tests.

## Independent exact audit

Artifacts:

* /tmp/lambert_boundary_geometry.py
* /tmp/lambert_boundary_geometry.log
* /tmp/lambert_boundary_geometry.json
* /tmp/lambert_boundary_geometry_audit.py
* /tmp/lambert_boundary_geometry_audit.log

The construction forms the Lambert prefixes by accumulating divisor
coefficients. The independent audit instead reconstructs every prefix by
finite geometric rows:

    S_n=sum_(d=2)^n ((d!)^floor(n/d)-1)
                       / ((d!-1)*(d!)^floor(n/d)).

It then checks all boundary numerators, the minimal common denominator,
every kernel vector, both coefficient pairs and their exact error intervals,
the weight-basis determinant, the projected determinant, and the kernel
Gram determinant. All six audits passed.

The interval certificate uses N=2638, W=N!, and

    L=sum_(n=2)^N floor(W/(n!-1)),
    L/W < alpha < (L+N+2)/W.

Both computation and audit have completed; neither remains running.
The sharper general analytic estimates developed alongside this experiment
are Lean-verified separately in LambertSharperOperatorBounds.lean and
FactorialGeometricProductBound.lean. They still do not establish the missing
infinite nonvanishing assertion. Nothing has been submitted as a solution
of the original conjecture.
