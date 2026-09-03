# Three-row zero-pair kernels

This is verified auxiliary work, not a settlement of Erdős 68.
`Submission/Spec.lean` is unchanged with its original `sorry`.

## Verified algebra

`ThreeBoundaryKernel.lean` compiles without warnings and has a built olean.
Its two printed principal axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`.

Let C>0 clear three rational boundaries, and write b_i=C*B_i in Z.
If b_1-b_0 and b_2-b_0 are coprime, the integral weights satisfying

    sum_i w_i=0,    sum_i w_i*b_i=0

are exactly the integer multiples of

    (b_2-b_1, b_0-b_2, b_1-b_0).

The proof uses an explicit Bezout identity and also handles zero differences.
Consequently, if a coordinate of this primitive kernel has absolute value
strictly greater than Q, no nonzero zero-pair vector lies in the weight box
|w_i|<=Q.

Combining this with the earlier pigeonhole lemma gives:
if C<(Q+1)^3, there are bounded cleared weights whose coefficient pair is
nonzero. With common retained coefficient A!=0 and row errors at most eta,
`small_nonzero_pair` supplies integers a,z with

    (a,z)!=(0,0),    |a*x-z|<=3*Q*eta.

This last inequality still permits a*x-z=0. No second independent pair or
nonzero-valued form has been constructed for the target series.

Main declarations:

* zero_pair_iff_multiple
* kernel_bound_of_zero_pair
* bounded_nonzero_pair
* small_nonzero_pair

## Exact finite structural test

The external script `/tmp/lambert_three_rows.py` tested the raw operator
product_(d=2)^K(d!*E^d-1), with three rows H,H+1,H+2 at H=K^2, for

    K=3,4,5,6,8,10,12,16,20,24,32.

It computed the exact common denominator, gcd of the two integral boundary
differences, primitive zero-pair vector, and a three-dimensional cleared
lattice basis. All 33 retained basis pairs were nonzero. Exact intervals
certified their values nonzero; two values had absolute value below one
(both at K=3), and the other 31 had absolute value above one. Thus these
finite tests did not produce a useful vanishing-error family.

For example, at K=32 the common denominator had 12618 bits, the primitive
zero-pair vector had a largest coordinate of 8802 bits, and the largest
basis weights had 4206 bits. Its three errors were all much greater than
one. Logarithms recorded in the output are diagnostics, not proof premises.

The interval certificates use W=5000! and

    L=sum_(n=2)^5000 floor(W/(n!-1)),
    L/W < alpha < (L+5002)/W.

Artifacts:

* /tmp/lambert_three_rows.py
* /tmp/lambert_three_rows.log
* /tmp/lambert_three_rows.json

The computation has finished. Its finite outputs are not Lean theorems or
an asymptotic impossibility result.

## Why the remaining distinction is essential

Even a large primitive zero-pair vector and coprime boundary differences
are compatible with a rational limiting value. For N>=2, take x=A=1,
C=N^2, and

    B_0=1-1/C,  B_1=1-N/C,  B_2=1-(N+1)/C.

The boundary differences are coprime after multiplying by C, and the
primitive zero-pair vector is (-1,N,1-N). Nevertheless the short vector
(-1,-1,1) produces the nonzero pair (-1,-1), of value zero at x=1.
For N=m^3 and Q=m^2, m>=2, the cardinal inequality C<(Q+1)^3 and the large
kernel-coordinate condition both hold, while 3*Q*max_i|1-B_i| tends to zero.
Thus the verified nonzero-pair construction alone cannot be promoted to
an irrationality proof. This example is algebraic analysis here, not a new
Lean declaration, and does not model the exact Lambert boundaries.

No complete proof or disproof has been obtained or submitted.

## Exact image of the cleared-pair map

`ThreeBoundaryImage.lean` now compiles without warnings, with a built olean.
Its two printed axiom audits contain only the three permitted axioms.
For arbitrary integral b_i,C,s,z (without a coprimality assumption), it proves

    exists integral w with sum w_i=s and sum w_i*b_i=C*z
      iff gcd(b_1-b_0,b_2-b_0) divides C*z-b_0*s.

The reverse implication explicitly lifts a Bezout identity. The result
includes the case of equal boundaries, where the gcd is zero. Consequently,
if the two differences are coprime, every pair (s,z) is attainable.
The declarations are `cleared_pair_iff_gcd_dvd` and
`cleared_pair_surjective`.

This is exact algebraic control of the image, not a useful bound on the
weights of its lifts. In particular, surjectivity supplies independent
pairs but does not make their errors small, while the earlier bounded
construction supplies a small pair but not independence or a nonzero value.
No estimate combining these two requirements has been obtained. The original
conjecture remains unchanged and unproved; nothing has been submitted.
