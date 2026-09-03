# Nonsingular late raw-error Hankel blocks

This is verified auxiliary progress, not a settlement of Erdos 68.
`Spec.lean` remains unchanged with its original `sorry`.

`LambertRawHankelNonsingular.lean` compiles without warnings, has an olean,
and both principal axiom audits use only `propext`, `Classical.choice`,
and `Quot.sound`.

For d>=12 and

    H >= (d+1)*(3*(log2(d)+1)+130),

define the real d-by-d matrix

    M(i,j)=rawTail(d-2,H+i+j),  0<=i,j<d.

`rawHankel_isUnit` proves that M is invertible, and
`rawHankel_det_ne_zero` proves det(M)!=0. If M*w=0 and w!=0, the
height-independent short-combination theorem detects a nonzero output
at an index n in [H,H+d), contradicting the row indexed by n-H.

## Remaining arithmetic gap

These entries have the form A*alpha-B_(H+i+j), where A is integral and
B is rational. The determinant is therefore affine in alpha, but its
coefficients need not be integral. Multiplying by a common denominator
preserves nonvanishing but can destroy smallness. No growing family of
small nonzero integer linear forms, nor an adequate primitive determinant
content estimate, has been proved.

The previous exact determinant experiments used different finite parameter
ranges and did not yield useful small cleared forms. They do not rule out
a future construction, and this matrix theorem does not remedy their
arithmetic estimates by itself. No proof or disproof of the original
conjecture has been obtained in this continuation.
