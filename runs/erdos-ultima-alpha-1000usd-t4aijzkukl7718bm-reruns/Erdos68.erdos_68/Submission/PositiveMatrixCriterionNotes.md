# Dimension-relative determinant criterion

This is verified auxiliary work, NOT a settlement of Erdős 68.
`Submission/Spec.lean` remains unchanged with its original `sorry`.
No proof or disproof of that conjecture has been submitted.

`PositiveMatrixCriterion.lean` compiles without warnings and has a built
olean. Its four printed principal axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`.

For integer d-by-d matrices A,B, write M(x)=x*A-B. The file verifies

    den(q)^d det M(q) = det(num(q)*A-den(q)*B),

where the right side is the real cast of an integer. Consequently

    det M(q)>0  ==>  det M(q)>=den(q)^(-d).

The resulting sufficient irrationality criterion is:

    for every epsilon>0 there are d,A,B with
    0<det M(x)<epsilon^d.

The dimension may vary, including zero (for which the displayed strict
inequality cannot hold). Positive definiteness is not required in the
formal statement; strict positivity of the determinant is sufficient.
No matrix family satisfying this criterion for the target is supplied.

## A verified limitation

For x=1/2, A=I_d and B=0, the determinant is exactly 2^(-d). These positive
determinants tend to zero even though x is rational. This is verified as
`half_identity_det` and `rational_example_positive_det_tendsto`.
Thus plain convergence to zero with increasing dimension is not enough.
The dimension-relative estimate must not be discarded.

## Status of the construction problem

The original-tail Hankel experiment previously used entries X-S_(h+i+j).
Their X coefficient matrix has rank one, making those determinants affine.
A separate test now considers factorial-scaled entries

    (h+i+j)! * (X-S_(h+i+j)),

whose determinant has degree d. Those rational polynomials must still be
converted to primitive integer polynomials before estimating their values.
Their raw determinants alone do not provide integral forms. The numerical
construction and its independent audit are separate from the Lean criterion;
neither is a proof of the original conjecture.

Reviewing the modified Engel coordinates also produced no integer descent
or exclusion of the exact consecutive multipliers. No complete informal
argument for the original conjecture is currently awaiting formalization.
