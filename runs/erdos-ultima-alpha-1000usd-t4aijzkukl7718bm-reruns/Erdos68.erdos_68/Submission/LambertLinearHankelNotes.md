# Linear-threshold real-weight detection and Hankel nonsingularity

Verified auxiliary progress, NOT a proof or disproof of Erdős 68.
`Submission/Spec.lean` remains unchanged with its original `sorry`.

`LambertLinearHankel.lean` compiles without warnings and has a built olean.
All three printed principal axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`.

## New statements

For d >= 12, H >= 420*d, and any nonzero REAL vector w indexed by ZMod d,
there is n in [H,H+d) with

    sum_j w_j*rawTail(d-2,n+j.val) != 0.

There is no integrality or coefficient-height restriction on w. Its support
is d consecutive shifts; this does not extend the arbitrary-support
integer theorem beyond its factorial height bound.

Consequently the d-by-d raw-error Hankel matrix

    M_(i,j)=rawTail(d-2,H+i.val+j.val)

is invertible and has nonzero determinant for H >= 420*d.

Principal declarations:

* `weighted_window_bound_real`
* `first_window_lower_real`
* `real_weight_detection`
* `rawHankel_isUnit_linear`
* `rawHankel_det_ne_zero_linear`

## Proof

Set c_j=w_j/rate(d)^j. Since the support contains one copy of each cyclic
phase, its weighted absolute coefficient sum is exactly mass(c). No
coefficient-height estimate or tail-of-support estimate is necessary.

The existing first-row mass theorem bounds its full-phase response below by

    exp(-48)*mass(c)/(rate(d)+1).

The newer remaining-row mass estimate bounds the weighted full-phase
response of all later rows above by

    exp(-48)*mass(c)/(6*d).

The second is strictly smaller when c is nonzero. Thus the total response
cannot vanish at every phase. Applying this to a vector in the Hankel
matrix kernel proves injectivity and invertibility.

The older arbitrary-real-weight Hankel bound was

    H >= (d+1)*(3*(log2(d)+1)+130).

The new threshold is linear in d, but its constant is larger: it is not a
pointwise improvement for every d. Both sufficient bounds remain valid.

## Remaining arithmetic gap

Each entry is A*alpha minus a rational boundary, so the determinant is
affine in alpha. Nonsingularity is not an integer-coefficient assertion.
No upper bound on the primitive integer coefficient pair sufficient to
preserve smallness has been obtained. In particular the row-cancellation
operator still has quadratic shift degree, which contributes to the
factorial boundary-clearing cost even with the new linear starting index.

No complete proof or disproof of the conjecture has been obtained or
submitted. No external numerical computation is used in the new proofs.
