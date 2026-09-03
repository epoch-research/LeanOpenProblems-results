# Quadratic windows: small-or-zero forms and a verified rank obstruction

This is auxiliary work, NOT a settlement of Erdős 68. Spec.lean is unchanged
with its original sorry. No complete proof or disproof has been obtained or
submitted.

## Explicit asymptotic construction

`LambertQuadraticWindow.lean` specializes the existing boundary-clearing and
pigeonhole framework to

    cancelled rows ds=[2,...,K+1],
    H=K^2, D=K^2, Q=(4*K^2)^4=256*K^8.

The common denominator C is bounded without Stirling or a factorial-product
lower bound. Since sum(ds)<=2*K^2,

    C <= (4*K^2)! <= (4*K^2)^(4*K^2) = Q^D < (Q+1)^D.

For K>=16, `quadratic_window_small_or_zero` supplies

    w != 0, |w_i|<=Q,
    b=sum_i w_i*boundary(ds,H+i) in Z,
    |coefficient(ds)*(sum_i w_i)*alpha-b| <= 256/K^2.

`arbitrarily_small_or_zero` makes the epsilon quantifier explicit. The actual
bound inherited from the row estimate is much stronger:

    D*Q*eta, eta=2^(K+1)/(K+1)^(floor(K^2/2)-1).

These statements allow both a zero coefficient pair and a zero value. They
do NOT imply irrationality.

## The same parameter choice cannot supply two independent small pairs

`BoundedBoundaryDependence.lean` proves a general determinant estimate.
Suppose all rows have the same retained coefficient A and

    |A*x-B_i|<=eta.

Let two integer weight vectors w,v, each bounded by Q in D coordinates,
clear their aggregate boundaries to integers b,d. Write s=sum w, t=sum v.
Then

    |s*d-b*t| <= 2*(D*Q)^2*eta.

Crucially, A cancels from this determinant estimate. If the right side is
less than one, the integer determinant is zero. The theorem is
`bounded_window_dependence`; its contrapositive is
`independent_requires_large_weights`.

For the quadratic parameters above and K>=32, the right side is strictly
less than one. This is `quadratic_window_rank_bound`. Consequently
`quadratic_window_pair_dependence` proves that EVERY two integrally cleared
forms using these weights have dependent coefficient pairs. This is an
unconditional obstruction, not merely failure of the pigeonhole proof.

One nonzero-valued form would still suffice if available at each accuracy.
No such nonvanishing assertion is proved. In particular, do not apply the
independent-pair criterion to this quadratic-window polynomial-weight family.
The older linear-window LLL tests used different parameters and are not
contradicted by this theorem; controlling their useful final minima remains
unproved.

## Verification

Both files compile without warnings, have built oleans, contain no proof
holes, and their principal printed axiom audits list only propext,
Classical.choice, and Quot.sound. No external computation is trusted.
