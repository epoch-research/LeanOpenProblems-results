# Rank-one counting and direct row subtraction

Verified auxiliary work, NOT a proof or disproof of Erdos 68.
`Submission/Spec.lean` is unchanged with its original `sorry`.
No complete proof or disproof has been obtained or submitted.

## New verified files

* `RankOneBoundaryCounting.lean`
* `LambertUnfilteredDetection.lean`
* `LambertRowSubtractedBoundary.lean`
* `RowSubtractedCountingBarrier.lean`

All four compile without warnings and have built oleans. All their printed
principal axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
They contain no holes. No numerical calculation is used as a premise.

## Shared rational offsets cost one residue coordinate

For an m-by-D real matrix f, suppose

    f_ij = gamma - b_ij,  b_ij integers,
    L*gamma is an integer, L>0,
    0 <= f_ij <= R,
    D*Q*R <= M,
    L*(M+1)^m < (Q+1)^D.

`bounded_kernel` constructs nonzero integer weights w_j with |w_j|<=Q,
L dividing sum w_j, and sum_j w_j*f_ij=0 for every output i.

For box inputs u_j in {0,...,Q}, encode the sum of the inputs modulo L and
the floors of their m real output values. There are at most L*(M+1)^m codes.
A collision gives integer differences between outputs with identical floors;
each difference lies strictly between -1 and 1, so is zero.

The rational-endpoint wrapper `rational_endpoint_kernel` applies this to
C*(q-B_ij), where C clears each boundary. Its cardinality bound has one factor
q.den, not q.den^m. The more general theorem permits using the reduced
denominator of C*q instead. `factorial_matrix_kernel` packages boundaries
that are finite integer-coefficient factorial series, cleared by T!.

This guarantees nonzero WEIGHTS only. `sum_zero_of_small_modular_weights`
proves that D*Q<L forces their retained sum to be zero. No useful-pair or
nonzero-value claim is inferred from the counting theorem.

## Unfiltered nonvanishing

Write

    F_d(n)=sum_(e>=d) 1/[(e!)^floor(n/e)*(e!-1)], d>=2.

`LambertUnfilteredDetection.unfiltered_detection_nonzero` proves that for

    d>=12, H>=420*d, 4Q<=d!,

any nonzero finite integer vector with absolute coefficients at most Q
has a nonzero combination sum_j w_j*F_d(n+j) at some H<=n<H+d.
The support length is unrestricted. This is the unfiltered row sum: no
quadratic-degree shift product is applied.

The proof reuses the established phase-mass estimates with the empty shift
list. The first row has positive cyclic response mass, while the complete
sum of all later rows is smaller in that full output window. Leading zero
weights are trimmed exactly as in the earlier filtered detector.

## Exact connection with the original target

Put

    beta_d = alpha - sum_(e=2)^(d-1) 1/(e!-1),
    B_d(n) = S_n^Lambert
             - sum_(e=2)^(d-1) [1/(e!-1)-r_e(n)].

`tail_affine` proves F_d(n)=beta_d-B_d(n) for the exact original alpha.
`boundary_factorial_integral` proves n!*B_d(n) is integral, and
`boundary_common_integral` proves T!*B_d(n) is integral whenever n<=T.
Thus direct row subtraction genuinely removes the quadratic shift degree
from the boundary-clearing endpoint. `value_rational` identifies beta_d
with an explicit rational number under a rationality hypothesis on alpha.

The individual row-partial integrality proof uses the exact row jump and
multinomial divisibility, not an assumption that a removed denominator
divides n!. Cancellation inside each finite geometric row is retained.

## A uniform obstruction to this particular counting construction

There is nevertheless an arithmetic/size obstruction even after charging
the shared denominator only once. `scaled_tail_ge_square` proves

    H>=18, 2<=d<=floor(H/2)+1
      ==> H!*F_d(H) >= H^2.

Keep the row e=floor(H/2)+1. Its tail is at least 1/(e!)^2; the earlier
central factorial inequality gives the displayed lower bound. This is a
bound for the actual unfiltered tail, not merely a limitation of an upper
estimate.

For T>=H+D, factorial growth then gives

    T!*F_d(H) >= H^D.

Consequently, if a floor range 0,...,M contains the first image, so that
T!*F_d(H)<M+1, and Q+1<=H^d, then

    (Q+1)^D <= (H^D)^d <= (M+1)^d <= L*(M+1)^d

for every L>=1. This is `floor_range_cardinality_not_lt`. In particular
Q+1<=H^d holds throughout the available detector budget 4Q<=d! and
H>=420*d.

`cardinality_not_lt` also packages the usual uniform-image estimate:
if eta>=F_d(H), D,Q>=1, and D*Q*T!*eta<=M, the counting hypothesis cannot
hold at the detector's coefficient bound, for ANY parameters in this range.
This is an all-parameter result, not an asymptotic calculation or finite test.

## Scope

The obstruction concerns clearing by T! and counting images by this common
box/floor range. It does NOT exclude a smaller aggregate or common clearing
factor, a sharper count exploiting dependencies between coordinates, a
controlled useful lattice lift, or a different nonvanishing theorem.

The new rank-one count is valid, and the unfiltered detector and exact
boundaries are valid, but the displayed construction cannot combine them
into an irrationality proof. No infinite carry violation or independent
small-form family has been obtained. No complete informal solution is
awaiting formalization, and Spec.lean has not been altered.
