# Variable-row annihilation with integral aggregate boundaries

This is an external exact construction and independent arithmetic audit,
NOT a Lean theorem and NOT a settlement of Erdős 68. Spec.lean is unchanged
with its original sorry. No complete proof or disproof has been obtained.

## Difference from the earlier short-window interpolation

The previous VariableLambertInterpolation test chose K pivot columns and
normalized the retained coefficient to one, leaving a unique rational
operator. Clearing its reduced boundary produced large errors in every case.

The present test keeps free coefficients. For H<=n<H+D, put

    S_n = sum_(m=0)^n lambertCoeff(m)/m!,
    r_d(n) = 1/[(d!)^floor(n/d)*(d!-1)].

It seeks integer weights z_n satisfying

    sum_n z_n*r_d(n)=0,  2<=d<=K,
    B=sum_n z_n*S_n in Z.

Then A=sum_n z_n is an integer and the exact full-target form is A*alpha-B.
No sign is inferred from the weights. The general previously verified
VariableRowAnnihilation theorem implies L_K divides A, where

    L_K=lcm_(2<=d<=K)(d!-1).

Let T=H+D-1 and C be the minimal common denominator of the S_n in the
window. The integer constraint matrix has rows

    (d!)^(floor(T/d)-floor(n/d)), 2<=d<=K,

with a final zero column, and last row

    (C*S_H,...,C*S_T,-C).

An integer kernel vector is (z_H,...,z_T,B). Sage's integral kernel and
LLL algorithms select candidates. LLL is a search procedure, not a trusted
mathematical premise.

## Completed finite test

Parameters:

    K in {3,4,6,8,10,12},
    H in {K^2,2K^2},
    D in {2K,4K}.

All 24 cases completed. All 56 returned nonzero coefficient pairs have
exactly certified nonzero errors in (-1,1). Both signs occur. The projected
pairs have rank two in every case.

More specifically, the gcd of their pair determinants in coordinates
(A/L_K,B) is one in every case. Thus these returned pairs generate Z^2
in those coordinates. Together with the general divisibility constraint,
this identifies the exact pair image as L_K*Z x Z for each tested window.
It supplies no uniform upper bound for integral lifts of those pairs.

At (K,H,D)=(12,288,24), the two pairs have retained coefficients of 440 and
441 bits. Their absolute errors are respectively less than 2^(-310) and
2^(-307), checked by exact rational inequalities. The largest weight sizes
are 438 and 441 bits. The corresponding case with D=48 gives the same
absolute errors, with different signs. These are finite bounds only.

## Independent audit

Construction:

* /tmp/variable_boundary_lattice.py
* /tmp/variable_boundary_lattice.log
* /tmp/variable_boundary_lattice.json

Audit:

* /tmp/variable_boundary_lattice_audit.py
* /tmp/variable_boundary_lattice_audit.log

The construction builds S_n by accumulating divisor coefficients. The audit
instead uses the finite geometric-row identity

    S_n=sum_(d=2)^n ((d!)^floor(n/d)-1)
                      /[(d!-1)*(d!)^floor(n/d)].

It verifies every stored weight sum, every row annihilation, the exact
integer boundary, coefficient and weight bit counts, the constraint-matrix
ranks, all projected pair determinants, and every error classification.

For full-target error certification the construction uses N=1200 and

    W=N!, L=sum_(d=2)^N floor(W/(d!-1)),
    L/W < alpha < (L+N+2)/W.

The audit independently recomputes the intervals with N=1220 and verifies
containment in the stored intervals. Both stages use exact rational
arithmetic; reported logarithms are diagnostics only. All 24 cases and
56 forms passed. No calculation remains running.

## Remaining gap

There is no proof that the useful lattice vectors remain sufficiently short
for an infinite parameter sequence. A nonzero weight vector may give the
zero coefficient pair; under hypothetical rationality even a nonzero pair
may have zero value. Neither the integral-kernel dimension nor finite LLL
success excludes this possibility uniformly.

The previously verified independent-pair irrationality criterion would apply
if two independent integer forms with errors tending to zero were available
for arbitrarily large parameters. This test does not establish that premise.
No new Lean declaration, infinite nonvanishing theorem, or complete informal
solution was obtained, and no submission check was made.

## Subsequent all-index weight construction (informal proof)

The following is an elementary mathematical construction, not yet a Lean
declaration. It shows why a stronger weight bound based only on cancellation
and a nonzero retained sum cannot be assumed. It does not provide integral
late boundaries or settle the conjecture.

Let K>=2 and let A>0 be an integer divisible by every d!-1, 2<=d<=K.
Define v_d backwards, for d=K,K-1,...,2, by

    v_d = A*d!/(d!-1)
            - sum_(k=2)^floor(K/d) v_(kd)/(d!)^(k-1).

Then for every such d:

    v_d is an integer multiple of d!,
    0 <= v_d <= 2A.

For integrality, the first summand is an integer multiple of d!. By
backwards induction, v_(kd) is an integer multiple of (kd)!. Multinomial
integrality says (d!)^k divides (kd)!, so each remaining summand is also an
integer multiple of d!.

For the bounds, write B=d!>=2. Nonnegativity of the later v's gives
v_d<=A*B/(B-1)<=2A. Their upper bounds, together with the geometric sum,
give

    v_d >= A*B/(B-1) - 2A*sum_(k=2)^infinity B^(-(k-1))
         = A*(B-2)/(B-1) >= 0.

Set v_0=v_1=A and v_(K+1)=0, and define

    z_j=v_j-v_(j+1), 0<=j<=K.

All z_j are integers, |z_j|<=2A, and sum z_j=A. For a fixed 2<=d<=K,
finite summation by parts gives

    sum_(j=0)^K z_j/(d!)^floor(j/d)
      = A-(d!-1)*sum_(k=1)^floor(K/d) v_(kd)/(d!)^k
      = 0,

where the last equality is precisely the defining equation for v_d.
Dividing by d!-1 gives annihilation of r_d(j).

If H is divisible by every d in 2,...,K, then r_d(H+j) is a constant
multiple of r_d(j), so the same weights annihilate every selected row at
the indices H,...,H+K. In particular A=L_K is always attainable in these
aligned windows with max |z_j|<=2L_K. This is only a bound on the weight
coordinates, not a claim that the aggregate boundary at H is integral.

At H=0 that boundary is integral, but gives no new approximant. Indeed
all rows d>K are absent from every S_j, j<=K; cancellation of the other
row tails gives exactly

    sum_(j=0)^K z_j*S_j = A*sum_(d=2)^K 1/(d!-1).

Thus the resulting form is simply A times the ordinary original-series
tail. At a later aligned H, no corresponding integrality or smallness
after boundary clearing has been proved. The construction therefore
neither proves irrationality nor contradicts any theorem about the full
integral-boundary lattice.

## Lean verification of the bounded aligned construction

`Submission/AlignedRowAnnihilator.lean` now verifies the core of the preceding
construction. It compiles without warnings and has a built olean. Its three
printed principal axiom audits contain only propext, Classical.choice, and
Quot.sound. There are no proof holes in that auxiliary file.

The definition `solve A N d` recursively constructs the integer v_d/d!.
The integral multinomial quotient is used directly in the recursion, so
integrality is not inferred from numerical rational reconstruction.
`value_equation` verifies the rational recurrence, and `value_bounds` proves
0<=v_d<=2A by backwards induction and the finite geometric-sum bound.

Principal declarations:

* value_bounds
* weight_bound
* weight_sum
* weight_annihilates
* weight_annihilates_aligned
* commonDenominator_pos
* exists_bounded_aligned_annihilator

The final theorem takes N>=2 and H divisible by every d in 2,...,N. It gives
integer weights with retained sum exactly L_N, maximum absolute weight at
most 2L_N, and exact cancellation of every selected geometric row at
H,...,H+N. The private `weighted_floor_sum` lemma verifies the summation-by-
parts identity including its terminal boundary, rather than assuming it.

The explanatory identity for the aggregate boundary at H=0 in the preceding
section has not been separately packaged as a new Lean theorem here. More
importantly, the final theorem asserts neither boundary integrality at a
late H nor smallness or nonvanishing of the full-target integer form. It
therefore does not supply a proof or disproof in Spec.lean. No submission
check was made, and no computation remains pending.
