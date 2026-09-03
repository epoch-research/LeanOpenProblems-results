# A quantitative common-multiple bound for factorial-minus-one rows

This is verified auxiliary arithmetic, NOT a settlement of Erdős 68.
Spec.lean remains unchanged with its original sorry. No proof has been submitted.

FactorialMinusOneLcmBound.lean compiles without warnings, has a built olean,
and contains no proof holes. Its six printed axiom audits use only propext,
Classical.choice, and Quot.sound.

## Pairwise gcds and a block bound

Write d_n=n!-1. For j<i the file proves

    gcd(d_(k+i),d_(k+j)) divides (k+j+1)...(k+i)-1.

For 0<=j<i<n and k>=2 this gives

    gcd(d_(k+i),d_(k+j)) <= (k+n)^n.

The proof does not assume pairwise coprimality. The general arithmetic
lemma is

    product_i a_i divides L * product_(j<i) gcd(a_i,a_j)

whenever every a_i divides L. It is proved by induction, using the
standard gcd-of-a-product divisibility inequality. Bounding the triangular
product coarsely by (k+n)^(n^3) then gives, for positive L,

    [d_k]^n <= L*(k+n)^(n^3)

whenever all d_(k+i), 0<=i<n, divide L.

## An explicit growing lower bound

For m>=5, take k=4m^2 and n=m. The factorial block estimate gives

    d_(4m^2) >= m^(4m^2),
    4m^2+m <= m^3.

The preceding common-multiple bound therefore implies

    m^(m^3) <= L.

In particular,

    m^(m^3) <= lcm_(0<=j<m) ((4m^2+j)!-1).

This is an explicit superlinear logarithmic lower bound on the lcm, using
a short block near a quadratic index. No asymptotic optimality is claimed.

## Application to arbitrary integer row weights

Use VariableRowAnnihilation.factorial_row_denominator_dvd. If integer
weights z_i, at arbitrary natural sample indices, annihilate every geometric
Lambert row d=4m^2+j, 0<=j<m, and A=sum_i z_i is NONZERO, then

    m^(m^3) <= |A|.

For D weights with |z_i|<=Q, this gives m^(m^3)<=D*Q.
The main names are:

* pair_gcd_dvd_ratio
* block_common_multiple_bound
* quadratic_block_height
* quadratic_block_lcm_height
* annihilator_coefficient_height
* annihilator_weight_height

## Remaining gap

The assumption A!=0 is essential. Every row denominator divides A=0, so
this estimate cannot by itself exclude nonzero weight vectors whose retained
coefficient vanishes. Nor does it prove a nonzero total linear form or an
analytic error bound that supplies a settlement. The existing pigeonhole
construction still allows zero coefficient pairs. No complete proof or
disproof of the original conjecture has been obtained.

## Review against the existing boundary lattice

The new height estimate does not directly constrain the outer window
weights w_i in LambertBoundaryForms. After expanding the raw operator,
the retained coefficient is

    A_K * sum_i w_i,   A_K=product_(d=2)^(K+1)(d!-1).

The expanded weights also include the coefficients of
product_(d=2)^(K+1)(d! E^d-1). They are not bounded merely by the outer
weight bound Q. Applying annihilator_weight_height with D,Q taken from
the outer window, while ignoring this convolution, would be invalid.

When the quadratic row block used in the lcm theorem lies among the
already cancelled rows, A_K itself is a positive common multiple of all
its denominators. Hence the lcm lower bound is already satisfied by A_K;
it does not force a larger nonzero sum of the outer weights.

The possibility sum_i w_i=0 and integral boundary zero is unchanged.
The new arithmetic estimate therefore has not supplied the nonzero pair
or nonzero value required by IntegerFormCriterion. This review produced
no new proof or disproof and no change to Spec.lean.
