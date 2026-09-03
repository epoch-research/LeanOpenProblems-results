# Unit-constant auxiliary polynomials

This is auxiliary work, not a settlement of Erdős 68. Spec.lean is unchanged
and retains its original sorry. No proof or disproof has been submitted.

## Verified criterion

`UnitConstantPolynomialCriterion.lean` imports `MonicPolynomialCriterion`.
It compiles without warnings, has a built olean, and both printed principal
axiom audits use only propext, Classical.choice, and Quot.sound.

For P in Z[X] with P(0)=1, its reverse is monic. If a rational r>1 were a
root of P, then 1/r would be an integer root of its reverse, contradicting
0<1/r<1. The file proves:

* reverse_monic_of_constant_one
* rational_eval_ne_zero
* irrational_of_unit_constant_small_polynomials

The last theorem states: if x>1 and for every positive natural b there is
P in Z[X] with P(0)=1 and

    |P(x)| < b^(-natDegree P),

then x is irrational. It uses the already verified denominator clearing
in MonicPolynomialCriterion. No such family is constructed for alpha.

## Exact maximal-jet experiment

For the Lambert function

    F(z)=sum_(d>=2) z^d/(d!-z^d),  F(1)=alpha,

seek integer coefficients in

    P(z,X)=sum_(j=0)^D sum_(i=0)^M c_(i,j) z^i X^j,
    sum_i c_(i,0)=1,

such that P(z,F(z)) vanishes through z^N. The final constraint imposes
constant coefficient one only after specializing z=1. These are exact
integer linear equations after factorial scaling of the jets. The script
`/tmp/lambert_unit_at_one.py` uses M=2D, HNF for feasibility, the saturated
FLINT integer kernel, and weighted LLL to select a feasible form. The
trivially feasible starting index is N=M-1, not the earlier monic starting
index. Completed results:

    D | largest feasible N | first infeasible | height bits | log2 |Q(alpha)|
    1 |                  2 |                3 |           2 |        0.592
    2 |                  9 |               10 |          11 |        8.561
    3 |                 20 |               21 |          63 |       46.515
    4 |                 29 |               30 |          68 |       50.328
    5 |                 54 |               55 |         412 |      365.550

Here Q(X)=P(1,X); all five actual specialized degrees equal D. The displayed
logarithms are diagnostic only. Exact intervals certify every selected
absolute value exceeds one. There was no failed unit-coordinate extraction
among these five cases. The experiment completed.

## Lower-order comparison

`/tmp/lambert_unit_at_one_lower.py` uses M=2D and tests feasible N in

    {2D-1, 2D, 3D, 4D, floor(D^2/2)}.

There are thirty retained forms: all feasible cases through D=6, and
(D,N)=(7,13),(7,14),(7,21),(7,24). Ten specialize to the constant one;
twenty have absolute value greater than one. The calculation was stopped
at (D,N)=(7,28) before a retained form, and no degree-eight cases ran.
No conclusion is claimed for these unfinished cases. Trailing zero
coefficients are removed and the actual specialized degree is recorded.

## Independent exact audit and limitations

`/tmp/lambert_unit_audit.py` independently rechecks all jet equations, the
specialized polynomial, its constant coefficient one, its actual degree,
and an exact rational interval value. The interval is

    W=1500!, L=sum_(n=2)^1500 floor(W/(n!-1)),
    L/W < alpha < (L+1502)/W.

Its output is `/tmp/lambert_unit_audit.log`; the two experiment scripts have
matching .log and .json artifacts. All 35 retained forms passed the audit.
These external finite computations are not Lean theorems, asymptotic bounds,
or minima over the feasible affine lattices.

In particular, the selection method's lack of values below one is NOT an
obstruction to such values. For example,

    P_0(z,X)=z^2+(z-2)X

has P_0(1,X)=1-X and P_0(z,F(z))=z^3/6+O(z^4). Thus P_0^D is feasible
with M=2D through N=3D-1, and has specialized value (1-alpha)^D. Its
D-th-root absolute error is the fixed alpha-1, however, not a quantity
tending to zero. It therefore cannot furnish the full degree-dependent
criterion. This example also illustrates why looking only at unit-coordinate
rows of an LLL basis misses useful affine combinations.

The decisive arithmetic-height/analytic-error construction is still missing.

## Separate recurrence review

The exact consecutive-multiplier modified Engel recurrence was reviewed
again. The normalized update differs from the ordinary Engel update, and
the known square-denominator cancellation identity yields no descending
integer height. No new theorem excluding the factorial multiplier pattern
was proved. None of these investigations settles the conjecture.

No computation mentioned here remains running. Spec.lean is unchanged.
