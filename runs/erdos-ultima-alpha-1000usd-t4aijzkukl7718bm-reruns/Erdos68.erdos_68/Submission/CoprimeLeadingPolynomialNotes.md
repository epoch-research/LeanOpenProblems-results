# Coprime-leading and irreducible auxiliary polynomials

This is auxiliary work, not a settlement of Erdős 68. Spec.lean is unchanged
with its original sorry. No proof or disproof has been submitted.

## New verified files

All three files below compile without warnings, have built oleans, and their
printed principal axiom audits contain only propext, Classical.choice, and
Quot.sound. They do not construct a sufficiently small family for alpha.

### CoprimeLeadingPolynomialCriterion.lean

For a finite family P_i in Z[X], suppose integers u_i satisfy

    sum_i u_i leadingCoeff(P_i)=1.

If r is a common rational root, the rational root theorem says its reduced
fraction-ring denominator divides every leading coefficient, hence divides
one. Thus r is an integer. This is `integer_of_common_roots`.

`irrational_of_small_polynomials` states: for a noninteger real x, it suffices
that for every positive natural b there is such a finite family with

    |P_i(x)| < b^(-natDegree(P_i))   for every i.

The actual degree of each polynomial is used. Large Bezout coefficients do
not affect this contradiction, since they are used only after all the values
have been shown to vanish under rationality. No coefficient-size estimate
for those Bezout coefficients is asserted.

### SpecializationFactorRemoval.lean

The outer variable in P in (Z[X])[z] is z. For nonzero P, remove its maximal
power of z-1 to obtain Q with Q(1,X) not identically zero. This does not
increase the outer degree. The file defines substitution into a rational
formal power series F(z) and proves that the vanishing jets at z=0 are
unchanged: z-1 is a unit in Q[[z]]. The main theorem is
`nonzero_specialization_preserving_jets`.

This removes identically zero specialization, NOT a root at the particular
number alpha. No analytic norm or coefficient-height bound is proved here.

### IrreduciblePolynomialCriterion.lean

A primitive irreducible integer polynomial of degree at least two has no
rational root, by Gauss's lemma. The file gives the corresponding criterion
using the same strict degree-dependent error bound.

It also verifies the specific Eisenstein-at-two criterion: if P is primitive,
has degree at least two, its leading coefficient is odd, all lower
coefficients are even, and its constant coefficient is not divisible by
four, then it has no rational root. The principal criterion is
`irrational_of_mod_four_small_polynomials`.

## Homogeneous Lambert-jet tests

For F(z)=sum_(d>=2) z^d/(d!-z^d), use all coefficients of P(z,X) with
z-degree M=2D and X-degree D. Require vanishing through z^N. The integer
kernel is computed from the factorial-scaled jet equations using FLINT.

`/tmp/lambert_coprime_leading.py` tests feasible parameter pairs with

    N in {2D,3D,floor((U-1)/3),floor((U-1)/2),floor(2(U-1)/3)},
    U=(M+1)(D+1),

removing duplicates. All 23 groups through D=6 completed, as did D=7,N=14
and N=21. The D=7,N=39 kernel calculation was stopped before a retained
result. Nothing is claimed for unfinished groups.

Each LLL basis row with nonconstant, nonzero specialization yields an
integer polynomial. The specialized content is removed before measuring
its value; full bivariate coefficient integrality is not imposed after that
normalization. There are 745 retained distinct forms within their groups.
Thirty have absolute value below one. None meets the test bound
2^(-actual degree). Leading gcds among values below one are often one,
but this supplies no growing-denominator criterion.

## Weighted comparison and factor removal

`/tmp/lambert_coprime_leading_weighted.py` completed all 23 groups through
D=6. Its coefficient weights are

    w_(i,j)=6^i * 5^(M-i) * 4^j.

They are motivated by the circle radius 6/5 and a bound F(6/5)<4; no theorem
of optimality or rigorous asymptotic height bound is inferred from the
choice. The algorithm also removes common powers of z-1 before specializing,
and strips powers of X from the specialized polynomial (alpha>1). The latter
operation lowers both the degree and the absolute value. It records the
removed powers so that the exact specialization can be reconstructed.

There are 567 retained forms. Thirty have absolute value below one. Exactly
two meet the tested bound 2^(-degree):

    D=2,N=6:  X-1,                  tested b=1,2,3;
    D=2,N=7:  2X^2+27X-37,          tested b=1,2,3,4,8.

The leading gcd at b=4 and b=8 in the second group is two, not one. No other
retained forms meet any tested b>=2 bound. Forty retained forms have powers
of X stripped; none of the retained forms required z-1 removal. The tested
b list was 1,2,3,4,8,16,32,64,128,256,1024.

`/tmp/lambert_coprime_audit.py` independently rechecks all jets, contents,
specializations, removed X factors, actual degrees, interval values, and
leading gcds. All 1312 retained forms passed. All are certified nonzero by
the intervals. Its log is `/tmp/lambert_coprime_audit.log`.

## Eisenstein modulo four experiment

`/tmp/lambert_eisenstein.py` imposes, after specialization,

    Q_0=2 (mod 4),  Q_j=0 (mod 2) for 0<j<D,  Q_D=1 (mod 2).

Slack variables express these as integer linear equations. HNF tests exact
feasibility. In a homogeneous kernel with auxiliary coordinate t, every
odd t has the same Eisenstein congruences, so it is unnecessary to extract
a row whose auxiliary coordinate is exactly one. Primitive specialization
preserves the congruences because its content is odd.

Completed maximal feasible jet indices (M=2D):

    D | max N | first infeasible N
    2 |    12 |                 13
    3 |    26 |                 27
    4 |    42 |                 43
    5 |    64 |                 65

For each D=2,...,5, forms were selected at N=M-1,M,3D,4D,maxN: twenty groups
and 89 retained forms. Exact intervals certify every selected absolute
value exceeds one. The degree-six feasibility search was stopped before
a maximum or forms were obtained. No degree-six result is claimed.

At the maximal jets, the selected coefficient height in bits was respectively
48,669,1085,6000. The diagnostic logarithms base two of their absolute values
were approximately 40.372,647.498,1046.056,5934.520. These logs are not the
certificates. `/tmp/lambert_eisenstein_audit.py` checks all 89 forms using
exact integers and rational intervals, including every jet equation and
all Eisenstein congruences; all passed. Its log has the matching basename.

## Exact intervals and scope of computations

Every interval audit in this note uses

    W=1500!, L=sum_(n=2)^1500 floor(W/(n!-1)),
    L/W < alpha < (L+1502)/W.

The experiment scripts have corresponding .log and .json files. These are
external exact finite calculations, not Lean theorems or asymptotic bounds.
The selected basis rows are NOT value minimizers. For example, in the
Eisenstein ansatz with D=2,M=4,N=3, the admissible polynomial
z^4*(X^2-2) specializes to X^2-2 and has absolute value below one. Thus the
89 selected values exceeding one cannot be used as a no-small-form theorem.

Irreducibility also does not remove the degree-dependent error requirement.
As a mathematical example, for m>=2,

    R_m(X)=(X^2-2)^m+2*(2X-3)

is monic and Eisenstein at two, but R_m(3/2)=4^(-m) tends to zero at a rational
point. Its degree is 2m, so the value is exactly 2^(-degree), not strictly
smaller. This example is a mathematical observation here, not a new Lean
family declaration.

## Remaining gap

The nonvanishing criteria are verified. A uniform construction meeting the
strict degree-relative smallness requirement remains missing. A homogeneous
Siegel bound supplies small-or-zero values, but does not automatically give
coprime leading coefficients or a chosen Eisenstein congruence class among
the sufficiently small forms. Feasibility of an integral jet system does not
bound the size of a representative in a prescribed affine or congruence class.

No proof of the original conjecture follows. No computation mentioned in
this note is still running, and Spec.lean remains unchanged.
