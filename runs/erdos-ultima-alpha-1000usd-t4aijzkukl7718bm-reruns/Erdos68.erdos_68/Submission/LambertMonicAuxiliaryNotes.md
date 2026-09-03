# Monic auxiliary polynomials for the Lambert regrouping

This is auxiliary research, not a settlement of Erdős 68. `Spec.lean` is
unchanged with its original `sorry`; nothing has been submitted.

## Verified nonvanishing criterion

`MonicPolynomialCriterion.lean` compiles without warnings, has a built olean,
and its printed principal axiom audits use only the permitted axioms.
It proves that for an integer polynomial P and rational r,

    den(r)^degree(P) * P(r)

is an integer. Hence a value of absolute size strictly below
`den(r)^(-degree(P))` must vanish. The rational root theorem then gives:
if x is not an integer and, for every positive integer b, some monic integer
P satisfies

    |P(x)| < b^(-degree(P)),

then x is irrational. This avoids a separate nonvanishing hypothesis for
monic polynomials, but supplies no such family for the target.

The degree-dependent bound is essential. For instance, powers of X-1 tend
to zero at every real x in (1,2), including rational x, so mere convergence
of monic polynomial values to zero would not suffice.

Main declarations:

* scaled_rational_eval_integer
* rational_small_polynomial_zero
* irrational_of_monic_small_polynomials

## Distinct exact finite jet test

This uses F(z)=sum_(d>=2) z^d/(d!-z^d), not the direct generating series
covered by MonicAuxiliaryObstructionNotes.md. Let

    P(z,X)=X^D + sum_(j<D) B_j(z)*X^j, B_j in Z[z].

The scripts calculate the integral factorial-scaled coefficients of F^j.
They use integer Hermite normal form to test whether the coefficients
through z^N of P(z,F(z)) can all vanish. The full-degree test permits every
shift that can contribute through N. Feasibility is monotone in N.
The completed exact calculations give:

    D | largest feasible N | first infeasible N
    1 |                  1 |                  2
    2 |                  5 |                  6
    3 |                 13 |                 14
    4 |                 19 |                 20
    5 |                 23 |                 24
    6 |                 41 |                 42
    7 |                 56 |                 57
    8 |                 59 |                 60
    9 |                 69 |                 70
   10 |                104 |                105

These are external exact linear-algebra results, not Lean declarations or
an asymptotic law. They must not be interpreted as an all-degree bound.

A separate completed test restricts the z-degrees of the lower coefficients
to M in {D,2D,4D}, for D=2,...,9. It distinguishes ordinary vanishing jets
from the weaker requirement that the jets be integral (allowing a further
integer polynomial to cancel them). In particular M=2D permits the listed
maximal vanishing jets for all tested D=2,...,9.

Artifacts:

* /tmp/lambert_monic_jets.py, .log, .json
* /tmp/lambert_monic_shortdegree.py, .log, .json

## Constructed monic polynomials and their values

A further script takes M=2D and maximal feasible N, computes the saturated
integer kernel, and uses LLL with a weighted monic coordinate to find an
integer polynomial with leading X-coefficient exactly one. Every retained
coefficient vector is checked against all jet equations exactly. Then it
forms Q(X)=P(1,X), which remains monic.

Completed cases D=2,...,7:

    D | N  | M  | coefficient height, bits | diagnostic log2 |Q(alpha)|
    2 |  5 |  4 |                        5 |                       3.092
    3 | 13 |  6 |                       19 |                      12.091
    4 | 19 |  8 |                       22 |                      13.579
    5 | 23 | 10 |                       18 |                       9.732
    6 | 41 | 12 |                       63 |                      38.207
    7 | 56 | 14 |                      101 |                      57.602

Exact interval arithmetic, not the displayed logarithms, certifies that
all six values have absolute value greater than one. The enclosure used is

    W=2000!, L=sum_(n=2)^2000 floor(W/(n!-1)),
    L/W < alpha < (L+2002)/W.

The degree-eight kernel calculation was stopped before producing a result;
no conclusion is claimed for it. No process remains running.

Artifacts:

* /tmp/lambert_monic_forms.py
* /tmp/lambert_monic_forms.log
* /tmp/lambert_monic_forms.json

## Remaining mathematical problem

Monicity handles rational-root nonvanishing, but a uniform arithmetic-height
and analytic-error construction is still missing. Feasibility of the jet
systems does not bound the size of an integer monic solution. A homogeneous
Siegel/pigeonhole estimate cannot automatically be imposed on a prescribed
leading coefficient. None of these finite tests establishes an asymptotic
impossibility result or proves irrationality. The conjecture is unsettled
in this workspace.

## Fixed initial-row removal: completed exact test

The further script `/tmp/lambert_monic_removed.py` uses

    F_K(z)=sum_(d>K) z^d/(d!-z^d),
    beta_K=F_K(1)=alpha-sum_(d=2)^K 1/(d!-1).

For each K in {2,3,4} and D in {2,...,6}, it imposes leading X-coefficient
one and z-degree at most M=2D on all lower coefficients. It determines the
maximal feasible vanishing index N by exact integer HNF, constructs a
monic solution via an exact saturated kernel and LLL, and checks the
specialized polynomial using rational interval arithmetic. Results:

    K | D | N  | selected Q(X) | diagnostic log2 |Q(beta_K)|
    2 | 2 |  5 | X^2           | -3.960
    2 | 3 | 10 | nontrivial    |  0.386
    2 | 4 | 15 | nontrivial    |  2.192
    2 | 5 | 18 | nontrivial    |  1.466
    2 | 6 | 25 | nontrivial    | 11.971
    3 | 2 |  7 | X^2           | -8.449
    3 | 3 | 11 | X^3           | -12.673
    3 | 4 | 15 | X^4           | -16.897
    3 | 5 | 19 | X^5           | -21.122
    3 | 6 | 25 | nontrivial    |  4.376
    4 | 2 |  9 | X^2           | -13.282
    4 | 3 | 14 | X^3           | -19.923
    4 | 4 | 19 | X^4           | -26.564
    4 | 5 | 33 | nontrivial    | 20.445
    4 | 6 | 41 | nontrivial    | 10.891

These are only the selected LLL forms, not minimizers of the value or an
impossibility theorem. Every selected value below one comes from X^D.
Its D-th-root error is beta_K, independent of D, and so does not furnish
the degree-relative decay required by the verified criterion. The increase
in real analytic radius does not by itself control the height of a monic
solution. Rational shifts of denominators 1,5,115 for K=2,3,4 respectively
also have to be accounted for if using a denominator for alpha directly.

The exact enclosure used W=1500! with

    L=sum_(n=2)^1500 floor(W/(n!-1)),
    L/W < alpha < (L+1502)/W.

The .json and .log files have the same basename as the script. All fifteen
cases completed. These external computations are not Lean theorems. No
new claim of irrationality or rationality follows; Spec.lean is unchanged.

## Monicity only at z=1: further completed comparisons

The separate ansatz allows

    P(z,X)=sum_(0<=j<=D,0<=i<=M) c_(i,j) z^i X^j,
    sum_i c_(i,D)=1.

Thus Q(X)=P(1,X) is monic, without requiring its leading coefficient as a
polynomial over Z[z] to be the constant polynomial one. A final integer
linear equation imposes this constraint. The script
`/tmp/lambert_monic_at_one.py` uses M=2D, exact HNF feasibility tests, and
a weighted kernel reduction to select forms. Completed maximum-jet results:

    D | largest feasible N | first infeasible | selected value log2
    1 |                  3 |                4 |    0.326
    2 |                 12 |               13 |   82.365
    3 |                 24 |               25 |  259.467
    4 |                 41 |               42 |  986.790
    5 |                 63 |               64 | no selected monic row

The final entry means only that none of the returned LLL basis rows had
unit last coordinate. Integer feasibility was verified, so this is NOT
an infeasibility result. A Bezout combination would be needed to construct
a monic specialization from that basis. The degree-six feasibility search
was stopped before producing a result; no claim is made for that degree.
The four retained values were independently certified to have absolute
value greater than one. Higher attainable vanishing order did not control
the heights of these selected solutions.

A lower-order comparison, `/tmp/lambert_monic_at_one_lower.py`, retains the
same M=2D and uses N in {floor(D^2/2), the earlier constant-monic maximum}.
Completed cases for D=2,...,6, using the FLINT computed integer kernel:

    D | N  | height bits | diagnostic log2 |Q(alpha)|
    2 |  2 |           1 |  0.652
    2 |  5 |           1 |  0.652
    3 |  4 |           1 |  0.978
    3 | 13 |          10 |  6.244
    4 |  8 |           1 |  1.304
    4 | 19 |          14 |  6.946
    5 | 12 |           1 |  1.630
    5 | 23 |          13 |  8.205
    6 | 18 |           1 |  1.956
    6 | 41 |          48 | 26.912

Each height-one entry specializes to X^D. All ten selected values were
independently certified above one in absolute value. These are not value
minimizers and do not exclude other choices in the affine lattices.
The degree-seven computation was stopped before retaining a result.
An earlier run with Sage's default echelon integer kernel encountered a
PARI stack overflow at (D,N)=(5,23); it was rerun successfully for the
completed cases using `right_kernel_matrix(algorithm='flint',
basis='computed')` on the transpose. The earlier partial log and JSON have
the suffix `_pari`; they are not the final comparison table.

The .log and .json files have the same basenames as their scripts. The
independent audit `/tmp/lambert_monic_audit.py` rechecks every retained
coefficient vector against all factorial-scaled jet equations, checks
Q is monic, and re-evaluates its value with exact rational intervals using
W=1500!. Its output is `/tmp/lambert_monic_audit.log`. It checked 15 removed-
row forms (eight monomials below one, seven forms above one), four maximum-
jet specialization forms, and ten lower-jet specialization forms. The
last two groups all have absolute value above one. Floating-point logs in
the tables are diagnostics only.

`MonicPolynomialCriterion.lean` was recompiled successfully, with only the
three permitted axioms in its printed audits. No new Lean theorem settling
the original conjecture has been obtained. All computations mentioned in
this update have finished or been stopped. Spec.lean remains unchanged with
its original sorry, and no proof or disproof has been submitted.
