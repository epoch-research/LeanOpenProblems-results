# Diagonal Padé investigation (not a proof)

Let

    f(z) = sum_{k>=0} z^k / ((k+2)!-1),
    alpha = f(1).

For degree n, set Q(0)=1 and solve the usual [n/n] Padé equations

    sum_{j=0}^n Q_j c_{k-j} = 0,  k=n+1,...,2n,
    c_k = 1/((k+2)!-1).

Then P_k = sum_{j=0}^{min(k,n)} Q_j c_{k-j}, and P(1)/Q(1)
is a rational approximation to alpha. The linear systems and reduced
rational approximants were computed with exact SymPy rational arithmetic.
The errors below were estimated with 100-decimal-digit mpmath arithmetic;
they are diagnostics, not Lean certificates or rigorous error bounds.

    degree | reduced denominator bits | log10(abs(den*alpha-num))
         1 |                        7 |                 -0.732565
         2 |                       17 |                  0.840056
         3 |                       75 |                 15.455235
         4 |                      161 |                 38.608591
         5 |                      319 |                 83.216964
         6 |                      561 |                154.722625
         7 |                      930 |                260.160637
         8 |                     1421 |                406.350089
         9 |                     2089 |                605.954353
        10 |                     2962 |                862.725746

Thus this particular approximation family has not supplied small scaled
errors suitable for an integer-linear-form argument. These finite tests
do not establish an asymptotic theorem, and do not rule out a different
Padé, continued-fraction, or auxiliary-function construction.

No proof or disproof of the target follows. Submission/Spec.lean remains
unchanged.

## Distinct test: Padé approximants of the factorial Lambert regrouping

The previous table uses coefficients 1/((k+2)!-1). A different function is

    F(z) = sum_(d>=2) z^d/(d!-z^d),
    G(z) = F(z)/z^2,
    c_k = sum_(d | k+2, d>=2) 1/(d!)^((k+2)/d).

Thus G(1)=alpha, and c_k=A_(k+2)/(k+2)!, with the verified Lambert
coefficients. These rational coefficient denominators are substantially
smaller than those of the previous function. The same diagonal Padé
construction was tested separately for G.

    degree | reduced denominator bits | log10(abs(den*alpha-num))
         1 |                        5 |                 1.244598
         2 |                       13 |                 2.716845
         3 |                       32 |                 7.606173
         4 |                       51 |                13.274747
         5 |                       84 |                21.957737
         6 |                      119 |                32.508646
         7 |                      164 |                44.424850
         8 |                      213 |                59.338989
         9 |                      275 |                76.740329
        10 |                      341 |                95.989463
        11 |                      419 |               118.788640
        12 |                      504 |               141.934745

The errors have positive sign except at degrees 9 and 12. The logarithms
are numerical diagnostics, but the weaker assertion abs(den*alpha-num)>1
was checked separately using exact rational arithmetic at all twelve
degrees. The exact computation uses

    L = sum_(k=2)^40 1/(k!-1),
    L < alpha < L + 2/(41!-1),

and verifies that the rational interval

    [den*L-num, den*(L+2/(41!-1))-num]

lies entirely outside [-1,1]. The displayed enclosure of alpha follows
from the positive tail and the elementary ratio bound for successive terms.

The scripts are /tmp/lambert_pade_test.py (floating-point diagnostics) and
/tmp/lambert_pade_exact.py (exact rational check). Reduced numerators and
denominators are saved in /tmp/lambert_pade_exact.json. These new finite
checks have NOT been formalized in Lean. They do not give an asymptotic
impossibility theorem and do not settle the conjecture.


## Further distinct test: finite Stieltjes moment Padé approximation

Define

    H_N(z) = sum_(k=2)^N 1/(k!-z),
    c_j(N) = sum_(k=2)^N 1/(k!)^(j+1).

The c_j(N) are rational, with denominator dividing (N!)^(j+1).
The infinite-row moments would instead be the irrational factorial-power
constants; they must not be treated as rational coefficients.

For m>=1, the [m-1/m] approximant used here has Q(0)=1 and satisfies

    sum_(j=0)^m Q_j c_(k-j)(N) = 0,  k=m,...,2m-1,

omitting terms with negative subscripts. Its numerator has degree at most
m-1. Evaluate P(1)/Q(1) and reduce the resulting rational a/b.

The following finite checks use exact rational arithmetic for the Padé
systems and for enclosure of b*alpha-a. The decimal logarithms are only
diagnostics. The interval certificates use

    L = sum_(k=2)^50 1/(k!-1),
    L < alpha < L + 2/(51!-1).

For every listed case except (m,N)=(1,3), the exact interval for b*alpha-a
is disjoint from [-1,1]. For (1,3), it lies inside (-1,1).

    m | N  | reduced denominator bits | log10(abs(b*alpha-a)), diagnostic
    1 |  3 |    3 |  -0.110983
    1 |  4 |    8 |   1.314166
    2 |  4 |   12 |   1.626099
    2 |  6 |   39 |   8.670219
    3 |  5 |   37 |   8.148946
    3 |  8 |  125 |  31.914924
    4 |  6 |   84 |  21.463994
    4 | 10 |  308 |  84.966293
    5 |  7 |  146 |  39.226942
    5 | 12 |  610 | 173.583243
    6 |  8 |  237 |  65.738273
    6 | 14 | 1071 | 310.122474
    7 |  9 |  400 | 113.817413
    7 | 16 | 1753 | 512.921387
    8 | 10 |  605 | 174.418135
    8 | 18 | 2661 | 783.833576

Artifacts: /tmp/stieltjes_factorial_pade.py and
/tmp/stieltjes_factorial_pade.json. These computations have not been
formalized in Lean. They prove no asymptotic impossibility result and do
not settle the target. Submission/Spec.lean is unchanged.

## Further distinct test: Weniger delta-type transformation

For S_t=sum_(n=2)^t 1/(n!-1), start s and order k>=1, set

    w_j = (-1)^j choose(k,j) (s+j+1)_(k-1) ((s+j+1)!-1),
    R_(s,k) = (sum_(j=0)^k w_j S_(s+j)) / (sum_(j=0)^k w_j),

where (x)_m is the rising factorial. This uses the next omitted term as
remainder estimate. It is not the earlier diagonal power-series Padé family.
After reducing R=a/b, the same integer-linear-form diagnostic is |b*alpha-a|.

The 36 cases s in {2,5,10}, 1<=k<=12 were calculated using exact rational
arithmetic. Every case except (s,k)=(2,1) has its exact enclosure for b*alpha-a
outside [-1,1]. The exceptional enclosure is inside (-1,1). The enclosure is
based on

    L=sum_(n=2)^64 1/(n!-1),
    L < alpha < L+2/(65!-1).

Selected diagnostics (decimal logarithms are only numerical diagnostics):

    start | order | denominator bits | log10 |b*alpha-a|
        2 |     1 |                7 |        -0.732565
        2 |     4 |               35 |         2.681762
        2 |     8 |              113 |        20.858663
        2 |    12 |              252 |        55.451213
        5 |     1 |               31 |         3.943889
        5 |    12 |              386 |        91.431335
       10 |     1 |              120 |        25.311494
       10 |    12 |              709 |       178.475496

Artifacts: /tmp/weniger_factorial_test.py and
/tmp/weniger_factorial_test.json. These external checks are not Lean-verified,
prove no asymptotic obstruction, and do not settle the conjecture. Spec.lean
is unchanged.

## Nonlinear test: quadratic Hermite–Padé forms

This is a distinct construction, with quadratic rather than linear forms in
alpha. It has not yielded a proof. The calculations described here use exact
rational arithmetic externally; they are **not Lean-verified**.

For each N=1,...,6, construct polynomials P_0(z), P_1(z), P_2(z) of degree at
most N, not all zero, such that

    P_0(z) + P_1(z) f(z) + P_2(z) f(z)^2

has zero coefficients in degrees 0,...,3N+1. There are 3N+3 unknown
coefficients and 3N+2 equations. In every completed case the exact nullspace
had dimension one. Evaluate the three polynomials at z=1 and clear and
reduce their denominators together, obtaining a primitive integer quadratic

    Q_N(X) = a_0 + a_1 X + a_2 X^2.

Two different series f were used:

* Direct: f(z)=sum_(k>=0) z^k/((k+2)!-1).
* Lambert: f(z)=sum_(d>=2) z^(d-2)/(d!-z^d).

Both have f(1)=alpha. In all twelve completed cases, a_2 is nonzero and the
integer discriminant is not a nonnegative square. Thus none of these
quadratics has a rational root. This is the useful nonvanishing property
that would distinguish such forms from arbitrary Dirichlet approximations.

However, **all twelve exact enclosures for Q_N(alpha) lie outside [-1,1]**.
The small analytic remainder has been lost upon integer coefficient clearing.
The enclosures use

    L=sum_(k=2)^100 1/(k!-1),
    L < alpha < U=L+2/(101!-1).

The polynomial range on [L,U] is enclosed exactly by its endpoint values,
including its vertex value if the vertex lies in [L,U]. The following
logarithms are only diagnostics, not the certificates themselves:

    family  | N | largest coefficient bits | log10(abs(Q_N(alpha)))
    direct  | 1 |                       28 |                 3.912
    direct  | 3 |                      418 |               114.244
    direct  | 6 |                     3305 |               971.104
    Lambert | 1 |                       20 |                 5.536
    Lambert | 3 |                      106 |                28.966
    Lambert | 6 |                      403 |               115.455

If one could instead construct rational-root-free integer quadratics with
Q_N(alpha) tending to zero, rationality alpha=p/q would force the nonzero
integers q^2 Q_N(alpha) to tend to zero, a contradiction. The tested families
provide no such convergence result. These finite checks also do not prove
an asymptotic impossibility theorem for these or other nonlinear forms.

Artifacts: `/tmp/quadratic_factorial_hermite.py` and
`/tmp/quadratic_factorial_hermite.json`, with separate direct and Lambert
logs and JSON copies. The initial attempt at direct degree 7 was interrupted;
no result for that degree is claimed. There is no related process still
running. Spec.lean is unchanged and the target remains unsettled.

## Factorial-scaled-tail interpolation with leading-degree cancellation

This is another exact rational approximation experiment, not a Lean theorem
and not a solution. It specifically uses the unrestricted rational polynomial
kernels developed in RationalKernelForms.lean, so no unnecessary clearing of
all polynomial coefficients is imposed.

Let S_1=0 and S_n=sum_(k=2)^n 1/(k!-1). Interpolate the values

    H(n)=n!*(B-S_n),  n=1,...,N.

They force all kernel rows 2,...,N to vanish and H(1)=B. Require the
interpolant's highest-degree coefficient to vanish. With

    w_(N,n)=(-1)^(N-n) choose(N-1,n-1) n!,
    D_N=sum_(n=1)^N w_(N,n),

this gives the rational boundary

    B_N=(sum_(n=1)^N w_(N,n)*S_n)/D_N.

Thus the degree is at most N-2, rather than the generic N-1. This condition
is the vanishing of the (N-1)-st forward difference of the nodal values.
Only the reduced denominator of B_N is used below.

For N=2,...,25 the values and error intervals were computed externally using
Python fractions.Fraction. The interval for b*alpha-a, where B_N=a/b is
reduced, uses L=S_100 and U=L+2/(101!-1). All cases 3<=N<=25 have their exact
interval disjoint from [-1,1]. N=2 gives B_2=2 and error in (-1,0).
The signs alternate in this finite range; no infinite sign assertion is made.

Selected results (logarithms are diagnostics only):

    N | reduced denominator bits | log10(abs(b*alpha-a))
    3 |                        4 |                  0.448
    5 |                       18 |                  3.021
   10 |                       98 |                 22.476
   15 |                      264 |                 66.835
   20 |                      546 |                145.255
   25 |                      933 |                255.057

Artifacts: /tmp/factorial_tail_interpolation.py and
/tmp/factorial_tail_interpolation.json (including exact rational enclosures).
These computations do not prove an asymptotic obstruction and do not settle
Erdős 68. No proof or disproof has been submitted; Spec.lean is unchanged.

## Joint type-II Padé systems for the factorial-power columns

These exact external computations test a common-denominator construction,
not a proof of the target. No related new Lean theorem is asserted.

For j=1,...,J define

    F_(j,r)(z)=sum_(n>=0) n^r z^(jn)/(n!)^j,

where n^0=1, including n=0. Two systems were tested: just r=0, and the full
list 0<=r<j. For d functions and an integer m>=1 set L=d*m. Choose a common
Q of degree at most L so that each Q*F-P has zero coefficients in degrees
L+1,...,L+m, with each P of degree at most L. The linear nullspace is computed
over Q. When it is one-dimensional and Q(1)!=0, form the reduced rational
approximation

    R=(sum_(j=1)^J P_(j,0)(1))/Q(1)-2J

to beta_J=sum_(j=1)^J sum_(n>=2) 1/(n!)^j. Only the reduced denominator of
this aggregate R is used for the error test.

Completed systems:

* r=0 only: J=1,2,3 and m=1,...,5;
* full r-list: J=2 and m=1,...,5;
* full r-list: J=3,m=1 has nullity two (no distinguished approximant chosen);
* full r-list: J=3,m=2 has nullity one and was evaluated.

The full J=3,m=3 calculation timed out; no result is claimed for it or for
later full J=3 orders. No process remains running.

The J=1 systems recover useful Padé approximation of exp(1)-2: their scaled
errors are in (-1,1) and decrease in magnitude through the tested range.
For J>1, every completed case with m>=2 has its exact scaled-error interval
outside [-1,1]. This includes the full derivative systems. The m=1 cases
with a one-dimensional nullspace have scaled error in (-1,1), but this gives
no asymptotic family.

Error certification uses

    L0=sum_(n=2)^120 sum_(j=1)^J 1/(n!)^j,
    L0<beta_J<L0+2J/(121!).

All interval endpoints and the approximants are rational and computed with
exact arithmetic. The decimal logarithms in the output are diagnostic only.
These forms approximate beta_J, not alpha; controlling the omitted columns
would be a further requirement even if a useful family for beta_J were found.

Artifacts: /tmp/joint_factorial_pade.py and /tmp/joint_factorial_pade.json.
These finite failures prove no asymptotic obstruction. Spec.lean is unchanged,
and the original conjecture is still unproved and undisproved in this work.

## Interpolation at reciprocal-factorial nodes

This is a separate exact external calculation, not a Lean proof. The
construction specializes the rational telescoping kernels to constant H_j,
equivalently to a single polynomial in the reciprocal factorial.

Put x_n=1/n!, S_1=0, and S_n=sum_(k=2)^n 1/(k!-1). For any polynomial H
with H(0)=0, the row differences telescope to H(1):

    sum_(n>=2) [H(x_(n-1))-H(x_n)] = H(1).

Consequently row cancellation through n=N is equivalent to
H(x_n)=B-S_n for n=1,...,N, with B=H(1). Require

    H(X)=X^r Q(X),   deg Q<=N-2,   r>=1.

The vanishing leading divided difference for Q gives

    w_n = (n!)^(N+r-2) / product_(1<=k<=N,k!=n)(n!-k!),
    B_(N,r) = [sum_(n=1)^N w_n S_n] / [sum_(n=1)^N w_n].

The common factor omitted from the divided-difference weights cancels in
this ratio. For r=1 the denominator sum is 1; for r=2 it is sum n!.
More generally it is the complete homogeneous symmetric polynomial of
degree r-1 in 1!,...,N!, so it is positive. This formula is mathematical
reasoning, not a Lean-verified interpolation theorem.

The script /tmp/reciprocal_factorial_interpolation.py evaluates the formula
with fractions.Fraction for r=1,2,3 and 2<=N<=20. For reduced B=a/b it uses

    L=S_100, U=L+2/(101!-1),
    b*L-a < b*alpha-a < b*U-a.

Only b, the reduced denominator of B, is cleared. Every completed case with
3<=N<=20 has its exact error interval outside [-1,1]. All three N=2 cases
have error in (-1,1), but this gives no infinite family. For r=1 the error
is positive at N=3 and negative at every tested N>=4; for r=2,3 it is
positive throughout the tested N>=3 range.

Selected diagnostics (decimal logs are not the certificates):

    r | N  | reduced denominator bits | log10(abs(b*alpha-a))
    1 | 10 |                      394 |  109.761896
    1 | 20 |                     4287 | 1269.432753
    2 | 10 |                      422 |  119.260361
    2 | 20 |                     4351 | 1290.047154
    3 | 10 |                      441 |  125.026760
    3 | 20 |                     4416 | 1309.649149

Exact approximants and interval endpoints are stored in
/tmp/reciprocal_factorial_interpolation.json. No asymptotic impossibility
claim follows from this finite test. This attempt has not supplied a proof
or disproof, and Submission/Spec.lean is unchanged.

## Review of moment-based denominator cancellation

A subsequent review found no additional integer-form construction here.
The exact infinite Stieltjes moments of sum_(n>=2) 1/(n!-z) are the
factorial-power constants E_(j+1), not rational numbers. Their replacement
by finite-row moments leads to the finite systems already tested above.
For lower Stieltjes approximants, the omitted positive row tail remains
part of the error; a small quadrature error for the finite-row function
alone therefore does not bound the error against alpha by that quadrature
error. Expanding a finite-row transform at infinity gives integer moments
sum_(n=2)^N (n!)^j, but these moments diverge as N tends to infinity and
cannot be used as coefficients of the infinite transform.

No asymptotic denominator/error bound, infinite carry-change theorem, or
complete proof/disproof has been obtained from this review. This is not a
new Lean-verified result. The original Spec.lean remains unchanged.
