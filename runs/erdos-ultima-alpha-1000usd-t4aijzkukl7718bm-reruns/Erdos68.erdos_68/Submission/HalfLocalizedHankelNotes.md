# Half-integer-localized monic Hankel forms

This is an external exact finite construction and independent audit, NOT a
Lean theorem and NOT a settlement of Erdős 68. `Spec.lean` remains unchanged
with its original `sorry`. No complete proof or disproof was obtained.

## Construction

Put

    R_k(x)=(x+1)...(x+k)-1,
    P_N(x)=product_(j=1)^N (2*x+2*j+1),
    W_(K,N)(x)=P_N(x)*product_(k=5)^K R_k(x)^2.

The empty product at K=4 is one. For an arbitrary integer polynomial P,
use the integer prefix-adjusted boundary

    A(P)=13685*P(1),
    B(P)=13685*sum_(k=5)^(degree P) (P div R_k)(1)+17132*P(1).

The constants come from the exact prefix

    sum_(k=1)^4 1/R_k(1)=17132/13685.

The existing monic polynomial-division identity therefore gives

    A(P)*alpha-B(P)
      =13685*sum_(k>=5) (P mod R_k)(1)/R_k(1).

For i,j=0,...,m-1, form the matrix

    M(X)_(i,j)=13685*W_(K,N)(1)*X-B(W_(K,N)*x^(i+j)).

Every matrix entry has integer affine coefficients. Its X coefficient
matrix is a scalar multiple of the all-ones matrix, hence has rank one;
the determinant is affine with INTEGER coefficients, without any additional
termwise boundary-denominator clearing. Its primitive coefficient pair is
still computed by dividing the two coefficients by their gcd.

No positivity assertion for this whole growing matrix family is assumed.
Multiplying a half-integer kernel by an arbitrary square does not preserve
the previously proved row-positivity theorem. For example, at k=5,
P_1(x)*x^4=(2*x+5)*x^4 has quotient 2 on division by the monic R_5, and its
remainder at 1 is 7-2*719=-1431. This is an elementary explanatory identity,
not a separately packaged Lean theorem here.

## Parameters and exact results

The test uses

    K in {4,6,8}, m=2,...,12,
    N in {0,m,2m,m^2}, with duplicates removed.

All 129 cases completed:

* 79 primitive errors are greater than one;
* 46 primitive errors are less than minus one;
* 4 determinants are identically zero;
* there are no ambiguous interval classifications and no small nonzero forms.

The zero cases are

    (K,m,N)=(4,2,0),(4,2,2),(4,3,0),(4,4,0).

For every nonzero case the affine coefficient is nonzero. Thirty-two
full-target matrices are certified positive definite by the exact Schur
complement test, but all their primitive errors are also greater than one.

Selected diagnostics (not sign or magnitude certificate premises):

    K   m    N    primitive denominator bits   log2 absolute error upper
    4   2    4                 17                         3.178
    4   8   64               2791                      2740.901
    6   8   64               3017                      2939.609
    8  12  144              12836                     12734.682

These are finite failures only. They do not prove an asymptotic obstruction
for this family or exclude other localized matrix constructions.

## Construction and independent audit

Artifacts:

* `/tmp/half_localized_hankel.py`
* `/tmp/half_localized_hankel.log`
* `/tmp/half_localized_hankel.json`
* `/tmp/half_localized_hankel_audit.py`
* `/tmp/half_localized_hankel_audit.log`

The generator computes the boundaries from integer reciprocal Laurent
coefficients of sum_(k>=5) 1/R_k. This is finite formal-series arithmetic;
no convergence of the Laurent series at x=1 is assumed. It constructs
Sage integer matrices, checks the determinants at X=0,1,2, verifies the
rank-one Schur formula when the lower block is invertible, and reduces the
integer pair.

The independent audit uses Python/GMP integer and rational arithmetic,
not Sage polynomial or matrix algorithms. It reconstructs the polynomials,
divides each one by the monic row polynomials, and checks every quotient-
remainder identity. Quotients of successive x-multiples are updated from
their remainders. Thus it verifies all boundaries without the generator's
Laurent recurrence. A separate Bareiss implementation checks the determinants
at 0,1,2 and all lower-block principal minors. It also rechecks primitive
normalization, positive definiteness, and all interval classifications.

Both stages retain the FULL original sum using factorial-grid enclosures

    W=G!, L=sum_(d=2)^G floor(W/(d!-1)),
    L/W < alpha < (L+G+2)/W.

The generator uses G=6000; the audit uses G=6023 and verifies interval
containment. All 129 audits passed. Floating-point logarithms are diagnostics
only; exact rational inequalities determine every classification.

No process, audit, or compilation remains pending. No new Lean declaration
or submission check was made. The required small nonzero integer-form family
is still missing, and the original conjecture remains unresolved here.
