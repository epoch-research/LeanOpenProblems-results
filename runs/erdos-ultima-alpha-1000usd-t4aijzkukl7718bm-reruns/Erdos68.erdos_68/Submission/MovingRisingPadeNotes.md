# Moving factorial parameters in rising-tail Padé forms

This is an external exact construction and independent audit, NOT a Lean
proof or a settlement of Erdős 68. `Spec.lean` is unchanged with its original
`sorry`. No complete proof or disproof has been obtained or submitted.

## Two-parameter tail representation

For A a positive integer define monic integer polynomials

    R_(A,k)(w)=product_(j=1)^k (w+A*j)-A^(k-1),   k>=1,
    U_A(w)=sum_(k>=1) A^(k-1)/R_(A,k)(w).

At A=N!, w=A*N, with N>=1,

    U_A(w)=alpha-S_N,  S_N=sum_(d=2)^N 1/(d!-1).

Indeed R_(A,k)(A*N)=A^(k-1)*((N+k)!-1). The series at this evaluation
point is exactly the original convergent tail.

For any integer polynomial P of degree M, monic division gives

    P=R_(A,k)*Q_k+T_k.

All Q_k,T_k have integer coefficients, and Q_k=0 for k>M. Therefore

    P(w)*(alpha-S_N)-B
      =sum_(k>=1) A^(k-1)*T_k(w)/R_(A,k)(w),
    B=sum_(k=1)^M A^(k-1)*Q_k(w) in Z.

This is an integer-boundary identity for the TAIL, not automatically an
integer-boundary identity for alpha: the finite rational prefix S_N must
still be included. The test includes it and reduces the final rational
candidate completely. The general identity is explanatory mathematics in
this note; it was not separately formalized in a new Lean file.

This differs from the previously tested fixed-parameter rising expansions.
The cases N=1 and N=2 overlap some earlier fixed evaluations, while the
larger values move both the factorial parameter and the evaluation point.

## Exact Padé construction

Write the formal Laurent expansion U_A(w)=sum_(r>=1) a_r(A)*w^(-r).
Each a_r(A) is an integer obtained from finitely many rows. For degree M,
choose a rational monic P=sum_(i=0)^M p_i*w^i satisfying

    sum_(i=0)^M p_i*a_(r+i)(A)=0,  1<=r<=M.

Clear and remove the polynomial coefficient content. At w=A*N calculate
its integer value and the integer boundary above, then reduce

    S_N+B/P(w)=a/b,  b>0.

No convergence of the Laurent series at the evaluation point is assumed.
Each candidate is checked against an enclosure of the FULL original sum.

## Completed finite test

Parameters:

    N in {1,2,3,4,6,8,12,16}, M=1,...,20.

All 160 systems were solved exactly. At (N,M)=(1,1), P(w)=0, so that
candidate is discarded. The other 159 have the following certified errors:

    2 in (0,1), 3 in (-1,0), 89 greater than 1, 65 less than -1.

The five small cases, listed as (N,M,a,b), are

    (1,2,11,9), (2,1,4,3), (2,2,164,131),
    (3,1,107,85), (4,1,548,437).

EVERY tested case with N>=6 has absolute error greater than one. For
orientation only, at (N,M)=(16,20) the primitive denominator has 6806 bits
and the diagnostic log2 of the error is about 6631.17. The classification
uses exact rational inequalities, not that diagnostic logarithm.

This finite failure is not an asymptotic impossibility theorem. It supplies
no useful growing sequence of nonzero small integer forms.

## Independent audit

Construction artifacts:

* /tmp/moving_rising_pade.py
* /tmp/moving_rising_pade.log
* /tmp/moving_rising_pade.json

The generator computes Laurent coefficients by reciprocal-series recurrence,
solves the rational Padé systems, and evaluates polynomial-part boundaries
from those coefficients. Its enclosure uses the factorial grid G=6000:

    W=G!, L=sum_(d=2)^G floor(W/(d!-1)),
    L/W < alpha < (L+G+2)/W.

Independent audit artifacts:

* /tmp/moving_rising_pade_audit.py
* /tmp/moving_rising_pade_audit.log

The audit uses ordinary Python integers and Fraction, not Sage matrix or
polynomial algorithms. It reconstructs every monic row polynomial and
performs polynomial division, checks each quotient/remainder identity,
reconstructs the integer boundary, verifies the vanishing Laurent
coefficients from the remainders, and checks the primitive rational pair.
It recomputes the full-target enclosure on the distinct grid G=6023,
verifies interval containment, and rechecks all 159 classifications.
All audits passed. Diagnostic infinities in an initial log were corrected
by computing logarithms from integer bit lengths; no sign or magnitude
classification ever depended on those logs. The rerun and audit completed.

No computation or compilation is pending. The original conjecture remains
unproved and undisproved in this workspace.
