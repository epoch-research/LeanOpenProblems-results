# Shifted Hankel determinants of the original partial-sum tails

This is an exact external construction test, NOT a Lean-verified theorem
and NOT a settlement of Erdős 68. Spec.lean is unchanged with its original
sorry. No proof or disproof has been obtained or submitted.

## Construction

Write S_h=sum_(k=2)^h 1/(k!-1), with S_1=0. For h>=1 and m>=2 consider

    D_(h,m)(X)=det_(0<=i,j<m)(X-S_(h+i+j)).

The X-dependent matrix has rank one, so this is affine in X. Put

    v_i=S_(h+i)-S_h                      (1<=i<m),
    C_(i,j)=-(S_(h+i+j)-S_(h+i)-S_(h+j)+S_h).

Subtracting the first row and column gives the block matrix with top-left
entry X-S_h, off-diagonal entries -v, and lower block C. When C is invertible,
its determinant vanishes at

    R=S_h+v^T C^(-1) v.

The experiment reduces R=B/A, A>0, and tests the FULL target error
A*alpha-B. It does not assume any general determinant sign or convergence
result. These use the original partial sums, not the distinct shifted
row-cancelled Lambert prefixes in ShiftedLambertHankelNotes.md. Some of
these parameters recover cases of the earlier direct Padé investigation.

## Exact finite results

Parameters:

    m=2,...,10,
    h in {1,2,m,2m,m^2}, duplicates removed.

All 43 lower blocks C are invertible. After full reduction:

* 19 errors are greater than one;
* 22 errors are less than minus one;
* (h,m)=(1,2) gives (A,B)=(4,5), with error in (0,1);
* (h,m)=(2,2) gives (A,B)=(90,113), with error in (-1,0);
* there are no ambiguous cases.

For example, at (h,m)=(100,10), A has 70719 bits and the diagnostic
base-two logarithm of the absolute error is approximately 70022. The
logarithm is not a certificate premise.

Certificates use N=10000, W=N!, and

    L=sum_(k=2)^N floor(W/(k!-1)),
    L/W < alpha < (L+N+2)/W.

All systems, fractions, and error comparisons use exact rational arithmetic.
The independent audit recomputes the full m-by-m determinant at X=0,1,2,
checks affinity, verifies that its leading coefficient is det(C), and
reconstructs its root without using the block solve. It also checks every
stored interval and independently verifies each classification using a
second factorial grid with N=10017. All 43 audits passed.

Artifacts:

* /tmp/original_tail_hankel.py
* /tmp/original_tail_hankel.log
* /tmp/original_tail_hankel.json
* /tmp/original_tail_hankel_audit.py
* /tmp/original_tail_hankel_audit.log

Both computations completed. No process remains running.

## Exact simplification at size two

As a mathematical identity (not a new Lean declaration), with d_n=n!-1,

    R_(h,2)=S_h+(1/d_(h+1))^2/(1/d_(h+1)-1/d_(h+2))
           =S_(h+1)+1/(d_(h+2)-d_(h+1))
           =S_(h+1)+1/((h+1)*(h+1)!).

Thus size two is just a simple corrected partial sum. Its small numerical
error alone does not control the reduced denominator, and two initial
small forms do not give an irrationality proof.

These finite failures are not an asymptotic impossibility theorem. No
infinite nonvanishing or non-stabilization result has been proved, and no
new Lean theorem resolving the original conjecture was produced in this
continuation.
