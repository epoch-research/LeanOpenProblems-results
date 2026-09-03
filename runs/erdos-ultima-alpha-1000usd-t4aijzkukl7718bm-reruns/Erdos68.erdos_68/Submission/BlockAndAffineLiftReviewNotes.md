# Block congruences and a geometric affine-lift obstruction

Informal mathematical review, NOT a new Lean theorem and NOT a settlement
of Erdős 68. Spec.lean remains unchanged with its original sorry.

## Block review

The least-prime-factor, prime-block, and combined omitted-column moduli
concern the exact original Lambert coefficients. Their factorial-scaled
tails are still too large for the available integer-tail criteria. The
rowwise-floor representation has small tails but does not inherit these
congruences. No CRT block construction closing both requirements was found.
No numerical search was performed in this review.

The new uniform filtered gcd bound and raw-boundary common-denominator
lower bound remain valid, but do not by themselves yield an inhomogeneous
lift with bounded weights and a prescribed nonzero weight sum.

## Why coprime differences and geometric growth are insufficient

Here is an elementary general example, not a model asserted to equal the
actual Lambert boundaries. Let integers B>=3, M>0, D>=2, and put

    R_j=M*B^j+j,  0<=j<=D.

The differences from R_0 have gcd one. Indeed, writing

    a=R_1-R_0=M*(B-1)+1,
    b=R_2-R_0=M*(B^2-1)+2,

one has b-(B+1)*a=-(B-1), and gcd(a,B-1)=1. The remaining differences
cannot increase the gcd. Consequently the integer affine equations

    sum_j w_j=1,   sum_j w_j*R_j=0

are feasible: use Bezout on the differences, then choose w_0 to enforce
the prescribed sum.

Nevertheless, no such solution can satisfy |w_j|<=Q and

    Q*D*(D+1)/2 < M.

For otherwise the second equation becomes

    M*sum_j w_j*B^j + sum_j j*w_j = 0,

and the second sum has absolute value strictly less than M. Since it is
an integer multiple of M, it must be zero, and hence sum_j w_j*B^j=0.
Reducing that equality modulo B-1 gives B-1 | sum_j w_j=1, impossible.

Thus even coefficients close to geometric growth, together with gcd-one
differences and affine feasibility, need not give dimension-root-sized
fixed-sum lifts. The example does not disprove such a bound for the actual
Lambert data, which would require a separate argument using their structure.

## Status

No new infinite nonvanishing statement, short useful lift, or complete
informal proof/disproof was obtained. No submission was made. The completed
Lean results from the preceding continuation are documented in
FilteredGcdUniformBoundNotes.md and remain auxiliary.
