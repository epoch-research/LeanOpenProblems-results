# Explicit large-divisor block — not a settlement

Spec.lean remains unchanged with the original sorry. No proof of the
conjecture or irrational counterexample has been found. No incomplete
proof was submitted.

New file: ExplicitLargeDivisorBlock.lean.
Namespace: Erdos972ExplicitLargeDivisorBlock.
All three principal declarations compile and audit with only propext,
Classical.choice, and Quot.sound.

## Explicit parameter choice

Define

    blockStart(alpha,N,v) = floor(alpha*N)/v + 1

with NATURAL-number division after the floor.

`blockStart_bounds` proves, if alpha>=1, v>0, v<=N, v^2+2<=N and
alpha+1<v, that D=blockStart(alpha,N,v) satisfies

    0<D<N,
    floor(alpha*N)<=D*v,
    N<=D*v,
    alpha*v<D,
    D*v<=(alpha+1)*N.

`root64_square_add_two_le_sixth` verifies the quadratic-size condition for
N=u^6 and v=root64(u), once u>0 and v>=2.

## Actual centered dispersion estimate

`exists_explicit_large_block_dispersion` proves that for every alpha>1
irrational and B there are u>B and D, with u>0, such that

    N=u^6, v=root64(u), D=blockStart(alpha,N,v),
    0<D<N, N<=D*v, D*v<=(alpha+1)*N,

and, writing R_d for the actual prime-input divisor row,

    sum_{D<d<=2D} (R_d-psi(N)/d)^2
      <= N*v*((14*alpha+15)*log N+49).

Thus the earlier block conditions have been checked for a concrete block
starting strictly below N. This is an instantiation of the preceding
moment estimates, not a new signed cancellation theorem. In particular,
the interval (D,2D] need not be wholly below N; only D<N is asserted.

The proof uses the same actual irrational good scales as
LargeDivisorBlockMoment.lean. It does not assume an unproved prime-row
estimate.

## Remaining gap

The displayed upper energy still does not supply the strict signed lower
gap required by the four-factor reduction, nor a positive prime-pair count.
No claim is made that this upper energy is sharp or that stronger methods
cannot improve it. The original conjecture remains unresolved.
