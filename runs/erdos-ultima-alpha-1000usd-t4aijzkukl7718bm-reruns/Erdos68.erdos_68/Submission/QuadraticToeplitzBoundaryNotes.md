# Quadratic clearing of positive Toeplitz errors: unresolved

This is mathematical analysis, not a new Lean theorem and NOT a settlement
of Erdos 68. Spec.lean is unchanged with its original sorry. No proof or
disproof has been submitted in this continuation.

## Proposed alternative to determinant clearing

Use a geometric peak from TailDominantToeplitz.lean, so that for every D

    E_ij = s*(A*alpha-B_(H+|i-j|))

is positive definite, where s is 1 or -1, A is integral, and B_n is rational.
For a nonzero integer vector w, the quadratic form gives

    w^T E w = s*A*(sum w_i)^2*alpha
                - s*sum_(i,j) w_i*w_j*B_(H+|i-j|) > 0.

Thus it would suffice to find nonzero bounded integer vectors for which the
quadratic boundary is integral and the displayed positive value tends to
zero. This is a single quadratic congruence, rather than clearing every
matrix output or the affine determinant. No such family has been obtained.

If C clears the boundaries and b_k=C*B_k, the arithmetic condition is

    C divides sum_(i,j) w_i*w_j*b_(H+|i-j|).

The earlier linear pigeonhole lemma does not imply a small solution of this
quadratic congruence. Colliding quadratic residues gives an integral
DIFFERENCE of two quadratic values, which need not retain strict positivity.

## Why a dimension-only bound is insufficient

There is no general small-zero theorem of the form suggested merely by
counting C quadratic residue classes against (Q+1)^D vectors. For the form
sum_i w_i^2, if D*Q^2<C, every nonzero vector with |w_i|<=Q has value strictly
between zero and C, and therefore is not a zero modulo C. Increasing D does
not justify replacing this obstruction with the linear pigeonhole exponent.

There is also a rational comparison with the same basic Toeplitz positivity
and factorial boundary integrality. Take x=A=1 and

    f(n)=1/n!, B_n=1-f(n).

For H>=3 the Toeplitz matrix f(H+|i-j|) is strictly diagonally dominant:

    f(H+k)/f(H) <= (H+1)^(-k),
    sum_(j!=i) f(H+|i-j|) <= (2/H)*f(H) < f(H).

Its boundaries satisfy n!*B_n in Z, and the diagonal values tend to zero.
Nevertheless every nonzero integer w with integral quadratic boundary has

    w^T E w = (sum w_i)^2 - w^T B w

a strictly positive INTEGER, and hence at least one. These properties alone
therefore cannot establish the needed small quadratic forms. This is a
comparison sequence, not the actual Lambert tail and not a disproof of the
conjecture. No claim is made that it satisfies all the additional Lambert
row identities.

## Status

A quantitative short quadratic-congruence solution theorem for the ACTUAL
Lambert boundaries could still be useful. Neither the existing scalar
boundary lattice nor the Toeplitz positivity theorem supplies it. No such
new arithmetic estimate, infinite carry violation, or complete proof has
been obtained. No numerical search or compilation was run for this note.
