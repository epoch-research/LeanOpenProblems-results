# Endpoint arithmetic for positive polynomial kernels

This is auxiliary progress, not a settlement. Spec.lean is unchanged and
still contains its original sorry. No proof or disproof has been submitted.

Both `PositiveKernelBoundary.lean` and `PositiveKernelUnitBoundary.lean`
compile without warnings and have built oleans. Every printed axiom audit
lists only propext, Classical.choice, and Quot.sound.

## Exact boundary formula

For the unshifted polynomial column operator

    L_j H(X) = X^(j+1) H(X-1) - H(X),

write Q=sum_(j=0)^(J-1) L_j H_j. The verified endpoint identity is

    B = sum_j H_j(1) = -Q(0)-Q(1).

If a single-square kernel has the polynomial identity

    Q(X) = J*A - R(X)^2,

then necessarily

    B = R(0)^2 + R(1)^2 - 2*J*A.

For the earlier two-variable ansatz, R(X) here is R(X,1). The file also
verifies the corresponding formula for an arbitrary finite sum of squares.
Thus only the two endpoint evaluations are needed for the aggregate
boundary; clearing all polynomial coefficients remains unnecessary.

## Local arithmetic restriction

The second file proves by a mod-four infinite descent that an integer
congruent to three modulo four cannot be a sum of two rational squares.
Consequently, for integral A and B in the single-square construction,

    B + 2*J*A is not congruent to 3 modulo 4.

In particular, if J is odd, A=1 and B=1 are impossible, regardless of the
polynomial degrees. This is `unit_boundary_ne_one`.

## Limitations

These identities supply no sequence of small nonzero forms. The mod-four
restriction applies to a single square, not automatically to an arbitrary
sum of squares: the endpoint expression then has more than two squares.
Nor does the restriction give an asymptotic lower bound on the necessary
integer coefficient A as J increases. Fixed A alone could not yield the
required irrationality sequence in any case, since B is integral.

Using rational positive-semidefinite Gram matrices instead of a single
square may avoid local quadratic-form obstructions. No construction with
controlled integral A,B and errors tending to zero has been obtained that
way. Positivity certificates for individual lower rational bounds would
not themselves prove irrationality.

There is no complete informal proof, pending successful construction, or
running computation. The original conjecture remains unproved and
undisproved in this work.
