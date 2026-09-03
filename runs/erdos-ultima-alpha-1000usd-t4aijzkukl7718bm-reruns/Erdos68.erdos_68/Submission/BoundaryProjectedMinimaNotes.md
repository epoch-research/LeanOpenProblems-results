# Weight growth does not supply projected nonvanishing

This is a mathematical review, not a new Lean theorem or a settlement of
Erdős 68. Submission/Spec.lean remains unchanged with its original sorry.

## Proposed shortcut and its problem

In the boundary lattice, weights w map to a coefficient pair

    (A*sum(w_i), sum(w_i*B_i)).

A bound on the size of a weight vector is not a bound on its distance from
the zero-pair subspace. In particular, proving that the shortest weight vector
with a nonzero coefficient pair grows with the window would not, by itself,
force two independent projected pairs with errors tending to zero. Large
components along the zero-pair subspace can conceal a small projected step.
A successive-minimum argument must retain these projection/angle factors.

## Elementary rational example

Take N>=2, C=N^4, x=A=1, and three rational boundaries

    B_0=B_1=1-1/C,   B_2=1-N/C.

All row errors are positive and at most N/C=N^(-3). Integral boundary
clearing is exactly

    C divides w_0+w_1+N*w_2.

The vector (1,-1,0) is a short zero-pair vector. The vector (N,0,-1)
has the nonzero coefficient pair (N-1,N-1), whose value at x=1 is exactly
zero. Its norm grows with N.

More generally, suppose |w_i|<=Q, 2Q<N, and (N+2)Q<C. If the boundary is
integral, then the displayed divisible integer has absolute value below C,
so it equals zero. Consequently |N*w_2|=|w_0+w_1|<=2Q<N, whence w_2=0
and w_0+w_1=0. Every such bounded cleared vector therefore has zero pair.
For example Q=floor((N-1)/3) satisfies these bounds for N>=2 and tends to
infinity. Thus even the minimum weight size for a nonzero projected pair
can tend to infinity while the limiting number remains rational and there
are nonzero coefficient pairs of value zero.

This example does not model the exact Lambert boundaries. It only rejects
an inference based on weight-size growth alone. No applicable upper bound
on the final useful projected minima, or nonvanishing theorem for the actual
Lambert forms, was established in this review. Nothing has been submitted
as a proof or disproof of the original conjecture.
