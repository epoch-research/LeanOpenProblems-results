# Actual near-linear subsets with bounded difference multiplicity

This does NOT settle Erdős 773. The required Sidon multiplicity is one;
the new bound depends on the exponent loss and can be larger than one.
`Spec.lean` remains unchanged with its sole admission for 0 < epsilon <= 1/3.

## Verified theorem

`BoundedDifferenceSelection.lean` proves, in namespace
`Erdos773.BoundedDifferenceSelection`:

    near_linear_bounded_differences

For every real epsilon>0, there is a natural g such that, for all sufficiently
large N, an actual finite set A subset [1,N] satisfies

    |A| >= N^(1-epsilon),

and, for every positive D,

    #{(a,b) in A x A : a<b and b^2=a^2+D} <= g.

Thus the selected vertices are integral, unlike the earlier fractional
relaxation. However, this is a relaxed capacity condition, not Sidon itself.
There is no claim that this A has a Sidon subset of comparable size.

## Finite selection argument

Work first with the root vertices `Fin N`, mapped to naturals by a -> a+1.
For a fixed positive difference, the larger endpoint determines the smaller
one. Therefore k distinct representations have k distinct larger endpoints;
the least smaller endpoint is not among these. Their union contains at least
k+1 roots. This also covers representations sharing a root (square APs),
without incorrectly assuming that all representation pairs are disjoint.

For a fixed g, declare the union of any g+1 representations of a common
positive difference to be forbidden. Every such union has at least g+2
vertices. If each difference has at most K representations, the number of
forbidden supports is at most

    N^2 * K^(g+1).

Here the positive differences range over [1,N^2], and the estimate
`choose(r,g+1) <= r^(g+1)` bounds each family. Bernoulli alteration gives an
actual selected set B with all capacities at most g and

    |B| >= p*N - N^2*K^(g+1)*p^(g+2).

The proof then transfers B injectively to the natural roots. It verifies the
capacity condition for EVERY positive difference, including D>N^2, for which
there are no representations.

## Asymptotic parameters

Choose a natural g>4/epsilon, and put

    p = N^(-epsilon/2),
    K = N^(epsilon/4),
    rho = epsilon*(g+1)/4 - 1 > 0.

The existing divisor estimate eventually bounds every representation count
by K. With S=N^(1-epsilon/2), the deletion term is exactly S*N^(-rho).
Eventually it is at most S/2; the desired N^(1-epsilon) is also at most S/2.
This proves the displayed cardinality bound without a remaining constant
factor.

## Audit and scope

The file imports only the already verified `Hypergraph` and
`FractionalSquareSidon` modules, not the admitted `Spec` theorem. It has no
admissions or new axioms, and compiles without warnings. The axiom audit of
`near_linear_bounded_differences` reports exactly

    propext, Classical.choice, Quot.sound.

Build log: `/tmp/bounded-difference-selection.log`.

This is a positive integral relaxed-selection theorem. It neither improves
the known exponent for actual Sidon subsets nor supplies a fixed-power upper
bound disproving the conjecture. The outstanding step is still multiplicity
ONE with a near-linear number of roots. No proof submission was made.
