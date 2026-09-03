# Sparse deletion obstruction to a density-only argument

The original conjecture in `Spec.lean` remains unproved and undisproved. Its
statement and original `sorry` have not been changed.

## Checked result

`DyadicDeletionExplore.lean` defines `pruned A` by deleting the larger summand
of every representation of every target `2^k`. Thus

* `pruned A` is a subset of A;
* its representation counts never exceed those of A;
* `sumRep (pruned A) (2^k)=0` for every k.

If `r_A(n) <= K+C log(n+2)` with nonnegative K,C, then

    count A N - count (pruned A) N = O((log N)^2) = o(sqrt N).

Indeed, any deleted a<N comes from a target `2^k<=2a<2N`, and each target
requires at most `r_A(2^k)` deletions. Summing the logarithmic bound for
`k<=log_2(2N)` gives the displayed estimate.

Consequently all counting limits normalized by `sqrt(N log N)` are preserved.
If that counting limit is nonzero, the pruned representation ratio cannot
converge to ANY real constant: dyadic holes force a putative limit to zero,
while the cumulative representation/counting inequality contradicts the
nonzero counting limit.

Main results:
- `quadratic_log_bound`
- `discrepancy_div_sqrt_limit`
- `exists_same_density_and_holes`
- `witness_has_same_density_nonconvergent_subset`

All compile; the olean has been built. `DyadicDeletionAxiomCheck.lean` audits
the main results for the permitted axioms.

## Scope

This rules out the shortcut that a sharp counting profile plus an upper
representation envelope would force pointwise convergence. It is conditional
on the input set and is NOT a disproof of the original existential theorem.
A density-maximization approach would need an additional genuinely local
property (not merely the asymptotic counting constant).
