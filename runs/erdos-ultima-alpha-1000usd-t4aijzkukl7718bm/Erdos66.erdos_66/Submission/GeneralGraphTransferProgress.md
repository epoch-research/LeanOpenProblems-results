# General graph transfer, interpolation, and finite patching

## Original task status

The original conjecture remains neither proved nor disproved.
`Submission/Spec.lean` is unchanged and still contains its original `sorry`.
No proof submission has been made. None of the following finite results is
being asserted as a solution of Erdős 66.

## Completed and checked files

1. `TranslatedGraphPartitionExplore.lean`
2. `UniformGraphColorTransferExplore.lean`
3. `QuarticGraphExplore.lean`
4. `EvenPolynomialGraphExplore.lean`
5. `BoundedGraphInterpolationExplore.lean`
6. `AnchoredGraphColorTransferExplore.lean`
7. `HistogramPatchExplore.lean`
8. `GraphPatchExplore.lean`
9. `PatchedGraphSetExplore.lean`

All nine compile and have current oleans. `GeneralGraphTransferAudit.lean`
audits 44 declarations. Its output, saved in `GeneralGraphTransferAudit.log`,
contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Graph-independent color selection

Vertical translates of an arbitrary graph f:F->F form a complete disjoint
partition of F^2. Write n=|F| and

    sumCoeff(f,u;t,s) = #{x : f(x)+f(t-x)=s-u}.

If every sum fiber has size at most D, the weighted graph sum satisfies

    graphSum(f,V;t,s)^2 <= D^2 n energy(label-sums,V).

The constant-kernel sum is exactly n^2, for EVERY graph. Thus the same
centered color energy controls every later graph; the coloring can be chosen
before the graph and its bound D.

For a finite family of symmetric coarse kernels K_k, nonnegative weights w_k,
and

    Budget = sum_k w_k (8 n^2 var(K_k) + 2 n diag(K_k)),

one coloring gives

    w_k error(f,k;t,s)^2 <= D^2 n Budget

for every later bounded-sum graph and all fine targets. The actual-set
version uses disjoint fine graph slices; coarse color sets can overlap.

## Polynomial examples and finite anchoring

For odd characteristic, x^4+x has every sum fiber bounded by four. In
characteristic other than 2 or 3, no one horizontal reflection preserves
its graph. This does NOT assert that every selected row of every union of
translates lacks reflection symmetry.

More generally, a positive even-degree polynomial has every sum fiber
bounded by its degree in odd characteristic. Arbitrary values on a finite
column set T admit a monic interpolant of degree 2(|T|+1), giving that bound.
One coloring chosen beforehand therefore accommodates all such later data,
with actual-set error-squared factor [2(|T|+1)]^2 n Budget.

This preserves reference GRAPH columns, not arbitrary Boolean subsets of
the plane. Constant values prescribed on a reflection-closed T force a sum
fiber of size at least |T|, so arbitrary prescriptions cannot have a bound
independent of |T|.

## Sharper finite patching

For finite maps differing only on T, the histogram changes obey

    sum_q |hist_f(q)-hist_g(q)| <= 2|T|,
    sum_q (hist_f(q)-hist_g(q))^2 <= 4|T|^2.

For graph functions agreeing off T, their pair maps

    x -> s-(f(x)+f(t-x))

can differ only on T union (t-T), of cardinality at most 2|T|. Consequently

    sum_q |sumCoeff_f(q)-sumCoeff_g(q)| <= 4|T|,
    sum_q (sumCoeff_f(q)-sumCoeff_g(q))^2 <= 16|T|^2.

Cauchy--Schwarz with the SAME graph-independent label energy gives

    (graphSum_f(V)-graphSum_g(V))^2 <= 16|T|^2 energy(V).

Combining this with a base graph of fiber bound D yields

    error_g(K)^2 <= (2 D^2 n + 32|T|^2) colorEnergy(K).

Thus one coloring, chosen before the base graph and before arbitrary finite
patch data, gives the actual-set estimate

    w_k error_g,k^2 <= (2 D^2 n + 32|T|^2) Budget.

`exists_actual_patched_graph_budget` uses the canonical patch

    g_patch(x) = if x in T then prescribed(x) else f(x).

It proves exact actual-set agreement with the prescription on T and exact
agreement with the base off T. The additive patch coefficient avoids the
extra field-cardinality factor that would result from treating the patch
only as a graph with fiber bound D+2|T|.

## Quantitative and infinite limitations

For a single kernel of mean mu, variance comparable to mu, and target mean
M=n^2 mu, the base contribution to the current relative squared-error bound
is of order D^2 n/M. The patch contribution is of order |T|^2/M. In particular,
this estimate does not establish vanishing relative error when the fine
field size greatly exceeds the logarithmic target mean. These are limitations
of the available bound, NOT lower bounds on actual errors of all sets.

A small fine field could avoid that numerical loss, but the finite-family
coarse budget would still need to be controlled uniformly over an infinite
tail. No such coarse construction has been proved. Choosing one coloring
before all later graphs does not remove the coarse-target quantifiers.

Finite-column agreement also does not supply estimates at all intermediate
natural-number scales, and does not prove that the threshold function in
`Erdos66Compactness.conjecture_iff_finite_prefixes` can be selected independently
of the final cutoff. The existing same-modulus, integer-prefix, and
probabilistic partial results have not been combined into that missing
uniform feasibility theorem. No universal obstruction negating the original
existential statement has been established either.

## Subsequent update: universal complete-partition transfer

UniversalCompleteProgress.md records a checked matrix-basis argument removing
the finite coarse-target budget. One coloring now precedes all later real
kernels, graphs, patches, and infinite coarse families. The bound retains an
unnormalized centered matrix norm and explicit color-dimension losses. It
still does not construct the coarse profile or compatible changing moduli.
