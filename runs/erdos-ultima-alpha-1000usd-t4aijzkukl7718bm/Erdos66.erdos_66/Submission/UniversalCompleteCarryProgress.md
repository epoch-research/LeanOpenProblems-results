# Complete partitions through ordinary integer carries

## Original task status

The conjecture in Submission/Spec.lean is still neither proved nor disproved.
Its original import, statement, and sorry are unchanged. No proof submission
has been made. The results here are conditional fixed-field transfer results,
not a solution of the existential logarithmic-limit statement.

## Compiled production files

* UniversalCompleteCyclicExplore.lean
* UniversalCompleteNaturalExplore.lean

Both have current oleans. UniversalCompleteCarryAudit.lean audits eighteen
principal declarations; the saved log uses only propext, Classical.choice,
and Quot.sound. Neither production file contains a sorry or a new axiom.
A few unused-section-variable warnings remain harmless.

## Complete plane colors

Fix an odd prime p, rho:Fin p~ZMod p, and a finite nonempty color type alpha
of cardinality q. The previously selected universal coloring omega assigns
one color to each vertical translate of any later graph f. Define

    color(x,y)=omega(rho^-1(y-f(x))),
    P_a={(x,y):color(x,y)=a}.

The P_a form a COMPLETE disjoint partition of the field plane. Their mixed
counts are exactly the universal graph sum for the ordered indicator kernel
of (a,b). If f has sum fibers at most D and

    10 D^2 q^4 <= epsilon^2 p,

then simultaneously for all colors a,b and all fine targets,

    |r_(P_a,P_b)-p^2/q^2| <= epsilon p^2/q^2.

The coloring precedes f, D, epsilon, and all coarse data. The fourth-power
color cost is retained; no growing-alphabet loss is silently discarded.

## Cyclic thickening preserves completeness

Two-coordinate thickening by K sends a plane set to its inverse image under

    ZMod((pK)^2) -> (ZMod p)^2,

using the existing radix digit equivalence and coordinate reduction. Hence
it preserves both disjointness and complete coverage, not just mixed-count
bounds. The thickened colors Q_a have

    beta = K^2 p^2/q^2,
    eta = epsilon + 2(1+epsilon)/K,

and for all cyclic targets

    |r_(Q_a,Q_b)-beta| <= eta beta.

This uses the checked TWO carry-fiber formula, not an additive embedding of
the field plane into the cyclic group.

## Actual natural-number operator

Repeat the cyclic colors over L outer blocks, then let arbitrary infinite
coarse sets B_a choose the active colors in each block. Write

    M=(pK)^2, H=ML,
    w(k)=#{a:k in B_a},
    F(n)=sum_(k=0)^n w(k)w(n-k).

For every n>0, z in ZMod M, and outer digit 0<=r<L, the genuine natural set
A satisfies

    |r_A(nH+z.val+M r)
       - beta [r F(n)+(L-r)F(n-1)]|
      <= beta [L eta+1+eta] [F(n)+F(n-1)].

The theorem exists_universal_complete_natural chooses omega before ALL
later K,L, graphs, infinite coarse families, and natural targets meeting
the explicit hypotheses. There is no finite coarse-target budget.

Exact membership is also proved: the coarse quotient belongs to the coarse
set indexed by the uniquely determined fine color. If all coarse colors
are nonempty, every natural residue modulo H is attained. This is a full
projection statement, NOT asymptotic residue equidistribution.

Agreement of all coarse prefixes gives exact agreement of the corresponding
natural prefixes, with the graph, field, coloring, K, and L kept FIXED.
This is not a changing-operator compatibility theorem.

## What the scalar main term does and does not supply

The missing coarse profile is still an integer-weight convolution: w(k)
is the cardinality of a finite active-color set, not an arbitrary real
fractional profile. The existing analytic square-root profile cannot simply
be substituted for w.

The normalization is beta L=H/q^2. Thus a hypothetical coarse asymptotic
F(n)~a log n would give a leading natural coefficient H a/q^2, subject to
vanishing errors. Complete coverage does not automatically dilute arbitrary
coarse inputs to the required density.

Moreover, at fixed p and nonzero D the displayed sufficient condition does
not permit epsilon to tend to zero, and the fixed carry estimates retain
their K- and L-dependent errors. Choosing larger parameters independently
at each tolerance is NOT a proof of one infinite limit. An accurate coarse
source or a compatible changing-scale construction is still needed.

The subsequent conceptual review of sparse rounding and recursive routing
did not produce either of those missing ingredients or a universal
contradiction. In particular, no claim is made that the fixed-field routed
peak obstruction also excludes changing fields or point-dependent routing.

## Subsequent universal Bernstein refinement

UniversalBernsteinColorProgress.md records a checked eighteen-declaration
refinement: a finite mask list gives one coloring for all later nonnegative
kernels, with a quadratic-times-logarithmic leading alphabet cost and an
explicit range term. Actual infinite mixed counts and the same ordinary
natural carry operator are included. The coarse profile and changing-scale
compatibility remain unresolved; this is not a solution of Spec.lean.
