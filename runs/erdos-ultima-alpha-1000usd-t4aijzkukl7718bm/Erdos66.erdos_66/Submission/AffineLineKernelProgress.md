# A finite unit-mean affine-line lift

## Status

The original conjecture is still unresolved. Spec.lean is unchanged.
The two new production files compile:

* AffineLineKernelExplore.lean
* AffineLineAssemblyExplore.lean

Nine declarations are audited in AffineLineKernelAudit.log. Only propext,
Classical.choice, and Quot.sound occur.

## Exact finite kernel

Over an odd finite field F of size q, let

    L_u = {(x, u*x+u^2) : x in F}.

Different slopes have exactly one mixed representation at every target.
For equal slopes,

    r_(L_u,L_u)(x,y) = q if y=u*x+2*u^2, and 0 otherwise.

For every target (x,y), at most two slopes satisfy that equation.
For an arbitrary real matrix K, the checked weighted identity is

    sum_(u,v) K(u,v) r_(L_u,L_v)(x,y) - sum_(u,v) K(u,v)
      = q sum_(u: y=u*x+2*u^2) K(u,u) - sum_u K(u,u).

If 0<=K(u,u)<=g, the absolute error is at most 2qg. No off-diagonal
bound on K is needed.

## Actual assembled sets

Let A_u be pairwise disjoint color classes in any additive group G. Replace
each a in A_u by the fiber {a} x L_u. For the resulting set B,

    |r_B(t,(x,y))-r_A(t)| <= 2qg

whenever r_(A_u,A_u)(t)<=g for every u. Its cardinality is exactly q|A|.
If G is finite, the ambient cardinality grows by q^2, so

    |B|^2 / |G x F^2| = |A|^2 / |G|.

Thus this finite transfer does not have a hidden multiplicative mean cost.
It is a product-group identity, not a statement about ordinary integer
carries or a natural-number asymptotic.

## Missing properties

The translated lines do NOT preserve the old zero slice:

    (a,0,0) in B iff a in A_0.

This failure is explicitly proved as mem_lift_zero. Replacing the lines by
linear lines would keep that slice but would make all the parallel-pair
contributions concurrent at zero; the displayed two-slope estimate would
no longer hold there.

No iteration preserving the requisite color quality has been constructed.
A naive polynomial recoloring gives a growing mixed-count bound, not the
uniform bound needed for infinitely many steps. This recoloring observation
is mathematical review, not an additional theorem in these files.

Moreover, the existing SidonColorWitnessExplore theorem proves that a
hypothetical natural witness's long prefixes require order log N Sidon
colors. One cannot assume an order sqrt(log N) Sidon decomposition for
those prefixes. It would therefore be invalid to apply the new finite
error estimate to an infinite witness by silently postulating that coloring.

No compatible prefix-preserving natural lift, sublogarithmic quadratic
rounding, or negation of the original existential statement follows here.
