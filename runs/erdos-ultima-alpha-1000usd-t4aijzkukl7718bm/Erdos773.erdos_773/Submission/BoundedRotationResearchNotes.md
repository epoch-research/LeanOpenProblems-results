# Polynomial-height square-graph realization

## Main conjecture remains UNSETTLED

Spec.lean is unchanged with its sole sorry at line 2031, for
0 < epsilon <= 1/3. The strongest actual asymptotic lower bound remains
M(N) >= N^(2/3)/500 eventually. No coefficient-one endpoint, exponent
improvement, or disproof has been obtained. No proof was submitted.

Spec SHA-256:
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14

## New quantitative result

The previously nonquantitative finite graph realization now has the bound

    every root <= 56*n^8+28,

for any graph on n core vertices. All previous relation-preservation,
positivity, injectivity, exact Sidon/independence equivalence, and legal
selection statements remain valid.

This is NOT a near-linear construction. For the complete graph there are
n^2-n selected square-Sidon roots, at the n^8 height scale. This 1/4-scale
finite construction is weaker than the existing asymptotic 2/3 lower bound.

## RotationFiniteGrid.lean

Namespace Erdos773.QuadraticRotationTrade.

- exists_grid_nonzero: a nonzero multivariate polynomial has a nonzero
  evaluation on S^n if its total degree is less than |S|. This is deduced
  from Mathlib's Schwartz-Zippel theorem, with the finite product cardinality
  and nonzero denominator handled explicitly.
- avoid_integer_grid: for nonzero polynomials P, each of total degree <=d,
  choose L>d|P|. There is an integer evaluation with every coordinate in
  [3L+1,4L] avoiding all of P. Apply the grid theorem to their nonzero product.
- root_card: the formal Root n type has exactly n^2 elements. Its bijection
  with Fin n x Fin n sends core a to (a,a), plus(a,b) to (a,b), and
  minus(a,b) to (b,a).
- poly_degree/value_degree/pair_difference_degree: the roots have degree
  <=1 and all differences of two pair-square sums have degree <=2.
- bounded_pair_specialization: there are at most (n^2)^4=n^8 nonzero
  pair-sum discrepancies. Taking L=2n^8+1 gives a relation-preserving
  integer evaluation on [3L+1,4L]^n.
- natRoot evaluates the roots directly in the naturals:

      core = 5*x_a,
      plus = 3*x_a+4*x_b,
      minus = 4*x_a-3*x_b.

  The grid bounds imply 4*x_a>3*x_b, so natural subtraction agrees with
  the formal rational subtraction and all roots are positive. Each root
  is at most 28L=56n^8+28. No denominator-clearing loss is needed here.
- bounded_integer_model supplies the positive injective model and the
  biconditional for EVERY pair-square relation, with the stated height.
- model_height_lower proves the elementary necessary height n^2<=N for
  any positive injective realization of all n^2 root labels below N.

The gap between n^2 and n^8 is real. No optimality assertion is made for
Schwartz-Zippel, and no n^(2+o(1)) specialization is proved.

## BoundedSquareGraphRealization.lean

Namespace Erdos773.SquareGraphRealization.

- realize_bounded transfers the bounded model to an arbitrary finite graph.
- selected_card: exactly 2|E| private vertices are selected.
- vertex_card: the carrier has n+2|E| vertices.
- complete_selected_card: for the complete graph the selected count is
  n^2-n, with total carrier cardinality n^2.
- sidon_set_below_height: an actual set A subset [1,56n^8+28] has |A|=2|E|
  and its square-value image is Sidon.

## Important scope refinement: these are late legal states

In the complete-graph model, reaching the prescribed residual graph requires
n^2-n selections out of n^2 carrier vertices. More generally there are two
private selected vertices per original edge. Thus the realization result
alone does NOT obstruct an early-time greedy estimate. It does not establish
that a bad spectral state occurs before a desired extraction horizon, or
with appreciable probability in any specified process.

The initial hypergraphs are still not claimed regular, and the carrier is
still a selected finite subset of positive roots, not the entire interval.
The old SquareGraphRealizationResearchNotes.md statements about absence of
ANY height bound are superseded by the new polynomial bound, but all its
other scope restrictions remain.

## Verification

Both modules compile cleanly and have oleans. All eleven printed main audits
use only propext, Classical.choice, Quot.sound. Neither imports admitted
Spec.lean. They contain no admissions or native_decide calls.

Fresh logs:

    /tmp/rotation-finite-grid-final.log
    /tmp/bounded-square-graph-final.log

Spec.lean and its sole import remain unchanged. Nothing incomplete was
submitted as a proof of the original conjecture.
