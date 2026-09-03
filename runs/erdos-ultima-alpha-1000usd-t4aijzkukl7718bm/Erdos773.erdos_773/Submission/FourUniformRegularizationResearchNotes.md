# Regularizing the four-uniform extraction problem

This is NOT a settlement of Erdős 773. The conjecture in Spec.lean is unchanged,
and no new actual Sidon exponent or endpoint has been established.

## New verified module

`FourUniformRegularization.lean` imports only the clean HypergraphDegreeTrim
module. It has a clean build, a built .olean, and eight printed axiom audits,
all using only propext, Classical.choice, and Quot.sound.

Let H be a four-uniform hypergraph on a finite type alpha. Suppose every
vertex degree is at most D, and every distinct pair has codegree at most
K, where K>=1. `exists_regularization_prime` constructs a prime p and a
four-uniform hypergraph G on

    alpha x (Fin 4 x ZMod p),

with the following verified properties:

* D <= p, 3 < p, and p <= 2*max(D,5).
* Every degree in G is EXACTLY D.
* Every distinct pair in G has codegree at most K, with no additive loss.
* Every edge-intersection bound k>=1 holding for distinct edges of H also
  holds for distinct edges of G. Thus the absence of three-vertex overlaps
  is preserved.
* Every independent B in G supplies an independent A in H with

      |B| <= 4*p*|A|.

There are exactly 4*p copies, at most 8*max(D,5). This is a polynomial-size
regularization, not an unspecified arbitrarily large enlargement.

## Construction and proof

More generally work over a finite field F with an injective row-label map
h : Fin 4 -> F. A copy edge is e x {c}, for e in H and a fixed copy c.
For each original vertex a, choose a slope set S(a) with cardinality
D-degree_H(a). For every slope s in S(a) and intercept t in F, add the edge

    {(a,(i,t+s*h(i))) : i in Fin 4}.

Each such edge has four vertices. Every new vertex belongs to exactly one
line of each selected slope, so its old and new degrees add to D.

Two distinct line edges have at most one common vertex, by solving the two
linear equations for slope and intercept. A copy edge and a line edge have
at most one common vertex: the copy fixes both copy coordinates, while the
line fixes the original label. Distinct copies of old edges are disjoint.
These facts prove the intersection bounds.

The sharper pair-codegree preservation uses a dichotomy. If two vertices
have the same copy coordinates, their original labels differ, so no line
edge contains both; their old codegree is exactly the original codegree.
If their copy coordinates differ, no old edge contains both, and their new
codegree is at most one. Thus the bound is K, not K+1.

For extraction, partition any independent set by copy coordinates and
choose a largest slice. A forbidden original edge in the slice would give
a forbidden copied edge in B. The sum of the slice cardinalities is exactly
|B|. `independent_density_transfer` explicitly proves the real-valued version:
any lower bound rho on the independent-set density transfers unchanged.

Bertrand's postulate provides the bounded prime. Row labels are 0,1,2,3 in
ZMod p, with injectivity checked from p>3.

## Scope and next quantitative issue

The module is a reduction, not an independence estimate. In particular, it
does NOT prove the sparse-hypergraph logarithmic gain. Merely applying the
already proved Caro--Tuza theorem after regularization does not produce that
gain or improve the 2/3 exponent.

The contemplated next extraction argument is a quantitative random-greedy
analysis for regular four-uniform hypergraphs with small codegrees and no
three-vertex edge overlaps. Such a theorem has NOT been formalized or assumed.
Tracking only four-edges would be insufficient: selecting vertices creates
residual constraints of sizes two and three, as well as closed vertices.

Even a logarithmic-gain theorem would, by itself, address the logarithmic
loss at the 2/3 scale, not the entire near-linear conjecture. A further
square-specific argument is still needed for epsilon<1/3.

The residue-fiber review preceding this module found no improved compatible
partial-fiber selector. Modular pair matching does not remove cross-fiber
positive-difference intersections. No new universal obstruction is claimed.

Log: /tmp/four-uniform-regularization.log.
Main-file check: /tmp/spec-regularization-check.log.
