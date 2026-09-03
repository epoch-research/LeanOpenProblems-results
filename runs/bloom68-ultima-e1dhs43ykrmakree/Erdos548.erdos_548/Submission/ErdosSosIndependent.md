# Erdős–Sós: independently checked reductions and obstacles

**Status:** No proof of the unrestricted conjecture was obtained. The separate file
`ErdosSosIndependent.lean` compiles and contains no `sorry`, new axiom, or import of
`Submission.Spec`. `Submission/Spec.lean` was not modified.

## 1. Verified weighted pruning lemma

Let `G` be a finite simple graph and `w : V(G) → Q`. If

    e(G) > sum_v w(v),

there is a nonempty vertex set `S` such that `H = G[S]` satisfies

    e(H) > sum_{v in S} w(v),
    d_H(v) > w(v) for every v in S.

In fact, `S` can be chosen so that, for every nonempty `X ⊆ S`,

    |{edges of H incident with X}| > sum_{v in X} w(v).

Proof: choose `S` of minimum cardinality among the positive-surplus sets. For
nonempty `X ⊆ S`, minimality gives

    e(G[S \ X]) ≤ sum_{v in S \ X} w(v).

Subtract this from the strict inequality for `S`. Singleton `X` gives the degree
bound. No assumption that the weights are nonnegative is needed. If they are
nonnegative then `H` also has an edge.

Lean declarations, all in namespace `ErdosSosIndependent`:

- `edgesOn`, `card_edgesOn`: the edge set being counted is exactly the
  conventional induced graph's edge set.
- `exists_density_minimal_set`
- `exists_incidence_dense_set`
- `exists_weighted_incidence_dense_set`
- `card_edgesOn_delete_vertex`, `card_neighbors_inter`
- `exists_induced_degree_gt_weight`
- `exists_density_core`
- `exists_degree_ge_of_density`
- `exists_erdos_sos_core`

The last declaration retains strict density and gives `k ≤ 2*d_H(v)` for every
vertex, and some vertex of degree at least `k`. It does **not** assert minimum
degree at least `k`.

Instantiation with `w(v)=(k-1)/2` gives the important condition

    e_H(X) + e_H(X, V(H) \ X) > (k-1)|X|/2             (*).

Double counting gives `sum_{v in X}(2*d_H(v)-d_{H[X]}(v))` equal to twice
the incident-edge count. In particular, every nonempty `X` contains a vertex
`v` with `2*d_H(v) - d_{H[X]}(v) ≥ k`. This pointwise consequence is weaker than
(*). The full incidence condition (*) must not be replaced just by the
minimum/maximum degree bounds.

## 2. Exact positive embedding lemma: a bunch of leaves

Suppose a tree `T` with `k` edges has a vertex `r` adjacent to `l` leaves. If

    delta(H) ≥ k-l,    d_H(x) ≥ k,

then there is an injective homomorphism `T → H` taking `r` to `x`.

Proof: delete those `l` leaves from `T`. The remaining rooted tree has `k-l`
edges. Embed it starting at `x` by the usual rooted greedy algorithm: before
adding a vertex, at most `k-l-1` already used vertices can be neighbors of the
image of its parent. Then append the deleted leaves at `x`; the existing copy
uses at most `k-l` neighbors of `x`, leaving at least `l` unused neighbors.

Consequently the safe density core proves Erdős–Sós whenever some vertex has at
least `floor(k/2)` leaf neighbors. In particular this covers all stars and double
stars. This embedding lemma is proved mathematically here, not formalized in the
Lean file. Its stronger prescribed-root form was checked on 10,307 instances
using all graphs in NetworkX's graph atlas (graphs of order at most 7).

## 3. Exact bipartite case reconstructed from the corpus

Source: Maya Stein, *Kalai's conjecture in r-partite r-graphs*, arXiv:1912.11421.
Local file: `/corpus/src/1912.11421/KalaiBip.tex`.
The asymmetric core is at lines 95–106; greedy embedding at 116–121; its pruning
proof at 126–182.

Let the color-class sizes of `T` be `a ≤ b`, so `a+b=k+1`. Write the host's
bipartition as `A ⊔ B`, with `|A| ≥ |B|`. Set

    w(v) = a-1 for v in A,
    w(v) = b-1 for v in B.

Then

    sum_v w(v)
      = (a-1)|A| + (b-1)|B|
      = (k-1)n/2 - (b-a)(|A|-|B|)/2
      ≤ (k-1)n/2 < e(G).

Weighted pruning gives a nonempty bipartite subgraph with degree at least `a`
on its `A` side and at least `b` on its `B` side. Map the tree's larger class to
`A`, smaller class to `B`, and embed in a parent-before-child order. Every time a
new vertex is needed in the smaller class, fewer than `a` positions there have
been used, while its parent has at least `a` neighbors there; likewise with `b`.
This is a full elementary proof for bipartite hosts. The weighted-pruning part is
formalized; the colored greedy embedding is not.

### Why this does not prove the general case

For `k=3`, let `G` be two triangles sharing exactly one vertex. Then `n=5`,
`m=6>5=(k-1)n/2`. All simple cycles in `G` are triangles, so every bipartite
subgraph is a forest and has average degree strictly below 2. Thus one cannot
pass to a bipartite subgraph while retaining the Erdős–Sós density threshold.

A bipartite double cover preserves average degree but an injective copy in the
cover need not project injectively. For example, the double cover of `K3` is
`C6`, which contains `P4`, whereas `K3` does not. Even when the original graph
satisfies the strict density hypothesis, a particular copy can project badly:
in the double cover of `K4`, the path `(1,0),(2,1),(3,0),(1,1)` projects with a
repeated vertex.

## 4. Explicit obstacles to other shortcuts

### A. Minimum/maximum degree alone is insufficient

Take `k=6`. Let `G` consist of two copies of `K4` sharing one vertex `z`:
`|G|=7`, `e(G)=12`, `delta(G)=3=ceil(k/2)`, and `Delta(G)=6=k`.
Let `T` be the once-subdivided claw, with edges

    0-1, 0-2, 0-3, 1-4, 2-5, 3-6.

It is not contained in `G`. Any injective map is spanning. If the center `0`
maps to `z`, the three connected two-vertex branches must fit in the two
three-vertex components of `G-z`, which is impossible. If some other tree vertex
maps to `z`, deleting it from `T` leaves a component with at least 5 vertices,
again impossible in `G-z`.

This is not an Erdős–Sós counterexample: its average degree is below `k-1`.
It shows exactly why the full retained density cannot be discarded.

### B. The centroid cannot always be put at a maximum-degree vertex

Let `k=4`, `G=K_{2,7}`, and let `T=P5`, rooted at its middle vertex. Then
`n=9`, `m=14>13.5`, and `G` is a minimum-cardinality density witness: every
proper induced subgraph has at most `3|V|/2` edges. Therefore it satisfies (*)
for every nonempty `X`.

Nevertheless the root cannot map into the two-vertex part, whose vertices have
degree 7. The root and the two endpoints of `P5` lie in the same color class,
and would require three distinct vertices in that two-vertex part. Every copy
has its middle vertex in the degree-2 part. There are exactly 420 labelled
copies, with 60 having their middle at each of the seven degree-2 vertices.
`K_{2,8}` gives the same obstruction while satisfying the literal `+1` edge
hypothesis of `Spec.lean`.

This also rules out a common entropy shortcut: there is no distribution on
injective copies of this rooted tree whose root marginal is the stationary
measure `d(v)/(2m)`. That measure puts probability 1/2 on the degree-7 part, while
any injective-copy distribution puts probability 0 there. Conditioning a
stationary tree-indexed random walk on injectivity does not preserve its
stationary vertex marginals.

## 5. Other source results and the unresolved step

- `/corpus/src/1906.10219/erdos_sos.tex`, main theorem near lines 15–20:
  the exact result requires fixed maximum tree degree, `k ≥ delta*n`, and
  sufficiently large `n`. Choosing parameters separately for each input does
  not remove these hypotheses, because `n0` depends on them.
- `/corpus/src/1804.06791/intro.tex`: approximate dense/sublinear-degree result,
  with genuine slack and degree restrictions.
- `/corpus/src/1804.06567/1804.06567.tex`: exact result for spiders; its equation
  `eq-S` is condition (*) above. Its rerouting lemmas are specific to legs of a
  spider. A general tree need not be a spider.
- `/corpus/src/2206.03339/no_trees_of_fixed_size.tex`: spectral variant requiring
  a different, generally much larger spectral threshold; it does not follow
  from the target average-degree inequality.
- The searched sources describe Ajtai–Komlós–Simonovits–Szemerédi's large-`k`
  proof as announced/unpublished. No complete unrestricted proof was found in
  the corpus or in mathlib. Mathlib's Andrásfai–Erdős–Sós theorem is a different
  theorem about triangle-free graphs.

For the exact incidence route, the remaining task would be: given a `T`-free
host, construct a nonempty vertex set `X` whose incident-edge count is at most
`(k-1)|X|/2`. An arbitrary partial embedding does not produce such a set. Proving
this for arbitrary trees would itself be equivalent to the conjecture (iterate
the deletion of such sets). It is not a routine consequence of the weighted
pruning lemma, and no proof of that missing embedding/obstruction lemma was
obtained.

## Verification

`lake env lean Submission/ErdosSosIndependent.lean` succeeds.
For each main lemma, `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]`, not `sorryAx`.
The explicit noncontainment/root claims were checked with NetworkX's
`subgraph_is_monomorphic` / `subgraph_monomorphisms_iter`, i.e. **non-induced**
containment. All 511 nonempty subsets of `K_{2,7}` were checked for (*); the
minimum doubled strict surplus was 1. The asymmetric bipartite-core argument
was additionally checked on 332 small parameter/host instances.
