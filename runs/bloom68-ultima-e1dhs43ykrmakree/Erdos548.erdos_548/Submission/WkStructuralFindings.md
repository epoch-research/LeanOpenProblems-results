# The W_k tree-embedding candidate: proved structural cases and induction barriers

**Status.** I did not settle the unrestricted implication `W_k => every k-edge tree`.
The results below are proved sublemmas, a literature consequence for spiders, and
counterexamples to **rooted strengthening attempts**, not counterexamples to W_k
itself. The numerical searches are not a proof. Throughout, graphs are finite,
simple and nonempty, `k >= 1`, and containment means **non-induced** containment.
`Submission/Spec.lean` was not modified.

Write

    W_k: for every nonempty X, some v in X has 2 d_G(v) - d_{G[X]}(v) >= k.

## 1. Exact bootstrap, degeneracy and orientation interpretations

Put `tau(v) = max(0, k-d_G(v))`. Initially activate every vertex with degree at
least `k`; thereafter activate `v` when it has at least `tau(v)` active neighbors.
Then **W_k holds if and only if all vertices eventually activate**.

Indeed, the activation inequality is `d_G(v) + number of earlier neighbors >= k`.
For a remaining set `X`, its left side is exactly `2d_G(v)-d_{G[X]}(v)`. Thus a
failed process leaves precisely a nonempty *resistant set*

    d_{G[X]}(v) >= 2d_G(v)-k+1 for every v in X.

Conversely, no resistant set can lose its first vertex to the process. This also
shows that the order of eligible activations does not matter for success.

This is an instance of **general-threshold dynamic monopolies / resistant
subgraphs**. A reference is Manouchehr Zaker, *On dynamic monopolies of graphs
with general thresholds*, arXiv:1103.1112, Section 2, Propositions 1 and 2
(`/corpus/src/1103.1112/1103.1112.tex`). In the terminology of variable
degeneracy, W_k is strict `f`-degeneracy for `f(v)=2d_G(v)-k+1`: every nonempty
induced subgraph has a vertex of degree less than its `f` value. This should not
be conflated with newer notions called “weak degeneracy” involving a saving
operation.

Equivalently, there is an **acyclic** orientation satisfying

    d^+(v) + 2d^-(v) >= k for all v.

Orient each edge from earlier to later in an activation order, and conversely
use a topological order of the orientation. Acyclicity cannot be omitted: a
cyclically oriented triangle has weighted degree 3 everywhere and cannot
contain a 3-edge tree.

Useful necessary conditions are

    delta(G) >= ceil(k/2),
    every component has a vertex of degree >= k,
    3e(G) >= k|G|.

The first two use singleton sets and entire components. The last follows by
summing the ordering inequalities; ordinary degrees contribute `2e(G)` and
earlier-neighbor counts contribute `e(G)`. The last bound is sharp, for example
on `K_{r,2r}` with `k=2r`. Thus the weakening genuinely allows average degree
`2k/3`, well below the Erdős–Sós density threshold.

## 2. A stronger deletion rule for order tails

Arbitrary deletion of `r` vertices only preserves `W_{k-2r}`: the potential of
a surviving vertex decreases by twice the number of its deleted neighbors.

**Tail-deletion lemma.** If `v_1,...,v_n` witnesses W_k, then
`G[{v_1,...,v_{n-r}}]` satisfies `W_{k-r}` (when this parameter is nonnegative).

**Proof.** Earlier-neighbor counts for the retained order do not change, and
each ordinary degree decreases by at most `r`. Therefore each retained score
is at least `k-r`. This proves the claim.

For one last vertex `z`, put `H=G-z` and `S=N_G(z)`. More precisely, the retained
order obeys

    d_H(v) + earlier_H(v) >= k-1 if v in S,
    d_H(v) + earlier_H(v) >= k   if v not in S,
    |S| >= ceil(k/2).

The last inequality follows from the score `2d_G(z)` of the final vertex.
This heterogeneous condition must not be silently replaced by just W_{k-1}.
For example, let `k=6`, `H=K_{3,5}`, and let `S` consist of three vertices in the
5-vertex part. Then H has W_5 and `|S|=3`, but adjoining a new vertex adjacent
exactly to S gives maximum degree 5, hence no 6-edge star. This is a
counterexample to that *weaker induction input*, not a W_6 counterexample.

## 3. A proved two-for-one independent-interface theorem

**Theorem.** Let `r >= 1`, let S be an independent set of size r, and let H be
an arbitrary graph satisfying

    |H| >= k,                delta(H) >= k-2r.

Join every vertex of S to every vertex of H. Then `S vee H` contains **every
k-edge tree**. It also satisfies W_k, by activating S first and H second.

This theorem remains a containment theorem if arbitrary edges are added inside
S. It does not assume any particular structure of H or of the target tree.

**Proof.** Let `A,B` be the tree's bipartition, with `a=|A| <= b=|B|` and
`a+b=k+1`.

* If `a <= r`, put A into S and B into H. The required edges are all cross edges.
* Suppose `a > r`. Choose U to be the r highest-degree vertices of A. Since
  the sum of the degrees in A is k and `k >= 2a-1`,

      sum_{u in U} d_T(u) >= rk/a >= 2r-r/a > 2r-1.

  The left side is an integer, hence it is at least `2r`. Also U is independent.
  Consequently `F=T-U` is a forest with

      e(F) = k - sum_{u in U} d_T(u) <= k-2r,
      |F| = k+1-r <= |H|.

  Use the forest-embedding theorem below to embed F into H; map U arbitrarily
  and injectively into S. Every deleted edge goes between U and F, so the
  complete interface supplies all its edges.

The forest theorem used here is:

> Every forest F embeds into every H with `|H| >= |F|` and `delta(H) >= e(F)`.

This is Theorem 1 of Mark Goldberg and Malik Magdon-Ismail, *Embedding a Forest
in a Graph*, arXiv:1011.3882; see `/corpus/src/1011.3882/intro.tex` and the proof
in `theorem.tex`. Isolated forest vertices can be placed in unused host vertices
after embedding the nontrivial components. This is **not** the naive greedy
forest algorithm; the cited theorem uses global re-embeddings.

Finally, in the proposed activation order, each vertex of S has degree `|H|>=k`,
and each `h in H` has score `d_H(h)+2r>=k`, proving W_k as well. QED.

**Rooted refinement within this class.** If a specified tree vertex u has
maximum degree in a smaller bipartition class, then u can be placed at any
specified `s in S`. In the first case use the bipartite embedding. In the
second case choose the r highest-degree vertices to include u, and map u to s.

This is a precise implementation of “an earlier neighbor counts twice”: r
independent tree vertices save at least `2r` tree edges, and the complete
interface makes the resulting forest attachments unrestricted. The same
argument does not apply to arbitrary earlier-neighbor sets.

## 4. Complete multipartite hosts: an exact criterion and a global proof

**Theorem.** Every complete multipartite graph satisfying W_k contains every
k-edge tree.

Let its part sizes be

    1 <= c_1 <= ... <= c_m,       n = sum c_i,       t = n-k.

W_k implies `n>=k+1`, hence `t>=1`. Its exact multipartite characterization is

    W_k  iff  c_i <= t + sum_{j<i} c_j for all i.             (1)

To prove necessity, apply W_k to the union of parts `i,...,m`. A vertex in part
j of this union has score `n-c_j + sum_{h<i}c_h`; the largest such score occurs
in its smallest part i. Sufficiency follows by activating whole parts in
increasing-size order: each vertex in part i then has exactly this score.

We need the following elementary subset-sum lemma.

> If positive integers c_i satisfy (1), the intervals `[s,s+t-1]`, where s runs
> through their subset sums, cover every integer from 0 to `n+t-1`.

**Proof of the lemma.** The empty prefix covers `[0,t-1]`. If a prefix has total
P and covers `[0,P+t-1]`, adjoining the next c gives that interval and its
translate by c. Since `c<=P+t`, the two intervals touch or overlap, giving all
of `[0,P+c+t-1]`. Induct. QED.

Now let the target tree have bipartition sizes a,b, where `a+b=k+1`. Apply the
lemma to `a+t-1`. There is a subset sum s such that

    a <= s <= a+t-1 = n-b.

Group the corresponding host parts together, and all other parts together.
Every edge between the two groups is present, so G contains `K_{s,n-s}`. Map
the two tree color classes into the two groups. This gives the desired tree.

This proof chooses the host bipartition **globally** rather than trying to
change the orientation of an already fixed tree embedding by local swaps.

An exact parameter formula is also available:

    max{k: W_k holds} = n - max_i (c_i - sum_{j<i} c_j).

The subtracted quantity is precisely the largest gap between consecutive
distinct subset sums. The interval lemma bounds all gaps from above; for an i
attaining a positive difference, there is no subset sum strictly between the
prefix sum and c_i, proving the matching lower bound.

## 5. End blocks that cannot occur in a counterexample

A stronger statement than just “block graphs work” is useful: **a W_k graph
with a clique or complete-bipartite end block already contains every k-edge
tree.** Here an end block has one cut vertex, and all its other vertices have
no neighbors outside that block. The graph may have arbitrary other blocks.

### Clique end block

Let B be the clique and x its cut vertex. For `X=B-{x}`, every v in X has

    2d_G(v)-d_{G[X]}(v) = 2(|B|-1)-(|B|-2) = |B|.

Thus `|B|>=k`. Take a k-clique in B containing x, and an outside neighbor y of x.
For any target tree, put a leaf at y, its parent at x, and all remaining tree
vertices in the clique. If the connected graph is a single clique instead,
W_k gives clique size at least `k+1` directly. In particular **block graphs
cannot supply a counterexample**.

### Complete-bipartite end block

It is enough to consider `k>=3`; the smaller k are immediate from a degree-k
vertex. Write the end block as `K_{a,b}` with cut vertex x in its b-part. Its
parts have size at least 2, since a leaf bridge would have a degree-1 vertex,
contradicting `delta(G)>=ceil(k/2)`.

Singleton sets give `a,b>=ceil(k/2)`. For `X=V(B)-{x}`, the potentials are `b+1`
on the a-part and a on the remaining b-part. Therefore

    max{a,b+1} >= k.

If `a>=k`, the block contains every target by its bipartition. Otherwise
`b>=k-1`, so it contains every nonstar k-edge tree: its smaller color class has
size at most `ceil(k/2)` and its larger class has size at most `k-1`. The k-star
is supplied by the degree-k vertex in the whole graph. This proves the claim.

Thus graphs whose blocks are all complete bipartite also cannot be
counterexamples; the single-block case follows from Section 4.

## 6. New engineered obstructions to seed-rooted induction

### 6.1 Even a maximum-degree tree vertex need not be placeable at any seed

For even k, take disjoint sets

    |A_1|=|A_2|=k/2,       |B_1|=|B_2|=k-2,

and one further vertex s. Put in all edges between A_i and B_i and all edges
from s to `A_1 union A_2`, and no others. Then

    d(s)=k,       d(a)=k-1 for a in A_i,       d(b)=k/2 for b in B_i.

The order `s, A_1, A_2, B_1, B_2` has score exactly k at every vertex, so this is
W_k with **exactly one bootstrap seed**, s. Also

    |G|=3k-3,       e(G)=k(k-1),       3e(G)=k|G|.

In particular this construction attains the sharp low-density bound.

Use `k=14`. Construct T from vertices `h_0,h_1,h_2,h_3` and three connectors
`c_1,c_2,c_3`, with edges

    h_0-c_i-h_i  for i=1,2,3.

Add three leaves at h_1, three at h_2, and two at h_3. This is a 14-edge tree
with color classes

    A_T={h_0,h_1,h_2,h_3},      |B_T|=11.

Its only maximum-degree vertices are h_1 and h_2, both of degree 4; both are
leaf-parents in the **smaller** color class.

**Neither h_1 nor h_2 can map to s.** On deleting either h_i, the large
component C of T-h_i has 3 vertices of A_T and 8 of B_T. Its connector c_i is
in B_T and must map to a neighbor of s, hence to an A_j. The connected image
of C lies wholly in one component `G-s=K_{7,12} disjoint union K_{7,12}`. Its
bipartition is thereby fixed, forcing its eight B_T vertices into the
seven-vertex A_j, a contradiction.

Nevertheless T embeds unrooted: put its four A_T vertices into A_1 and its
eleven B_T vertices into B_1. This embedding even avoids s.

So the proposed principle

> “Choose a maximum-degree vertex of the tree, in its smaller color class if
> possible, and put it at a degree-at-least-k vertex of G”

is false under W_k, even if the chosen tree vertex must be a leaf-parent and
one is free to choose among all maximum-degree vertices. The positive rooted
refinement in Section 3 therefore genuinely needs its complete interface.

### 6.2 A smaller, 2-connected example against an arbitrary smaller-color leaf-parent

Blow up a 6-cycle by independent parts `(A,B,C,D,E,F)` of sizes

    (6,6,3,6,6,1),

joining exactly consecutive parts completely. Degrees by part are
`(7,9,12,9,7,12)`. For k=12 activate C and F, then B and D, then A and E. This
certifies W_12. The graph is 2-connected, with 28 vertices and 120 edges.

Let the target have a path `ell-u-c-z` and nine additional leaves at z. It has
12 edges, `d_T(z)=10`, and smaller color class `{u,z}`. The vertex u is a
leaf-parent. It cannot map to the sole vertex f of F: z would then have to map
to a distance-two vertex of f, and these are precisely B and D, whose vertices
have degree 9.

An unrooted copy is explicit: put `z` at `C_0`, `c` at `B_0`, `u` at `A_0`,
`ell` at f, and put the nine other leaves at the other five B vertices and any
four D vertices. Again this is only a rooted counterexample.

## 7. A sharp global endpoint lemma, and the spider literature

### 7.1 A self-contained potential lemma for freely rooted paths

**Global endpoint lemma.** Suppose H has a Hamiltonian path, and let S be the
set of all vertices that can be an endpoint of any Hamiltonian path in H.
Then, for **every** `v in S`,

    2d_H(v)-d_{H[S]}(v) <= |H|-1.                            (2)

**Proof.** Write a Hamiltonian path ending at v as `x_0,...,x_l=v`, where
`l=|H|-1`. Let `A=N_H(v)` and

    B={x_{i+1}: x_i in A}.

Rotating the path at the edge `vx_i` shows that every vertex of B belongs to
S. Also `|B|=|A|=d_H(v)`, and `x_0 in S-B`. Put
`epsilon=1` if `x_0 in A`, and 0 otherwise. Since

    |A union B| <= |H|-1+epsilon,
    |A intersect S| >= |A intersect B|+epsilon,

we obtain

    d_{H[S]}(v) >= 2d_H(v)-(|H|-1+epsilon)+epsilon,

which is (2). QED.

**Corollary.** W_k implies a path of k edges. Take a longest path P in G, let
`H=G[V(P)]`, and form S as in the lemma. No vertex of S has a neighbor outside
P, or a Hamiltonian path of H ending there could be extended. Thus the
potentials in (2) are exactly the G-potentials on S. Applying W_k to S gives
`k <= |P|-1`. This uses all possible endpoints, not a prescribed root, and
removes the extra one present in the fixed-root endpoint bound.

The bound does **not** extend to arbitrary trees even if one takes the union
of all leaf supports over all spanning copies. For a small exact obstruction,
let H have vertices `0,...,6` and edges

    01,02,03,04,05,12,23,25,34,46.

Let F have edges

    10,12,13,04,45,46.

Thus F consists of two degree-three hubs joined through a degree-two vertex,
with two leaves at each hub. In any spanning copy, host vertex 6 must be a
leaf, so host vertex 4 is a hub. Its degree is exactly three. The other hub
cannot be adjacent to 4, since then one of 4's three neighbors would be
unavailable for its three required tree neighbors. The only nonneighbor of
4 of degree at least three is host vertex 2, which is therefore the other hub.
The middle vertex is either 0 or 3. In the first case the leaves are
`{1,3,5,6}`; in the second they are `{0,1,5,6}`. Both cases occur.
Consequently the union of all leaf supports is exactly

    S={0,1,3,5,6},

but `2d_H(0)-d_{H[S]}(0)=10-3=7>6=e(F)`. This is a counterexample to extending
(2), not to W_k. It pinpoints why the path closure argument does not by itself
prove the tree conjecture.

### 7.2 The spider literature already uses exactly W_k

Genghua Fan, Yanmei Hong and Qinghai Liu, *The Erdős–Sós Conjecture for Spiders*,
arXiv:1804.06567, formulate their main embedding argument after a
minimal-counterexample reduction to incident density. But the source explicitly
states, immediately after equation `eq-S`:

> “Then there is v in S such that d(v)-e(v,S)/2 >= k/2. The condition [eq-S]
> is always used like this in this paper.”

See `/corpus/src/1804.06567/1804.06567.tex`, line 83. That displayed pointwise
condition is exactly W_k, not full incident density.

An audit of the later appeals to `eq-S` gives:

* lines 226 and 228: choose reroutable path endpoints with the pointwise bound;
* line 237: choose the end of an outside path with that bound;
* line 270: another attainable endpoint set;
* line 274: apply the bound to the clique `L_j union {x}`. All induced degrees
  there are `ell_j`, so W_k gives exactly `d(x') >= (k+ell_j)/2`, as required;
* line 296 and the other minimum-degree uses: singleton instances.

There is no later use of a stronger summed incident-density inequality in the
embedding argument. Components inherit W_k, so the connectedness assumption
is harmless; an entire component supplies a degree-k starting vertex.
Also `W_k => W_{k-1}`, as needed for their induction on tree size. The local
path-extension lemmas are stated with explicit local hypotheses rather than
reapplying incident density to a deleted host.

**Consequence of their proof:** W_k suffices for every k-edge **spider**.
This is a cited proof adaptation, not a self-contained new spider proof or a
claim about arbitrary trees. In particular, W_k's exact pointwise hypothesis
was already being exploited in this part of the Erdős–Sós literature, even
though the theorem is stated using incident density and does not name W_k.

## 8. Verification and the remaining gap

Run

    python3 Submission/WkStructuralChecks.py

The script checks ordering equivalence against every nonempty subset on graph
atlas hosts, exact tail certificates, the multipartite interval and capacity
claims through 17 vertices, independent deletion on all unlabeled trees through
11 vertices, small non-induced forest/interface embeddings, end-block capacity
bounds, the global endpoint lemma, and the two explicit rooted obstructions
and unrooted injections. All checks passed. In particular:

| Check | Completed instances |
|---|---:|
| W_k ordering versus direct subset definition on atlas hosts | 9,727 |
| Tail-deletion certificates | 4,524 |
| Multipartite bipartition capacities (1,211 partitions through n=17) | 101,112 |
| Independent-deletion choices (435 trees through 11 vertices) | 1,501 |
| Cited forest theorem on qualifying atlas pairs | 22,346 |
| Independent-interface non-induced embeddings | 1,085 |
| Complete-bipartite end-block capacities for nonstars | 15,780 |
| Global endpoint inequality on Hamiltonian atlas hosts | 852 |
| Longest-path bound versus W on nonempty atlas hosts | 1,252 |

The all-leaf-support obstruction has exactly 16 labelled spanning embeddings,
whose supports were enumerated as an additional check of the direct proof.
The raw verification output is `/tmp/wk_structural/rigorous_checks.log`.
The proofs above do not depend on exhaustive numerical tree searches.

The unchanged SHA-256 of `Submission/Spec.lean` is

    674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103

**Unresolved:** general W_k hosts, including arbitrary multiround activation
with nonuniform neighborhoods. Section 3 removes r independent tree vertices
and saves at least 2r edges, but its forest can be re-embedded freely only
because all interface edges exist. For a general activation order, the forest
has shape-dependent attachment requirements to particular earlier vertices.
Neither a prescribed seed-root rule nor a fixed-core/local Hall obstruction
solves those global requirements. No theorem here asserts that they can always
be satisfied, and no counterexample to the unrestricted W_k conjecture was
found.
