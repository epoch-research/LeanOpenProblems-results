# Erdős–Sós: an independent augmentation/certificate attempt

**Status: the unrestricted conjecture was not proved.** The results below are proved reductions, exact counterexamples to particular augmentation shortcuts, and explicitly delimited computational checks. No unproved embedding assertion is being supplied as a solution. `Submission/Spec.lean` was not modified.

Write `I_G(X) = e_G(X) + e_G(X,V(G)\X)` for the number of edges incident with `X`. The target condition is

    I_G(X) > (k-1)|X|/2  for every nonempty X.                 (ID_k)

## 1. What is special about the spider proof

Source: `/corpus/src/1804.06567/1804.06567.tex`, especially `eq-S`, `lem-longpath`, `lem-xv1v2`, `lem-xPQ`, `lem-xvw`, and the choices in `eq-choice-T1`.

The endpoint rerouting lemma says that if `P` is a fixed-root path on `p+1` vertices and `S` is its set of possible other ends under spanning reroutes, then

    2 e(v,V(P)) - e(v,S) <= p+1  for v in S.

Its proof pairs a neighbor of an endpoint with the successor of that neighbor: reversing the tail preserves a path. The extension lemmas then use two interchangeable ends and an outside path end, with charges of the form

    2 e(x,L) + e({v,w},L) - 2|L|,

sometimes with an extra correction involving the set of attainable ends. The embedded legs are chosen lexicographically, including maximization of their induced edge counts. This is much more than a greedy embedding or a degree argument.

For a general branch, reversing a path through it need not preserve the attached rooted subtrees. The following counterexample shows that even allowing **all** spanning re-embeddings of a branch, rather than just elementary rotations, does not recover the same endpoint inequality.

### A seven-vertex counterexample, with the designated leaf in the larger color class

Let the host have vertices `a,b,x1,x2,y1,y2,z` and edges

    ab, ax1, ax2, by1, by2, zx1, zx2, zy1, zy2.

Let `F` have edges

    ab, ax1, ax2, x2z, by1, by2,

with designated leaf `z`. This is a tree with two degree-three vertices, not a spider. The color class containing its designated leaf has four vertices; the other class has three.

In every spanning embedding of `F` into this host, the two adjacent degree-three vertices of `F` must map to `a,b`: these are the only adjacent host vertices both having degree at least three. The vertex preceding the designated leaf must therefore be one of `x1,x2,y1,y2`. Its only neighbor other than the relevant center is the host vertex `z`. Hence the support of the designated leaf over **all** spanning embeddings is exactly

    S = {z}.

There are eight labeled embeddings, and

    2 d_H(z) - d_{H[S]}(z) = 8 > 7 = |F|.

The same support occurs after fixing `a` to the host `a`. Thus neither freeing the branch root nor requiring that the distinguished leaf lie in the larger color class repairs this proposed generalization. This is a counterexample to a *local rerouting inequality*, not to Erdős–Sós.

## 2. A family of incidence-minimal hosts with trapped local embedding components

For any integer `a>=1`, put

    k = 2a,  b = a(2a-1)+1,  G = K_{a,b}.

Then

    2e(G) - (k-1)|G| = 1.

Moreover, every proper induced subgraph has density at most `(k-1)/2`. Indeed an induced subgraph is `K_{x,y}`. If `x<a`, then

    2xy - (2a-1)(x+y) = (2x-2a+1)y - (2a-1)x <= 0.

If `x=a` and the subgraph is proper, then `y<=b-1=a(2a-1)`, and the same surplus equals `y-a(2a-1)<=0`. Therefore these hosts satisfy `(ID_k)` and are minimum-cardinality density witnesses.

Let `T=P_{2a+1}`, with vertices `0,...,2a`, and embed `F=T-{2a}`. Consider the orientation of the bipartition in which the even labels of `F` occupy the small host class. All `a` vertices of that class are occupied. The parent `2a-1` of the missing leaf lies in the large class, so all its neighbors are occupied. No state with this bipartition orientation extends to `T`.

For any two embeddings of the connected bipartite graph `F`, changing the bipartition orientation changes the image of **every** label. Consequently a move changing at most `2a-1=k-1` labels cannot change this orientation. A sequence of such moves starting in a blocked orientation can never augment, although `G` contains `T` in the opposite orientation.

For `K_{2,7}` and `F=P4`, there are exactly 168 labeled states. Under single-label replacements there are four components, each of size 42; two components are entirely blocked and two entirely extendible. All 84 blocked states remain separated from all 84 extendible states even if a move may change up to three labels. This was checked exhaustively.

This is stronger than saying that a prescribed root can be bad: a search with no initially prescribed root can still start in a whole trapped component. Any successful general state method needs genuinely global moves, changing the partial domain substantially, or a rule selecting the correct component. It is not enough to assert that a maximal locally reconfigurable state is augmentible.

## 3. A valid two-vertex extension and its exact scope

### Incidence transport under deletion

If `G` satisfies `(ID_k)` and `U` has `s` vertices, then `G-U` satisfies `(ID_{k-2s})`, whenever that parameter is relevant. For nonempty `X` disjoint from `U`,

    I_{G-U}(X) = I_G(X) - e_G(X,U)
               > (k-1)|X|/2 - s|X|
               = (k-2s-1)|X|/2.

No embedding assertion is needed for this reduction.

### Universal-vertex extension lemma

For every tree `T` with `k>=2` edges, one can choose a tree `R` with `k-2` edges such that the following holds:

> If `G` has at least `k+1` vertices, `u` is universal in `G`, and `G-u` contains `R`, then `G` contains `T`.

**Proof.** Every tree with at least two edges has either two leaves with a common parent or a pendant two-edge path whose leaf-parent has degree two. This follows by considering the neighbor of an end of a longest path.

* If `T` has leaves `l1,l2` at `p`, take `R=T-{l1,l2}`. Embed `R` in `G-u`, move the image of `p` to `u`, use the freed old image of `p` for `l1`, and use a vertex outside the old image and `u` for `l2`. All changed edges are incident with the universal vertex. The spare vertex exists because the old image has `k-1` vertices.
* If `l-p-q` is pendant with `d_T(p)=2`, take `R=T-{l,p}`. Embed `R` in `G-u`, place `p` at `u`, and place `l` at a spare vertex.

Both maps are injective and preserve every tree edge. This proves the lemma.

Applying the lemma to the cone on `N(u)` gives a useful sufficient condition: if `d_G(u)>=k` and `G[N(u)]` contains every `(k-2)`-edge tree, then `G` contains every `k`-edge tree.

The construction was checked on all 434 nonisomorphic tree types with `2<=k<=10`, using hosts consisting only of the smaller tree, one spare vertex, and a universal vertex. Thus no accidental extra host edges were used.

**Consequence for a proof by induction on `k`:** assuming Erdős–Sós for `k-2`, an incidence-minimal counterexample for `k` cannot have a universal vertex. This is a valid conditional reduction, not a proof that an arbitrary high-degree vertex suffices.

### Why the same two-step algorithm cannot just use a maximum-degree vertex

Let `T` be the path

    0-1-2-3-4-5-6

with extra leaves `2-7` and `4-8`. It has eight edges and color classes

    A = {1,3,5,7,8},  B = {0,2,4,6}.

It has no pair of sibling leaves. The only degree-two parents of leaves are `1,5`, both in `A`.

Take `G=K_{4,29}`. It is the incidence-minimal graph from Section 2 with `a=4`. Every vertex of degree at least eight lies in the four-vertex host class. In every embedding of `T`, the five-vertex class `A` must map to the 29-vertex class. Thus neither of the two possible pendant-two-path parents can map to any high-degree vertex. Nevertheless `T` certainly embeds, by its bipartition.

So the particular connected-tree two-vertex reduction above cannot work by placing its special parent at an arbitrary degree-`>=k` vertex. A possible broader state must allow deletion of a leaf-parent with several nonleaf neighbors, leaving a **forest with several attachment vertices**, rather than merely another tree. This observation identifies an actual interface issue; it is not an asserted solution of that forest-packing problem.

## 4. Fixed-core leaf augmentation has an exact Hall witness, but not the needed incidence witness

Let `L` be the leaves of a tree with at least two edges and `C=T-L`. Fix an injective embedding `phi:C->G`. Let `l(p)` be the number of leaves at `p`.

The embedding extends to `T` if and only if, for every subset `A` of leaf-parents,

    |N_G(phi(A)) \ phi(C)| >= sum_{p in A} l(p).               (H)

**Proof.** Make one left-side matching slot for every tree leaf and use the unused host vertices on the right. A leaf-slot at `p` sees `N_G(phi(p))\phi(C)`. Hall's theorem applies. Slots with the same parent have identical neighborhoods, so the strongest Hall inequality for any set of represented parents uses all their leaf-slots. These are exactly (H).

Thus failure gives an exact set `A` with fewer available neighbors than leaf slots. However this does not, by itself, give `I_G(phi(A)) <= (k-1)|A|/2`.

For example, in `K_{2,7}` embed the core `1-2-3` of `P5` by

    phi(1)=2, phi(2)=0, phi(3)=3,

where the small host class is `{0,1}`. The two leaf slots have only the unused host neighbor `{1}`. Their parent-image set is `X={2,3}`, yet

    I_G(X)=4 > 3 = (k-1)|X|/2.

All nonempty sets in this host have positive incidence surplus. A Hall obstruction at a fixed core therefore cannot be promoted to the desired global certificate without changing or optimizing the core embedding.

The Hall characterization was independently checked against non-induced embeddings with the entire core fixed on 4,467 small instances, including 2,284 nonextendible cores.

### Gallai–Edmonds has the same rooted-versus-global issue

For the once-subdivided `m`-star, embeddability with center `u` is exactly the existence of an `m`-edge matching in the graph on `V(G)\{u}` retaining only edges incident with `N_G(u)`. Each matched edge supplies one leg.

For `G=K_{m,b}` and `u` in its small class, this graph is `K_{m-1,b}` and has matching number `m-1`. The usual Tutte–Berge witness is the `(m-1)`-vertex side; deleting it leaves `b` odd singleton components. With `b=m(2m-1)+1`, the original host is incidence-minimal and does contain the spider with its center in the other class. Hence a rooted matching obstruction is not already a global incidence certificate. For larger branches, their entire vertex footprints, not just matched endpoint pairs, must be made disjoint.

## 5. Weighted orientations are an exact reformulation, not an embedding proof

For a finite host with `n` vertices, `(ID_k)` is equivalent to the existence of numbers on the ends of each edge satisfying

    w_{uv}+w_{vu}=1, w_{uv},w_{vu}>=0,
    load(v) := sum_{u in N(v)} w_{vu} > (k-1)/2  for every v.

The reverse implication follows because `sum_{v in X} load(v) <= I_G(X)`.

For the forward implication one can require the uniform lower load

    (k-1)/2 + 1/(2n).

Indeed the strict integral inequality gives `2I_G(X)-(k-1)|X|>=1`, so the total incident-edge capacity of every set exceeds this demand for that set. Apply the capacitated Hall/max-flow theorem to the bipartite incidence network whose edge-nodes have supply one. Unassigned residual edge capacity can be split arbitrarily afterward. This proves the exact reformulation.

For `K_{2,7}`, assigning each edge weight `2/9` at its small-class endpoint and `7/9` at its large-class endpoint gives load `14/9>3/2` at every vertex. The blocked embedding states in Section 2 still exist. Balanced fractional loads alone do not justify a local augmentation or prescribed-root embedding claim.

## 6. Finite investigation of the pointwise weakening

I also tested the weaker property

    every nonempty X contains v with 2d_G(v)-d_{G[X]}(v) >= k.  (W_k)

It is decidable by repeatedly removing such a vertex; equivalently there is an ordering with `d(v)+number_of_earlier_neighbors(v)>=k` for every vertex. Its implication for arbitrary tree containment was **not proved**. It survived the following searches, so these searches produced no structural counterexample to that particular weakening:

| Host family | k | tested host/parameter pairs satisfying W_k | tree-containment tests | failures |
|---|---:|---:|---:|---:|
| Connected graph atlas, order at most 7 | 2–6 | 2,214 | 4,816 | 0 |
| All connected 8-vertex graphs with minimum degree at least 3, below/equal ES density | 6–7 | 1,160 | 14,116 | 0 |
| All connected 9-vertex graphs with minimum degree at least 3, below/equal ES density | 6–8 | 47,966 | 671,098 | 0 |
| All connected 10-vertex graphs with minimum degree at least 4, below/equal ES density | 7–8 | 1,184,152 | 34,168,808 | 0 |
| All connected 10-vertex graphs with minimum degree at least 5, below/equal ES density | 9 | 8,791 | 931,846 | 0 |

The emphasis on below-threshold hosts distinguishes the weakening from merely retesting small cases of Erdős–Sós. Every nonisomorphic tree of the stated order was tested. Graphs were generated with `nauty-geng`. The custom exact tree matcher was independently cross-checked against NetworkX on 21,109 atlas graph/tree pairs, including 3,129 negative containment instances.

A further randomized search used 300,000 clique/independent-set blow-ups of templates on 3–6 vertices. For 112,686 below-threshold host/tree parameter instances satisfying `(W_k)`, exact matching/Hall checks found all tested radius-two trees (equal-sized star branches, with edge counts between 9 and 28). This is a sample, not exhaustive coverage and not a theorem.

Raw programs/logs for these larger searches are in `/tmp/es_augment/`, in particular `scan_weak.cpp`, `trees.txt`, `tree_metadata.json`, `weak*.log`, `scan_blowup.py`, and `blowup.log`.

## 7. Verification and remaining limitation

Run

    python3 Submission/ErdosSosAugmentationChecks.py

for the small exact checks of the concrete results. It succeeds. Containment is non-induced throughout, and displayed injections were checked edge by edge.

`Submission/Spec.lean` retained SHA-256

    674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103

before and after this work.

The unresolved issue is not weighted pruning, fixed-core Hall matching, or the two-vertex tree decomposition. It is converting globally optimized, shape-sensitive partial embeddings—potentially with several attachment vertices and different bipartition orientations—into the required low-incidence set in an arbitrary `T`-free graph. No proof of that implication was obtained, and none of the experimentally surviving variants above is being treated as proved.
