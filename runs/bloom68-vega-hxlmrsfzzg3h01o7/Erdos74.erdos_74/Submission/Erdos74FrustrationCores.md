# Erdős 74: frustration-critical cores do not have the proposed finiteness property

## Status and main conclusions

This is a mathematical investigation, **not a proof or disproof of Erdős 74**. No Lean formalization is attempted. Write `tau(G)` for the minimum number of edges whose deletion makes `G` bipartite. Unless stated otherwise, graphs are finite and simple.

The source examined is Chiara Cappello and Eckhard Steffen, *Frustration-critical signed graphs*, arXiv:2112.02664, local file

    /corpus/src/2112.02664/Frustration_critical_graphs_arXiv.tex.

The strongest counterexample obtained here is:

> For every integer `a >= 2` and every positive even integer `L`, there is a simple graph `G(a,L)` which is frustration-critical, non-decomposable in the paper's sense, irreducible in the paper's sense, and satisfies
>
>     |V(G(a,L))| = a L + 4a + 3,
>     tau(G(a,L)) = 3a^2 + 5a + 1,
>     chi(G(a,L)) = 2a + 4,
>     minimum_degree(G(a,L)) >= 2a.

In particular, `a=2` gives arbitrarily large **simple, minimum-degree-four, irreducible, non-decomposable 23-critical graphs of chromatic number 8**. Their growing parts are balanced chains of complete bipartite graphs, not degree-two paths.

Thus there is **no order bound in terms of t for general irreducible non-decomposable t-critical signed graphs**, even when restricted to antibalanced signatures on simple graphs, and even after imposing any fixed lower bound on chromatic number.

This does **not** rule out the desired local-witness theorem. These examples have bounded-size high-frustration, high-chromatic subgraphs. In particular, for fixed `a` their large balanced chains are unnecessary for their chromatic number. It does rule out using the paper's irreducibility and non-decomposability, by themselves, to justify an order bound.

Other conclusions:

* The four-chromatic graph `M(K3)` has no frustration-critical subgraph of minimum degree at least three. Thus such a subgraph cannot be forced at chromatic threshold four.
* Frustration decomposition is not a chromatic decomposition. A frustration-critical graph can decompose into edge-disjoint triangles while having arbitrarily large chromatic number.
* If `H` is a spanning subgraph with `tau(H)=tau(G)>0`, then `chi(G) <= 2 chi(H)`. This factor is sharp even when `H` is frustration-critical. An additive-one assertion for an **arbitrary chosen** frustration-critical core is false.
* An additive-one assertion using a maximum over **all** suitable critical subgraphs is a different statement. No such general theorem, and no theorem forcing an actual minimum-degree-three critical subgraph at some threshold `K >= 5`, is proved here.

## 1. What the cited paper actually supplies

Under the all-negative signature, the signed frustration index is exactly ordinary edge bipartization `tau`.

The relevant statements in the source are:

1. Proposition `critical_subgraphs`, lines 164–177: a graph of frustration `k` contains an `m`-critical subgraph for every `1 <= m <= k`.
2. Theorem `characterizations`, lines 181–213: a signed graph of frustration `k` is `k`-critical iff every edge belongs to a minimum signature. For an ordinary graph, this means that every edge is monochromatic in some maximum cut.
3. Definition and Proposition `decomp_trivial`, lines 296–332: decomposition is into edge-disjoint critical subgraphs whose frustrations add. Their edge sets exhaust a critical graph. This is not asserted to be a block decomposition or a clique-sum decomposition.
4. Theorem `Sub_Dec`, lines 366–433: their signed multiedge subdivision preserves frustration, criticality, and decomposability.
5. Theorem `Non_decomp_2_neighbors`, lines 446–475: a non-decomposable critical signed graph with at least three vertices is a proper subdivision iff it has a vertex with exactly two neighbours.
6. Lines 477–565 classify irreducible critical graphs only for frustration 1 and 2.
7. Proposition `charact_S*`, lines 585–597, identifies `S*` with the critical signed graphs having no two edge-disjoint negative circuits. Theorem `CS*2`, lines 697–774, gives the cubic/projective-planar structure for this **special subclass**, not for all non-decomposable critical signed graphs.

The source does not give a general bound on the orders of irreducible `t`-critical graphs. In fact such a bound is false, as Section 3 proves.

The special `S*` theorem is intrinsically low-chromatic as an ordinary underlying-graph theorem: for frustration at least three, its irreducible cores are cubic, are not `K4`, and are three-colourable by Brooks' theorem. The simple realizations at frustration one are odd cycles, while frustration two has the exceptional unsubdivided `K4`. It cannot be read as a structural theorem for arbitrary high-chromatic non-decomposable critical graphs.

## 2. Two preservation lemmas

These lemmas are used only as mathematical statements, not as claims quoted from the paper.

### 2.1 Replacing a parallel bundle by a balanced two-terminal network

Let `M` be a signed multigraph and let `P` replace a bundle of `b` same-sign parallel edges between terminals `x,y`. Suppose `P` is balanced, shares no other vertices with `M`, and has the following boundary cost: for fixed terminal signs, the minimum number of bad edges inside `P` is zero when the old bundle is satisfied, and `b` when it is unsatisfied. Equivalently, after switching `P` positive, its minimum `x-y` cut has size `b`, with the appropriate terminal parity.

Then frustration is unchanged.

If every edge of `P` belongs to a minimum `x-y` cut, criticality of `M` implies criticality of the replaced graph. For old edges, extend a minimum signature of `M` containing that edge. For a new edge, choose a minimum signature of `M` containing the replaced bundle, and a minimum terminal cut of `P` containing the desired edge.

**Non-decomposability is preserved.** Suppose the replaced graph decomposes as edge-disjoint `H_1,H_2` with positive frustrations adding to `tau(M)`. Write `P_i=H_i intersect P`, and let `b_i` be the minimum terminal-cut size in `P_i`, taking `b_i=0` if its terminals are disconnected. Balancedness implies that replacing `P_i` by `b_i` copies of the original bundle sign preserves `tau(H_i)`.

For any minimum terminal cut `D` of `P`,

    b_1 + b_2 <= |D intersect E(P_1)| + |D intersect E(P_2)| = b.

Thus the two projected graphs can use disjoint copies of the original bundle. They are edge-disjoint subgraphs of `M` whose frustrations add to `tau(M)`. Extracting critical subgraphs from them gives a decomposition of `M`, a contradiction. The same argument covers decompositions into more than two pieces by grouping pieces.

### 2.2 Splitting a vertex into identical independent twins

Suppose a vertex of a signed multigraph is split into `a` independent twins, distributing `a` parallel copies of each incident edge as one copy at each twin, with identical signs and neighbours at every twin.

Frustration is unchanged: with all other vertex signs fixed, each twin has the same two possible costs, so all twins can be given the same minimum-cost sign. Conversely, any colouring after identification lifts. Several such twin classes may be treated successively.

If the identified graph is frustration-critical, so is the split graph: an optimal cut making an old parallel bundle bad makes every corresponding split edge bad.

Non-decomposability is also preserved. Identification can only increase the frustration of an arbitrary subgraph. If a decomposition of the split graph has frustrations summing to `t`, its projected, edge-disjoint subgraphs have frustrations at least those values. Their sum cannot exceed the frustration `t` of the identified graph. Equality therefore holds, and extracting critical subgraphs gives a decomposition of the identified graph.

Edges are treated as distinct throughout projection, even when they become parallel.

## 3. The unbounded irreducible non-decomposable family

### 3.1 A finite non-decomposable weighted complete graph

Fix `a >= 2` and put `q=2a+3`. Let `M_a` have two heavy vertices `x,y` and `q` unit vertices `U`:

* one edge between every pair of unit vertices;
* `a` parallel edges from each heavy vertex to every unit vertex;
* `a^2` parallel edges between `x,y`.

All edges are negative. Equivalently this is a weighted complete graph with vertex weights `a,a,1,...,1` and edge multiplicity equal to the product of endpoint weights.

The total vertex weight is `4a+3`. A cut whose one side has weight `s` contains exactly `s(4a+3-s)` edges, with multiplicity. Consequently the maximum cut has size

    (2a+1)(2a+2),

attained by sides of weights `2a+1` and `2a+2`. Since

    |E(M_a)| = 7a^2 + 11a + 3,

we have

    t_a := tau(M_a) = 3a^2 + 5a + 1.                         (1)

This graph is critical. The cuts with one side `{x,y,u}` or `{x,y,u,v}` are optimal, and collectively make every edge bad in at least one optimum.

Here is a direct proof of non-decomposability. Suppose a subgraph `J` is one part of a frustration-additive edge partition of `M_a`. Every optimal cut of `M_a` must then be optimal on `J`; call its constant bad-edge count `c`.

Write:

* `w` for the number of `xy` edges in `J`;
* `y_ij in {0,1}` for its edge on unit pair `i,j`;
* `Y=sum y_ij`, `d_i=sum_{j!=i} y_ij`;
* `h_i` for the combined number of `xi` and `yi` edges in `J`, so `0 <= h_i <= 2a`.

Optimal cuts with heavy-side unit set `{i}` give

    w + h_i + Y - d_i = c.

Thus `h_i-d_i=z` is independent of `i`. Optimal cuts with heavy-side unit set `{i,j}` give

    w + h_i + h_j + Y - d_i - d_j + 2y_ij = c,

so `z+2y_ij=0` for every pair. Hence all `y_ij` have one common value, either zero or one.

If that value is zero, then `z=0`, all `h_i=0`, and comparison with an optimal cut separating `x,y` gives `w=0`. Thus `J` is empty.

If it is one, then `d_i=2a+2`, `z=-2`, and `h_i=2a`. Each of the two heavy-to-unit multiplicities is therefore its full value `a`. An optimal cut separating the heavy vertices, with `a+1` unit vertices beside `x` and `a+2` beside `y`, has bad-edge count

    a(2a+3) + binom(a+1,2) + binom(a+2,2)
      = 3a^2+5a+1.

The cut with heavy side `{x,y,i}` has count

    w + 2a + binom(2a+2,2) = w + 2a^2+5a+1.

Equality forces `w=a^2`. Thus `J` is all of `M_a`. No nontrivial frustration-additive partition exists.

### 3.2 Replace the heavy bundle by a long balanced network

Choose a positive even integer `L`. Between `x,y`, replace their `a^2`-edge bundle by `L` independent layers of size `a`, complete bipartite graphs between consecutive layers, and `a` parallel edges from each terminal to each vertex of its adjacent layer.

Every level cut has `a^2` edges. Orient all edges forward through the levels: every internal vertex has `a` incoming and `a` outgoing edges, giving a unit-capacity flow of value `a^2`. Hence these level cuts are minimum cuts, and every network edge belongs to one.

The level bipartition makes the network bipartite. Monotone terminal-to-terminal paths have length `L+1`, and every terminal-to-terminal path has the same odd parity because `L` is even. Thus the all-negative network is balanced and has exactly the same boundary cost as the old negative bundle. Section 2.1 proves that the replaced multigraph is still `t_a`-critical and non-decomposable.

### 3.3 Split the heavy vertices to obtain a simple graph

Split each heavy vertex into `a` identical independent twins. Each twin is joined to every unit vertex and every vertex in the adjacent network layer. Section 2.2 preserves frustration, criticality, and non-decomposability.

The result is the following especially simple explicit graph `G(a,L)`:

* a clique `U` of order `q=2a+3`;
* independent layers `A_0,A_1,...,A_{L+1}`, each of order `a`;
* all edges between consecutive layers;
* all edges from `U` to `A_0 union A_{L+1}`;
* no other edges.

It has

    |V| = aL+4a+3,
    |E| = a^2 L + 7a^2 + 11a + 3,
    tau = t_a = 3a^2+5a+1.

Interior-layer vertices have degree `2a`, endpoint-layer vertices degree `3a+3`, and unit-clique vertices degree `4a+2`. In particular the graph is simple with minimum degree at least four, and has no vertex with exactly two neighbours. It is irreducible in the paper's sense.

The clique `U` together with any endpoint-layer vertex is a `K_(2a+4)`, giving the chromatic lower bound. For the upper bound, colour `U` with `q` colours, both endpoint layers with one new colour, and the internal layers alternately with two of the clique colours. Thus

    chi(G(a,L)) = 2a+4.

This proves the main counterexample theorem.

### 3.4 What this counterexample does and does not show

For any fixed chromatic threshold `K`, choose `a` with `2a+4 >= K`. Then `t_a` is fixed but the order of an irreducible, non-decomposable, minimum-degree-three-or-more, `t_a`-critical graph tends to infinity with `L`.

Moreover, since the full graph is frustration-critical, any subgraph retaining its full frustration `t_a` must retain every edge. Thus there cannot even be a bounded-order actual subgraph preserving the **full** frustration of all such cores.

However, a certificate need not preserve full frustration. Already

    G(a,L)[U union A_0 union A_{L+1}]
        = K_(2a+3) join an independent set of size 2a

has order `4a+3`, chromatic number `2a+4`, and frustration

    t_a-a^2 = 2a^2+5a+1.

For example, `a=2` gives an eleven-vertex subgraph of frustration 19, independent of `L`. There is also a `K_(2a+4)` on `2a+4` vertices. Consequently this family is **not** an obstruction to choosing a smaller-frustration local certificate. It specifically invalidates the general irreducible-core order bound and the assertion that only degree-two paths can account for unbounded critical order.

The growing balanced strips have edge-cuts of size `a^2` (four in the first example). The paper's two- and three-edge-sum discussion does not eliminate these strips. Frustration-additive recursive decomposition does not eliminate them either: the entire graph `G(a,L)` is non-decomposable.

These examples are outside `S*`: their unit clique already contains two vertex-disjoint odd triangles. They do not disprove a possible size bound within the stronger hereditary-indecomposability class `S*`, and they do not refute a theorem requiring sufficiently large odd girth. No such additional theorem is established here.

## 4. Chromatic number four does not force an actual minimum-degree-three critical subgraph

Let `Q=M(K3)`, with base triangle `a,b,c`, independent shadows `a',b',c'`, where each shadow is adjacent to the other two base vertices, and an apex `z` adjacent to all three shadows.

A three-colouring gives distinct colours to `a,b,c`; each shadow is then forced to have its corresponding base colour, leaving no colour for `z`. Giving `z` a fourth colour proves `chi(Q)=4`.

There are exactly four nonempty subgraphs of `Q` having minimum degree at least three. To see this, such a subgraph cannot be confined to the base triangle. A shadow has only its two base neighbours and the apex as neighbours, so including one forces the apex; the apex forces all three shadows, and the shadows force all base vertices and all nine non-base edges. Each base vertex needs at least one base-triangle edge. Thus the possible subgraphs are `Q` itself and `Q` minus one base-triangle edge.

If the retained base edges number `b` (two or three), these graphs have frustration exactly `b`. Each retained base edge belongs to its own triangle using the opposite shadow, and these triangles are edge-disjoint. Conversely, putting all base vertices and `z` on one side and all shadows on the other makes precisely those `b` base edges bad.

Deleting any apex-shadow edge leaves all these triangles intact, so it does not lower frustration. None of the four subgraphs is frustration-critical.

Therefore `Q` has **no** frustration-critical subgraph of minimum degree at least three.

This refutes a threshold-four forcing claim and a three-colourable fallback. It does not refute a four-colourable fallback or a forcing theorem at some threshold `K >= 5`.

If “3-core” means the usual iteratively peeled core, every frustration-critical subgraph of this seven-vertex example also has empty 3-core: any nonempty 3-core would be one of the four spanning subgraphs just listed, leaving no vertices available outside it, hence would make the critical graph itself one of those four noncritical graphs. In contrast, the one-step branch-induced graph of the three edge-disjoint triangles is the base `K3`. These notions of core must not be conflated when interpreting the proposed `+1` lemma.

## 5. Frustration decomposition cannot be treated as a chromatic decomposition

Given an arbitrary graph `J`, retain each edge `uv` and add a new private vertex `w_uv` adjacent to `u,v`. Call the result `D(J)`.

Its edges partition into `|E(J)|` triangles. Thus

    tau(D(J)) >= |E(J)|.

Every prescribed two-colouring of the original vertices extends to the new vertices with exactly one bad edge per triangle: if `u,v` agree, put `w_uv` opposite; if they differ, put it on either side. Hence equality holds.

Every edge can be the unique bad edge in its triangle in such an optimum. Therefore `D(J)` is frustration-critical and decomposes into those 1-critical triangles.

For `chi(J)>=3`, any proper colouring of `J` extends to each new degree-two vertex using a third colour, so

    chi(D(J)) = chi(J).

Taking `J=K_r` gives arbitrarily high chromatic number despite a complete frustration decomposition into triangles. Distinct triangles even share at most one vertex; their incidence need not form a tree. The decomposition theorem does not justify taking the maximum chromatic number of the chosen pieces.

This observation concerns a chosen decomposition, not a maximum over all critical subgraphs of `D(J)`; the original `J` remains a subgraph.

## 6. A valid comparison, and why an arbitrary-core additive-one comparison fails

If `H` is a spanning subgraph of `G` with `tau(H)=tau(G)=t>0`, take a maximum cut of `G`. All of its `t` bad edges must belong to `H`, since its restriction to `H` already has at least `t` bad edges. Thus `E(G) minus E(H)` is bipartite. Combining its two-colouring with a proper colouring of `H` gives

    chi(G) <= 2 chi(H).                                       (2)

This factor is sharp even for frustration-critical `H`.

For example, let `J` be two disjoint `K_r`'s joined by one edge, where `r>=3`, and let `H=D(J)`. Then `H` is connected and frustration-critical, with

    chi(H)=r,  tau(H)=r(r-1)+1.

Give all original vertices of the first clique cut-colour zero and those of the second cut-colour one. Extend across the private triangle vertices with one bad edge per triangle. Obtain `G` by adding all edges between the two sides of this cut.

The cut still has `r(r-1)+1` bad edges, while `H` supplies the same lower bound. So `tau(G)=tau(H)`. The original two cliques now form a `K_(2r)`, and (2) supplies the matching upper bound. Hence

    chi(G)=2r.

Thus `chi(G) <= chi(H)+1` is false for an arbitrary selected critical subgraph. For `r>=4`, the ordinary 3-core of `H` is precisely `J`, so replacing `H` by that chosen core does not repair the assertion.

For any graph `H`, deleting vertices of degree at most two gives

    chi(H) <= max(3, chi(core_3(H))).                         (3)

Likewise, a colouring with at least three colours of the one-step branch-induced graph extends over its degree-two paths and cycles. Equations (2) and (3) give the safe estimate

    chi(G) <= 2 max(3, chi(core_3(H)))

for a frustration-preserving critical `H`.

The 3-core need not itself be frustration-critical. Re-criticalizing it can lose chromatic number again. None of these facts proves an additive-one estimate with a maximum over **all** critical cores, nor a bounded-depth recursive reduction.

## 7. The precise remaining local-witness question

A sufficient theorem for a negative answer is:

> There exist a fixed `K` and a function `B : positive integers -> positive integers` such that every finite graph of chromatic number at least `K` contains a subgraph `H` with
>
>     t=tau(H)>=1,   |V(H)|<=B(t).

One can replace `B` by an increasing unbounded majorant, and set

    f(n) = min {t>=1 : n<=B(t)} - 1.

Then `f` is nondecreasing and divergent, but such a witness violates `tau(H)<=f(|V(H)|)`. Compactness transfers the resulting finite chromatic bound to infinite graphs. The witness is an actual subgraph, not a suppressed signed core or a minor.

The counterexamples above do not refute this statement. They show that its proof cannot simply consist of:

1. extract an arbitrary frustration-critical graph;
2. suppress degree-two paths;
3. apply a finite irreducible non-decomposable order bound.

Step 3 is false even for simple, high-chromatic, minimum-degree-four graphs. Step 1 also does not preserve chromatic number with the proposed arbitrary-core additive-one bound. A successful argument would still need a new chromatically useful selection or reduction theorem, or a direct multiscale certificate theorem of the type investigated in the other notes.

No universal divergent counterfunction for unrestricted graphs is established here. No conclusion contradicting the expanding-projective-annulus obstruction to polynomial witnesses is asserted.

## Verification

`Submission/check_Erdos74FrustrationCores.py` checks:

* exact maximum cuts and edge-criticality of small instances of the new family;
* the claimed order, size, degrees, clique lower bound, and explicit proper colouring;
* exact maximum cuts of the weighted base graphs and a modular-rank certificate corroborating their non-decomposability (the proof above is independent of this computation);
* with `--milp`, infeasibility of the necessary binary additive-decomposition equations for each tested full strip graph, using SciPy/HiGHS;
* exhaustive enumeration of the minimum-degree-three subgraphs of `M(K3)`;
* the connected sharp factor-two example with `r=3`.

Reproduce the complete checks with

    python3 Submission/check_Erdos74FrustrationCores.py --milp

The output is saved in `Submission/Erdos74FrustrationCoresChecks.txt`. Omitting `--milp` requires only NumPy and NetworkX.

The computation is a consistency check. The arbitrary-parameter counterexample and its non-decomposability are proved above, not inferred from finite samples. No claim of novelty or of an up-to-date literature resolution is made.
