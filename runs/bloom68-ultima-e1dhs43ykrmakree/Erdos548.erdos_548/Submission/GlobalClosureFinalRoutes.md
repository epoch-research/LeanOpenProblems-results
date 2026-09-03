# Additional global closure attempts: variable degeneracy and degree balancing

## Status

**No unrestricted Erdős–Sós proof or disproof was obtained.** Spec.lean and all other Lean files remain unchanged. The results below identify exact, independently audited gaps; none is an assumed embedding theorem.

## 1. Variable-degeneracy hole moving: a proved mechanism with the wrong state space

The W_k condition from critical density is

    for every nonempty X, some v∈X has 2d_G(v)−d_{G[X]}(v)≥k.

Equivalently, G is strictly f-degenerate for f(v)=2d_G(v)−k+1, or there is an acyclic orientation with outdegree+2 indegree≥k. A direct consequence is that the induced layer {v:d_G(v)≤D}, if nonempty, is (2D−k)-degenerate. This does not itself embed a specified tree.

A genuine degree-tight closure appears in Bang-Jensen, Schweser and Stiebitz, *Digraphs and variable degeneracy*, arXiv:2012.09713. Source:

    /corpus/src/2012.09713/variable_degeneracy_arxiv.tex
    claim_non-partitionable_eulerian, around lines 182–214.

In a connected digraph D with sum_i f_i(v)≥max(d⁺(v),d⁻(v)), suppose D has no f-partition and an f-partition of D−v is given. Failure to insert v into every part forces equality of the whole degree budget. In each part i, every bad induced subgraph after insertion must contain every neighbor of v in that part. Consequently any such neighbor can replace v as the hole. Repeating this move makes the whole reached component Eulerian with both degrees equal to f_i. The same proof applies to bidirected graphs and gives ordinary degree equality in the reached component.

The primary independently read the source proof, including the equality chain and why deleting a neighbor removes EVERY obstruction. This is a valid hole-changing closure, but the states are partitions into degenerate induced subgraphs. Images of specified rooted trees do not form that state space: moving a hole across an arbitrary incident host edge need not preserve the multiple adjacencies of an internal target role. No transfer theorem was established.

The graph f-partition theorem under sum_i f_i(v)≥d_G(v) does not directly apply to the single W-function unless d_G(v)≥k−1. Adding another part merely permits the trivial partition (G,empty), since G is already strictly f-degenerate. Empty parts and unspecified shapes are essential differences, not details that can be omitted.

### Why the cover/transversal theorem also does not fix injectivity

Lu, Wang and Wang, *Cover and variable degeneracy*, arXiv:1907.06630, define a cover by requiring edges between any two cells to form a MATCHING:

    /corpus/src/1907.06630/Brooks-SFDT.tex, around lines 26–30.

For a natural tree-embedding encoding, a cell consists of all possible host images of one target vertex. Equal-image conflicts between two cells are matchings, but forbidden host-nonedge pairs for adjacent target vertices generally are not. Thus the natural conflict graph is not a cover of the stipulated type. Allowing a transversal merely to be f-degenerate for f>1 would also allow actual violated embedding constraints. The source does not establish the needed injective embedding.

### Other checked source limits

* Zaker, arXiv:1103.1112, gives the bootstrap ordering/resistant-set equivalence with resistance d_K(v)≥d_G(v)−τ(v)+1. Taking τ(v)=k−d_G(v) recovers W_k, not a shape-compatible tree augmentation.
* Iriarte Giraldo, arXiv:1412.8114, `dual.tex`, around lines 2091–2136, encodes percolation by monomial ideals. The characterization still concerns resistance, not a prescribed tree's isomorphism type.
* Fan–Hong–Liu, arXiv:1804.06567, explicitly say that their incidence hypothesis is used only through W_k (`1804.06567.tex`, around line 83). The proved embedding conclusion is for spiders. The primary independently checked this passage.
* The Friedman–Pippenger expansion condition quoted in arXiv:0706.4100 requires |N(X)|≥(d+1)|X| for all small X. W_k does not imply it: K_(r,2r) satisfies W_(2r), but its 2r-side has only r neighbors.

No unrestricted W_k theorem was found in this scoped search.

## 2. Extremal degree balancing: the legitimate implication and the missing lift

Fix a missing k-edge target T. A hypothetical counterexample can be chosen with minimum host order, then maximum edge count, then minimum sum of squared degrees Φ. This retains proper induced-set sparsity and the incident-edge inequalities.

If δ(G)≥k−1, choose a vertex h of degree≥k, greedily embed T minus a leaf with its parent at h, and restore the leaf using an unused neighbor of h. Thus a counterexample has u,v with d(u)≥k and d(v)≤k−2.

Choose x∈N(u)\(N(v)∪{v}), and transfer ux to vx. The degree gap guarantees an x exists. The new graph G' has the same number of edges and

    Φ(G')−Φ(G)=−2(d(u)−d(v)−1)<0.

Extremality therefore implies G' contains T. Every such copy uses the new edge vx. Removing that edge yields two embedded components of T−e, but this does not reconnect them in G: u can already be occupied, and substituting its role may destroy other required edges.

The unresolved step is a GLOBAL lifting of one of these switch-created copies, or extraction of a low-incidence set from all failures. Neither edge saturation nor the variance inequality proves it.

## 3. An analytic obstruction to replacing the missing lift by local assumptions

For r≥3 put k=2r, and let T be the tripod with arm lengths r−1,r−1,2. Let G consist of two cliques A∪{h} and B∪{h}, with |A|=|B|=r and no A–B edges. Then

    n=2r+1, e=r(r+1), d(h)=2r, d(w)=r for w≠h.

The tree T has maximum degree three and is absent from G. A copy would span G. If a noncentral target vertex mapped to h, the component toward the tripod center would have more than r vertices after deleting that vertex, so fit in neither wing. If the center mapped to h, the component orders r−1,r−1,2 would have to partition into two sums equal to r. No subset has sum r.

Choose v∈A and any nonempty proper S⊂B, with t=|S|. Transfer all edges hs, s∈S, to vs. Then

    Φ(G_S)−Φ(G)=2t(t−r)<0.

Yet G_S contains T explicitly. Choose s∈S and b∈B\S, put the center at v, and use these three arms:

1. a path through all r−1 vertices of A\{v};
2. a path starting v–s through all r−1 vertices of B\{b};
3. the path v–h–b.

All edges exist and the arms are otherwise disjoint. At t=0 the graph is T-free, and at t=r it is isomorphic to G by swapping h and v, so it is T-free again. Every intermediate partial transfer creates T and decreases variance. G is also T-saturated, and the donor h is universal, so the recipient's old neighborhood is nested in the donor's.

This does NOT refute ES or a transfer theorem using full positive-density extremality. Its density deficit is

    ((k−1)/2)n−e(G)=r²−r−1/2>0.

It is not edge-count extremal: the T-free graph K_(2r) plus an isolate has r(r−2) more edges. It rules out using minimum degree, a high donor, saturation, nested neighborhoods, or convexity along the transfer as substitutes for the missing global proof.

## Conclusion

The variable-degeneracy theorem rigorously moves holes, but not holes in specified-tree embeddings. Variance extremality rigorously creates copies after balancing, but does not lift them back. Neither gap was resolved. No new complete theorem can be inserted into Spec.lean on the basis of these attempts.
