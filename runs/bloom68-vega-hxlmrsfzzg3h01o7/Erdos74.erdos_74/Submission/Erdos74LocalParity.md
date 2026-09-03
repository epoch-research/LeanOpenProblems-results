# Erdős 74: local parity certificates and a criticality obstruction

## Status

These are mathematical partial results, not a proof or disproof of Erdős 74. No Lean is used. The main reduction below removes the global parameter tau(G) from the extraction of a frustration witness **when bounded-length cycle-parity constraints already require many defects**. A stronger rooted argument gives logarithmic witnesses from one odd-cycle equation and bounded-length even-cycle checks, without a surface or bounded-incidence hypothesis. The parity-profile formulation is also shown to be equivalent to the original arbitrarily-slow question after reparametrizing the function.

The unproved part remains showing that a suitable scale/coset with a large minimum defect support must occur in every graph of sufficiently large chromatic number. The Hajós example shows that a direct tau-free version of the supplied no-delay lemma, valid for every r, is false even under 4-criticality.

Write tau(G) for the minimum number of edges whose deletion makes G bipartite. Unless explicitly stated otherwise, graphs in the arguments are finite and simple. Subgraphs need not be induced or connected.

## 1. A bounded-arity sparse-solution lemma

Let E be a finite coordinate set and let A be a system of affine equations over F_2. Suppose every equation involves at most q coordinates, where q >= 2. Let

    d(A) = min {|supp(x)| : x satisfies A}.

Assume the system is consistent and d(A) >= r >= 1. There is a subsystem A' involving at most

    q + q^2 + ... + q^r <= 2 q^r

coordinates such that every solution of A' has at least r nonzero coordinates among those coordinates.

### Proof

Build a rooted search tree whose nodes carry sets S of coordinates, starting with S empty. At a node with |S| < r, the vector 1_S cannot satisfy A. Choose an equation Q_S that it violates. Branch over all e in Q_S minus S, giving the child S union {e}. Stop at depth r. (A branch with Q_S contained in S has no children.)

Let A' consist of the chosen equations. There are at most 1 + q + ... + q^(r-1) internal nodes, so the coordinate bound follows.

Suppose x satisfies A'. Starting at S empty, maintain S contained in supp(x). At an internal node, x and 1_S have different parities on Q_S. They agree, with value 1, on Q_S intersect S. Thus some e in Q_S minus S has x_e = 1. Follow this child. After r steps, S contains r distinct nonzero coordinates of x. This proves the claim.


The exponential dependence on r cannot be replaced by a polynomial for arbitrary bounded-arity affine systems. For example, take a full binary tree with r vertex-levels, one variable x_v per tree vertex, the equation x_root=1, and, at each nonleaf v with children a,b, the homogeneous equation x_v+x_a+x_b=0. Every solution contains a root-to-leaf path of ones, so its weight is at least r; a single such path is a solution of weight r. If any nonleaf equation is omitted, the path from the root to that vertex, with all other coordinates zero, satisfies all remaining equations and has weight at most r-1. Thus every subsystem certificate retaining the weight-r lower bound must retain all nonleaf equations, and involves all 2^r-1 coordinates. This is an abstract parity example, not a claim about realizability by cycle equations of a simple graph.

The relevant branching depth counts **new nonzero coordinates**, not logical derivation length. No bound on coordinate occurrence, number of equations, proof length, or total coordinate set is needed.

## 2. Application to graph frustration

For an integer L >= 3 define

    a_L(G) = min |F|,

where F ranges over subsets of E(G) satisfying

    |F intersect E(C)| = |E(C)|  (mod 2)

for every cycle C of length at most L. This is a parity condition, not merely the condition of meeting every short odd cycle. In particular, short even cycles impose constraints too.

For a two-colouring p: V(G) -> F_2, define

    x_p(uv) = 1 + p(u) + p(v).

This is the indicator of its monochromatic edges. On every cycle C, summing gives

    sum_{e in C} x_p(e) = |E(C)|  (mod 2).

Conversely, satisfying these equations for **all** cycles is equivalent to being the monochromatic-edge vector of a two-colouring: integrate 1+x along paths from a root in each component.

Consequently:

* a_L(G) is well-defined, nondecreasing in L, and at most tau(G).
* It is zero when L is below the odd girth.
* It equals tau(G) once the cycles of length at most L span the entire binary cycle space; certainly this holds for L >= |V(G)|.

### Local parity certificate theorem

**If a_L(G) >= r, there is a subgraph H of G with**

    tau(H) >= r,
    |V(H)| <= L + L^2 + ... + L^r <= 2 L^r.

### Proof

Apply the search-tree construction to the cycle-parity equations of length at most L. Let H be the union of the cycles selected at its internal nodes. There are at most 1 + L + ... + L^(r-1) selected cycles, each with at most L vertices, giving the stated vertex bound.

Every two-colouring of H satisfies the parity equation on every selected cycle. Its monochromatic edges must therefore number at least r, by the sparse-solution lemma. Hence tau(H) >= r.

Equivalently, the proof can be read directly as a deletion certificate. At a node S, take a short cycle on which S has the wrong parity. Any putative cut agreeing with all selected bad edges in S must supply another bad edge from that cycle outside S. Every root-to-leaf branch charges r distinct bad edges.

This is an actual subgraph witness; it does not create edges, contract paths, or count repeated copies of one original edge as different defects.

## 3. A class for which this proves the desired near-logarithmic obstruction

Suppose chi(G) >= 4, its odd girth is g, and its binary cycle space has generators of length at most L. Then a_L(G) = tau(G).

Recall the elementary cut-support argument: the endpoints U of a minimum bad-edge set satisfy |U| <= 2 tau(G). If G[U] were bipartite, one of its bipartition classes would be an independent set meeting every bad edge; recolouring it with a third colour would properly three-colour G. Thus G[U] contains an odd cycle, and

    2 tau(G) >= g.

Set r = (g+1)/2. The local parity certificate theorem gives

    tau(H) >= r,
    |V(H)| <= 2 L^r.

In particular, if for fixed constants A >= 1 and d >= 1 the cycle space has generators of length at most A g^d, then

    |V(H)| <= exp(O_{A,d}(r log r)).

This implies

    tau(H) >= c_{A,d} log |V(H)| / log log |V(H)|

for sufficiently large |V(H)|, with the finitely many small cases handled by reducing the constant or using regularized logarithms. To see the inversion, write x = log |V(H)|. If r >= x the conclusion is immediate; otherwise log r <= log x and x <= K r log r <= K r log x.

Thus an appropriately small constant multiple of log n / log log n, taken to be zero on an initial finite interval, forces three-colourability **within this class**. This is not yet an assertion for arbitrary graphs.

### Relation to the projective-plane construction

For a cellular projective-plane quadrangulation Q, its binary cycle space is spanned by the facial quadrilaterals together with any noncontractible odd cycle C. For a shortest such cycle of length g, one can take L = max(4,g). Therefore the argument above gives a near-logarithmic witness without using the degree of the dual graph.

The logarithmic dual-ball result in Erdos74Notes.md is stronger than this basic application for surfaces. The rooted refinement in Section 3A recovers and slightly improves that logarithmic conclusion algebraically. Both parity arguments extend beyond embeddings, manifold structure, and bounds on the number of faces incident with an edge.

More generally, if a graph is the one-skeleton of a complex whose cells have bounded boundary length and whose binary first homology is generated by a short odd cycle, then its cycle space has exactly this kind of generating set. If an integer torsion/winding argument additionally proves non-three-colourability, the same extraction applies.


## 3A. A stronger rooted certificate: logarithmic, without a dual graph

There is a useful improvement when the only inhomogeneous equation is one odd-cycle equation. It avoids repeatedly paying its possibly large arity.

### Rooted homogeneous certificate lemma

Let B be a homogeneous binary linear system, every row of which has support size at most q >= 3. Let C be a set of g coordinates. Suppose

    Bx = 0,   sum_{e in C} x_e = 1

is consistent and has minimum solution weight at least r.

There is a subsystem, retaining the C equation, with the same lower bound r, obtained by selecting at most

    g [1 + (q-1) + ... + (q-1)^(r-2)]

rows of B (zero rows if r=1). In particular, the large C equation is used just once at the root.

Proof: branch first on an edge e in C, setting S={e}. At a node with 0 < |S| < r, if 1_S violates a row Q of B, select Q and branch on each e in Q minus S. Since Q is homogeneous and is violated, |Q intersect S| is odd and in particular nonzero; hence there are at most q-1 children. If 1_S satisfies B, then its C parity must be zero, since otherwise it would be a full solution of weight less than r. Close this branch without adding an equation. Stop ordinary branches when |S|=r.

Let A' consist of the root equation and the selected homogeneous rows. To prove its minimum weight is at least r, suppose otherwise and take a **minimum-weight** solution x of A'. Its C parity is one, so choose e in C intersect supp(x) at the root. As before, at a violated homogeneous row one can select a new coordinate in supp(x), maintaining S contained in supp(x). This path cannot reach a closed branch: there S is nonempty, satisfies every original homogeneous row, and has C parity zero. Thus x+1_S would still satisfy A', with strictly smaller weight. The path must reach |S|=r, the desired contradiction.

The minimum-support pruning is essential. A general solution may contain such a removable homogeneous piece, but a minimum solution cannot.

### Graph form

Let C be an odd cycle of length g in a graph G. Let E be a collection of even cycles of lengths at most q. Define

    d_E(C) = min {|F| : |F intersect C| is odd,
                         |F intersect Q| is even for every Q in E}.

If d_E(C) >= r, then there is a **connected actual subgraph** H of G satisfying

    tau(H) >= r,
    |V(H)| <= g (q-1)^(r-1).

Indeed use C and the even cycles selected by the rooted certificate. Each selected even cycle meets the previously selected graph in at least one edge, since Q intersect S is nonempty and S consists of already selected edges. It therefore introduces at most q-2 new vertices. Summing over the tree gives

    |V(H)| <= g + (q-2) g sum_{i=0}^{r-2}(q-1)^i
            = g (q-1)^(r-1).

Every cut-defect vector on H satisfies all its selected equations. The rooted lemma therefore proves tau(H)>=r. This argument uses neither an embedding nor any bound on the number of even cycles containing a given edge.

### Consequence for short even generators plus one odd generator

Suppose the binary cycle space of a non-three-colourable G is generated by even cycles of length at most q together with a shortest odd cycle C of length g. Then d_E(C)=tau(G), so with r=(g+1)/2,

    tau(H) >= r,
    |V(H)| <= g (q-1)^(r-1).

For fixed q this is a logarithmic witness, not merely a log n / log log n witness. For q=4 the explicit bound is

    |V(H)| <= (2r-1) 3^(r-1) <= 4^r,
    tau(H) >= (1/2) log_2 |V(H)|.

The elementary inequality displayed here holds for r=1,2,3,4 by direct evaluation, and propagates from r>=4 since

    3 (2r+1)/(2r-1) <= 4.

In particular this gives a purely parity-based alternative to the dual-ball proof for projective-plane quadrangulations, with an improved explicit constant. More importantly, it proves the same conclusion for arbitrary binary cycle spaces with the generating property, with no surface or bounded-incidence assumption.

This still does **not** handle arbitrary four-chromatic graphs. If G has ordinary girth greater than q, there are no even-cycle rows of length at most q at all, and d_E(C)=1. Thus the additional generating/coset-distance hypothesis cannot simply be dropped.

## 4. A precise general gap

A sufficient next theorem would be:

> There exist fixed k, delta > 0 and L_0 such that every graph with chromatic number at least k and sufficiently large odd girth has some L >= L_0 for which a_L(G) >= L^delta.

This statement is **not proved here**, and is not asserted to be true or known. It is a proposed intermediate target, substantially more precise than an appeal to bounded fan-in.

If it held, set r = ceil(L^delta). The parity-certificate theorem would give a hereditary frustration witness of order at most 2 L^r, hence exp(O_delta(r log r)). A sufficiently small constant multiple of log n / log log n (zero for small n) would then rule out chromatic number k. This would give the requested negative conclusion for Erdős 74.

There is also a useful necessary consequence of the hereditary hypothesis, with no chromatic assumption:

**If tau(H) <= f(|V(H)|) for every H contained in G, with f nondecreasing and f(n) = o(log n / log log n), then, uniformly for sufficiently large L, a_L(G) < L^delta for every fixed delta > 0.**

Proof: if a_L(G) >= ceil(L^delta) = r, the certificate gives n <= 2 L^r and

    r <= f(n) <= f(ceil(2 L^r)) = o(r),

since log(2 L^r) / log log(2 L^r) is asymptotic to r/delta as L tends to infinity. Contradiction. The threshold depends only on f and delta, not on G or tau(G).

For an arbitrary divergent f one may work with its nondecreasing tail-minimum minorant when seeking a counterexample to the universal Erdős statement.

## 4A. The parity-profile reformulation is qualitatively equivalent

Write T_n(G) for the maximum tau(H) over all subgraphs H with at most n vertices. For finite graphs, the elementary restriction argument and the certificate theorem give

    T_L(G) <= a_L(G),
    a_L(G) >= r  implies  T_{ceil(2 L^r)}(G) >= r.

The first inequality holds because a short-cycle parity solution on G restricts to a full cycle-parity solution on every at-most-L-vertex subgraph.

These two implications show that replacing the hereditary frustration profile by a_L does not change the **arbitrarily slowly divergent** version of the problem, after reparametrizing the function.

Explicitly, let h(L) be any nondecreasing integer-valued function tending to infinity, for L>=3. Set

    N_L = ceil(2 L^(h(L)+1)),
    f(n) = min {h(L) : L>=3 and N_L>=n}.

Then f is nondecreasing and tends to infinity. Indeed, for each K there are only finitely many L with h(L)<K, and their N_L have a finite maximum. Also f(N_L)<=h(L). Consequently, if every subgraph H of G satisfies tau(H)<=f(|V(H)|), then a_L(G)<=h(L) for every L: otherwise the certificate with r=h(L)+1 would give a subgraph on at most N_L vertices with tau at least h(L)+1, contradicting monotonicity of f.

Conversely, if a_L(G)<=h(L) for every L, then every n-vertex subgraph satisfies tau(H)<=h(n), for n>=3; smaller subgraphs are bipartite.

The same argument applies to infinite graphs. Define a_L to be the least size of a finite support satisfying the short-cycle equations, or infinity if none exists. If a_L>=r, the finite search tree still extracts a finite witness. Alternatively, the compactness of the space of binary vectors of support at most r shows that finite solvability with that weight bound implies global solvability.

Therefore Erdős 74 is equivalent to asking for infinite-chromatic graphs with a_L bounded by an arbitrarily slowly divergent prescribed function of L. This is a reformulation, not a solution. Its advantage is that it isolates a finite-support parity quantity while preserving the strength of the original question.

## 5. Why 4-criticality alone does not remove a delay parameter

Here is a rigorous obstruction stronger than merely having large critical order at fixed tau.

### Arbitrarily delayed second frustration at fixed odd girth

**For every N there is a 4-critical graph G of odd girth 3 such that every subgraph H on at most N vertices has tau(H) <= 1.**

Choose a 4-critical graph J of ordinary girth greater than N+2, and an edge uv of J. Such J exist by the classical existence of graphs of arbitrarily large girth and chromatic number, followed by taking a 4-critical subgraph.

Let D = K_4 - ab, on vertices a,b,c,d. Identify a with u, retain J-uv, and add the edge bv. This is the Hajós join of K_4 and J.

### Chromatic criticality

In any three-colouring of D, a and b have the same colour: they are both adjacent to the adjacent vertices c,d. The new edge bv would therefore force u and v to have different colours. This would extend the colouring of J-uv to J, a contradiction. The graph is four-colourable: take a four-colouring on J-uv; choose b different from v, then choose distinct colours for c,d outside the colours on a,b.

It is edge-critical, as follows.

* If an edge e of J-uv is deleted, three-colour J-e, where u and v differ because uv is present. Put b in u's colour and c,d in the other two colours.
* If bv is deleted, three-colour J-uv and extend with b=a and c,d in the other colours.
* If an edge e of D is deleted, a three-colouring of K_4-e has a and b different, since ab is an edge there. Combine its restriction with a three-colouring of J-uv, in which u and v necessarily have the same colour.

There are no isolated vertices, so this gives 4-criticality in the usual all-proper-subgraphs sense.

### The hereditary small-subgraph bound

Let |V(H)| <= N. The part of H inside J-uv is a forest, because J has girth greater than N+2. A cycle using bv would also use a b-to-u path through D and a u-to-v path in J-uv. Every such latter path has length at least girth(J)-1, so no such cycle fits in H. Other cycles cannot traverse the two pieces, which otherwise meet only at u. Consequently every cycle of H is contained in D.

Deleting cd makes D bipartite, and therefore makes H bipartite. This proves tau(H) <= 1. The graph still contains the triangle acd, so its odd girth is exactly 3.

### Exact global frustration

There is also an exact identity:

    tau(G) = tau(J) + 1.

For fixed two-colours on a,b, the minimum number of bad edges of D is 1 if a=b and 2 if a differs from b. Minimizing also over b and including bv gives

    min cost on D plus bv = 1 + 1_{u=v}.

For a fixed cut on J-uv this is one more than the cost of restoring uv. Minimizing proves the identity.

For 3 <= L <= N, in fact a_L(G)=1: all cycles of those lengths lie in D, and choosing F={cd} meets the parity equations there. Thus the local parity profile can have an arbitrarily long plateau even in 4-critical graphs of fixed odd girth.

This does not refute a multiscale near-logarithmic witness theorem: the graph J can supply a witness at a much later scale. It does rule out bounding the first tau>=2 witness solely in terms of odd girth and 4-criticality.

In particular, the supplied no-delay lemma cannot simply have its global t=tau(G) parameter replaced by an arbitrary function of r alone while retaining its stated hypotheses for every r. Take r=1: odd girth 3 is greater than 2r, but the first tau>=r+1 witness can be larger than any prescribed N, even in a 4-critical graph. This refutation does not rule out a theorem restricted to sufficiently large odd girth and an adaptively chosen later scale.

## 6. The bounded-fan-in warning

The sparse-solution lemma explains exactly what a useful bounded-arity certificate must supply: each branch must force **a new bad original edge**.

The cut equations can always be written with arity three as

    x_uv = 1 + p_u + p_v.

But p_u,p_v are free vertex-colour variables, not bad-edge coordinates. Branching on them need not increase the frustration count. Introducing auxiliary variables to make long parity equations fan-in two has the same problem. Thus syntactic bounded arity of a DPLL or propagation proof is not enough.

A long odd cycle already demonstrates the issue: it has no constant-size nonbipartite subgraph, despite having this arity-three presentation. Any argument that charges every such propagation step as a new frustration unit would fail on that example.

The missing step for general graphs is therefore not the sparse bounded-arity extraction, which is proved above. It is obtaining sufficiently strong bounded-length constraints at an appropriate scale, or an alternative certificate with an equally valid new-bad-edge charging rule.
