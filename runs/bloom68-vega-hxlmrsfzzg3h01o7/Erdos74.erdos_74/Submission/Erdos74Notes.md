# Erdős 74: a concrete obstruction to the proposed polynomial negative route

## Status of this work

This does **not** prove or disprove Erdős Problem 74. No up-to-date literature status was verified: attempts to access the exact problem page and the exact cited paper failed because network name resolution is unavailable. No broad corpus search was performed.

What is proved below is a counterexample to the suggested universal square-root witness, and indeed to every positive power-law witness at chromatic number 4. This is a mathematical proof, not just an inference from computations. No claim of novelty is made.

Write tau(H) for the minimum number of edges whose deletion makes H bipartite.

## Main partial theorem

**For every alpha > 0 and epsilon > 0 there exists a finite graph G with chi(G) = 4 such that every subgraph H of G satisfies**

    tau(H) <= epsilon |V(H)|^alpha.

Consequently, there is no absolute c > 0 such that every graph of chromatic number at least 4 has a subgraph H with tau(H) >= c sqrt(|V(H)|). The same is true with sqrt(n) replaced by any n^alpha, alpha > 0.

The graphs can additionally have arbitrarily large odd girth. Passing to a 4-critical subgraph preserves the conclusion.

## Explicit construction

Start with the usual three-quadrilateral cellulation of the projective plane whose graph is K4. The face boundary walks, in order, are

    F1 = (0,1,2,3), F2 = (0,1,3,2), F3 = (0,2,1,3).

Every edge is in exactly two faces, and each vertex link is a triangle. Subdivide every K4 edge into an odd number L >= 3 of edges. Call the resulting graph S_L. It has 6L-2 vertices, odd girth 3L, and is 3-colourable. Each old face now has boundary length 4L.

Fill each of the three faces as follows, using an integer R >= 1.

Given its current boundary cycle (v_i), of even length m, attach an annulus with outer cycle

    w_(0,0), w_(0,1), w_(0,2), w_(1,0), ..., w_(m-1,2).

Add the radial edges v_i w_(i,0) and v_i w_(i,2). Its quadrilateral faces are

    (v_i, v_(i+1), w_(i+1,0), w_(i,2)),
    (v_i, w_(i,2), w_(i,1), w_(i,0)),

with cyclic indices. Repeat R times. The boundary length is multiplied by 3 at every step. Finally add a cap vertex joined to every other vertex of the final boundary cycle. All cap faces are quadrilaterals.

Call the resulting graph G_(L,R). There are three cap vertices, one in each original face. Write P_(L,R) for the graph with these cap vertices removed.

### Why chi(G_(L,R)) = 4

Each annulus retracts homomorphically onto its inner boundary, fixing that boundary: send

    w_(i,0) -> v_(i-1), w_(i,1) -> v_i, w_(i,2) -> v_(i+1).

Hence P_(L,R) maps homomorphically to S_L and is 3-colourable. Colour all three cap vertices with a fourth colour.

For the lower bound, suppose that a 3-colouring exists and identify the colours with Z/3Z. Give each oriented edge the integer increment +1 or -1 agreeing with its colour difference modulo 3. The sum around each quadrilateral is both even, between -4 and 4, and divisible by 3; it is therefore zero. Summing over the quadrilaterals filling each old face shows that the increment sum on each F_i is zero.

As oriented chains, after subdivision just as before subdivision,

    F1 + F2 - F3 = 2 C,

where C is the subdivided triangle (0,1,2,0), of odd length 3L. Thus its increment sum would be zero. A sum of an odd number of signs +/-1 cannot be zero. Contradiction.

This is the familiar winding-number proof behind **Youngs' theorem on nonbipartite projective-plane quadrangulations**; the displayed chain identity makes it explicit for this construction.

### Odd girth and a global edge-deletion bound

Every face interior, including its cap, is bipartite. Thus an odd cycle must meet S_L.

An odd cycle not using a cap lies in P_(L,R), which maps to S_L, so it has length at least 3L. A cycle using a cap and meeting S_L has length at least 2(R+1), since each of its two routes from the cap to S_L traverses all R annuli. Consequently

    odd_girth(G_(L,R)) >= min(3L, 2R+2).

For R >= 2L the odd girth is exactly 3L.

There are 24L radial edges between S_L and the first annuli. Delete them, and delete one edge from each of the subdivided opposite edges 01 and 23. The base becomes bipartite, and all face interiors are separate bipartite graphs. Therefore

    tau(G_(L,R)) <= K_L := 24L+2,

independently of R.

## The hereditary logarithmic estimate

The essential point is an estimate for **arbitrary subgraphs**, not just the full graph or a complete annular prefix:

    tau(H) <= 2 + 4 log_2(|E(H)|+1)             (H a subgraph of P_(L,R)).    (1)

Here is the proof.

In the dual of each annulus, call its first and second quadrilateral at position i respectively A_i and B_i. Retain the dual edges from A_i to B_i and from A_i across its one outer boundary edge; retain the two dual edges from B_i across its two outer boundary edges. Repeating through the annuli gives a full rooted binary tree below each original boundary edge. At the outer face its leaves can be continued by free infinite binary trees. Different original boundary-edge trees have disjoint quadrilateral vertices.

Mark a retained dual edge exactly when the primal edge it crosses belongs to H. There are at most M=|E(H)| marked edges in any one tree. A full binary tree with M marked edges has a root-to-infinity ray meeting at most log_2(M+1) marked edges. One proof is induction on M: choose the child branch containing fewer marked edges, counting its initial edge. If the initial edge is marked, its remaining subtree has one fewer marked edge; if it is unmarked, no cost is paid. This gives the stated logarithmic bound. For M=0 the assertion is immediate.

Choose an edge e on the subdivided 01 path and an edge e' on the subdivided 23 path. Both belong to old faces F1 and F2. In each of those two faces, connect e to e' by two outward dual rays joined through the outer face. The four rays together cross at most 4 log_2(M+1) edges of H. Add e and e' themselves, at cost at most 2.

Deleting the crossed edges makes H bipartite. This can be seen directly, without relying on a max-cut duality theorem. Properly 2-colour S_L minus e,e'. On the boundary of F3 this colouring alternates throughout; on each of F1,F2 it alternates except at e,e'. Each face annulus is naturally bipartite. In F1 and F2 flip this natural bipartition on one side of the dual arc connecting e to e'. Its boundary colours now agree with those of S_L, and the only potentially monochromatic edges are precisely the crossed edges. This yields (1).

Equivalently, the two base edges and four dual rays form a noncontractible dual closed walk. Every odd primal cycle has odd mod-2 intersection with that walk, and therefore meets the deleted edges.

The uncapped graph P_(L,R) has maximum degree at most 9. If H is any n-vertex subgraph of the **capped** graph and n < R, its nonbipartite components cannot contain a cap: such a component meets S_L, and a path from S_L to a cap alone requires at least R+2 vertices. Discarding bipartite components leaves a subgraph of P_(L,R), with at most 5n edges. Hence

    tau(H) <= B(n) := 2 + 4 log_2(5n+1)       whenever n < R.                (2)

For all n, tau(H) <= K_L.

### Deduction of the main theorem

Given alpha,epsilon > 0, choose odd L >= 3 so large that

    B(n) <= epsilon n^alpha for every n >= 3L.

This is possible because log(n)=o(n^alpha). Choose integer R >= 2L so large that

    K_L <= epsilon R^alpha.

For an n-vertex subgraph H:

* n < 3L: H is bipartite, by the odd-girth bound;
* 3L <= n < R: apply (2);
* n >= R: apply tau(H) <= K_L <= epsilon R^alpha <= epsilon n^alpha.

This proves the theorem.

## Why this does not solve the arbitrary-slow problem

The estimate driving the construction is logarithmic, not an arbitrary diverging function. It gives no construction for f(n)=log log n, for example, and it only asserts chromatic number 4 rather than unbounded finite chromatic numbers.

There is also an actual logarithmic barrier within the projective-quadrangulation class. The following argument makes it explicit.

First, an elementary lemma valid for all graphs: let F be the monochromatic edges of any cut and U their endpoints. If G[U] is bipartite, one of its bipartition classes is an independent set meeting every edge of F; assign it a third colour. Thus if chi(G)>=4 and the odd girth is g,

    2 tau(G) >= g.                                                         (3)

Now let Q be a nonbipartite quadrangulation of the projective plane, let C be a shortest odd cycle of length g, and put r=ceil(g/2). By Youngs' theorem and (3), tau(Q)>=r. The dual graph has maximum degree 4. Take its radius-r ball B about the at most 2g dual vertices incident with edges of C. Then

    |B| <= 4g 3^r.

Let H consist of primal edges whose dual edges have both ends in B, and their endpoints. Then |V(H)| <= 16g 3^r.

For completeness, weighted max-cut duality here says that tau(H) is the minimum H-edge weight of a noncontractible dual cycle. One direction follows from mod-2 intersection with odd primal cycles. For the other, extend any two-colouring of H to all vertices of Q. Its monochromatic edges have even incidence at every dual vertex (all primal faces are even), so form an Eulerian dual subgraph. Their odd intersection with C forces a noncontractible dual cycle among them.

Every noncontractible dual cycle meets C. If it stays inside B, its entire length is counted and is at least tau(Q)>=r. If it leaves B, at least r of its edges inside B are counted on the way out from C. Hence tau(H)>=r. Since g<=2r and r>=2,

    |V(H)| <= 32r 3^r,
    log_2 |V(H)| <= 5r,
    tau(H) >= (1/5) log_2 |V(H)|.

Thus sublogarithmic bounds really do exclude nonbipartite projective-plane quadrangulations, even though no power-law bound does. Extending such an argument to arbitrary 4-chromatic graphs remains unproved here; not every chromatic obstruction is supplied by this surface structure.

## Other useful checks

A much simpler warning against a global-order bound: take independent triples T_0,...,T_L, put a triangle in T_0, join consecutive triples by K_(3,3) minus the same-label matching, and add an edge between equal-label vertices of T_0 and T_L, for odd L>=3. Every 3-colouring propagates the initial three distinct colours unchanged along the triples, contradicting the last edge. The graph is 4-colourable, and deleting the three initial triangle edges makes it bipartite. Its first two triples already contain three edge-disjoint triangles, so tau=3. This refutes a global-order bound but by itself does not refute a hereditary one.

## Lean and computation

`Submission/Erdos74Analysis.lean` compiles under the installed Lean 4.27/mathlib environment without `sorry`, `axiom`, or `admit`.

It contains:

* a faithful proposition `Statement` for Problem 74, quantifying over all finite subgraphs and finite sets of **unordered edges**;
* a proof that absence of every finite colouring is equivalent to chromatic number top;
* the independent-cover three-colouring lemma;
* the cut-support lemma used in (3).

The surface construction and its estimates above are proved mathematically, not formalized in Lean.

Targeted computations were consistency checks, not substitutes for these proofs. The annular construction was implemented in `/tmp/projective_frustration.py`. For L=3, the capped examples with R=0,1,2,3,4 had respectively

    (vertices, edges, tau, odd girth)
    (19,   36,   6, 5)
    (127,  252, 20, 7)
    (451,  900, 21, 9)
    (1423,2844, 21, 9)
    (4339,8676, 21, 9).

All faces were checked to have length 4 and the Euler characteristic was 1. Tau was calculated via signed dual shortest cycles; independent max-cut MILP checks agreed on the first two capped examples and on several uncapped examples. Thirty random induced-subgraph comparisons also agreed. The 19-vertex example was independently certified not 3-colourable and 4-colourable by Sage's MILP colouring routine. The binary-tree estimate was exhaustively checked on all 16,384 markings of a depth-3 binary tree.


Additional exact certificates in `/tmp/check_annular_certificates.py` were checked for (L,R)=(3,1),(3,2),(3,4),(5,3),(7,2): an explicit proper 4-colouring, the integer face-chain identity giving twice the odd base triangle, the explicit 24L+2-edge bipartizing deletion, and maximum degree at most 9 after removing the three caps.
