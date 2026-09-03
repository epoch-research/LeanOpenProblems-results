# A global two-budget certificate, and the remaining vertex-augmentation gap

**Status: no full Erdős–Sós proof.** The result proved here is a constructive global edge-budget lemma, not an embedding theorem in disguise. It preserves a given partial embedding, fixes a chosen surplus edge, works with the actual density hypothesis in both parities, and identifies exactly where the original incidence surplus goes. A subcubic family shows that, even for a blocked maximal proper subtree, this surplus can be forced onto an edge whose two endpoints are already occupied. No Lean specification was changed.

All graphs are finite and simple. Embeddings are injective homomorphisms, not induced embeddings.

## 1. Two-budget lemma

Write

\[
 a=(k-1)/2,\qquad e(G)=a n+\eta,\qquad
 \eta\in\{1/2,1\},\qquad e_G(S)\le a|S|\quad(S\subsetneq V(G)).
\]

Let \(F\subseteq E(G)\) be an **existing** protected edge set. Choose an edge \(e_0=xy\), choose its direction \(x\to y\), and choose a rational \(0\le b\le a\) such that

\[
 d_F(v)-\eta\mathbf1_{\{e_0\in F,\ v\in e_0\}}\le b
 \qquad\text{for every }v.                                      \tag{1}
\]

Then there are nonnegative red and blue directed weights on the edges of G satisfying:

* the four weights on each undirected edge (two directions, two colors) sum to one;
* every edge of F has its entire weight blue;
* every vertex has red outweight \(a-b\);
* every vertex has blue outweight \(b\), except x, which has \(b+\eta\);
* the blue weight on \(x\to y\) is at least \(\eta\).

These weights are found by a finite max-flow computation. There is no tree-embedding oracle or leaf-count recurrence in the construction.

### Proof

Remove weight \(\eta\) from \(e_0\), obtaining a weighted graph B. It satisfies

\[
 w_B(E)=an,\qquad w_B(E(S))\le a|S|\quad\text{for every }S.
\]

At each vertex put a red bin of capacity \(a-b\) and a blue bin of capacity b. Each weighted edge must allocate its weight to bins at its endpoints. Protected edges may use only blue bins; other edges may use either color.

For any set A of positive-weight edges, put

\[
 U=V(A\setminus F),\qquad Z=V(A)\setminus U.
\]

The adjacent bins have total capacity \(a|U|+b|Z|\). Every edge of A not contained in U is protected and has an endpoint in Z. Therefore

\[
 w_B(A)
 \le w_B(E(U))+\sum_{z\in Z}d_{B[F]}(z)
 \le a|U|+b|Z|.                                                \tag{2}
\]

These are the weighted Hall inequalities. Explicitly, use source-to-edge arcs of capacities equal to edge weights, edge-to-allowed-bin arcs of unlimited capacity, and bin-to-sink arcs of the stated capacities. Inequality (2) says every cut has capacity at least \(w_B(E)\); max flow allocates all edge weight. Total bin capacity is also an, so every bin is full.

Interpret allocation to a bin at v as weight directed away from v. Restore the removed weight as blue weight \(\eta\) on \(x\to y\). This proves every assertion. QED.

### Integral specialization: fixed-edge, multiple-color protection

If \(a=r\), then \(\eta=1\). For integral \(b=q\), integral max flow assigns every edge of \(G-e_0\) wholly to one endpoint and one palette. Label the q blue outgoing edges at each vertex with q distinct colors, and similarly label its \(r-q\) red outgoing edges. This gives

\[
 G=P_1\dot\cup\cdots\dot\cup P_{r-q}
       \dot\cup Q_1\dot\cup\cdots\dot\cup Q_q
       \dot\cup\{e_0\},                                      \tag{3}
\]

where every P and Q is a spanning map (each component is unicyclic), and every P avoids F.

Thus, whenever \(\Delta(F-e_0)\le q\), one can delete **r−q entire functional colors**, protect all of F, and keep the **specified actual edge** \(e_0\) as surplus. There is no bound on \(|F|\). In particular, an existing subcubic partial tree can be protected from \(r-3\) colors, with any chosen protected edge pinned, when \(r\ge4\).

For even k, the flow construction still works; with half-integral b its output can be taken half-integral. We do **not** identify its blue support with an integral q-circuit or apply an odd-parameter embedding theorem to a doubled multigraph.

## 2. An exact, computable incidence invariant

Let C be the vertices reachable from x along positive blue arcs, and put \(X=V(G)\setminus C\). Write \(I_B\) for incident **blue weight**, and \(R(C,X)\) for red weight directed from C into X. Then

\[
 \boxed{e_B(C)=b|C|+\eta},\qquad
 \boxed{I_B(X)=b|X|},\qquad
 \boxed{I_G(X)=a|X|+R(C,X)}.                                  \tag{4}
\]

Indeed, no blue arc leaves C. All blue outweight of C is internal, while all blue weight incident with X has its tail in X. Red incident weight is its total outweight on X plus red weight entering from C. These observations give (4).

For nonempty X, criticality now gives the quantitative identity

\[
 R(C,X)=\eta+a|C|-e_G(C)\ge\eta.                              \tag{5}
\]

So this algorithm produces a concrete vertex set with **exactly zero blue incidence surplus**. Its entire surplus in the original graph is explicitly recorded on the red boundary. It does not silently replace density by minimum degree or by \(W_k\).

In the integral specialization, C is the unique q-circuit of the blue graph, and it contains both endpoints of \(e_0\). To see the circuit inequalities, a proper subset of C avoiding x has at most q times its order in edges. A proper subset containing x has an outgoing blue arc by reachability; that arc has integer weight at least one, so the same bound holds. Any positive subset must contain x and have no outgoing arc, hence must contain C. No such integral-circuit conclusion is needed for (4).

### What happens to connected pruned-subtree states

For a component D of the forest \(F-C\), let t be its order and let h be the number of protected edges from D to C. Every one of those h edges is blue and directed from D into C. The \(t-1\) internal tree edges are also entirely blue. Since D has total blue outweight bt,

\[
 \boxed{h\le(b-1)t+1}.                                      \tag{6}
\]

At b=1, every outside component has at most one attachment, so a tree F meets C in a connected subtree whenever the intersection is nonempty. At b=2, even one outside vertex may have two attachments. Connected-pruned-subtree states therefore are not automatically closed under this rank reduction.

## 3. A blocked maximal partial state for subcubic nonspiders

For every \(r\ge3\), put \(k=2r+1\), and take

\[
 W=\{0,\ldots,2r\},\quad u=2r+1,\quad v=2r+2,
\]
\[
 A=\{0,\ldots,r-1\},\qquad B=\{0,1\}\cup\{r+1,\ldots,2r-2\}.
\]

Let G consist of the clique on W, all edges from u to A, all edges from v to B, and uv. Then

\[
 |G|=2r+3,\qquad e(G)=r|G|+1,\qquad d_G(u)=d_G(v)=r+1.
\]

It is an actual r-circuit. For a proper subset with t clique vertices and j added vertices, j≤1 gives
\(e(S)\le\binom t2+jr\le r(t+j)\). If j=2 then t≤2r. For t≥1,

\[
 rt-\binom t2=t(2r+1-t)/2\ge r,
\]

so \(e(S)\le rt+r+1\le r(t+2)\); t=0 is immediate.

Protect the tree F with edges

\[
 u0,u2,\quad v0,v1,v(2r-2),
\]

and the path \(2-3-\cdots-(2r-3)\). It has

\[
 e(F)=2r=k-1,\quad |F|=2r+1=k,\quad\Delta(F)=3,
\]

with v its unique degree-three vertex. Add a new leaf \(\ell\) at u to obtain T. Thus T has k edges and **two degree-three vertices**, u and v: it is a nonspider subcubic tree, well within the low-maximum-degree case.

The displayed embedding of \(F=T-\ell\) is **nonextendible**. Its image is

\[
 V(F)=\{0,\ldots,2r-2\}\cup\{u,v\},
\]

which contains every neighbor of u. The only unused host vertices, \(2r-1,2r\), are not adjacent to u. So this is a maximal-cardinality proper connected-subtree state, not an easily extendible smaller state.

Set \(e_0=v0\). Then \(\Delta(F-e_0)=2\), and the lemma applies with **b=2**, preserving all \(k-1\) edges and deleting r−2 functional colors in the integral case.

**Every feasible two-budget flow with these parameters excludes the missing leaf's parent u from C, even if fractional allocations are allowed.**

Proof: v has exactly r−2 incident edges outside F. Its red outweight is r−2, so all those edges are wholly red and directed away from v. In particular,

\[
 R(v\to u)=1.
\]

Vertex u has red outweight r−2 and this additional incoming red unit. Its total incident edge weight is r+1, so its incident blue weight is at most two. Its blue outweight is already two. Hence it has **zero incoming blue weight** and cannot be reached from either endpoint of \(e_0\). QED.

Changing the pinned protected edge does not repair this at b=2: condition (1) forces that edge to meet v, the unique degree-three vertex. For all three choices and either direction, the same argument excludes u.

### Explicit output: the entire critical surplus is an occupied chord

For \(i=1,\ldots,r\), let \(R_i=\{\{j,j+i\}:j\in W\}\), with arithmetic modulo \(2r+1\). These spanning 2-factors partition the clique. Choose

\[
 Q_1=R_1+u0+v1,\qquad
 Q_2=R_2+u2+v(2r-2),\qquad e_0=v0.
\]

For j=1,…,r−2, the red map is \(R_{j+2}\) together with

* vu and u1, when j=1;
* \(u(j+1)\) and \(v(r+j-1)\), when j≥2.

These maps partition G as in (3) and avoid F. Orient each clique factor by \(j\to j+i\), the pendant edges toward the clique, and \(e_0\) from v to 0. Then

\[
 C=W\cup\{v\},\qquad X=\{u\},\qquad R(C,X)=1.
\]

The **only** red arc from C to X is \(v\to u\). Both endpoints are occupied, and u is precisely the blocked attachment vertex. Moreover, \(F[C]\) has two components: the star at v and the path \(2-3-\cdots-(2r-3)\). The outside singleton u has two protected attachments, attaining equality in (6).

This is **not** an Erdős–Sós counterexample. T embeds after reembedding F: send \(\ell\) to host u, send its parent (the tree vertex named u) to host 0, and map all other tree vertices bijectively to the remaining clique vertices. Every required edge exists. What fails is the proposed support/escape shortcut while retaining the given maximal partial state, not global embeddability.

## 4. Exact remaining gap

The two-budget lemma gives a global construction and the exact invariant (4), but **does not give a T-shaped vertex augmentation**.

To finish this route, one must jointly change the protected partial embedding (possibly its connected domain), the flow, and the blue reachable set, with a proved progress invariant, so that either an injective T-copy results or a nonempty original-host set has incidence at most \(a|X|\). It is not enough merely to preserve existing partial-tree edges and steer their support: Section 3 proves that every admissible flow at the proposed reduced budget excludes the missing leaf's parent, even for a subcubic maximal partial state. Nor does the guaranteed red escape furnish an unused vertex: in the explicit output its entire unit of critical surplus is the occupied chord vu. A different budget or a reembedding may succeed; no general joint progress theorem was proved.

No theorem establishing that joint vertex-augmentation step was obtained. The general Erdős–Sós assertion, including arbitrary low-maximum-degree trees, therefore remains unresolved here. The failed uniform leaf recurrence, stationary-root claims, and local rotation closure are not used.

## 5. Verification

Run `python3 Submission/ErdosSosGlobalCertificateChecks.py`.

The exact checker passed:

* 30,789 clique-family proper-subset type bounds and 87,024 direct proper-subset audits across the main and auxiliary families;
* the blocked maximal-partial-state construction for r=3,…,40: 38 explicit decompositions and 228 independent max-flow checks covering every admissible pinned edge and both directions;
* 4,297 flow instances on 136 critical atlas host/parameter pairs, including 2,550 genuinely half-integral outputs;
* 37 additional flows with genuinely non-half-integral rational budgets and outputs;
* 85 even-parameter flows on the critical split graphs from the prior leaf-count counterexamples, and 47,345 exact split-subset type bounds;
* 406 auxiliary integral decompositions and 55 further max-flow decompositions at other rank pairs;
* all edge weights, endpoint quotas, protected edges, reachability, identities (4)–(6), zero leaf extensions for the displayed partial states, and explicit full nonspider T-embeddings.

In total this is 4,702 max-flow outputs checked with exact rational arithmetic. A separate small-case audit used neither the flow code nor its construction functions: at r=3 it checked every proper host subset, the explicit partition and lower circuit, and all 203,490 possible red-edge sets containing the forced edge. Exactly 45,880 are avoiding spanning maps; every one leaves the blocked leaf-parent with degree at most two in its complement.

The run log is `Submission/ErdosSosGlobalCertificateChecks.log`; the independent enumeration log is `/tmp/es_global_certificate/independent_blocked_leaf.log`.

The proofs above are mathematical, not Lean formalizations. `Submission/Spec.lean` is unchanged, SHA-256 `674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103`.
