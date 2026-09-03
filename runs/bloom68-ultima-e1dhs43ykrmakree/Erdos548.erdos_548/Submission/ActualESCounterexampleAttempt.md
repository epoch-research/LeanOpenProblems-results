# Actual Erdős–Sós counterexample attempt: exact capacity and completion certificates

## Outcome — no ES counterexample obtained

**This investigation does not disprove or prove the unrestricted Erdős–Sós assertion.** I obtained no finite pair `(G,T)` satisfying both the required strict density and actual unrooted noncontainment. None of the rooted, fixed-cut, fixed-interface, or connected-parity-kernel counterexamples in the existing reports is being relabeled as an ES counterexample.

The substantive results are:

1. An **actual unrooted, nonbipartite, low-maximum-degree tree-free trap**, with an exact proof covering every possible use of its bridge. It misses the requested density by a quantified amount.
2. An **all-completions bound** for that trap: even allowing every missing edge on the same vertex set, any tree-free completion remains strictly below the ES threshold. This is not merely failure of one proposed orientation or completion algorithm.
3. A **nonuniform chamber extraction theorem**. For a family of two-hub targets, arbitrary interfaces between complete bipartite chambers either supply a full tree copy or yield an explicit low-incidence set. The theorem includes the capacity-tight two-cycle case where the first packing construction genuinely collides.
4. An explicit infinite family of **fully critical, nonbipartite, `(k−2)`-degenerate hosts** outside several standard terminal certificates, including *every* balanced colored minimum-degree core. These hosts nevertheless have a direct two-interface target embedding. Thus their orientation certificates are not being mistaken for tree-freeness.
5. A supplementary exact-kernel observation: **perfect or near-perfect matchings eliminate all admissible unrooted exact parity-kernel gaps**. This is a tree-only statement, not an ES proof.

Two particularly relevant finite instances use the same 44-vertex tree from `TreeExactKernelFindings.md`:

| Host | `k` | `n` | `e(G)` | `(k−1)n/2` | Actual containment status |
|---|---:|---:|---:|---:|---|
| Bridge trap, Section 3 | 43 | 85 | 1,293 | 1,785 | **T-free**, but 492 edges below threshold |
| Critical chamber host, Section 6 | 43 | 203 | 4,264 | 4,263 | **Contains T**, by an explicit injection |

Moreover, **every T-free supergraph of the 85-vertex trap on the same vertices has at most 1,425 edges**, still 360 below threshold.

These are complementary failed counterexample models, not a disproof. The chamber theorem closes the specified model, **not the full ES proof**. No Spec or shared Lean file was edited, and no new Lean formalization is claimed.

---

## 1. Exact target and density conventions

All graphs are finite, simple, and undirected. Containment means an **injective, edge-preserving map**, not an induced embedding. For a `k`-edge tree, put

\[
 a=(k-1)/2,\qquad e(G)=a n+\eta.
\]

An actual strict-average counterexample needs

\[
 n\ge k+1,\qquad \eta>0,\qquad T\not\subseteq G.
\]

The literal specification asks for `eta >= 1`. If an actual T-free example had `eta=1/2`, two disjoint copies of its host would have surplus one and would remain T-free because T is connected. **No such half-gap example was obtained here.** The positive-density construction below already has literal surplus one.

For a proper-induced critical host,

\[
 e_G(S)\le a|S|\quad(S\subsetneq V(G)),
\]

and hence every nonempty X satisfies

\[
 I_G(X)=e(G)-e(G-X)\ge a|X|+\eta>a|X|.                 \tag{1}
\]

Here `I_G(X)` counts edges incident with X, counting internal edges once. The new chamber theorem extracts a set violating (1), rather than extracting a failed rooted state.

The supplied high-`Delta(T)` theorem, bipartite-host theorem, core terminal, matching-defect boundary terminal, and exact degree-two-quotient theorem are retained. None is challenged or assumed to exhaust the residual hosts.

---

## 2. Targets and the distinction between parity gaps and noncontainment

Let `T_d`, `d>=2`, have two adjacent hubs x,y. Each hub has d support neighbors; each support has two leaves. Then

\[
 |T_d|=6d+2,\quad k=6d+1,\quad a=3d,\quad
 \Delta(T_d)=d+1,\quad |A_T|=|B_T|=3d+1.                \tag{2}
\]

These are strictly below the already proved high-maximum-degree regime.

There is a matching of size `2d+1`: match every support to one of its leaves and match x to y. The supports together with one hub form a vertex cover of size `2d+1`. Therefore

\[
 \nu(T_d)=2d+1,\qquad \alpha(T_d)=4d+1.                \tag{3}
\]

Deleting any one leaf preserves that matching number, since its support still has another leaf.

At `d=7`, this is exactly the target with

\[
 k=43,\quad\Delta=8,\quad\nu=15,\quad\alpha=29.
\]

The known connected-core spectrum at core budget six is

\[
 [13,18]\cup[20,27],
\]

so an exact odd count 19 is impossible there; its minimum core size is seven. The checker independently rechecks the retained-hub count formulas. **This says nothing by itself about embeddings into a host.** In particular, the explicit critical host in Section 6 embeds this very tree using two interfaces, with no exact-19 kernel requirement.

For the more general chamber theorem, write `T(p,q;ell)` for two adjacent hubs with respectively p and q supports and ell leaves at every support. Its parameters are

\[
 k=(\ell+1)(p+q)+1,\quad
 a=(\ell+1)(p+q)/2,\quad
 \Delta=\max(p+1,q+1,\ell+1).                           \tag{4}
\]

The theorem uses `ell>=2`, `q>=1`, and

\[
 (\ell-1)q\le p\le\ell q.                              \tag{5}
\]

These targets also lie in the low-maximum-degree regime. In particular, `ell=2` covers all `q<=p<=2q`, not just the symmetric example.

---

## 3. A genuine all-role tree-free trap

### 3.1 Construction

Fix `d>=2` and `b>=4d+2`. Take disjoint sets

\[
 |C|=6d-2=k-3,\qquad |A|=2d,\qquad |B|=b.
\]

Choose `u in C` and `v in A`. The host `H(d,b)` has:

* a clique on C;
* a clique on `A-{v}`;
* all A–B edges;
* the one bridge uv;
* no other edges.

In particular, B is independent and v has no neighbor in `A-{v}`. The receiver `H[A union B]` has vertex cover A. The graph is nonbipartite, and there are no missing A–B edges to blame for its obstruction.

### 3.2 Proof of actual unrooted noncontainment

**Proposition 1.** `T_d` does not embed in `H(d,b)`.

A copy avoiding the bridge would lie in one of its two components. It cannot lie in C, which has only `6d-2` vertices. It cannot lie in the receiver, whose matching number is at most `|A|=2d`, whereas (3) gives `nu(T_d)=2d+1`.

If a copy uses the bridge, exactly one target edge maps to uv. Deleting that target edge splits T into components lying on the two sides. There are only three edge types, and **all are excluded**:

1. **Hub–hub edge.** Both components have `3d+1` vertices. The receiver component is a hub with d two-leaf supports, rooted at v. All its supports must lie in B, since `N(v)` inside the receiver is exactly B. Since B is independent, its `2d` leaves must lie in `A-{v}`, which has only `2d-1` vertices.
2. **Hub–support edge.** The component orders are 3 and `6d-1`. The larger component cannot fit in C, so it lies in the receiver, with its exposed hub at v. The opposite hub and the `d-1` remaining supports at v all lie in B. Thus A must contain v, the `2d-2` leaves of those supports, and the d supports of the opposite hub: at least `3d-1>2d` vertices.
3. **Support–leaf edge.** The component orders are 1 and `6d+1`. Again the larger component cannot fit in C. But it is a leaf-deleted `T_d`, which still has a matching of size `2d+1`, impossible in the receiver.

The argument chooses no root in advance and covers every target edge that could use the bridge. QED.

### 3.3 Exact density deficit

The construction has

\[
 n=8d-2+b,\qquad
 e(H)=20d^2-18d+5+2db,
\]

so

\[
 \boxed{3dn-e(H)=4d^2+12d-5+db>0.}                     \tag{6}
\]

Taking `b=4d+3` gives a particularly useful low-degree trap with high host vertices:

\[
 n=12d+1,\quad e(H)=28d^2-12d+5,\quad\Delta(H)=k,
\]

\[
 \boxed{3dn-e(H)=8d^2+15d-5.}                          \tag{7}
\]

The vertices of `A-{v}` have degree exactly k. Nevertheless the graph is genuinely T-free. Its exact degeneracy is `k-4`: the clique C supplies that lower bound; remove B, then the small A-block, then C for the upper bound.

For `d=7`, this gives `n=85`, `e=1293`, `Delta(H)=43`, and the missing 43-edge target has maximum degree eight. **It is not an ES counterexample: the deficit is 492.** Also

\[
 I_H(B)=2d|B|<3d|B|,
\]

so B is already an explicit forbidden incidence set for criticality.

### 3.4 An exact weighted-capacity audit of all target choices

This trap is a mixed complete blow-up of five types. A loop in the following quotient means a clique type, not a loop in the simple host:

| Type | Capacity | Allowed neighboring types |
|---|---:|---|
| 0: u | 1 | 1,2 |
| 1: `C-{u}` | `6d-3` | 0,1 |
| 2: v | 1 | 0,4 |
| 3: `A-{v}` | `2d-1` | 3,4 |
| 4: B | b | 2,3 |

Because all indicated interfaces are complete, a capacity-respecting quotient homomorphism is equivalent to an injective non-induced host embedding. The standalone checker computes, for each rooted target subtree and each possible quotient color of its root, **every attainable occupancy vector**, clipping only at the actual capacities. Child states are convolved over every allowed adjacent color. All root colors are allowed at the final state.

For `d=2,3,4,7`, the final state set is empty. These are completed exact DPs, not timeouts. The generic DP was independently compared with complete color-assignment enumeration on 72 small fixed tests, and a positive 44-vertex control is obtained by completing B to a clique. The universal noncontainment assertion is established by Proposition 1, not inferred from these finite audits.

---

## 4. Circuit-density completion cannot repair this trap on its existing vertices

Merely observing the negative surplus in (6) is insufficient: one should ask whether density can be added while preserving noncontainment. Here that question has a rigorous negative answer for **every completion on the same vertex set**.

**Theorem 2.** If `J` is a T-free supergraph of `H(d,b)` on the same vertices, with `d>=2`, `b>=4d+2`, then

\[
 \boxed{e(J)\le20d^2+2d-3+2db<3d|J|.}                 \tag{8}
\]

More precisely,

\[
 3d|J|-e(J)\ge4d^2-8d+3+db>0.                         \tag{9}
\]

### Every new edge incident with B creates the whole tree

There are just two missing-edge types incident with B:

* **A B–B edge xy.** Put the two hubs at x,y, put the `2d` supports bijectively into A, and put the `4d` leaves into `B-{x,y}`. The latter has at least `4d` vertices. This is a full copy.
* **A B–C edge xy, `x in B`, `y in C`.** Put one hub at x, its d supports in A, and its `2d` leaves in `B-{x}`. Put the other hub at y and its whole half-tree inside the clique C. This uses only `3d+1<=6d-2` clique vertices.

Thus a T-free completion adds **no B–B or B–C edge**. This resolves all choices of those endpoints, not one fixed interface assignment.

### A four-edge matching across C–A is also a full repair

The target has at least four distinct leaf parents, since `2d>=4`. Delete four leaves with distinct parents. The remaining tree has exactly `6d-2=|C|` vertices.

If the C–A graph of J has a matching of size four, map these four parents to the matched clique endpoints, map the deleted leaves to their matched A-endpoints, and map the other target vertices bijectively to the remaining clique positions. Every remaining edge lies in the clique. This again gives a full T-copy.

Therefore the C–A graph has matching number at most three. By bipartite matching/vertex-cover duality it has a vertex cover of size at most three, and hence at most

\[
 3\max(|C|,|A|)=3|C|
\]

edges. Equivalently, a cover with x vertices in C and y in A, `x+y<=3`, permits at most `x|A|+y|C|-xy<=3|C|` edges.

Counting all remaining possible edges gives

\[
 e(J)\le\binom{6d-2}{2}+\binom{2d}{2}+3(6d-2)+2db,
\]

which is exactly (8). Subtraction proves (9).

At `d=7`, `b=31`, the upper bound is **1,425**, whereas the strict ES threshold is **1,785**. Even an optimal tree-free completion of this fixed trap cannot come within 360 edges of it. No ES theorem, criticality assumption, or prescribed-root theorem is used in this completion bound.

Adding entirely new vertices is a different operation. The next theorem closes a substantial recursively coupled model for that operation, but not arbitrary external reservoirs.

---

## 5. A no-counterexample theorem for arbitrary nonuniform chamber interfaces

### 5.1 Statement

Fix the parameters in (4)–(5). Suppose the **entire vertex set** of G is partitioned into a nonempty family of chambers

\[
 M_i=A_i\mathbin{\dot\cup}B_i,\qquad
 |A_i|=\ell q,\quad |B_i|=\ell p+1,
\]

and each A_i–B_i interface is complete. Edges inside A_i, inside B_i, and between different chambers are otherwise **arbitrary**.

**Theorem 3 — full-copy/low-incidence dichotomy.** At least one of the following holds:

1. `T(p,q;ell)` embeds in G;
2. some nonempty B_i satisfies
   \[
   \boxed{I_G(B_i)\le a|B_i|.}                         \tag{10}
   \]

Consequently **no proper-induced critical host in this chamber class is T-free**.

This theorem is not a fixed-U forest extension. The hub roles and the leaf used for repair are selected from the actual host interfaces. All nonuniform boundary endpoint choices below are allowed.

### 5.2 Three explicit packing certificates

Call a cross-chamber edge from B_i to A_j an arc `i -> j`. Parallel choices of endpoints are allowed; this is just a bookkeeping digraph on the chambers.

#### Certificate A: a B_i–B_j edge, `i != j`

Use it for the hub edge. In chamber i use p support positions in A_i and `ell*p` leaf positions in `B_i` other than its hub. In chamber j use q supports in A_j and `ell*q` leaves in B_j other than its hub. Capacities suffice because `q<=p<=ell*q`.

Thus T-freeness excludes **every** cross-chamber B–B edge.

#### Certificate B: an arc `i -> j` and any internal edge in B_j

Map the p-hub to the B_i endpoint of the arc and the q-hub to its A_j endpoint. The p-half fits in chamber i as above.

For the q-half, choose one endpoint of the internal B_j edge as a support and its other endpoint as **one leaf**. Choose the other `q-1` supports in B_j, avoiding that leaf. Place the remaining `ell*q-1` leaves in `A_j` other than its hub. All these sets have the required capacities.

Thus, in a T-free graph, **any chamber receiving an arc has independent B_j**.

#### Certificate C: two consecutive arcs `i -> j -> h`

Map the p-hub to the first B_i endpoint and the q-hub to the first A_j endpoint. In chamber j, include the B_j endpoint of the second arc among the q supports and use its A_h endpoint as one leaf. All other `ell*q-1` right-side leaves occupy `A_j` other than its hub.

The p-half uses p supports in A_i and all `ell*p` available leaf positions in B_i other than its hub.

* If `h != i`, all image sets are automatically disjoint.
* If `h=i` and `p<ell*q`, choose the p supports in A_i **avoiding** the external leaf endpoint. The one spare position is enough.

This is a genuine whole-tree reembedding. It does not attempt to preserve an old forest embedding. It also verifies the return-walk case explicitly, rather than treating repeated chamber indices as if they were disjoint.

### 5.3 Interior capacities: extraction of a deficient chamber

First suppose `p<ell*q` and no displayed copy exists. Certificate A eliminates all B–B cross edges. Certificate C says the arc digraph has no directed walk of length two. It therefore has a vertex i with no outgoing arc.

All edges incident with B_i then lie inside its chamber. Since its internal graph is simple,

\[
\begin{aligned}
 I_G(B_i)
 &\le |A_i||B_i|+\binom{|B_i|}{2}\\
 &=\left(\ell q+\frac{\ell p}{2}\right)|B_i|\\
 &\le \frac{(\ell+1)(p+q)}2|B_i|=a|B_i|.              \tag{11}
\end{aligned}
\]

The last difference is

\[
 a-\ell q-\ell p/2=\frac{p-(\ell-1)q}{2}\ge0.
\]

This proves (10). In the symmetric two-leaf case `p=q=d`, the last inequality is equality. **Even if B_i is a clique, the full strict critical surplus forces a usable boundary edge.**

### 5.4 The capacity-tight boundary `p=ell*q`

Here a two-arc return walk really can collide: its external leaf would lie in A_i, and the p-half already uses every A_i position as a support. That collision is not ignored.

If the arc digraph has a sink, (11) still applies. Otherwise every chamber has an outgoing arc. If there is a two-arc path on three distinct chambers, Certificate C supplies T. If there is not, every directed component is a **closed two-cycle**:

* for `i -> j`, every outgoing arc of j must return to i;
* every outgoing arc of i must return to j;
* an incoming arc from any third chamber would form a three-chamber path.

Every chamber now receives an arc, so Certificate B makes each B_i independent in a T-free graph. Moreover B_i can have neighbors only in its own A_i and the paired A_j. Therefore

\[
 I_G(B_i)\le2\ell q|B_i|\le a|B_i|,                    \tag{12}
\]

because at `p=ell*q`,

\[
 a-2\ell q=\frac{(\ell-1)^2q}{2}\ge0.
\]

The seemingly closed phase cycle therefore has a **density deficit**, not an ES counterexample. This proves the boundary case and completes Theorem 3.

### 5.5 Scope of the extraction

For the 44-vertex target, the chambers have sizes `(14,15)`. The theorem permits arbitrary internal edges, arbitrary A–A couplings, and fully nonuniform A–B and B–B interfaces. It is considerably more general than an independent blow-up of a degree-two quotient.

The proof produces either an actual injection of **all** target vertices or an explicit original-host low-incidence set. A low-incidence output alone is not a noncontainment certificate; a graph can contain T and also have such a set. It is sufficient to contradict criticality.

Crucially, an arbitrary critical graph has **not** been shown to admit this chamber partition. Nor has every arbitrary tree been reduced to these two-hub targets. Those are genuine limitations, not hidden induction hypotheses.

---

## 6. An exact critical family outside several standard terminal tests

The chamber theorem is not confined to graphs that fail the density condition. The following construction meets the literal ES edge bound and all proper-set inequalities exactly.

### 6.1 Construction and quota orientation

Fix `d>=2`, `m>=5`, with chamber indices modulo m. In chamber i let

\[
 A_i=H_i\mathbin{\dot\cup}L_i,\quad |H_i|=|L_i|=d,
 \qquad |B_i|=2d+1.
\]

Label A_i cyclically by `0,...,2d-1`, with H_i the first d labels. Add:

1. `K_(2d)` minus the antipodal perfect matching on A_i;
2. a clique on B_i;
3. every A_i–B_i edge;
4. every B_i–H_(i+1) and B_i–H_(i+2) edge.

There are no other base edges. Finally add one edge

\[
 s\ell_* ,\qquad s=b_{0,0}\in B_0,
 \quad\ell_*=a_{3,d}\in L_3.                            \tag{13}
\]

The edge was absent from the base graph.

Orient A_i forward at cyclic distances `1,...,d-1`; every A_i vertex has internal outdegree `d-1`. Orient B_i forward at cyclic distances `1,...,d`; its internal outdegree is d. Orient all own-chamber A–B edges from A to B, and all cross-chamber edges from B to H.

Every base outdegree is `3d`:

\[
 (d-1)+(2d+1)=3d\quad\text{on A},\qquad
 d+d+d=3d\quad\text{on B}.
\]

The base orientation is strongly connected. Each A_i contains the directed cyclic-distance-one cycle; its vertices reach all of B_i; B_i reaches H_(i+1), from which the whole next A_i is reachable. The module cycle reaches all chambers.

Orient (13) from s to ell_*. Then outdegree is `3d` everywhere except `3d+1` at s, which reaches all vertices. Consequently

\[
 n=m(4d+1),\qquad e(G)=3dn+1,                           \tag{14}
\]

and for every proper S,

\[
 e_G(S)=3d|S|+\mathbf1_{s\in S}-\operatorname{out}_D(S)
 \le3d|S|.                                             \tag{15}
\]

If s is in S, reachability gives an outgoing arc; if not, its indicator is zero. This is a full criticality proof. **It certifies density and sparsity only; tree-freeness is checked separately and is false.**

### 6.2 Degrees and degeneracy

The degrees are exactly:

| Type | Degree |
|---|---:|
| H_i | `8d+1` |
| ordinary L_i | `4d-1` |
| ell_* | `4d` |
| ordinary B_i | `6d=k-1` |
| s | `6d+1=k` |

Delete all L_i. Every B_i then has degree exactly `5d`; the H_i vertices have degree `7d+2`. Thus this retained graph has minimum degree `5d`. Conversely, peeling L, then B, then the residual d-cliques shows exact degeneracy `5d`.

In particular, the `(k-1)=6d` core is empty and

\[
 \operatorname{degeneracy}(G)=5d\le6d-1=k-2.
\]

The graph is nonbipartite, since each B_i is a clique of order `2d+1>=5`.

### 6.3 Explicit exclusions, not a claim that every known certificate was tested

These hosts are outside the following specific routes for `T_d`:

* **High target maximum degree:** `Delta(T_d)=d+1<k/2`.
* **Nonempty `(k-1)`-core:** excluded by the exact peeling above.
* **A `K_k`-minus-matching block:** such a block has minimum degree at least `6d-1`. Its vertices cannot include L, whose ambient degree is at most `4d`. After deleting L, B has degree only `5d<6d-1`; after deleting B only disjoint d-cliques remain.
* **Exact one-apex CL on any subgraph:** the weakest relevant residual minimum degree is `k-Delta(T_d)=5d`. In a candidate subgraph J, no L vertex can belong to `J-s_root`, and none can be the degree-at-least-k root. Thus J lies in `G-L`. There, every B vertex has degree `5d<k`, so the root must be in some H_i. To have degree k it must retain a B-neighbor, but that neighbor has degree at most `5d-1` after root deletion. Contradiction.
* **Embedding the whole nonleaf subtree among high host vertices:** the high set is `union H_i` together with s. In its induced graph, s is the only vertex of degree at least `d+1`; all other degrees are at most d. The nonleaf subtree of `T_d` has two vertices of degree `d+1`, so it does not embed there.
* **A dense bipartite subgraph to which bipartite ES applies:** any bipartite subgraph is proper, since G is nonbipartite. Proper vertex sets are sparse by (15); on the full vertex set deleting even one edge exhausts the surplus in (14).
* **An exact degree-two-quotient independent blow-up:** every such graph is 3-colorable, whereas G contains a clique of order at least five. This exclusion does not address arbitrary approximate/completed templates.
* **Complete multipartite structure:** nonadjacent vertices in different H_i have different neighborhoods, so they are not the false twins required for a common part.
* **A `(k+2)`-vertex induced block with forest complement:** such a block would have at least `3d(k+2)+1` edges, contrary to proper-set sparsity in this larger G.

There is a stronger colored-core exclusion, proved next. **No claim is made that these exclusions exhaust every possible absorbing cut, local defect lift, or other certificate in the workspace.**

### 6.4 No bipartite subgraph has minimum degree `3d+1`

This excludes every balanced colored greedy core for `T_d`, regardless of how its host bipartition is selected.

Suppose a bipartite subgraph J has minimum degree `3d+1`, with its two colors entirely free.

**Ordinary low vertices cannot occur.** A vertex of L_i has, outside L_i, only its `2d+1` B_i neighbors and its `d-1` H_i neighbors: `3d` positions. An ordinary L_i vertex in J would therefore require an oppositely colored L_i vertex. Both low vertices have all neighbors inside the same `(4d+1)`-vertex chamber, except possibly the single extra edge at ell_*. Their two opposite-color neighbor sets are disjoint. They would require at least

\[
 2(3d+1)-1=6d+1>4d+1
\]

positions in that chamber, impossible.

**The exceptional low vertex cannot occur alone.** If ell_* remains after ordinary low vertices are excluded, its available degree is exactly `3d+1`. All of B_3, all but its matching partner in H_3, and s must have the opposite color. A vertex of B_3 then has at most two opposite-color neighbors in its own chamber, plus the `2d` possible high neighbors in the next two chambers. This is

\[
 2d+2<3d+1\quad(d\ge2),
\]

another contradiction. Thus J contains no L vertex.

**No B_i can occur.** After deleting L, B_i has external neighbors only in the three d-sets `H_i,H_(i+1),H_(i+2)`. If J uses both colors inside B_i, the opposite-color degrees of one vertex of each color sum to at most

\[
 |B_i|+3d=5d+1<2(3d+1).
\]

If J uses just one color in B_i, its cross-degree is at most `3d`. Both alternatives are impossible.

Only disjoint H_i cliques of order d remain, also impossible at that minimum degree. QED.

This is a global bipartition argument, not a check only of the natural A/B coloring.

### 6.5 Nevertheless the entire target embeds, without the surplus edge

An explicit copy is as follows:

* `x -> b_(0,0)`;
* `y -> a_(1,0)`;
* put the d supports at x into `a_(0,0),...,a_(0,d-1)`;
* put their `2d` leaves bijectively into `B_0-{b_(0,0)}`;
* put the d supports at y into `b_(1,0),...,b_(1,d-1)`;
* put one leaf of the support at `b_(1,0)` into `a_(2,0)`;
* put the other `2d-1` right-side leaves bijectively into `A_1-{a_(1,0)}`.

The two inter-chamber target edges are exactly

\[
 b_{0,0}a_{1,0},\qquad b_{1,0}a_{2,0}.
\]

They belong to the original interfaces. All other target edges are own-chamber A–B edges. All `6d+2` images are distinct. In particular, **the added surplus edge (13) is not used**: the equality-density base graph already contains T.

At `d=m=7`, this gives

\[
 \boxed{n=203,\ e=4264=21n+1,\ \delta=27,
 \ \operatorname{degeneracy}=35,\ k=43,\Delta(T)=8.}
\]

This is an exact low-degree critical **non-counterexample**, despite all the exclusions above. It illustrates why producing a critical circuit outside common terminals still does not establish noncontainment.

---

## 7. A supplementary matching explanation for exact-kernel flexibility

The connected parity-kernel gap is a useful warning, but it disappears for a broad class of targets.

**Proposition 4.** A tree with a perfect or near-perfect matching has an exact parity kernel for every admissible c.

* If T has a perfect matching M of size m, then for every `1<=c<=m-1` the core can contain **any prescribed tree vertex**.
* If T has a near-perfect matching M of size m, then for every `1<=c<=m` there is an unrooted exact kernel. No arbitrary-root conclusion is asserted in this case.

**Proof.** Contract every matching edge. The quotient is a tree whose blocks have size two, except for the one unmatched singleton in the near-perfect case.

In the perfect case choose a connected set of `m-c` pair-blocks, containing the block of the prescribed root. Its lift is a connected core of order `2(m-c)`. In the near-perfect case choose a connected set containing the unmatched block and `m-c` pair-blocks; its lift has order `2(m-c)+1`.

All vertices outside the core are partitioned into exactly c matching pairs. The endpoints of each such edge have opposite distance parity from the connected core. Therefore there are exactly c odd and c positive-even vertices. The odd set is independent, and every neighbor of a positive-even vertex is odd. This is the required kernel. QED.

For `T_7`, the matching deficiency is `44-2*15=14`, so this positive proposition does not remove its known gap. It does show that forcing a phase/cardinality obstruction through perfect-matching targets cannot simply reuse that gap. **Neither proposition nor the negative kernel example is a host noncontainment theorem.**

---

## 8. Verification and artifacts

Files added:

* `Submission/ActualESCounterexampleAttempt.md` — this report;
* `Submission/ActualESCounterexampleAttemptChecks.py` — standalone exact constructions and audits;
* `Submission/ActualESCounterexampleAttemptChecks.log` — completed run output.

Reproduce the full audit with

```sh
python3 Submission/ActualESCounterexampleAttemptChecks.py --mincut
```

The completed run passed in about 54 seconds in this environment. Its checks include:

* **4,824 full tree injections**, checked for domain, injectivity, and every target edge;
* **60 analytic chamber parameter triples**, including all tested leaf arities `2,3,4` and their permitted capacity ranges;
* **720 return-walk** and **960 three-chamber** repairs;
* **15 capacity-tight two-cycle low-incidence certificates**;
* all **128** presence/absence patterns of the six directed interfaces on three fixed chambers, with or without a B–B cross edge; a low-incidence result is not mislabeled as noncontainment;
* **11 bridge-trap parameter audits**, **308 leaf-deleted matching witnesses**, and explicit checks of all three target-edge cut types;
* **339 B–B** and **784 B–C** individual completion-edge repairs, including every such edge for the three smallest tested traps;
* **1,584 four-leaf matching completion repairs**;
* completed negative capacity DPs at `d=2,3,4,7`, retaining **168 cached subtree states** and checking **3,509 exact transitions**;
* **72** independent complete color-assignment comparisons for the DP, and a positive 44-vertex control;
* **five** full critical orientation/degree/degeneracy audits, including the displayed 203-vertex graph;
* **250 exact integer max-closure/min-cut certificates**: global maximum surplus one, and maximum surplus zero when omitting each vertex, for both the 45-vertex and 203-vertex critical graphs. These independently cover every proper vertex subset;
* **1,520 constructive matching-block parity-kernel certificates**, and the explicit `T_7` spectrum/minimum-core audit.

A separate exact-integer arithmetic audit also checked the displayed trap formulas through `d=200` and the chamber inequalities through leaf arity 30. It passed.

The all-subsets orientation proof, the bridge proof, the completion inequality, and the chamber extraction are the mathematical certificates. The checks do not infer a general theorem from finite success and do not treat a solver timeout as nonexistence. No blind numerical counterexample search was used.

Every pre-existing `Submission/*.lean` file was checksum-compared with its pre-investigation version and was unchanged. `Spec.lean` retains SHA-256

```
674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103
```

---

## 9. What remains unresolved

The actual requested disproof still requires **one pair simultaneously satisfying strict density and full unrooted noncontainment**. This report supplies neither that pair nor a proof that such a pair cannot exist generally.

The positive and negative certificates do establish the following precise boundaries:

* The five-type bridge-capacity obstruction is genuinely unrooted, but its density deficit cannot be repaired by **any** tree-free fixed-vertex completion.
* Nonuniform interfaces between the specified chambers cannot hide all repairs: either an explicit full copy is available or one chamber has an actual original-host incidence deficit. Tight two-cycles are included, not assumed away.
* An arbitrary external vertex or reservoir need not belong to a complete chamber, and an arbitrary critical host need not have the required chamber partition. The proof does not extend to those cases merely by repeating the orientation bookkeeping.
* General independent target sets and component re-embeddings remain available even when an exact connected parity kernel is unavailable. The 44-vertex target demonstrably embeds in the new critical family.
* The standard terminal exclusions in Section 6 do not provide a decomposition theorem for all remaining hosts. Their failure is not evidence of T-freeness.

**Final status: exact model-level progress, no actual ES counterexample, and no unrestricted ES proof.**
