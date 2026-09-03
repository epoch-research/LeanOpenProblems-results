# Forest interfaces: a proved marked lemma and genuine set-selection obstructions

**Status.** Neither unrestricted `W_k => every k-edge tree` nor Erdős–Sós is
proved here. The results are a self-contained marked-forest theorem for
triangle-free hosts, a consequent special case of W_k, and counterexamples to
specific stronger interface/root-selection claims. The main counterexample is
itself **triangle-free and incidence-dense**, and it **does contain the target
unrooted tree**. `Submission/Spec.lean` was not modified.

Throughout, graphs are finite and simple; embeddings are injective,
edge-preserving, and **not necessarily induced**. Write

    ID_k: I_G(X) > (k-1)|X|/2 for every nonempty X,
    W_k:  some v in X has 2 d_G(v) - d_{G[X]}(v) >= k, for every nonempty X.

Here `I_G(X)` counts edges with at least one endpoint in X.

## 1. Exact deletion bookkeeping and the unavoidable interface

The source theorem was checked in
`/corpus/src/1011.3882/intro.tex` and `theorem.tex`: Goldberg–Magdon-Ismail prove
that a forest F embeds if `|H| >= |F|` and `delta(H) >= e(F)`. Their induction
allows global re-embeddings; it does **not** preserve arbitrary marked roots.

For a fixed host order, put

    sigma_G(v) = d_G(v) + number of earlier neighbors of v.

If D is deleted and H retains the restricted order, the exact identity is

    sigma_H(v) = sigma_G(v)
                 - |N_G(v) intersect D|
                 - |N_G(v) intersect D intersect {vertices earlier than v}|.

Thus deleting a prefix S gives

    sigma_H(v) >= k - 2 q(v),       q(v)=|N_G(v) intersect S|,           (1)

while deleting a tail loses only one unit per deleted neighbor. These are
identities/inequalities about degrees, not marked-embedding assertions.

For an independent tree set U of size r, write `m=sum_{u in U} d_T(u)`.
Then F=T-U has

    e(F)=k-m,       |F|=k+1-r,       c(F)=m-r+1.

Contracting the components of F gives a bipartite tree on U and those
components. In particular, if r>1, some component has at least two incident
boundary edges. They can demand either an intersection list at one vertex or
several different marked vertices in that component.

For a chosen bijection `psi:U->S`, the exact list for a surviving tree vertex x is

    L_psi(x) = intersection_{u in N_T(x) intersect U} (N_G(psi(u)) intersect H),

with the empty intersection interpreted as V(H). An embedding of F respecting
these lists is equivalent to completing the chosen interface. The degree
transport (1) supplies no automatic compatibility of these lists with the
components of F. Section 4 gives an explicit failure even with ample degree,
large lists, full vertex-list Hall inequalities, and separate embeddability of
every component.

## 2. A proved one-mark-per-component theorem for triangle-free hosts

**Theorem.** Let F be a forest **without isolated vertices**, with p components
and e edges. Let H be triangle-free with `delta(H) >= e`. Choose one root in each
component of F. Then **every injective assignment of those p roots to H extends
to an embedding of F**.

Equivalently, if each of these roots has a list L_i in H, a list-respecting
embedding exists **if and only if** the p root lists satisfy Hall's condition.
No restrictions are imposed on nonroot vertices.

### Proof: initialize by a matching, then grow the forest

First, in any triangle-free graph of minimum degree at least p, every p-vertex
set R has a matching to distinct vertices outside R. To check Hall, suppose
`X subset R`, `Y=N_H(X)-R`, and `|Y|<|X|`. If X contained an edge uv, then
triangle-freeness would make N(u) and N(v) disjoint. Both are contained in
`R union Y`, whose size is at most `2p-1`, whereas their total size is at least
`2p`: a contradiction. Thus X is independent. But then any x in X has all its
neighbors in `(R-X) union Y`, a set of size less than p, again a contradiction.

Apply this with R the prescribed root images; `p<=e`. At each tree root choose
one incident tree edge, and embed these p disjoint edges using the matching.
The currently embedded portion P now meets each target component in a
connected subtree **with an edge**.

Suppose P is incomplete, and grow a component along a boundary edge xy, with
x already embedded. The occupied neighbors of the image of x pull back to an
independent set of P: two adjacent such neighbors would form a host triangle.
An independent set in a nontrivial tree C has size at most `|C|-1=e(C)`.
Consequently the total number of occupied neighbors is at most

    sum_C e(C) = e(P) < e <= d_H(phi(x)).

There is a fresh neighbor for y. This operation preserves the invariant and
finishes the embedding. It also proves the stronger extension statement for
**any** initial embedding meeting each component in a connected nontrivial
subtree. QED.

The no-isolates qualification matters for prescribed roots. Unmarked isolated
vertices may be placed afterwards if `|H|>=|F|`. Marked isolated vertices need
additional list room; the next corollary handles its isolated vertices last.

### Why the hypotheses are real

* Without triangle-freeness, even two prescribed one-edge components can fail.
  Take two triangles on `{0,1,2}` and `{3,4,5}`, joined by the edge `23`.
  The host is connected with minimum degree 2. Prescribe the two matching
  roots at 0 and 1. Both need an endpoint outside `{0,1}`, but their only
  available neighbor is 2. The root lists themselves have distinct
  representatives.
* Allowing two marks in one component also fails, **even with large lists**.
  In `H=K_{3,3}`, take F=P3 and require its two endpoints in opposite host
  parts. Both lists have size 3=|F| and `delta(H)=3>=e(F)=2`, but a two-edge
  path has endpoints in the same host part. Section 4 strengthens this to an
  actual incidence-dense tree-deletion interface in which each component is
  individually feasible.

## 3. A consequent W_k special case, without a universal interface

**Corollary.** Suppose G is triangle-free and satisfies W_k. Every k-edge tree
T with

    Delta(T) >= floor(k/2)+1

embeds in G. More precisely, every tree vertex u satisfying this inequality
can be mapped to **any** host vertex s with `d_G(s)>=k`.

Here the root prescription is a conclusion under an explicit additional
hypothesis, not a claim for arbitrary W_k targets.

**Proof.** Singleton sets in W_k give `delta(G)>=ceil(k/2)`. Put
`d=d_T(u)`, `e=k-d`, and H=G-s. Then

    delta(H) >= ceil(k/2)-1 >= e.

Let q be the number of nontrivial components of T-u and let l=d-q be the number
of isolated components, i.e. the leaf neighbors of u. Each nontrivial component
has exactly one vertex formerly adjacent to u. Assign these q roots to
arbitrary distinct neighbors of s, and use the theorem to embed their forest
into H. It uses e+q vertices. Since `d_G(s)>=k=e+d`, at least
`k-(e+q)=l` neighbors of s remain unused. Put the l leaf neighbors there and
u at s. The star case q=e=0 is immediate. QED.

The proof actually only needs G triangle-free, `d_G(s)>=k`, and
`delta(G-s)>=k-d_T(u)`.

**Obstruction checks.** In `K_{2,7}` with P5 rooted at its middle vertex and s
in the two-vertex part, the required forest has two edges but
`delta(G-s)=1`. In the stated W_14 maximum-root example the required forest
has ten edges but `delta(G-s)=7`. Neither is accidentally included in this
corollary.

## 4. Main counterexample: even globally choosing a bijection does not repair a fixed highest-degree tree set

This refutes the tempting extension of the complete-interface proof:

> Choose the r highest-degree vertices U in the smaller tree bipartition,
> delete r independent high-degree host vertices S, embed T-U using the
> transported degrees/minimum-degree forest theorem, and complete the
> nonuniform interface, allowing an arbitrary bijection U->S.

It fails even when S is **exactly the set of all maximum-degree host vertices**,
the target's top r vertices are **unique**, the host is triangle-free and ID_k,
and all forest components separately respect their attachment lists.

### Host: k=13, r=3

Take independent sets A,C,B of sizes

    |A|=3,       |C|=31,       |B|=7.

Let the core be `K_{34,7}` with parts `A union C` and B. For each pair
`ij in {01,02,12}`, take a separate wing `K_{16,16}` with parts P_ij and Q_ij.
Let H be the disjoint union of the core and these three wings.

Add an independent set `S={s_0,s_1,s_2}`. Join every s_i to all of A. For i<j,
join s_i to all of P_ij and s_j to all of Q_ij. Add no other edges.

Then

    |G|=140,       e(G)=1111,       |H|=137,
    delta(H)=7 = k-2r.

Host degrees are

    S:35,       A:10,       C:7,       B:34,       wing vertices:17.

Thus S is independent and consists of the **three unique maximum-degree
vertices**, all with degree at least k. G is connected and triangle-free:
H is bipartite componentwise, S is independent, and every N_G(s_i) is independent.

The order `S, A, B, C, wings` witnesses W_13. The initial scores in these blocks
are respectively at least `35,13,37,14,18`. Deleting its prefix S has exactly
the heterogeneous transport (1).

### A complete certificate of incidence density

Assign each edge total weight one, split between its endpoints as follows:

| Edge type | Endpoint allocation |
|---|---|
| S--A | all weight at A |
| A--B | `124/287` at A, `163/287` at B |
| C--B | `247/287` at C, `40/287` at B |
| inside a wing | `1/2` at each endpoint |
| S--wing | `1/3` at S, `2/3` at the wing endpoint |

The resulting loads are

    every core vertex: 247/41 > 6,
    each s_i:          32/3   > 6,
    each wing vertex:  26/3   > 6.

For every X, the sum of its vertex loads is at most I_G(X). Hence every
nonempty X satisfies `I_G(X)>6|X|`, which is **ID_13**. This is a rational,
all-subsets certificate, not an inference from the graph's average degree.

### Target and deletion set

Let T be the path `0-1-...-10`, with one additional leaf at each of 1, 5, and 9.
It has 13 edges and bipartition sizes 5 and 9. Its smaller class is

    {1,3,5,7,9}.

The unique three maximum-degree vertices are

    U={1,5,9},       d_T(1)=d_T(5)=d_T(9)=3.

Thus U really is the set prescribed by highest-degree selection, not a bad
tie-break. Deleting it leaves

    F = P3 on {2,3,4}  +  P3 on {6,7,8}  +  five isolated vertices,
    |F|=11,       e(F)=4 <= 7=delta(H),       sum_{u in U}d_T(u)=9>=2r.

So the ordinary Goldberg–Magdon-Ismail forest theorem applies with room to
spare.

### No bijection U->S extends

Fix **any** bijection U->S. The endpoints of each of the two P3 components
must lie in neighborhoods of **two distinct** seeds. A connected component
of F must embed wholly into one component of H.

* In a wing associated with a different seed pair, one of the two required
  endpoint lists is empty.
* In the wing associated with the required seed pair, the two endpoint lists
  are opposite bipartition classes. That is impossible for a P3.
* Therefore each P3 must lie in the core. All seed neighborhoods within the
  core are exactly A, so each P3 needs **two distinct A vertices**.

The two disjoint paths need four A vertices, but `|A|=3`. This proves failure
for all six bijections, without assumptions on an initial forest embedding or
on local reconfiguration moves.

Nevertheless:

* Every marked-vertex list has size 35; unmarked lists have size 137. All lists
  therefore have size at least |F|=11. In particular, Hall's inequalities for
  **all subsets of all forest vertices** hold trivially.
* Each P3 individually has a list-respecting embedding `a_0-b_0-a_1` in the
  core, for every assignment of its boundary seeds. Each isolated component
  is individually feasible as well.
* T embeds unrooted, even avoiding S, into any wing by its (5,9) bipartition.

Thus plain vertex-list Hall conditions plus separate component feasibility do
not transport the W-degrees. The actual obstruction is a **component packing
capacity**: every feasible copy of each of two components consumes two vertices
from the same three-vertex set. Component-aware support pruning exposes this
bottleneck, but the W/ID degree hypotheses do not remove it for this fixed U.

### Changing the tree deletion set repairs the same host interface

Keep **the same S**, but use `U'={1,3,5}`. This replaces the degree-three tree
vertex 9 by the degree-two vertex 3, sacrificing one unit of deleted degree
sum (`8` instead of `9`, still at least `2r`). An explicit path image is

    a_0, s_0, a_1, s_1, a_2, s_2,
    Q_02[0], P_02[0], Q_02[1], P_02[1], Q_02[2].

Place the extra leaves at tree vertices 1,5,9 respectively at

    P_01[0],       Q_12[0],       Q_02[3].

Every edge is present and all images are distinct. This embeds T with U' at S.
The example therefore directly supports **shape-sensitive dynamic selection**:
maximizing only the sum of deleted tree degrees is insufficient, even when
one can freely permute the host images.

A smaller member of the same construction uses wings K_{11,11}. It has 110
vertices and 676 edges and is still triangle-free ID_13, but then S is not the
maximum-degree set. The larger choice above preserves that stronger feature.

## 5. A stronger and smaller seed-root obstruction than the stated W_14 example

Take the familiar two-wing host with a vertex s and

    |A_1|=|A_2|=6,       |B_1|=|B_2|=10,

all A_i--B_i edges, and all s--A_i edges. Its degrees are 12 at s, 11 on the
A_i, and 6 on the B_i. The order `s,A_1,A_2,B_1,B_2` has **every score exactly
12**. Thus it is W_12 with exactly one degree-at-least-12 vertex. It has
33 vertices and 132 edges.

Let T consist of a central vertex z joined to three hubs h_1,h_2,h_3, and
three additional leaves at each hub. It has 12 edges; its smaller bipartition
class is **exactly the three hubs**, each of degree four and all its
maximum-degree vertices. The other class has ten vertices.

**No vertex in the entire smaller class can map to s.** After removing any
h_i, the large component contains two hubs and seven vertices of the other
class. Its vertex z must map to a neighbor of s, hence to some A_j. Connectivity
confines that component to one `K_{6,10}` wing, and its seven vertices in z's
color class must all map into the six-vertex A_j: impossible.

The target still embeds unrooted into one wing by its (3,10) bipartition.
Moreover, z, a degree-three vertex in the **larger** class, can be mapped to s:
place all three hubs in one A_j and their nine leaves in B_j.

This rules out even the relaxed rule “choose *some* vertex of the smaller tree
bipartition and place it at a seed.” A successful root/set rule cannot insist
on that color class. Again this is not a counterexample to W_12 universality.

## 6. Verification and what remains

Run

    python3 Submission/ForestInterfaceChecks.py

The checks passed:

* 8,833 prescribed-root atlas constructions for the triangle-free forest
  theorem; 2,487 root-matching Hall inequalities; 91 independent non-induced
  GraphMatcher cross-checks;
* 2,000 additional deterministic random constructions, including nonbipartite
  triangle-free blow-ups of C5;
* 2,057 rooted atlas constructions for the triangle-free W_k corollary;
* exact W orders, degree counts, rational endpoint-weight certificates,
  bipartition/capacity obstructions, and explicit successful injections;
* all 12,282 forest-list Hall inequalities over the six assignments in the
  main counterexample; complete enumeration of all 42 marked P3 copies per
  ordered seed pair and verification that every pair of required component
  copies intersects;
* compatibility with K_{2,7} and the stated W_14 example.

These finite checks audit the stated proofs and explicit examples; they are
not being offered as a proof of an unrestricted embedding conjecture.

`Spec.lean` retained SHA-256

    674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103

The remaining gap is precise: a general theorem must **jointly choose the tree
set, the host set, and component-compatible forest placements**, or else use a
marked state that retains and resolves component-capacity obstructions. Exact
scalar degree transport, highest-degree selection, arbitrary permutations of a
fixed interface, large raw lists, and vertex-list Hall inequalities do not
suffice. The one-mark triangle-free theorem handles a genuine part of the
interface problem, but not these multiple-boundary components and not arbitrary
low-maximum-degree targets.
