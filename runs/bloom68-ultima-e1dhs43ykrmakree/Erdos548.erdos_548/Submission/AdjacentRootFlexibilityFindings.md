# Adjacent root flexibility is false, even in 3-connected critical hosts

## Outcome

The proposed property is **false**, including its conditional version in which `T` is already known to embed. There is a counterexample with

| Quantity | Value |
|---|---:|
| Tree parameter `k` | 5 |
| Host order `n` | 20 |
| Host edges | `41 = (k-1)n/2 + 1` |
| Distinguished degree `d(s)` | 7, the **unique maximum** |
| Other host degrees | 3 and 6 |
| Vertex connectivity | 3 |
| Permissible tree roles `R_s` | **one vertex: the tree's hub** |

The target is a four-edge star with one edge subdivided once. Both endpoints of its terminal handle edge are unavailable at `s`. A full target copy lies entirely in a proper induced subgraph of the host.

This is not just a prescribed-root obstruction: the **exact** permissible-role set is determined, and its complement contains an edge. The host satisfies **full criticality**, not merely `W_5`. A second, **bipartite and 3-connected**, counterexample has 32 vertices and 65 edges. An infinite family below also gives adjacent unavailable **nonleaf** roles.

No Lean file or specification was edited. The mathematical proofs below do not depend on the finite checks.

## 1. Two useful construction/certificate lemmas

### 1.1 A root-reachable orientation certifies full criticality

Let `r` be a positive integer. Suppose a simple graph has an orientation `D` such that

* `d_D^+(s)=r+1`;
* `d_D^+(x)=r` for every `x != s`;
* every vertex is reachable from `s` in `D`.

Then

\[
 e(G)=r|G|+1,\qquad e(G[S])\le r|S|\quad(S\subsetneq V(G)). \tag{1}
\]

Indeed, writing `out_D(S)` for the number of arcs from `S` to its complement,

\[
 e(G[S])=r|S|+\mathbf 1_{s\in S}-\operatorname{out}_D(S).
\]

If `s` is absent, this is at most `r|S|`. If `s` belongs to a proper `S`, a directed path from `s` to a vertex outside `S` supplies an outgoing arc, giving the same bound. Summing all outdegrees gives the whole-graph count.

Thus these are normalized critical hosts for `k=2r+1`, with `eta=1`. In particular, for every nonempty `X`,

\[
 I_G(X)=e(G)-e(G-X)\ge r|X|+1. \tag{2}
\]

This construction principle permits a high maximum vertex whose nearby vertices have low degree; criticality does not rule out such a neighborhood.

### 1.2 The degree-ball obstruction determines several roles at once

Suppose `h` is a tree vertex, and every vertex of `B_L(s)-{s}` has host degree less than `d_T(h)`. Then

\[
 R_s\subseteq\{h\}\ \cup\ \{u:\operatorname{dist}_T(u,h)>L\}. \tag{3}
\]

For if `u != h` maps to `s`, the image of `h` is a different host vertex at distance at most `dist_T(u,h)` from `s`. An injective embedding requires its degree to be at least `d_T(h)`, a contradiction when that distance is at most `L`.

This lemma excludes an entire set of roles simultaneously. It does not assume ES, induced containment, or a fixed-root induction hypothesis.

## 2. The 20-vertex host

All subscripts on `p_i` and `c_i` in this section are modulo 6 where appropriate.

Take vertices

\[
 \{s\}\ \dot\cup\ \{a_1,\ldots,a_7\}\ \dot\cup\
 \{c_0,\ldots,c_5\}\ \dot\cup\ \{p_0,\ldots,p_5\}.
\]

There are exactly the following edges:

1. Join `s` to all seven `a` vertices.
2. On the `a` vertices put the three disjoint paths
   
       a1--a2,       a3--a4,       a5--a6--a7.

3. In the listed order, match `(a1,a2,a3,a4,a5,a7)` to `(c0,...,c5)`.
4. Join each `c_i` to `p_i` and `p_(i+1)`.
5. On `P={p0,...,p5}` put the edges `p_i p_(i+1)` and `p_i p_(i+2)`. This is `C_6^2 = K_(2,2,2)`.

Consequently

\[
 n=20,\qquad e=7+4+6+12+12=41,
\]

and

\[
 d(s)=7,\qquad d(a_i)=d(c_i)=3,\qquad d(p_i)=6. \tag{4}
\]

In particular `s` is the unique maximum, and `d(s)>=k=5`. The set `B_2(s)-{s}` is exactly the set of `a` and `c` vertices; every one has degree three. Every reservoir vertex `p_i` is at distance three from `s`.

### Full criticality: an explicit orientation

Orient the first two paths into directed triangles

    s -> a1 -> a2 -> s,       s -> a3 -> a4 -> s.

Orient the third as

    s -> a5 -> a6 -> a7 -> s,       a6 -> s.

Orient each endpoint-to-`c` edge toward `c`, both edges from each `c_i` toward `P`, and the reservoir edges as

    p_i -> p_(i+1),       p_i -> p_(i+2).

The outdegree of `s` is three; **every other outdegree is two**. All vertices are reachable from `s`: the displayed paths reach all `a` and `c` vertices, and the reservoir contains a directed six-cycle. Lemma 1.1 with `r=2` proves every proper induced subset is 2-sparse and the full surplus is exactly one.

This also establishes full incidence density `I_G(X)>=2|X|+1`. Since

\[
 \sum_{v\in X}\bigl(2d_G(v)-d_{G[X]}(v)\bigr)=2I_G(X)>4|X|,
\]

some integer summand is at least five. Thus the graph satisfies `W_5` as well. The counterexample does not disappear when `W_k` is strengthened to the full critical hypotheses.

### The graph is 3-connected

The reservoir `K_(2,2,2)` remains connected after deleting any two vertices. Consider any deletion set `Z` of size at most two.

* If `s` survives, at least one of the six endpoint--`c` paths from `s` to the reservoir still connects to a surviving reservoir vertex. All surviving `a` vertices reach `s`. A surviving `c_i` has a surviving port unless both its ports were deleted; in that exceptional case the entire core survives, so it reaches the reservoir via its `a` vertex and `s`.
* If `s` is deleted, only one further deletion is allowed. Every remaining component of each of the three displayed `a` paths still has an original endpoint with an intact `c` connection. Every surviving `c` has a surviving reservoir port. Thus every such component reaches the reservoir.

Orphaned `c` vertices also have their direct reservoir connections. Hence `G-Z` is connected. Conversely, the three neighbors of `c_0` form a cut isolating `c_0`. The vertex connectivity is exactly three.

Therefore neither cutvertices nor 2-separators are needed for the failure.

## 3. The target and its exact permissible-role set

Let

\[
 V(T)=\{z,\ell_1,\ell_2,\ell_3,v,u\},
\]

with edges

\[
 z\ell_1,\ z\ell_2,\ z\ell_3,\ zv,\ vu. \tag{5}
\]

Thus `z` has degree four, `v` has degree two, and `u` and the three `ell_i` are leaves. The edge to test is **`vu`**.

Every tree vertex other than `z` is at distance at most two from `z`. By (4), every host vertex in `B_2(s)-{s}` has degree three. Lemma 1.2 therefore gives

\[
 R_s\subseteq\{z\}.
\]

The reverse inclusion has the explicit embedding

| Tree vertex | `z` | `v` | `u` | `ell1` | `ell2` | `ell3` |
|---|---|---|---|---|---|---|
| Host image | `s` | `a1` | `c0` | `a2` | `a3` | `a4` |

Hence

\[
 \boxed{R_s=\{z\},\qquad u,v\notin R_s,\qquad uv\in E(T).} \tag{6}
\]

The complement of `R_s` induces exactly the edge `uv` and three isolated vertices. It is not independent.

### Containment is explicit, even avoiding s entirely

There is also a copy wholly inside `P`:

| Tree vertex | `z` | `v` | `u` | `ell1` | `ell2` | `ell3` |
|---|---|---|---|---|---|---|
| Host image | `p0` | `p1` | `p3` | `p2` | `p4` | `p5` |

All five required edges are edges of `C_6^2`. This establishes the conditional counterexample directly, without invoking ES.

Indeed, `P` is vertex-transitive. Composing this copy with its automorphisms shows that **every** tree role is permissible at **every** vertex of `P`. All those vertices have host degree six, below the unique maximum seven but above `k`. Thus choosing a different high host vertex can fix this instance; insisting on the maximum, or on an arbitrary prescribed high vertex, cannot.

## 4. Why the two complementary attachment choices both fail

The obstruction has a direct interpretation in the proposed cut-edge/marked-forest route for `uv`.

Put `H=G-s` and `A=N_G(s)={a1,...,a7}`. Every vertex of `A` has degree **two in H**.

* **Choose `v -> s`.** The forest `T-v` is a three-edge star centered at `z`, plus the isolated vertex `u`. Its required mark `z` must lie in `A`. But every member of `A` has only two neighbors in `H`, so even this marked star is impossible.
* **Choose `u -> s`.** The tree `T-u` is a four-edge star centered at `z`, marked at the leaf `v`, whose image must lie in `A`. Every possible image of its center adjacent to such a marked image has host degree three, because it lies in `B_2(s)-{s}`. The four required incident tree edges are impossible.

There is no successful arm of this disjunction. At the same time,

\[
 |H|=19,\qquad e(H)=34>19=(3-1)|H|/2.
\]

So `H` has ample lower-parameter ES density for `k-2=3`; in particular the needed unmarked three-edge star exists in the reservoir. The attachment, not the unrooted lower-parameter density, fails.

This is a concrete obstruction to the proposed two-choice induction state, not merely an unproved selection step. In this example a successful root must be allowed to move **outside the prescribed edge** (to `z`), or the host root must move away from the unique maximum.

The high-leaf-parent property is **not** refuted: `z` is a leaf-parent and its displayed image is the high vertex `s`.

## 5. A bipartite, 3-connected counterexample as well

The failure is not a peculiarity of triangles or of nonbipartite phases. Here is a second fully explicit host for the same tree (5).

Use three sets of path vertices, indexed by `i=0,1,2`, with paths

    a_(i,0)--b_(i,0)--a_(i,1)--b_(i,1)--a_(i,2).

Join `s` to all nine `a` vertices. Add six vertices `c_0,...,c_5`, joining `c_(2i)` to `a_(i,0)` and `c_(2i+1)` to `a_(i,2)`.

For the reservoir use

\[
 P=K_{5,5}-\{X_jY_j:0\le j<5\},
\]

with parts `X_0,...,X_4` and `Y_0,...,Y_4`. Subscripts on `X,Y` below are modulo five.

* Join `c_j` to `Y_(2j)` and `Y_(2j+1)`.
* List the six `b` vertices in the order `(b_(0,0),b_(0,1),...,b_(2,1))`. Join the `j`th of them, starting at zero, to `Y_(12+j)`.

These are all the edges. The graph is bipartite with sides

    {s, all b, all c, all X}       and       {all a, all Y}.

Its counts and degrees are

\[
 n=32,\qquad e=9+12+6+20+12+6=65=2n+1,
\]

\[
 d(s)=9,\quad d(a)=d(b)=d(c)=3,\quad d(X_j)=4,
 \quad (d(Y_0),\ldots,d(Y_4))=(8,8,8,7,7). \tag{7}
\]

Thus `s` is again the unique maximum. Its punctured radius-two ball consists of the `a,b,c` vertices, all of degree three.

For criticality, orient each displayed path from left to right, orient `s -> a_(i,0)` and `a_(i,1),a_(i,2) -> s`, and orient every `a`--`c`, `b`--`Y`, and `c`--`Y` edge toward the latter endpoint. Orient the reservoir by

    X_i -> Y_(i+1), Y_(i+2),       Y_(i+3), Y_(i+4) -> X_i.

Again `s` has outdegree three and every other vertex outdegree two. The reservoir contains a directed spanning ten-cycle: the step `X_i -> Y_(i+1) -> X_(i+3)` visits all indices. Every vertex is reachable from `s`, so Lemma 1.1 proves full criticality.

Lemma 1.2 and a copy with `z -> s`, `v -> a_(0,0)`, `u -> c_0`, and three other `a` images for the short leaves give **exactly `R_s={z}`**. An ordinary copy avoiding `s` is

    z -> X0,   v -> Y1,   u -> X2,
    ell1 -> Y2, ell2 -> Y3, ell3 -> Y4.

This graph is also 3-connected. The reservoir remains connected after two deletions: each side retains at least three vertices, and any two surviving `X` vertices have a common surviving `Y` neighbor. If `s` survives, its intact endpoint--`c` paths attach it to the reservoir; every surviving `a` reaches it. A surviving `b` either reaches a surviving neighboring `a`, or both those `a` vertices were deleted and its reservoir edge survives. The `c` vertices are handled as in Section 2. If `s` is deleted, one additional deletion cannot disconnect a remaining path component from both its endpoint attachments. The neighbors of any `c` give a three-vertex cut.

So even **bipartite criticality plus 3-connectivity plus a unique maximum** does not force unavailable roles to belong to just one tree color class.

## 6. An infinite family, including adjacent unavailable nonleaves

For any integer `r>=2`, put `k=2r+1`. Make `r+1` triangles `s a_i b_i s`, otherwise disjoint. Attach `r-1` distinct children to each `a_i` and each `b_i`. There are

\[
 C=2(r+1)(r-1)
\]

children. Give each child `r` private reservoir ports, so the reservoir order is

\[
 N=rC=2r(r^2-1).
\]

On these `N` ports put the `r`th power of a cycle, with edges from cyclic distances `1,...,r`. Each reservoir vertex is the port of exactly one child.

Orient each triangle `s -> a_i -> b_i -> s`, each parent--child edge toward the child, each child--port edge toward the port, and each reservoir edge forward by its cyclic distance `1,...,r`. Every non-`s` outdegree is `r`, the outdegree of `s` is `r+1`, and all vertices are reachable. Hence this is a full critical host, with

\[
 n=1+2r^2(r+1),\quad e=rn+1,
\]

\[
 d(s)=2r+2,\quad d(a_i)=d(b_i)=d(c)=r+1,\quad d(p)=2r+1. \tag{8}
\]

In particular `s` is the unique maximum and all other vertices within distance two have degree `r+1`.

### One permissible role for every odd k >= 5

Take a star of degree `2r`, subdividing one edge once. It has `2r+1=k` edges, hub degree `2r>r+1`, and every other vertex is within distance two of the hub. Thus `R_s` consists **only of the hub**, which can be realized using a parent--child path and other neighbors of `s`.

A copy inside the reservoir is explicit: put the hub at `p_0`, the length-two arm at `p_1,p_(r+1)`, and the short leaves at the other `2r-1` reservoir neighbors of `p_0`.

### The unavailable edge can have two nonleaf endpoints

For `r>=3`, instead take a hub `z` of degree `2r-1`, with `2r-2` short leaves and a length-three arm

    z--v--w--ell.

This is again a `k=2r+1` edge tree. Its hub degree `2r-1` exceeds `r+1`. Therefore neither `v` nor `w` can map to `s`, though both are nonleaves of degree two.

In fact its exact permissible-role set is

\[
 R_s=\{z,\ell\}. \tag{9}
\]

For `z -> s`, use an `s`--parent--child--port path for the long arm. For `ell -> s`, reverse that path, put `z` at the port, and use distinct reservoir neighbors for its short leaves. Every other role is excluded by (3). The whole tree also embeds inside the reservoir using `p_0,p_1,p_(r+1),p_(r+2)` for its long arm and suitable neighbors of `p_0` for its short leaves.

The first such nonleaf-edge example is `r=3`: `k=7`, `n=73`, `e=220`, unique maximum degree eight, and two adjacent unavailable internal degree-two roles.

## 7. Consequences and limits

1. **The precise property in the question is disproved**, even assuming containment in advance, even at a unique maximum, and even with full criticality and 3-connectivity. Bipartiteness does not repair it either.
2. Therefore an ES reduction cannot require that an arbitrarily selected tree edge always supplies one of its two endpoints as the role of a fixed maximum host vertex. Both complementary marked interfaces can be impossible in a genuine critical host.
3. All displayed trees are in the already CL-covered high-degree regime. These examples **do not refute a separately restricted version for `Delta(T)<=floor(k/2)`**, and no such restricted theorem is claimed here. They also do not refute the high-leaf-parent property. The main example actually realizes a leaf-parent at the chosen maximum.
4. No unrestricted ES proof is claimed. The outcome is a verified structural disproof of this proposed global root-flexibility route as stated, not a relabeling of it as a missing theorem.

## 8. Reproducible verification

Run

```
python3 Submission/AdjacentRootFlexibilityChecks.py
```

The saved output is `Submission/AdjacentRootFlexibilityChecks.log`. It passes the following independent/constructive audits:

* **All 1,048,575 proper induced subsets** of the 20-vertex graph, including the empty set: none has positive surplus. Exactly 99 nonempty proper subsets are tight; the whole graph has surplus one.
* **52 exact max-closure/min-cut exclusion tests**, one for each possibly omitted vertex of the two small hosts. Each independently maximizes `e(S)-2|S|` over all subsets avoiding that vertex and returns zero. Two additional unconstrained tests return one, uniquely on the whole vertex set.
* The explicit orientations, exact counts, unique maximum degrees, and root reachability; seven closed-form family instances `r=2,...,8` are also checked. No random host search is used.
* **740 connectivity checks**, covering deletion of every set of at most two vertices in the 20- and 32-vertex graphs, plus explicit three-vertex cuts.
* Exact permissible-role certificates using the degree-ball lemma and explicit injections; additionally **12 independent rooted subgraph-monomorphism decisions** determine all six roles in each small host. These are non-induced embeddings.
* **38 explicit full tree injections**, checked for every edge and for injectivity; six instances with an unavailable internal degree-two edge.
* Explicit `W_5` activation orders for both small hosts.

All ten existing Lean files retained their pre-investigation hashes. In particular, `Spec.lean` retained SHA-256

    674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103.
