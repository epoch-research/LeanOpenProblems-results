# Erdős–Sós through pseudoforest circuits: a sharp exchange lemma and exact obstructions

**Status: no complete Erdős–Sós proof was obtained.** The odd-parameter circuit reduction is valid. The main additional result here is a sharp, proved forbidden-edge recoloring lemma at exactly the `2r-1` size of a proposed smaller tree. There are also explicit obstructions to keeping the lower circuit spanning and to reconstructing even a star from an arbitrary decomposition. None is a counterexample to Erdős–Sós, and none is being represented as a complete embedding argument.

All graphs below are finite and simple unless a multigraph is explicitly specified. Embeddings are non-induced. `Submission/Spec.lean` was not modified. The mathematics below is proved on paper, not formalized in Lean.

## 1. The circuit reduction is valid; the orientation is root-reachable

For an integer `r >= 1`, call G an **r-circuit** when

    e(G) = r|G| + 1,
    e_G(S) <= r|S| for every proper S subset of V(G).             (C_r)

If `e(G) > r|G|`, choose an inclusion-minimal positive induced witness, and then delete edges until its edge count is `r|G|+1`. Every proper vertex subset remains sparse, so this produces `(C_r)`.

### Exact matroid identification

An edge set F can be partitioned into r pseudoforests if and only if

    e_F(S) <= r|S| for every S.                                  (1)

Here a pseudoforest has at most one cycle per component. To prove sufficiency, make r slots at each vertex, and match each edge to an endpoint slot. For an edge set A, its neighboring slots number `r|V(A)|`, at least `|A|` by (1). Hall's theorem gives an orientation with outdegree at most r. Give outgoing edges distinct colors at each vertex. Each color has outdegree at most one, hence is a pseudoforest. Necessity is immediate.

Consequently this is precisely the union of r copies of the bicircular/pseudoforest matroid. For an r-circuit G, every proper edge subset A is independent: if its vertex support is proper use `(C_r)`, and if its support is all of V use `|A| <= r|V|`. The whole edge set is dependent. Conversely, an edge circuit, after discarding isolated vertices, has `(C_r)`: a smaller dense vertex set or at least `r|V|+2` edges would give a proper dependent edge subset.

This matroid identification is standard, not a claimed new theorem. See Streinu–Theran, *Natural realizations of sparsity matroids*, arXiv:0711.3013, `/corpus/src/0711.3013/natural-arxiv.tex`, lines 65–68. It identifies `(k,l)` sparsity for `l<=k` with l graphic and `k-l` bicycle matroids.

### Incidence and degree consequences

For every nonempty X,

    I_G(X) := e_G(X) + e_G(X,V\X)
            = e(G) - e_G(V\X)
            >= r|X| + 1.                                      (2)

In particular,

    delta(G) >= r+1,       Delta(G) >= 2r+1,       |G| >= 2r+2.   (3)

The maximum-degree assertion follows from the average `2r+2/|G|`, and the order assertion uses simplicity. These degree consequences are not substituted for `(C_r)`.

### Correct orientation statement

For **every prescribed vertex z**, G has an orientation D with

    d_D^+(z)=r+1,       d_D^+(v)=r for v != z,                  (4)

and z reaches every vertex. Assign capacities `r+1` at z and r elsewhere in the same endpoint-slot matching. The total capacity equals e(G), and `(C_r)` verifies Hall, so all capacities are filled. For a proper S containing z,

    d_D^+(S,V\S) = r|S|+1-e_G(S) >= 1.                         (5)

Thus the vertices reachable from z cannot form a proper set. Conversely, an orientation with (4) in which z reaches all vertices implies `(C_r)`, by applying the outgoing-cut formula separately to sets containing and avoiding z.

Reversing a directed z-to-w path moves the surplus from z to w. Internal outdegrees do not change; the old root loses one outgoing edge and the new root gains one. The resulting orientation is again root-reachable by the preceding equivalence. This proves unrestricted surplus transport at the edge-assignment level, not at the tree-embedding level.

**Strong connectivity does not follow.** More precisely, a quota orientation (4) is strongly connected if and only if z belongs to every nonempty proper r-tight set `S`, where `e_G(S)=r|S|`. For a set avoiding z, its outgoing cut is exactly `r|S|-e_G(S)`; sets containing z already have positive outgoing cut by (5).

For example, join two disjoint copies of `K_{2r+1}` by one bridge. The result is an r-circuit, but no orientation can be strongly connected. Each clique is r-tight, and every nonempty proper part of a clique has deficit at least r, which absorbs the possible single bridge in every proper vertex subset.

## 2. Main additional lemma: a sharp forbidden-edge exchange theorem

A **spanning map** means a spanning pseudoforest with exactly n edges, equivalently every component is unicyclic. It can be oriented with exactly one outgoing edge at every vertex.

### Theorem: protect up to 2r-1 edges from one functional color

Let `r>=2`, let G be an r-circuit on n vertices, and let `F subset E(G)` with

    |F| <= 2r-1.

The following are equivalent:

1. `G-F` has no isolated vertex.
2. There is an edge partition

       E(G) = E(P) disjoint-union E(Q_1) ... disjoint-union E(Q_{r-1})
              disjoint-union {e},

   in which P and all Q_i are spanning maps and `E(P) intersect F` is empty.

Thus **any copy of a `(2r-1)`-edge tree of maximum degree at most r can be protected from one full functional color**: `(3)` guarantees that none of its vertices uses every incident host edge. The theorem also permits larger tree degrees, provided no host vertex is saturated by F. F need not itself be a forest.

### Proof

Necessity is immediate because P gives every vertex an incident edge outside F.

For sufficiency, build a bipartite matching problem. The left side is `E(G)`. The right side has:

* one red slot at each vertex, usable only by incident edges outside F;
* `r-1` other slots at each vertex, usable by every incident edge;
* one free slot, usable by every edge.

Both sides have `rn+1` elements. For a nonempty edge set A, put

    S = V(A),
    Z = S \ V(A\F),
    s = |S|,   z = |Z|.

Its neighboring slots number exactly

    (r-1)s + (s-z) + 1 = rs-z+1.                              (6)

If `A=E(G)`, the no-isolate assumption gives `z=0`, so Hall holds with equality. If A is proper, circuit independence gives `|A|<=rs`. Consequently a Hall failure requires `z>=2` and

    |A| >= rs-z+2.

Every edge of A not contained in `S\Z` belongs to F. Since `S\Z` is a proper vertex subset of G,

    |F| >= |A| - e_A(S\Z)
        >= rs-z+2 - r(s-z)
         = (r-1)z+2
        >= 2r,

contradicting the hypothesis. Hall therefore supplies a perfect matching.

All slots are filled. Edges assigned to the red slots form P; the other vertex slots give the Q_i after labeling their `r-1` colors; the free slot supplies e. Orient each assigned edge away from its slot's vertex. Every vertex has exactly one outgoing edge in each color, so each color is a spanning map. The red color avoids F. QED.

This is a genuinely global recoloring statement: the edge-slot perfect matching can be found by alternating-path exchanges. It allows the extra edge to change. It does **not** assert that exchanges preserve a fixed vertex embedding or its attachment roles.

### Sharpness, even when F is a tree of maximum degree r

Take a clique W of order `2r+1`. Add adjacent vertices u,v, each with exactly r neighbors in W, with their two neighbor sets intersecting in exactly one vertex. Let F be the `2r` edges from `{u,v}` to W.

Then G is an r-circuit. Its edge count is `r(2r+3)+1`. A proper subset meeting W in `x` vertices has clique deficit

    rx - binom(x,2) >= r       for 1 <= x <= 2r.

The contribution from u,v exceeds `r|S intersect {u,v}|` by at most one, so that deficit absorbs it. If all of W is retained, either at most one added vertex is present, giving no positive surplus, or the subset is all of V(G). Subsets missing W are plainly sparse.

F is a tree: u,v have degree r and are joined through their unique common neighbor, with `r-1` leaves at each. Its maximum degree is r (including when r=2). However

    G-F = K_{2r+1} disjoint-union K_2.

There are no isolated vertices, but no spanning map can cover the `K_2` component. Hence the theorem's conclusion fails at `|F|=2r`.

### A related direct deletion lemma

For any `|F|<=2r-1`, every tree component of `G-F` is an isolated vertex. If a tree component has vertex set X, (2) gives

    |{e in F : e has an endpoint in X}| >= r|X|+1 - (|X|-1)
                                       = (r-1)|X|+2.

For `|X|>=2` this exceeds `2r-1`. Thus, if F saturates no vertex, `G-F` has a spanning map even before asking that its complement decompose into the other colors. The Hall theorem above proves the stronger, simultaneous decomposition.

## 3. What rank reduction really gives

### Rooted lower-circuit lemma

Let `r>=2`, orient an r-circuit as in (4), and select **any one outgoing arc at each vertex**. These n arcs form a spanning map P. Set `H=G-E(P)`, retaining the other orientations, and put `q=r-1`. Then

    d_H^+(z)=q+1,       d_H^+(v)=q for v != z.

Let C be the set reachable from z in H. Then:

* `H[C]` is a q-circuit containing z;
* every vertex subset S with `e_H(S)>q|S|` contains C;
* consequently `H[C]` is the unique q-matroid circuit in H.

**Proof.** There are no arcs leaving C, so `e_H(C)=q|C|+1`. If `A` is a proper subset of C avoiding z, its edge count is at most `q|A|` by the outdegree quota. If A contains z, reachability inside C gives an arc leaving A, so the same bound holds. This proves the circuit assertion.

If S is positive, it must contain z, and the outgoing-cut formula forces its outgoing cut to be zero. It therefore contains every vertex reachable from z, hence C. The quotas also give `e_H(S)<=q|S|+1` for every S. A q-matroid circuit with vertex support S has exactly `q|S|+1` edges, so it must use **all** edges of `H[S]`. Thus any such circuit contains the already dependent edge set `E(H[C])`, and minimality makes it exactly `H[C]`. QED.

The selection of P must be compatible with the quota orientation, as above (in particular, any color from a full map decomposition plus an extra edge is compatible). An arbitrary spanning map need not leave a unique lower circuit. For example, take `H=K_4[{0,1,2,3}] disjoint-union {45}` and `E(P)={04,05,14,15,24,35}`. Then `G=H union P=K_6-{25,34}` is a 2-circuit and P is a spanning map, but H contains the six distinct bicircular circuits `K_4-f`, one for each clique edge f.

### Two other structural consequences

Every r-circuit has a spanning tree of maximum degree at most `r+1`. Choose a spanning out-arborescence in (4). A nonroot has one incoming tree edge and at most r outgoing tree edges; the root has at most `r+1` outgoing tree edges.

Also, for every vertex set U,

    c(G-U) + e_G(U) <= r|U|+1.                                (7)

For the components `C_1,...,C_c` of `G-U`, sum (2):

    rn+1-e_G(U) = sum_i I_G(C_i)
                >= r(n-|U|)+c.

This proves (7), including the empty and full U cases.

## 4. An unavoidable obstruction: the lower circuit cannot stay spanning

For every `r>=2`, let

    a=r+1,        b=r(r+1)+1,        G=K_{a,b}.

Then `n=(r+1)^2+1` and `e(G)=rn+1`. An induced subgraph is `K_{x,y}`. If `x<=r`,

    xy-r(x+y) = (x-r)y-rx <= 0.

If `x=r+1` and the subset is proper, `y<=b-1=r(r+1)`, so its surplus is `y-r(r+1)<=0`. Thus G is an r-circuit.

**G has no spanning `(r-1)`-circuit at all**, irrespective of which functional graph is removed. Such a circuit H would have minimum degree at least r, so counting its edges on the b-vertex side gives

    e(H) >= rb.

But its required edge count is

    (r-1)(a+b)+1 = rb-(r+1) < rb.

Equivalently, any n-edge spanning map P has total degree n on the b-side, exceeding b. Some b-side vertex loses at least two edges and has degree at most `r-1` in `G-P`, below the lower-circuit minimum degree.

The bounded-spanning-tree lemma is also sharp here: every spanning tree J has

    sum_{v in A} d_J(v) = n-1 = (r+1)|A|,

so `Delta(J)>=r+1`. A spanning lower circuit would have a spanning tree of maximum degree at most r, another contradiction.

These graphs still contain every `(2r+1)`-edge tree: put its smaller color class into A, of size `r+1`, and its larger class into B, whose size is at least `2r+1`. This is an obstruction to same-order rank induction, not to tree containment.

## 5. Even a spanning lower circuit need not supply any extendible smaller tree

This failure is stronger than a bad fixed root or one badly chosen smaller embedding: for the displayed decomposition, **all** embeddings of the required smaller tree fail.

### A six-vertex example

Let

    G = K_6 - {01,23},
    E(H) = {02,03,04,12,13,15,45},
    E(P) = {05,14,24,25,34,35}.

G is a 2-circuit; in fact every nonempty proper vertex subset is strictly 2-sparse, so every quota orientation of G is strongly connected. H is a spanning bicircular circuit: its three internally disjoint 0-to-1 paths are

    0-2-1,       0-3-1,       0-4-5-1.

P is a spanning unicyclic graph: the cycle is `2-4-3-5-2`, with leaves `0-5` and `1-4`. Thus this is a fully legitimate functional deletion, even leaving a lower circuit on all six vertices. Removing any edge from H gives the other spanning map plus the extra edge required by the original two-color decomposition.

Take `T=K_{1,5}`. Its only sibling-leaf reduction by two vertices gives `R=K_{1,3}`. In H, the only vertices of degree at least three are 0 and 1. Both have degree four in G. Consequently **no embedding of R in H extends to T in G**: after its three leaf neighbors are used, its center has only one unused neighbor, not two.

Yet G contains T, centered at either 4 or 5. There are exactly 12 labeled copies of R in H, all blocked, and 240 labeled copies of T in G.

This is not an obstruction to every possible exchange. For example, swap `02` from H with `24` from P. The new P is still a spanning map and the new H a spanning bicircular circuit. Now vertex 4 has degree three in H and degree five in G, so its smaller star extends.

### A family for every r>=2

The same failure occurs at every odd parameter. Take vertices

    u,v,a,b,c_1,...,c_{r-1},d_1,...,d_{r-1}.

Let G be `K_{2r+2}` minus the matching

    {ab, c_1d_1,...,c_{r-1}d_{r-1}}.

Let P consist of the 4-cycle `u-a-v-b-u` and the two pendant paths

    u-c_1-...-c_{r-1},       v-d_1-...-d_{r-1}.

P is a spanning map. G is an r-circuit: it has `rn+1` edges, and every proper subset has at most `2r+1` vertices, for which the complete-graph edge count is at most `r|S|`.

Set `H=G-P` and `q=r-1`. It has `qn+1` edges. Its degrees are

    d_H(c_{r-1})=d_H(d_{r-1})=2r-1,
    d_H(x)=2r-2 for every other x.

H is a spanning q-circuit. Sets of size at most `2r-1` are automatically q-sparse by simplicity. Deleting one vertex removes at least `2r-2>=r` edges. Deleting two vertices removes at least `4r-5>=2r-1` edges. These are exactly the remaining proper-set inequalities, for sizes `2r+1` and `2r` respectively.

Now take

    T=K_{1,2r+1},       R=K_{1,2r-1}.

Every copy of R in H is centered at one of the two displayed path ends. Those vertices have degree `2r` in G, so no such copy extends to T. The only possible centers of T in G are u,v, but their H-degrees are `2r-2`, too small even for R.

A shape-aware exchange repairs this particular family: move `ua` from P to H and `ac_{r-1}` from H to P. The new P is still unicyclic and spanning; the new H is still a q-circuit by the same minimum-degree check, and u now has H-degree `2r-1`. The point is the failure of arbitrary decomposition, not the impossibility of every joint optimization.

## 6. Even k: doubling has a parity caveat

Let `k=2r` and `q=2r-1`. After taking a minimal strict positive induced witness and deleting whole edges, its doubled surplus is

    s = 2e(G)-q|G| in {1,2}.

Its parity equals the parity of `|G|`, and every proper S satisfies `2e_G(S)<=q|S|`.

* If s=1, doubling every edge produces a q-circuit in the multigraph sense.
* If s=2, the doubled graph has `q|G|+2` edges and is **not** a circuit. Deleting any one edge-copy produces a q-circuit, but destroys the equal-pair multiplicity on that edge.

Concrete example: for `k=4`, take `G=K_{3,3}+01`, with 0 and 1 on the same side. It has n=6, m=10; every proper subset satisfies `2e(S)<=3|S|`, but doubling gives 20 edges, whereas a 3-circuit has 19. Each of the 20 single-copy deletions gives a 3-circuit and leaves the underlying simple graph unchanged.

The simple-graph odd-parameter embedding assertion cannot be applied verbatim to this multigraph circuit: a 3-circuit of this kind has only six vertices, so certainly cannot contain a seven-edge tree. A multiplicity-two/weighted counterpart must retain the rescaled even target parameter. The rational encoding is valid after accounting for this, but it is not an automatic reduction to the simple odd case.

## 7. Verification and precise remaining gap

Run

    python3 Submission/ErdosSosCircuitChecks.py

from `/workspace/leanproject`. It passes. It checks:

* all 17 r=1 and 31 r=2 circuits in the graph atlas (order at most seven);
* 320 quota orientations, 2,156 surplus transfers, 430 rooted rank-drop cores, and 5,296 component inequalities;
* all 17,460 forbidden edge sets of size at most three in those 31 r=2 circuits, including the exact 41 saturated-vertex failures;
* sharpness and the blocked-star family for r=2,...,6;
* 246,540 part-size inequalities in the complete-bipartite family for r=1,...,30;
* all 12 blocked smaller-star embeddings and all 240 full-star embeddings in the six-vertex example;
* the 20 single-copy deletions in the even-parity example.

The script also checks a deterministic-seed sample of 2,004 higher-r forbidden-set instances, for r=3,...,6, including four forced saturated-vertex failures. These numerical checks are supplemental, not the proof.

The SHA-256 of `Spec.lean` remains

    674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103.

### No circularity

The proved statements use endpoint-slot Hall matching, directed reachability, and edge counts. None assumes Erdős–Sós or its inductive embedding conclusion. The forbidden-edge theorem starts with an actual edge set F; it does not manufacture a copy of the target tree. The rank-drop theorem identifies the lower circuit but does not promise a prescribed rooted copy in it.

What remains unresolved is a **joint, shape-sensitive choice of decomposition, lower-tree embedding, and attachment vertices**. The smaller circuit may be genuinely nonspanning, as Section 4 proves. Even if it is spanning, all smaller-tree embeddings can fail to extend for a chosen decomposition, as Section 5 proves. Moving surplus or protecting existing tree edges from one color does not by itself solve these vertex-occupancy and attachment constraints. No valid universal reconstruction lemma, and therefore no complete Erdős–Sós proof, was obtained.
