# Connected-density atoms: a new reduction, not an Erdős–Sós proof

## Status

**The unrestricted Erdős–Sós conjecture is not proved here.** The result is an exact reduction of a connected-density strengthening to a smaller, more structured class of hosts. For odd parameters it reduces the proposed low-deficit candidate to **circuits of the union of graphic matroids**, rather than the pseudoforest circuits used in the earlier reports.

All statements below are mathematical, not Lean formalizations. `Spec.lean` and all other Lean files were left unchanged. No conjectural ES theorem or announced asymptotic result is used. “New” here means a reduction not present in the Submission reports reviewed; no claim of literature priority is made.

The only external embedding input is the proved finite edge-sum list-packing theorem of Győri–Kostochka–McConvey–Yager, *A list version of graph packing*, arXiv:1501.02488. Its statement is available in `/corpus/src/1501.02488/b-e_2015_01_01arXiv.tex`, theorem `List B-E`. The ordinary Bollobás–Eldridge edge-sum packing theorem is its zero-list special case. These are **not** maximum-degree-product conjectures.

## 1. Precise unresolved statement

Fix `k >= 4`, put

    a = (k-1)/2,       r = floor(k/2).

Call a finite simple graph C an **a-atom** if

    e(C) = floor(a (|C|-1)) + 1,                                      (A1)
    e_C(S) <= a (|S|-1) for every nonempty proper S subset V(C).        (A2)

The proposed remaining assertion is:

> **A_k — UNPROVED.** Every a-atom C with `|C| >= k+2` contains every k-edge tree T with `Delta(T) <= r`.

There is no root prescription, no fixed near-copy, and no fixed embedding role in A_k.

**Reduction theorem.** A_k is equivalent to the following connected-density assertion:

> **U_k.** Every connected finite simple H with `|H| >= k+1` and
>
>     e(H) > a (|H|-1)
>
> contains every k-edge tree T with `Delta(T) <= r`.

In particular, proving A_k for all k, together with the already established high-target-degree theorem, would prove the requested Erdős–Sós statement. This is a sufficient stronger route to ES; **ES itself is not asserted to imply U_k or A_k**.

For `k=2r+1`, U_k says

    e(H) >= r |H| - r + 1,

with H connected and of order at least `2r+2`, but **without a minimum-degree assumption**. Section 5 proves that A_(2r+1), U_(2r+1), and the user’s candidate with the additional assumption `delta(H) >= r` are all equivalent. None is proved here.

## 2. Packing input, with its exceptions accounted for

The list edge-sum theorem says the following. Let P and Q be graphs on two separate sets of m vertices, and let L be a bipartite graph between those sets, encoding forbidden vertex assignments. If

    Delta(P), Delta(Q) <= m-2,
    Delta(L) <= m-1,
    e(P) + e(Q) + e(L) <= 2m-3,

then there is a bijection f avoiding both edge conflicts between P and Q and all forbidden pairs in L, except for the seven classical exceptional unordered pairs {P,Q}.

In every application below, P is a connected nonstar tree of order at least four. All graphs occurring in those seven exceptional pairs are disconnected. Thus none of the exceptions can occur here. Taking Q to be the complement of the host converts a packing into a non-induced tree embedding.

## 3. A boundary terminal for the minimum atom order

The following lemma handles the only place where merely unrooted spanning packing would be insufficient.

**Boundary lemma.** Let T have k edges, `k >= 4`, and `Delta(T) <= r=floor(k/2)`. Let J have exactly k vertices and at most `r-1` missing edges. If an ambient graph contains J and an edge `xy` with `x in J`, `y outside J`, then it contains T.

The conclusion does **not** assert arbitrary prescribed-root embedding of T minus an arbitrary leaf.

### Proof

T is not a star. The vertices of T that are not leaves induce a tree with at least two vertices. Choose an end vertex p of that internal tree. It has exactly one nonleaf neighbor u; write `d=d_T(p)`, so `2 <= d <= r`, and all its other `d-1` neighbors are leaves.

Remove p and these `d-1` leaves. The remaining tree R is connected and has

    m = k+1-d >= k+1-r >= 3

vertices, with u as its attachment vertex. We will put p at x and one of its leaves at y.

Write `q=e(complement J) <= r-1`, and let

    B = V(J) minus ({x} union N_J(x)),       t=|B|.

Thus t is the number of missing edges of J incident with x. Also

    d_J(x) >= k-1-q >= r >= d.                              (1)

**Case 1: R is not a star.** Reserve any `d-2` neighbors of x for the other leaves at p; call the reserved set D. Put

    K = J - ({x} union D).

Then `|K|=m`, every vertex of B remains in K, and

    e(complement K) <= q-t.                                (2)

On the two m-vertex sides, take P=R, Q=complement K, and let the only list prohibitions be `u -> b` for `b in B`. The forbidden-assignment graph L has t edges. Since

    q <= r-1 <= k-d-1 = m-2,

all required maximum-degree bounds hold: R is a nonstar tree, Q has at most q edges, and L has maximum degree at most t. The edge sum satisfies

    e(R) + e(Q) + e(L)
      <= (m-1) + (q-t) + t
       = m-1+q
      <= 2m-3.                                            (3)

The list-packing theorem embeds R into K with u avoiding B, hence with the image of u adjacent to x. Restore p at x and its leaves at y and D. This is an injective T-copy.

**Case 2: R is a star.** Its center has degree `m-1 >= ceil(k/2)`. Because `Delta(T) <= floor(k/2)`, this case forces

    k=2r,       d=r,       m=r+1.

The attachment vertex u cannot be the center: its additional edge to p would give degree r+1 in T. Thus u is a leaf of R. Equivalently, T consists of two degree-r hubs at distance two, with r-1 pendant leaves at each hub.

At most `2q <= 2r-2` vertices of J are incident with a missing edge, so J has at least two universal vertices. Choose a universal vertex c different from x. By (1), choose a further neighbor z of x, and choose `r-2` additional neighbors of x avoiding c and z. Map p to x, the other hub to c, their intervening vertex u to z, one leaf at p to y, and the other leaves at p to those `r-2` chosen neighbors. Map the remaining `r-1` leaves of the hub at c to all remaining vertices of J. Universality of c verifies their edges. This gives T also in Case 2. QED.

This argument pays for the possible root restrictions exactly: deleting x removes t missing edges, and the single remaining attachment list introduces exactly t forbidden assignments. There is no halved forest threshold, presumed rooted packing theorem, or unproved switching step.

## 4. Atom extraction and the two terminal orders

Let H be connected, with `|H| >= k+1` and `e(H)>a(|H|-1)`. Choose a **nonempty** vertex set U of minimum cardinality with

    e_H(U) > a (|U|-1).

All its proper nonempty subsets satisfy (A2). Delete edges of H[U] until (A1) holds, and call the resulting spanning graph C. Deleting edges preserves (A2). This extraction is unconditional; it does not assume an embedding of any smaller tree.

Every a-atom has at least k vertices. Indeed an atom has order m>1, and

    m(m-1)/2 >= e(C) > (k-1)(m-1)/2

implies `m>k-1`.

There are three cases.

* **`|C|=k`.** Exactly

      binom(k,2) - [floor((k-1)^2/2)+1] = r-1

  edges are missing from C. Since `|H|>=k+1` and H is connected, there is an H-edge from U to its complement. The boundary lemma embeds T in H, using only C and that edge. The fact that C may have been obtained by deleting edges from H[U] causes no issue.

* **`|C|=k+1`.** Here

      e(C)=binom(k,2)+1,
      e(complement C)=k-1=|C|-2.

  The ordinary edge-sum theorem embeds every nonstar spanning tree: its k edges and the k-1 complement edges sum to `2(k+1)-3`, both maximum degrees are at most `(k+1)-2`, and a connected spanning tree excludes all exceptional pairs. In particular it embeds every target under consideration.

* **`|C|>=k+2`.** This is exactly the unproved assertion A_k.

Consequently A_k implies U_k.

Conversely, atoms are connected (proved next), and an atom of order at least k+2 satisfies the hypotheses of U_k. Thus U_k implies A_k. This proves the claimed equivalence, without proving either statement.

For ordinary ES, first pass to a connected positive-density component of G. Its order is at least k+1 by simplicity, and `e(H)>a|H|` certainly implies `e(H)>a(|H|-1)`. Thus U_k would settle the low-target-degree range; the supplied high-degree theorem settles its complement. For k<4 the low-target-degree range is empty for nontrivial k-edge trees.

## 5. What is genuinely stronger about the new residual hosts

### 5.1 Connectivity, both parities

Every a-atom is connected and has no cutvertex.

If it had c>=2 components, (A2) summed on their vertex sets would give

    e(C) <= a (|C|-c) <= a (|C|-1),

contrary to (A1). If x were a cutvertex and the components of C-x were `X_1,...,X_c`, apply (A2) to the proper sets `X_i union {x}`. Every edge is counted exactly once, giving

    e(C) <= sum_i a |X_i| = a (|C|-1),

again a contradiction. Since its order is at least k>=4, C is 2-vertex-connected.

For any partition into t>=2 nonempty parts `S_1,...,S_t`, put

    eta = e(C)-a(|C|-1) > 0.

Then

    number of edges between parts
       >= a(t-1)+eta.                                     (4)

This follows by subtracting the bounds `e_C(S_i)<=a(|S_i|-1)` from (A1).

### 5.2 Odd k: graphic circuits, not pseudoforest circuits

For `k=2r+1`, conditions (A1)-(A2) become

    e(C)=r(|C|-1)+1,
    e_C(S)<=r(|S|-1) for all nonempty proper S.              (5)

These are precisely the edge circuits of the union of r graphic matroids, on their nonisolated vertex support. In particular:

* C is 2-vertex-connected;
* every edge cut has at least r+1 edges, by (4);
* `delta(C)>=r+1`;
* **for every edge f, C-f decomposes into r edge-disjoint spanning trees**.

The last assertion follows from the standard Nash-Williams forest-decomposition theorem: every vertex set S of C-f spans at most `r(|S|-1)` edges, so it partitions into r forests. Their total size is `r(|C|-1)`; each forest has at most `|C|-1` edges, so every one is a spanning tree. Equivalently, use the Nash-Williams–Tutte spanning-tree packing criterion and (4) after deleting f. This standard matroid consequence is not an embedding theorem and is not used to smuggle in A_k.

Thus the precise odd remaining statement is:

> **GC_r — UNPROVED.** Every simple graph C of order at least `2r+3` satisfying (5) contains every `(2r+1)`-edge tree of maximum degree at most r.

This is a genuinely narrower host class than arbitrary connected hosts of small total deficit. It excludes bridges, cutvertices, all edge cuts of order at most r, and all proper induced sets with positive r-forest surplus. The decomposition colors are spanning trees, not possibly disconnected unicyclic maps.

Now let B_r denote the user’s candidate, including `delta(H)>=r`. We proved

    GC_r => U_(2r+1) => B_r.

Conversely, a graph in GC_r has minimum degree at least r+1, is connected, and has `e=r|C|-r+1`; hence B_r applies to it. Therefore

    GC_r  <=>  U_(2r+1)  <=>  B_r.                          (6)

This is an **equivalence reduction**, not a proof of B_r. It also shows precisely in what conditional sense the candidate's minimum-degree assumption can be removed.

### 5.3 Even k: the exact remaining half-integral atoms

For `k=2r`, the unresolved A_(2r) uses `a=r-1/2`. Deleting one vertex in (A2) gives the exact degree lower bound

    delta(C) >= r       when |C| is even,
    delta(C) >= r+1     when |C| is odd.                     (7)

Equation (4) gives edge connectivity at least r. If |C| is odd it gives at least r+1. When |C| is even, a cut with an even-size shore also has at least r+1 edges, by applying the integer floors in (A2) to both shores.

There is also a graphic-matroid description retaining the parity:

* If |C| is even, replace every edge by two parallel copies. The resulting multigraph has exactly `(2r-1)(|C|-1)+1` edges and is a circuit of the union of `2r-1` graphic matroids.
* If |C| is odd, double every edge and delete one of the two copies of any edge. The same edge count and circuit assertion hold.

Every proper vertex set has at most `(2r-1)(|S|-1)` edges in this multigraph. The full edge count and this sparsity prove the circuit assertion. The doubled description is structural only: it is **not** an embedding lift, and odd GC_r is not asserted to imply the even case.

## 6. Audit and limitations

The following potential gaps were checked explicitly in the proof:

1. The boundary edge is obtained in the original connected H, even if atom extraction deletes edges. All edges of C and the boundary edge still lie in H.
2. The minimum atom order k is not incorrectly treated as large enough to contain a k-edge tree. It uses the outside vertex y and the boundary lemma.
3. A prescribed root in a near-clique is not assumed. A pendant star is removed, leaving only one attachment-list restriction; its exact t-unit charge is paid by the t missing edges incident with x.
4. The remaining star is treated separately, because the list edge-sum theorem requires maximum degree at most m-2. This exceptional case occurs only for even k and is explicitly embedded.
5. The order k+1 terminal uses the exact edge sum `2m-3`, not an asymptotic packing statement.
6. The odd candidate is only proved equivalent to GC_r. No assertion that r spanning trees plus one extra edge automatically yields the requested tree is made.
7. The even doubled-edge circuit is not confused with a simple host or with a subgraph-preserving tree lift.
8. The reduced atoms generally have fewer than a|C| edges. They are **not** called positive-average-degree ES counterexamples, and no same-parameter ES induction hypothesis applies to them.

No bounded search for ES counterexamples or new partial Lean formalization was performed. The reduction is analytic. The displayed integer/parity formulas and the packing budget inequalities were additionally checked with exact integer arithmetic, but those checks are not a proof of the unresolved embedding assertion.

**Final outcome:** the missing low-degree step has been reduced, for both parities, to large 2-connected forest-density atoms. For odd k the user’s candidate is exactly equivalent to universality of large graphic-matroid circuits, with r edge-disjoint spanning trees after deletion of every edge. The complete conjecture and these explicit residual universality assertions remain unresolved.
