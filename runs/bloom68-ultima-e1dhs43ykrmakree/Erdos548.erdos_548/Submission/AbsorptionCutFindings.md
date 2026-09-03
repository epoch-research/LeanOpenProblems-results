# Sharp cut budgets and critical obstructions to unconditional extraction

**Outcome.** General extraction remains unproved. There is a sharp, quantified extraction lemma for a saturated high-degree clique; a critical family where every cross-feasible cut misses the budget by **exactly one**; and a broader critical construction with **no cross-feasible cut at all**, even when the high-degree vertices dominate the host. The latter also blocks the exact one-apex CL certificate on **every subgraph** throughout the low-tree-degree range. A rook-graph specialization additionally defeats complete-biclique and uniform small-defect clique/biclique certificates.

These are not Erdős–Sós counterexamples, nor a refutation of the full proposed union of terminal criteria. No tree-kernel lemma was investigated. No Lean/specification file changed.

## 1. A sharp cut lemma and an exact extraction class

All graphs are finite and simple, and k>=3. Here `a=(k-1)/2`, `e(G)=a|G|+eta`, and every proper induced set S satisfies `e(S)<=a|S|`. The constructed examples have eta=1; the finite enumeration uses `e(G)=floor(a|G|)+1`. Embeddings are non-induced injective homomorphisms.

Write `h=|A|`, `b=|B|`, and let the budget shortfall be

    M_c(A) = E_c(A) - delta_a(A).

For every cut satisfying the A-side cross-degree condition,

    M_c(A) >= (k+1)h/2 + e(A) - cb.                    (1)

Indeed, substitute `e(A,B)>=kh` in the definition. Equality holds precisely when every A-vertex has cross-degree exactly k. Thus absorption requires

    n >= h + ((k+1)h/2 + e(A))/c.

For an adjacent pair and c=1, this gives **n>=k+4**; the obstruction below attains the bound's shortfall exactly.

**Saturated-high-clique extraction theorem.** Let

    H = {v : d(v)>=k},     G[H] a clique,     Delta(G)<=k+1.

A universal vertex gives an absorbing singleton. If there is no universal vertex, every cross-feasible cut, for any positive c, has

    A={u,v},   d(u)=d(v)=k+1,   min_B d_A=1,

where `{u,v}` dominates B. Conversely every such dominating pair is cross-feasible. For every one of them,

    M_1({u,v}) = k+4-n.                                 (2)

Consequently **every available pair absorbs when n>=k+4**, whereas at `n=k+3` every pair fails by one. If no such pair exists, there is no cut; this is an exact, polynomially checkable obstruction in this class.

Proof: A lies in H, and an h-vertex clique consumes h−1 neighbors at each selected vertex. Thus `k<=d_B(x)<=k+2-h`, so h<=2. A singleton would be universal. For a pair, both degrees must equal k+1 and the cut has 2k edges. Its minimum B-degree is one: if it were two, both vertices would be universal. Now `delta_a(A)=k-2` and `E_1(A)=2k-(n-2)`, proving (2).

Another exact small-order rule: for `n=k+2`, k>=4, an absorbing cut exists **iff the complement has a component of order one or two**. Here h<=2; a singleton must be universal, while a pair must be complete to its k-vertex complement. Such pairs use c=2 and have zero excess. This rule includes absence of *all* cross-feasible cuts, not merely a budget failure.

## 2. The unit-budget obstruction is genuinely critical

For t>=2 put

    k=4t+1,   a=2t,   n=k+3.

Take a clique W of size k, partitioned into `X1,X2,X3,Z` of sizes

    t, t, t-1, t+2.

Add a triangle `p1,p2,p3`. Join pi to exactly the two X-groups other than Xi; give it no neighbors in Z. Then

    e(G)=an+1,
    d(Xi)=k+1,   d(Z)=k-1,
    d(p1)=d(p2)=2t+1,   d(p3)=2t+2.

Full criticality is particularly transparent. For odd k and `n=k+3`, the normalized edge count and `delta(G)>=a+1` imply criticality: sets of size at most k are automatically a-sparse; deleting one vertex removes at least a+1 edges; deleting two removes at least `2(a+1)-1=2a+1` edges.

The high set is the clique `X1 union X2 union X3`. Its only feasible cuts select two vertices from different X-groups. For **every** such cut,

    c=1,   |B|=k+1,   e(A,B)=2k,
    E_1(A)=k-1,   delta_a(A)=k-2,
    e(B)=(a-1)|B|.                                      (3)

Thus the entire critical surplus is consumed: the residual graph lands **exactly at**, not above, the `(k-2)`-edge induction threshold. Increasing c is impossible. There is no large-c bipartite escape for these partitions.

The whole-host CL sufficient condition fails whenever `Delta(T)<=2t`. Nevertheless these graphs have an actual terminal certificate for **every** k-edge tree: place any leaf outside W, its parent at a neighboring clique vertex, and the remaining vertices bijectively in W. This proves universality of the displayed family, not partition existence.

**The zero-gap boundary is attainable too.** For integer r>=1, a useful criticality-preserving operation replaces an r-edge matching M in a surplus-one r-critical graph by a new vertex joined to all 2r endpoints. Old degrees are unchanged, and the edge count increases by r. For a proper old set S, its surplus after including the new vertex is

    [e_G(S)-r|S|] + |{e in M : e meets S}| - r <= 0.

The set of all old vertices loses r edges and is also sparse. This proves full criticality preservation, **not** preservation of T-freeness. In the t=2 example, use a perfect matching of Z, the edge p1p2, and p3x with x in X1. The new graph has k=9, n=13. Each pair consisting of x and a vertex of X2 is cross-feasible and has **M_1=0**, giving genuine equality cases of the extraction theorem.

## 3. A regular-core obstruction: domination does not suffice

Let r>=3, k=2r+1. Take **any connected 2r-regular graph Q** containing disjoint r-sets U,V with every U–V edge present. Add adjacent vertices p,q, with

    N(p) = V union {q},     N(q) = U union {p}.

Call the result G. Then

    e(G)=r|G|+1,   H=U union V,
    d(H)=k,   d(Q-H)=k-1,   d(p)=d(q)=r+1.

**Full criticality.** For `S subseteq V(Q)`, regularity gives

    e_Q(S)-r|S| = -cut_Q(S)/2.

Adding only p changes this surplus to `-cut_Q(S)/2-|V-S|`, and similarly for q. Adding both changes it to

    1 - |(U union V)-S| - cut_Q(S)/2.                    (4)

For a proper vertex set this is nonpositive: if S misses H the first subtraction suffices; otherwise a nonempty proper cut of connected Q has positive even size. The full set has surplus one.

**No partition.** Since every high vertex has degree exactly k, an eligible A must be an independent subset of H. Completeness between U,V forces A wholly into one of them. But p has no neighbor in U and q has none in V. Hence some forced B-vertex has cross-degree zero. This excludes every positive c, including c>k/2.

**No exact one-apex CL certificate on any subgraph for `Delta(T)<=r`.** In a subgraph J, a vertex s with `d_J(s)>=k` must lie in H and retain all its G-neighbors. It therefore retains p or q. After deleting s that low vertex has degree at most r, whereas CL requires `delta(J-s)>=k-d_T(u)>=r+1`.

A useful large, high-dominating realization is obtained as follows. Give each h in H a private r-set P_h; put any `(2r-1)`-regular graph F on their union W. Add the private edges h–P_h and the complete U–V block. This is a connected 2r-regular Q, whatever F is. Thus

    |G|=2r²+2r+2,

H dominates all of G, yet the no-cut and all-subgraph CL obstructions persist. Distinct vertices of U have codegree r+1 and neighborhood symmetric difference exactly 2r; likewise in V. Criticality and large codegree do not force near twins even after excluding the low-degree CL case.

## 4. A quantified rook specialization beyond uniform packing certificates

Index W by `(b,i,j)`, with `b in {0,1}` and `0<=i,j<r`; row i of copy b is private to ui or vi. Let F consist of two r-by-r **rook graphs**—adjacency means same row or same column—plus the matching `(0,i,j)(1,i,j)`. F is `(2r-1)`-regular. For r>=3 the resulting G is nonbipartite and satisfies all of Section 3.

Direct neighborhood counts give

    maximum codegree = r+1,
    minimum |N(x) symmetric-difference N(y)| over x!=y = r,
    clique number = r+1.                                (5)

For the stronger defect bounds, put an edge between vertices whose G-codegree is at least three. Every clique of order at least two in this auxiliary graph lies in one of:

* `L=U union {p}` or `R=V union {q}`;
* one private row together with its high vertex, of size r+1;
* one column of one rook copy, of size r.

To verify this classification, all other pair types have codegree at most two. Within a rook copy the only remaining pair types share a row or column; a pairwise row-or-column-aligned set lies in one row or column. A high vertex can join only its own private row or its central group.

Every vertex outside a listed row/column set has at most one neighbor in it. Every vertex outside R has at most one neighbor in L, and conversely.

These facts yield two **quantified exclusions**:

1. If `|S|=N>=k+1` and G[S] has complement maximum degree d, then

       2d >= N-4.                                      (6)

   Otherwise every pair in S would have at least three common neighbors, contradicting the auxiliary clique bound r+1. In particular no such S satisfies the uniform subcubic near-clique packing bound `N>=6d`.

2. Complete any bipartite block on disjoint sets of sizes `p>=r+2`, `q>=r`, and let d be its maximum missing cross-degree. Then

       d >= ceil(r/2).                                 (7)

   If d were smaller, every pair on the q-side would have at least `p-2d>=3` common neighbors. That side lies in a canonical set above. Every p-side vertex needs at least `q-d>=2` neighbors there, forcing the p-side into the opposite central group, or into the same row/column set. The former has only r+1 positions; the latter has fewer still. Contradiction.

For a subcubic tree with color sizes r,r+2 and maximum degree three on both colors, (7) excludes the uniform asymmetric Hall criterion from `ExactBlowupFindings.md`: a capacity at least `6d` would force an opposite-side host degree at least `5d>2r+1=Delta(G)`. The weaker, zero-defect biclique certificate already fails by maximum codegree r+1.

Thus **cuts + exact one-apex CL + complete bicliques + these uniform small-defect clique/biclique bounds do not cover this family/tree combination**. This does not exclude general bipartite colored cores, local nonuniform lifting, or compensated degree-two-quotient completions.

## 5. Actual embeddings, and precisely what remains

These obstructions must not be confused with noncontainment.

* In the private-neighborhood construction, choose F to be r disjoint cliques K_(2r), each with one vertex private to every h. Every nonstar k-edge tree has two leaves with distinct parents. Delete them, embed the remaining 2r vertices into one clique, and use the distinct private high neighbors for the two leaves. Stars use a high vertex of degree k. This is a universal **two-leaf clique certificate**.
* In the rook construction there is an explicit nonspider subcubic example for every r>=4. Take the path on `2r-1` vertices, numbered from zero, and attach leaves at positions 1,2,3. It has k edges, three degree-three vertices, and color sizes r,r+2. In one rook copy, map the path along row 0 in increasing column order and then row 1 in decreasing order, omitting column 0 there. Map the three added leaves to row 2, columns 1,2,3. This is a direct injective embedding, despite all the exclusions in Section 4.

For **arbitrary F or Q**, a terminal embedding theorem has not been proved here. In particular, the rook example is not a proved counterexample to the full proposed coverage union. The new useful obstruction is a saturated, two-type high set whose independent subsets cannot dominate both low attachments; a prospective extraction theorem must explicitly exclude or terminally handle this configuration. T-freeness has not been used to eliminate it.

## 6. Verification

Run `python3 Submission/AbsorptionCutChecks.py`; output is in `Submission/AbsorptionCutChecks.log`.

* Exhausted all **24,666 normalized critical hosts** with `4<=n<=9`, `3<=k<n`: 9,437 have an absorbing cut; 2 have only a large-cross terminal among these cut tests; 2,666 have positive cross-degree cuts but no budget; 12,561 have no cross-feasible cut.
* Checked 14,473,499 proper induced subsets; independently compared unrestricted cut enumeration through order seven; audited 9,662 saturated-high-clique hosts, 2,231 exact cut identities, and 393 order-k+2 classifications.
* Checked 8,189 unit-gap cuts; built 29 full criticality orientation certificates. Such a certificate has outdegree r everywhere except one root of outdegree r+1, with that root reaching all vertices, which certifies every proper-set inequality.
* Audited the two regular-core families through r=12, including 149,146 rook neighborhood pairs and the auxiliary-clique/outside-neighbor classification.
* Verified **7,114 constructive embeddings**, including every nonisomorphic tree of the relevant orders for the one-/two-leaf clique certificates. No embedding backtracking is counted as a structural certificate.

These are mathematical proofs with supporting finite checks, not Lean formalizations. `Spec.lean` retains SHA-256 `674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103`.
