# Independent closing attempts after the weighted-list forest theorem

## Status

No unrestricted Erdős–Sós proof or counterexample was obtained. `Spec.lean` is unchanged, with both original placeholders; SHA-256 remains `674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103`. There are still 4,124 lines in the ten existing Lean files. No new Lean development was created during these attempts.

The results below are mathematical partial results. The primary checked their arguments and the cited packing statement; none is asserted to close the global embedding gap. Research-agent tools were read-only, so this checkpoint records findings they could not save themselves.

## 1. One-unit list discount and a two-interface W theorem

Write `W_k` for: every nonempty X contains v with `2d_G(v)-d_{G[X]}(v)>=k`. Its activation interpretation, acyclic orientation `out+2in>=k`, and tail-deletion rule are already in `WkStructuralFindings.md`.

### One prescribed root, other full lists

For a forest F of nontrivial rooted components, with e edges and m vertices, minimum host degree e suffices if one component root is prescribed at any vertex z and each other root has a list of size at least m.

Choose an a-leaf star at z for the prescribed a-edge component. The other lists, after avoiding its a+1 vertices, each have at least the total order of the other components; allocate disjoint component-order reservoirs. Apply the protected-star lemma from `WeightedListForestFindings.md` (one frozen star, no zero demands), then rooted-star dominance. This preserves z and respects all lists.

### Almost-full lists, including isolates

For any rooted forest F, with m>=1 vertices and e edges, suppose minimum host degree is e, every root list has size at least m-1, and the union of all root lists has size at least m. Then F embeds respecting the lists.

If all components are nontrivial, weighted Hall applies: a proper subfamily has order at most m-2, and the full family has the required union. If all are isolated, ordinary Hall applies. Otherwise let q>=1 be the number of isolates and M=m-q the nontrivial order. Embed the nontrivial forest using its lists, all of size at least M. If the isolates cannot be matched outside its image U, only the entire q-set can fail Hall: every proper subfamily has at least q-1 positions. Failure forces all isolate lists to be the same set A, of size m-1, containing U. Since the union of *all* lists has size at least m, some nontrivial root list contains z outside A. Reembed the nontrivial forest with that root prescribed at z by the previous lemma. At most M-1 vertices of A are then used, leaving at least q positions for all isolates.

A uniform two-unit discount is false: H=P3, F=an edge plus an isolate, edge-root list the two ends, isolate list the middle. Here delta(H)=e(F)=1 and the total union has order m=3, but no embedding respects both lists.

### Interfaces

Let T have k>=3 edges and D=delta(G).

* If target uv is an edge with `D+d_T(u)+d_T(v)>=k+3`, and host st is an edge with degrees at least k and k-1 respectively, then T embeds. Orient uv with u nonleaf and put u at s. Delete the two vertices. Residual forest order is m=k-1, edge count `k-d_T(u)-d_T(v)+1`, and minimum residual host degree is at least that count. The two possible lists have sizes at least m and m-1; the nonleaf u supplies a list of size m. The preceding lemma completes the forest.
* If target a-b-c is a path with d_T(b)=2 and `D+d_T(a)+d_T(c)>=k+3`, and two distinct degree-at-least-k host vertices have a common neighbor z, map a-b-c to that path. Residual forest order is k-2 and edge count `k-d_T(a)-d_T(c)`. Every attachment list has size at least k-2, and residual minimum degree is sufficient. The ordinary full-list theorem completes it.

### Explicit resistance set for targets with both signatures

If T has both displayed target interfaces and is absent from a nonempty G, let H be the degree-at-least-k vertices and X=V(G)\H. The first interface says H is independent and no high vertex neighbors a vertex of degree at least k-1. The second says every vertex has at most one high neighbor. X is nonempty. For x in X, either it has no high neighbor and degree at most k-1, or exactly one and degree at most k-2. Thus `d_G(x)+d_G(x,H)<=k-1`, equivalently `2d_G(x)-d_{G[X]}(x)<=k-1`. This contradicts W_k.

An infinite low-maximum-degree family covered this way: for r>=5, take path a-b-c-d, attach r-3 leaves at each of a and d and three leaves at b. It has k=2r edges, core degrees `(r-2,5,2,r-2)`, maximum degree at most r, and both required degree sums equal r+3. Since W_(2r) implies D>=r, every W_(2r) host contains this nonspider tree.

This is NOT unrestricted W-universality. Bounded-degree, heavily subdivided targets still have neither sufficient degree sum. The earlier full first-activation counterexample in `WkGlobalContinuation.md` is T-free but **not critical and not W**; do not describe it as a critical ES counterexample.

## 2. Stronger small-support packing terminal for circuit lifting

For k=2r+1, r>=2, an r-circuit has m=rn+1 and every proper induced set S has at most r|S| edges.

The classical Bollobás–Eldridge **edge-sum** packing theorem is explicitly stated at `/corpus/src/1501.02488/b-e_2015_01_01arXiv.tex`, lines 61–66. If two N-vertex graphs have maximum degree at most N-2 and edge sum at most 2N-3, they pack except for seven listed pairs. Both graphs in every exceptional pair are disconnected, with all components of order at most four. This is a proved theorem, not the maximum-degree-product conjecture.

Consequently a host on N>=4 vertices with at most N-2 missing edges contains every nonstar spanning tree: its complement has at most N-2 edges and maximum degree at most N-2; the connected nonstar tree satisfies the other hypotheses and excludes all exceptional pairs.

An r-circuit C on the minimum possible N=2r+2=k+1 vertices has exactly r missing edges. Deleting ANY q<=r edges leaves at most 2r=N-2 missing edges. Thus every nonstar target embeds using only original edges on every extracted circuit support of minimum order, irrespective of how many matching virtual edges are present. This strengthens the earlier q=1 terminal. For an actual matching pinch, a k-star uses at most one matching edge, necessarily pendant, and replaces that leaf with the new vertex if needed.

Also an r-circuit on n=k+2=2r+3 vertices has n-1 missing edges. Pad the k-edge tree with one isolate: its edge count is n-2 and the total is 2n-3. Circuit minimum degree excludes a complement vertex of degree n-1; the padded tree's component of order n-1>=6 excludes all exceptional pairs. Thus this host order is terminal too.

### Full-critical warning: even two pendant virtual edges may require moving the core

For every r>=2, put k=2r+1. Take W of order k, consisting of Q={q_1,...,q_r}, two vertices ell_1,ell_2, r-2 vertices b_j, and z. Let W induce K_k minus ell_1 ell_2. Add nonadjacent p_1,p_2 with N(p_i)=Q union {ell_i}. The resulting C has n=k+2, m=rn+1, delta=r+1, and is an r-circuit. For a proper subset using h vertices of W and j of the p_i, if 1<=h<=k-1 the W deficit is at least h(k-h)/2>=r and each p_i adds at most one surplus; h=0 and h=k are immediate (at h=k, propriety gives j<=1 and surplus -1+j).

Pinch matching M={p_1 ell_1,p_2 ell_2}: delete M and add v adjacent to its four endpoints and any r-2 Q vertices. Forward matching pinch preserves full r-circuit criticality (proved in `CircuitLiftingGlobalFindings.md`).

The target has core path p_1-q_1-...-q_r-p_2, leaves ell_i at p_i, and leaves b_j at q_j. It has k edges, maximum degree at most r, and its identity copy in C uses exactly the two pendant M-edges. In the pinched graph, each p_i has only v as a neighbor outside the fixed nonleaf core Q union {p_1,p_2}. Hence no leaf reassignment anywhere in the entire host repairs this particular fixed core: both leaves need v.

This is not T-noncontainment. Delete target ell_1, map target p_1 and q_2 (nonadjacent) to host ell_1 and ell_2, and map the other k-2 vertices arbitrarily bijectively onto the rest of W. The only missing W edge is then irrelevant. Restore ell_1 at v. It is also not a counterexample to the unresolved existential matching-resilience property.

Another full-critical fixed-role obstruction: for r=3,k=7, pinch M={ab} in C=K4 join I7, adding v adjacent to all four clique vertices. G=(K4-ab) join I8 is also a 3-circuit and universal via K4,8. The seven-edge spider of arm lengths 3,3,1 cannot map its branch vertex to v: every independent set containing that target vertex has size at most three, but any copy needs at least four vertices in the eight-vertex independent host part. This rules out a prescribed role, not unrooted lifting.

The exact existential resilience property (some T-copy in C uses no matching edge except at most one pendant edge) remains unproved for larger supports.

## 3. Qualitative fractional resistance is still a substantive global step

Let c=k-1, a=c/2, and assume G is T-free. Consider all actual embeddings of T-minus-a-leaf, with all target leaves allowed. For each state s let p_s be its missing leaf's parent image. Every neighbor of p_s is occupied, so its number of occupied nonneighbors other than itself is q_s=c-d_G(p_s).

Give states arbitrary nonnegative weights b_s, put alpha_v=sum_{p_s=v} b_s, and M=sum_s b_s q_s. Then

`2 [ sum_edges max(alpha_u,alpha_v) - a sum_v alpha_v ] = TV_G(alpha)-M`,

where `TV_G(alpha)=sum_edges |alpha_u-alpha_v|`.

Thus a parent-marginal certificate requires an actual proof of `TV(alpha)<=M`. Stationarity, entropy maximization, and positivity of M do not imply it. Every nonnegative vector on the attainable-parent support P is realizable by choosing one near-copy per parent. Coarea therefore shows that this parent-only conclusion is exactly the **localized** assertion that some nonempty X subset P has `I_G(X)<=a|X|`; fractional mixing does not weaken the selection problem. P is only known to be a subset of the degree-below-k vertices, not equal to all such vertices.

More generally, for any nonempty allowed support S,

`min_{alpha>=0,supp alpha subset S,sum alpha=1} sum_edges max(alpha_u,alpha_v) = min_{nonempty X subset S} I_G(X)/|X|`.

The endpoint-allocation minimax dual is the maximum, over allocations of each edge's unit mass between its endpoints, of the minimum vertex load on S. In a proper-induced critical host `m=an+eta`, eta>0, the global minimum ratio is exactly m/n and there is a balanced fractional allocation with all vertex loads m/n. This is an exact reformulation, not a tree-freeness argument.

Substituting Z(T)=0 into the previously derived weighted-count covariance identity yields only a tautology; it supplies no missing sign. A general agent independently rechecked this route and obtained no additional closure. The necessary shape-sensitive implication from the actual forest/near-copy deck to an ambient low-incidence set is still missing.

## 4. Preservation and source checks

No theorem statement or import in Spec was changed. No complete theorem should be submitted on the basis of these reductions. The large-tree AKSS result remains only an announced/unavailable proof in the checked corpus; `1912.02068/SimSze9.tex` line 506 says the authors are still writing it up. The theorem in `1906.10219/erdos_sos.tex` is restricted to fixed bounded degree, dense linear-size trees, and an n_0 threshold. Live website checking again failed DNS. These observations do not assert anything about inaccessible later literature.
