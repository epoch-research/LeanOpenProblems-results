# Cycle partitions hitting a prescribed spanning tree

## Status and main conclusions

**The unrestricted prescribed-tree question is not resolved here.** No counterexample for a spanning tree is obtained, and no general construction for all even simple graphs is proved. The same is true of the unrestricted prescribed-Hamilton-cycle and prescribed-tree fractional-feasibility questions. The tests below are diagnostics, not evidence promoted to a universal theorem.

There is, however, a general **integral** theorem on a nontrivial structural class:

> **Series-parallel theorem.** Let G be a connected finite simple even series-parallel graph. Let R be any spanning forest with at most two components. Then G has an exact edge partition into simple cycles, every one containing an edge of R.
>
> In particular, this holds for **every prescribed spanning tree T**, even after deleting **any one specified edge of T**. For a specified Hamilton cycle F, it holds even after deleting **any two specified edges of F**.

The proof is a complete marked series-parallel recurrence, with an invariant that accounts for the marked forest at every composition. It does not close arbitrary trails and then hope that their simple-cycle pieces remain marked.

Further rigorous outcomes:

* The two-component threshold is **sharp**: a specified three-component spanning forest in a six-vertex, 2-connected simple even series-parallel graph fails **even fractionally**. All six cycles are classified, and an integer Farkas certificate is given. **This is not a spanning-tree counterexample.**
* A separate global construction handles a class outside series-parallel graphs: take any cubic bipartite H with odd part size k >= 9, attach each part to its own new hub, and join the hubs. The prescribed double-star tree is hit by an exact, globally minimum partition of `(k+1)/2 = |V(G)|/4` cycles. If H is connected, G is 3-connected. This is a completed construction, not an endpoint-rerouting proposal.
* The universal existential-tree assertion is equivalent to the universal rank bound `c(G) <= r(G)`. The required forest-transversal condition is on **every subfamily** of a minimum partition, not merely its total cardinality. There is also a precise quantitative connection with the already proved fractional rank bound.
* Exact diagnostics pass for **all 2,018 connected even simple graphs through order nine**, up to graph isomorphism, and for **all their spanning trees**. There are **66,641,307** such tree instances, including the empty tree on one vertex. The order-nine verification uses an exhaustive branching certificate covering all trees, not a sample. All specified Hamilton cycles in these graphs pass as well.

All results are at paper level, not Lean-formalized; no priority claim is made. Only this new note and `ResearchTreeHittingCheck.py` are added to Submission. No specification or pre-existing research file is changed.

---

## 1. Exact formulations and what the fractional bound would say

Graphs are finite, simple and undirected unless an auxiliary multigraph is explicitly mentioned. “Even” means that **every degree is even**. A partition covers every edge exactly once, with vertex-simple cycles of length at least three. For the spanning-tree question G is connected. Write

```
r(G) = |V(G)| - kappa(G),
c(G) = minimum number of cycles in an exact edge partition,
c_f(G) = minimum sum_C x_C,  subject to sum_(C containing e) x_C = 1,
         x_C >= 0.
```

For a marked edge set R, let `C_R` be the simple cycles meeting R. The constrained fractional question is **feasibility** of

```
           sum_(C in C_R, e in C) x_C = 1   for every edge e,
           x_C >= 0.                                      (1.1)
```

If it is feasible, its cost automatically satisfies

```
sum_C x_C <= sum_C |E(C) intersect R| x_C = |R|.             (1.2)
```

Thus no additional optimization argument is needed to obtain cost `<= n-1` for a tree. Conversely, the unconstrained theorem `c_f(G) <= r(G)` in `ResearchFractional.md` does **not** restrict the support to `C_R` and is not a proof of (1.1).

The exact finite-dimensional Farkas obstruction is a signed edge weighting y with

```
y(C) <= 0 for every C in C_R,       y(E(G)) > 0.             (1.3)
```

Such a y rules out every nonnegative fractional solution, hence every integral partition. An integral infeasibility result alone would not necessarily supply (1.3).

For an integral partition meeting R, choose one marked edge in each cycle. The representatives are distinct, so its cardinality is at most `|R|`. A tree need not meet **every cycle of G**; the problem is to choose a partition that it meets. Nothing below confuses these two assertions.

For a Hamilton cycle F, the immediate bound analogous to (1.2) is `|F|=n`, not automatically `n-1`.

---

## 2. The marked two-terminal series-parallel lemma

A two-terminal network N has distinct terminals s,t. Start with a single edge and use:

* **Series composition:** identify the second terminal of one network with the first terminal of another. The children share only this junction.
* **Parallel composition:** identify corresponding terminals. The children share only their two terminals, and their edges are disjoint.

The underlying network in the lemma is simple. All its internal vertices have even degree. Let `lambda(N)` be its maximum number of edge-disjoint s--t paths and let

```
q(N) = d_N(s) mod 2 = d_N(t) mod 2.
```

Every s--t edge cut has parity q: sum degrees on its s-side, where only s can have odd degree. Thus `lambda(N)` has parity q. For the expressions above,

```
lambda(edge)=1,
lambda(series(A,B))=min(lambda(A),lambda(B)),
lambda(parallel(A,B))=lambda(A)+lambda(B).                 (2.1)
```

The series children have the same terminal parity, because their common junction has even degree. These are ordinary edge-connectivity facts, or follow directly by routing paths through the expression.

A **rooted spanning forest** R in N has one or two components, each containing at least one of s,t. In the two-component case the terminals are in different components. Every vertex of N belongs to this forest, including its isolated vertices.

### Lemma 2.1 — the full induction invariant

For every integer p satisfying

```
0 <= p <= lambda(N),             p = q(N) mod 2,            (2.2)
```

there is an exact partition of N into p simple s--t paths and simple cycles with the following properties:

1. Every cycle contains an R-edge.
2. At most one exported path avoids R. If it does, it is **literally the single edge st**, which is not in R.
3. If p=1 and R is connected, the exported path contains an R-edge.

In particular, every exported path is marked if N has no unmarked direct terminal edge. The proof also makes every exported path marked at a nontrivial series node.

The direct-edge exception is important. For a triangle consisting of a marked two-edge s--t path and an unmarked edge st, p=2 necessarily exports the unmarked edge. Dropping this exception would make the induction false.

We prove the lemma by strong induction on the number of edges. In particular, the smaller network formed by deleting a direct terminal edge in Section 2.5 is covered by the induction hypothesis even if it is not a literal child of the original expression.

### 2.1 Why the forest hypothesis is inherited

Restrict R to either child. A child-forest component containing neither child terminal could not connect to anything outside that child; it would give a component of R missing both parent terminals. Therefore each restriction is again a rooted spanning forest with at most two components.

At a series junction w, **the two child forests cannot both be disconnected**. Otherwise the component containing w would contain neither outer terminal. Consequently at least one child forest is connected. This is the fact used for p=1; an arbitrary family of previously constructed paths would not have it.

### 2.2 Leaf

The only admissible p is 1. Export the edge. If R is connected, that edge is marked; otherwise the allowed direct-edge exception applies.

### 2.3 Series composition

Use p paths in each child. Child cycles already satisfy the invariant. Concatenate paired child paths through their common junction; the concatenations are simple because the children have no other common vertex.

* If p=0, there is nothing to concatenate.
* If p=1, at least one child forest is connected. Property 3 makes its path marked, so the concatenation is marked.
* If p>=2, each child has at most one unmarked path. Pair paths so that the two unmarked paths, if both exist, are **not** paired together. Every concatenation is marked.

This is an exact one-use pairing of child paths, with no repeated edges, no residual trails, and no new unaccounted cycles.

### 2.4 Parallel composition: ordinary traffic values

Put `u=lambda(A)`, `v=lambda(B)` and choose

```
a = min(u,p+v),
b = min(v,p+u),
h = (a+b-p)/2.                                            (2.3)
```

Then a,b have the respective child parities, lie within their capacities, and

```
0 <= h <= min(a,b),          (a-h)+(b-h)=p.
```

For example, when `u>=v`, either `p<=u-v` and `(a,b,h)=(p+v,v,v)`, or `p>=u-v` and `(a,b,h)=(u,v,(u+v-p)/2)`. This also verifies all parity and nonnegativity assertions in (2.3).

Apply induction with a and b paths. There is **at most one unmarked path among both children**: every such path would be the original edge st, and simplicity permits only one such edge in the parent.

Pair h paths of one child with h paths of the other to make h cycles; export the remaining p paths. Each new cycle is marked, because a pair cannot consist of two unmarked paths. It is simple because the two path interiors are disjoint. It has length at least three: two distinct one-edge s--t paths would be parallel original edges, excluded by simplicity. The exported unmarked exception, if any, is still just st.

### 2.5 Parallel composition: enforcing property 3

It remains to ensure that an unmarked st edge is not the sole exported path when R is connected and p=1.

If no unmarked st edge exists, the preceding construction already does this. Otherwise let e=st be that edge and set `B=N-e`. In a series-parallel expression, a direct terminal edge is a parallel leaf: it cannot lie below a nontrivial series composition with the same terminals. Deleting that leaf and pruning its parallel ancestors leaves a nonempty two-terminal series-parallel network B, with all the original vertices.

The marked spanning tree R is contained in B, so B is connected. Its terminal degrees are even, because p=1 gives odd terminal degrees in N; its other degrees are unchanged. Consequently `lambda(B)>=2`.

Apply induction to B with two exported paths. Neither can be unmarked, since B has **no direct terminal edge at all**. Join one to e to make a marked simple cycle, and export the other marked path. All other cycles from B remain marked. This uses each original edge once and completes the induction. ∎

The checker implements exactly this recurrence, including (2.3) and the special deletion in Section 2.5. Exact-cover search is **not** used to manufacture the output of this theorem.

---

## 3. Global prescribed-tree theorem for series-parallel graphs

Here “series-parallel” includes connected graphs with articulation vertices: equivalently, the graph is K4-minor-free, or each nontrivial 2-connected block is a two-terminal series-parallel network when rooted at the ends of any of its edges. This standard block characterization is the only structural characterization of the class used here.

### Theorem 3.1

Let G be a connected finite simple even series-parallel graph. If R is any spanning forest with at most two components, G has a simple-cycle edge partition every member of which meets R.

**Proof.** For a 2-connected G, if R has two components choose an edge st crossing between them; if it has one component, choose any edge st. Use the block's two-terminal expression rooted at s,t and apply Lemma 2.1 with p=0. All degrees are even, so p=0 is admissible.

For general connected G, every edge-containing block is even. Indeed, take any ordinary simple-cycle edge partition of the even graph; every cycle lies in one block, and its blockwise restriction proves evenness.

The intersection of a connected component of R with a block B is connected inside B. A simple path between two vertices of a block cannot leave and re-enter it at different vertices: such an external ear would enlarge the block; re-entry at the same vertex would repeat a vertex. Hence the unique R-path stays in B. It follows that `R intersect E(B)` is a spanning forest of B with at most two components.

Apply the 2-connected case independently inside each block and unite the resulting partitions. Blocks partition the edges, and every output cycle is marked. The one-vertex edgeless graph is vacuous. ∎

### Consequences with the marking fixed in advance

For a connected even simple series-parallel graph with at least one edge, on n vertices:

* Every specified spanning tree T can be hit by the partition.
* For **any specified** `e in T`, the forest `T-e` has two components. The partition can be required to hit `T-e`, and therefore has at most **n-2 cycles**.
* If F is a specified Hamilton cycle and e,f are any two distinct specified F-edges, `F-{e,f}` is a spanning forest with two components. The partition can be required to hit this smaller set as well.
* All these assertions hold fractionally because they already hold integrally. No rounding theorem is used.

This is not just the feedback-set observation. For instance, take a triangle abc and add the paths `a-x-b`, `b-y-c`, `c-z-a`. The spanning tree

```
{ax, xb, by, yc, az}
```

misses the original triangle completely. The three lens cycles nevertheless give a tree-hitting partition. The proof of Theorem 3.1 handles arbitrary input trees, not only this example or a conveniently chosen decomposition.

---

## 4. Sharp obstruction for three forest components — including an exact LP certificate

Let s=0,t=1 and take four internally disjoint s--t branches:

```
P0 = (0,2,3,1),
P1 = (0,1),
P2 = (0,4,1),
P3 = (0,5,1).
```

Let G be their union and mark exactly `R=E(P0)`.

Then G is simple, 2-connected, even and series-parallel, with

```
n=6, m=8,
d(0)=d(1)=4,   d(2)=d(3)=d(4)=d(5)=2.
```

The spanning forest R has three components: `{0,1,2,3}`, `{4}`, `{5}`. Every simple cycle is the union of **exactly two branches**, so there are exactly six cycles. Exactly three are allowed: `P0 union Pj`, for j=1,2,3.

Any allowed fractional partition must give `P0 union Pj` coefficient 1 in order to cover branch Pj. This loads every edge of P0 three times, contradicting its load equation 1. In particular, an integral partition is impossible.

Equivalently, give branch P0 total price -1 and each other branch total price +1. One explicit edge weighting is

```
y(02)=-1,
y(01)=y(04)=y(05)=1,
y(23)=y(13)=y(14)=y(15)=0.
```

Every allowed cycle has weight 0, whereas `y(E(G))=2>0`. This is the exact Farkas certificate (1.3), with no solver tolerances.

Unrestrictedly, `P0 union P1` and `P2 union P3` form a two-cycle partition. Degree four at s gives the matching lower bound even fractionally, so

```
c(G)=c_f(G)=2 <= |R|=3,
```

despite infeasibility of the R-hitting relaxation. A small unconstrained value is not a support certificate.

Adding the single marked edge 04 gives a two-component forest and restores feasibility. It is still not a feedback edge set: the cycle `P1 union P3` avoids it. For example, the two cycles `P0 union P1` and `P2 union P3` both meet the enlarged marking.

**Scope:** this proves sharpness of Theorem 3.1 in the number of forest components, even within 2-connected series-parallel graphs. R is **not** a spanning tree, so the example does not answer the unrestricted tree question negatively.

---

## 5. A completed double-star construction beyond series-parallel graphs

### Theorem 5.1

Let H be any finite simple cubic bipartite graph with parts A,B of the same **odd** size k>=9. Add vertices s,t, all edges from s to A, all edges from t to B, and the edge st. Let

```
T = {sa : a in A} union {tb : b in B} union {st}.
```

Then T is a prescribed spanning double-star tree of the resulting even simple graph G, and G has a T-hitting partition with

```
c(G)=c_f(G)=(k+1)/2=|V(G)|/4.                              (5.1)
```

There is one cycle of length 6 and `(k-1)/2` cycles of length 10. If H is connected, G is 3-connected.

### Proof

A cubic bipartite graph has a perfect matching M by Hall's theorem. The remaining two-factor can be oriented cyclically; write sigma for its successor permutation. For each matching edge uv, take the path

```
P_uv = (sigma(u), u, v, sigma(v)).                         (5.2)
```

Its four vertices are distinct: sigma is a permutation without fixed points, and a matching edge is not in the two-factor. The k paths partition H's edges. Each vertex is an endpoint exactly once, as a value of sigma, and an internal vertex exactly once, as an endpoint of a matching edge. These are two **different** paths. Every path has one endpoint in each bipartition class.

Make a compatibility graph K on these k paths, joining two when their vertex sets are disjoint. Each path meets at most four others, one possible other path at each of its four vertices. Thus

```
delta(K) >= k-5 >= (k-1)/2.
```

A graph of odd order k with minimum degree at least `(k-1)/2` has a matching leaving only one vertex unmatched. For completeness, take a maximum matching of size m. If at least three vertices are unmatched, choose two, x,y. They have no unmatched neighbours. The absence of an augmenting path of length three implies that each matched edge contributes at most two to `d(x)+d(y)`. Hence

```
k-1 <= d(x)+d(y) <= 2m <= k-3,
```

a contradiction.

Pair the paths using such a matching of K. Close the single unmatched A--B path using its two hub spokes and st, obtaining the length-six cycle. Close each disjoint pair P,Q using

```
s -- A-end(P) -- P -- B-end(P) -- t
  -- B-end(Q) -- reverse(Q) -- A-end(Q) -- s.              (5.3)
```

This is a simple length-ten cycle: P,Q are vertex-disjoint and neither contains a hub. Every H-edge is used once; every spoke is used once because each base vertex was an endpoint once; st is used only by the unmatched path. Thus this is a **global integer partition**, with every edge and every possible vertex repetition accounted for. Each output cycle meets T.

There are `(k+1)/2` cycles, and every cycle contains s. The degree lower bound `c_f(G)>=d_G(s)/2=(k+1)/2` proves both global minimalities in (5.1).

Finally, if H is connected, deleting both hubs leaves H connected. If just one hub and one base vertex are deleted, every surviving vertex in the other hub's non-neighbour part still has at least two H-neighbours leading to that hub's part. If both hubs survive, their edge and all remaining spokes connect the graph. These cases prove 3-connectivity. ∎

No statement about arbitrary all-odd H or arbitrary double-star trees follows from this proof. Its completed pairing argument uses short paths and the bound of four conflicts per path. It is not a claim that arbitrary intersecting terminal paths can be rerouted without generating additional cycles.

---

## 6. The existential-tree variant and the exact missing condition

Fix a cycle partition `D={C_1,...,C_k}` of a connected graph G. For `A subset D`, let H_A be the spanning edge subgraph whose edges are the union of A. Then

```
min_(spanning trees T of G) |{C in D : C misses T}|
       = max_(A subset D) (|A|-r(H_A)).                    (6.1)
```

The empty subfamily makes the right-hand side nonnegative.

### Forest-transversal justification

A tree hitting h members of D supplies h distinct cycle representatives forming a forest. Conversely, an independent set of cycle representatives extends to a spanning tree. Thus the maximum number hit is the maximum size of an independent partial transversal in the graphic matroid.

The matroid transversal criterion is

```
there are independent representatives for all C in D
iff r(H_A) >= |A| for every A subset D.                   (6.2)
```

A short proof of sufficiency works for any finite matroid. Induct on the number of sets. If a nonempty proper subfamily J is tight, first choose its representatives by induction; they form a basis of its union. Contract that basis and apply induction to the remaining sets, using the inequality for `J union A`. If no proper nonempty subfamily is tight, choose a nonloop representative of one set and contract it. Every nonempty subfamily of the remaining sets previously had rank at least its size plus one, so the required inequalities survive the contraction. The one-set and empty cases are immediate.

For (6.1), put `d=max_A(|A|-r(H_A))`. Adjoin d independent dummy elements to the matroid and allow all d in every representative set. The enlarged sets satisfy (6.2), so at most d dummy representatives are needed and at least k-d real ones can be selected. Conversely any independent partial transversal has size at most `k-|A|+r(H_A)` for each A. This proves equality and (6.1).

### Universal equivalence

The following two **universal** assertions are equivalent:

1. Every connected even simple G admits some spanning tree and a partition meeting it.
2. Every even simple G satisfies `c(G)<=r(G)`; equivalently, every connected one satisfies `c(G)<=n-1`.

The forward implication is the distinct marked-edge count, componentwise. Conversely, choose a global minimum partition D of G. Every subfamily A is minimum on its union: otherwise replacing it improves D. Thus the universal rank bound gives

```
|A|=c(H_A)<=r(H_A)
```

for every A, and (6.2) supplies a spanning tree hitting D.

This argument uses the bound on **all even subunions**. A cardinality check `|D|<=n-1` for a single supplied partition is not the forest-transversal criterion.

Here is an exact example of that caveat. Take K7 on `0,...,6` and attach the triangle `(0,7,8)`. Partition K7 into the seven Fano triangles

```
(i, i+1, i+3) mod 7,             i=0,...,6,
```

and append the attached triangle. The resulting supplied partition has **eight cycles on nine vertices**, so `|D|=n-1`. Nevertheless, no tree hits all seven Fano triangles: their union has rank six, whereas hitting seven edge-disjoint cycles would require seven independent representatives there. This is a failure for that **supplied partition**, not for the graph. In fact, the alternative partition

```
(6,0,5,1,4,2,3), (6,1,0,2,5,3,4), (6,2,1,3,0,4,5), (0,7,8)
```

is hit by the tree consisting of the six edges `6i` for `i=0,...,5`, together with `07,78`. It is globally optimal even fractionally, since vertex 0 has degree eight. Both displayed partitions were checked for exact edge coverage, and the displayed tree was checked to hit the four-cycle partition. Enumeration of all 16,807 K7 trees also confirms that the minimum number of missed Fano triangles is exactly one.

### A consequence of the established fractional theorem

For any global minimum partition D of G, (6.1) and `c_f(H)<=r(H)` give

```
min_T |{C in D : C misses T}| <= floor(c(G)-c_f(G)).        (6.3)
```

Indeed, for every A one can use an optimal fractional partition on H_A and the integral cycles of `D\A`, obtaining

```
c_f(G) <= c_f(H_A)+|D\A| <= r(H_A)+c(G)-|A|.
```

Apply (6.1) and integrality of its left side. In particular, an integrality gap strictly less than one suffices for an existential hitting tree for **every minimum partition**.

This is only an existential structural consequence. It neither controls the integrality gap nor supplies a partition for an arbitrarily prescribed tree.

---

## 7. Relationship with a specified Hamilton cycle

A universal prescribed-tree theorem would imply the specified-Hamilton-cycle theorem immediately: apply it to `T=F-e`. In contrapositive form, a counterexample for F already fails for every Hamilton-path tree `F-e` on the same graph.

There is moreover an exact instance reduction preserving both feasibility and infeasibility. Given an even G with specified Hamilton cycle F, subdivide one F-edge uv by a new vertex w. Let F' be the subdivided Hamilton cycle and set

```
T' = F' - wv.
```

This is a spanning **Hamilton path** of the new simple even graph G'. Subdivision gives a bijection between simple cycles of G and G'. A cycle using w must use both uw and wv, so under this bijection

```
C meets F   iff   C' meets T'.                            (7.1)
```

Exact partitions correspond, and so do fractional exact partitions: the two subdivided edges have identical cycle-incidence rows in the load equations. Costs are unchanged. Thus the F-hitting problem is exactly a special case of the Hamilton-path-tree-hitting problem after adding one vertex, with both integral and fractional feasibility preserved. This is not a converse reduction from every prescribed tree to a Hamilton cycle.

Theorem 3.1 settles these variants on the series-parallel class. The unrestricted variants, including fractional feasibility, remain unsettled by this investigation.

---

## 8. Verification and precise scope of the diagnostics

The companion checker uses the existing exact `all_cycles` and `cycle_edges` helpers. An integer edge-mask recursion chooses a remaining edge and branches over **every allowed simple cycle** containing it and lying in the remaining edge set. Its memoized failure is an exact-cover failure, not an LP/MILP tolerance judgment. Every returned partition is checked for exact edge coverage.

Run the proved constructions and their small-state audits with:

```bash
PYTHONDONTWRITEBYTECODE=1 PYTHONHASHSEED=0 OPENBLAS_NUM_THREADS=1 \
  python3 Submission/ResearchTreeHittingCheck.py --proof-checks-only
```

The verified construction checks are:

* **25** connected even series-parallel graph-atlas graphs through order seven, with **3,047** input spanning trees / two-component spanning forests: the recurrence produces actual marked cycle partitions.
* **102** eligible rooted two-terminal networks through order six, with **6,572** rooted-forest / path-count states: all paths, cycles, parities, coverage, the literal-direct-edge exception, and the connected-forest p=1 invariant are checked.
* The six-vertex three-forest obstruction: all **6** cycles, its **3** allowed cycles, exact-cover infeasibility, the integer Farkas certificate, and an unrestricted two-cycle optimum.
* **33** cubic bipartite double-star constructions, through **204 vertices**, including a disconnected base and degree-preserving random bipartite switches. The final cycles are simple, partition every edge, have exactly the asserted lengths, and meet the matching degree lower bound.
* **41** specified Hamilton inputs through order six, with **1,727** individual cycle mappings: the subdivision bijection and equivalence (7.1) are checked against independent full enumeration in the subdivided graphs.

### All small graphs / all trees

The default command additionally enumerates all connected even graph-atlas graphs through order seven and every spanning tree and Hamilton cycle in each. The extended command is:

```bash
PYTHONDONTWRITEBYTECODE=1 PYTHONHASHSEED=0 OPENBLAS_NUM_THREADS=1 \
  python3 Submission/ResearchTreeHittingCheck.py --exhaustive-through 9
```

It uses `nauty-geng -cq n | nauty-pickg -q -E` for the larger orders. At orders eight and nine it can certify all trees more efficiently by the following **complete**, not sampled, recursion.

At a state A of permitted tree edges, discard the state if `(V,A)` is disconnected. Otherwise choose one spanning tree T contained in A and solve its constrained exact cover. If it succeeds with partition D, **any counterexample tree contained in A must avoid some C in D**, so it is contained in `A\E(C)`. Recurse on all these child edge sets that can contain a spanning tree. Each child deletes at least one edge, since D meets the chosen T. Memoization is over exact edge sets. This covers every possible counterexample tree; it does not assume that the one chosen T represents the other trees.

The completed small-graph results are:

| vertices | connected even graphs | spanning trees, all passed | specified Hamilton cycles, all passed |
|---:|---:|---:|---:|
| 1 | 1 | 1 | 0 |
| 2 | 0 | 0 | 0 |
| 3 | 1 | 3 | 1 |
| 4 | 1 | 4 | 1 |
| 5 | 4 | 159 | 13 |
| 6 | 8 | 816 | 26 |
| 7 | 37 | 41,963 | 686 |
| 8 | 184 | 781,034 | 4,510 |
| 9 | 1,782 | 65,817,327 | 165,242 |

All trees through order eight were also checked by direct subset enumeration. The order-nine universal recursion completed with **85,591** states in total and at most **3,261** states for any one graph. An independent symmetry-pruned run also passed. Tree totals were computed exactly by the matrix-tree theorem with fraction-free integer elimination, not rounded numerical determinants. At order nine the Hamilton assertion follows already from the all-tree certificate via `F-e`; its displayed count is obtained by full cycle enumeration.

Hashes of the even connected graph6 input streams, including their newline bytes:

```
n=8: 9bfa1e769e37999d95e4d771bac9b67023d039bf59f0ca5073ab5995ded83c17
n=9: 196eeadec18ead5254febb72a7937f32ebc278764bb8c1ec27ff6b1fcaa1e4fd
```

These results exclude spanning-tree or Hamilton-cycle counterexamples on at most nine vertices. They do **not** exclude larger counterexamples and do not establish the general fractional statement.

### Explicit remaining gap

The series-parallel proof depends on two facts that do not hold for arbitrary overlapping subgraphs: child interiors meet only at the prescribed terminals, and two-terminal composition leaves at most one exceptional unmarked **direct edge**. For a general graph, an exported unmarked object can be a longer path and two pieces can have additional common vertices. The recurrence then no longer guarantees that a marked closed trail splits into marked simple cycles.

No extension replacing those two facts has been proved here. No general constrained-cone feasibility theorem, no unrestricted integral tree-hitting construction, and no spanning-tree counterexample is asserted. The existential universal variant remains exactly the strong rank bound described in Section 6, not an easier consequence of the existing fractional result.
