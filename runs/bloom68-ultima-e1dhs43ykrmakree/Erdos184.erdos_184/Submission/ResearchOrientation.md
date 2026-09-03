# Global rainbow flips: a dense obstruction and a phase-coupled repair

## Status and principal results

**The general Erdős–Gallai O(n) cycle/edge decomposition theorem is not proved here.** The outcome is a specific obstruction to the proposed global iteration, together with an explicit global repair and a rigorously accounted refinement. This is more than another triangle-transitive-orientation lemma.

The main additional construction is on the **same** even, maximally vertex-connected graph

```
G_r = K_(2r,2r,2r),     n=6r,     m=12r²,     degree=4r.
```

It has an explicit old partition into `4r²` triangles and a valid rainbow-flip selection consisting of just `r` rainbow cycles, each of length `4r=2n/3`, using **every old colour**. In the resulting balanced orientation:

* every old triangle is transitive;
* there is another partition into `4r²` directed triangles;
* another legal, all-colours-used rainbow flip returns to the old triangle partition. Thus the forgetful iteration has an exact **period two**, with no improvement in the length or original-degree-weight multiset;
* freezing the rainbow cycles and splitting their expanded trails separately forces exactly `2r²+r` cycles. More generally, processing at most `B` expansions per independent batch costs at least `r+2r ceil(r/B)` when the rainbow cycles are retained separately. Even arbitrary cycle/edge repartitioning of each whole batch still has a quadratic-over-`B` lower bound;
* nevertheless, globally coupling the expansions gives `3r=n/2` directed cycles without changing the orientation. Coupling across the skeleton/residual split improves this to **`2r=n/3` directed Hamilton cycles**, which is optimal by the degree lower bound. Every Hamilton cycle has original-degree weight `3/2`.

The repair is a proved **phase-packet factorization and amalgamation theorem**. Complete cyclic even-layer blow-ups with alternating class sizes `a,b` have an optimal partition into `max(a,b)` directed simple cycles. Compatible packets with shared large vertex classes can be amalgamated before factorization: their cost is a maximum, not the sum of their individual costs. This allows unbounded overlap without paying once per rank or rainbow cycle.

Two further barriers clarify the quantifiers:

1. **Linear-vertex universality.** Every balanced orientation of an arbitrary simple graph on `N` vertices occurs as an induced Eulerian subdigraph of an all-old-triangles-transitive rainbow-flip output on at most `2N` vertices. Thus a theorem asserted for every induced Eulerian subdigraph of such outputs would already have to hold for all balanced orientations of simple graphs.
2. **Orientation-only weighted certificates fail in complete graphs.** Every Eulerian orientation of `K_n`, for odd `n>=3`, has exactly `n(n²−1)/24` directed triangles and admits a directed-cycle partition containing at least `n(n+1)/36` triangles. Even adaptive nonnegative edge weights that give every directed cycle weight at least one must have total weight at least `n(n+1)/12`. Making a dense balanced orientation acyclic after deleting only O(n) exceptional edges is also impossible: at least `(n²−1)/8` deletions are necessary, sharply.

Section 6 gives a fixed-original-degree ledger for **paid Eulerian packet transversals**. If a uniform packet-extraction statement were proved, the ledger would give O(n) with no logarithmic or log-star loss. That extraction statement is precisely what remains unproved; the restricted packet class constructed here is not asserted to suffice for every graph.

`Submission/Spec.lean` was not edited. Its SHA-256 before and after this investigation is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

The reproducible checker is `Submission/ResearchOrientationCheck.py`. The prior `ResearchHeavy.md` and `ResearchPackets.md` were only read.

---

## 0. Conventions and the genuine cycle/edge target

Graphs are finite, simple and undirected until oriented. A cycle is simple; all decompositions below are **edge partitions**, not covers or decompositions modulo two. Different cycles may share vertices. An orientation has one arc per undirected edge, never both directions. “Balanced” means equal in- and out-degree at every vertex, including componentwise balance.

For a nonisolated vertex use its degree in the original graph G, and put

```
w_G(C) = sum_{v in V(C)} 1/d_G(v).
```

For any cycle partition of an even subgraph H of G,

```
sum_C w_G(C) = (1/2) sum_v d_H(v)/d_G(v).                  (0.1)
```

Terms at isolated vertices of G are defined as zero. In particular the total is at most `n_0/2`, where `n_0` is the number of nonisolated vertices of G.

Working with even graphs loses only O(n) singleton pieces in the original problem. In a spanning forest, take the parity subgraph whose odd boundary is the set of odd-degree vertices of G. It exists by eliminating leaves in each tree and has at most `n−components(G)` edges. Removing it leaves an even graph; retain its edges as singleton pieces. The rainbow lemma below requires an initial partition into **cycles**; it does not silently treat singleton edges as cyclically orientable pieces.

---

## 1. Audit of the rainbow-flip argument

### 1.1 The construction is correct

Let `D={C_1,...,C_q}` be a cycle partition of an even graph G. Give all edges of `C_i` colour i.

Choose a rainbow simple cycle, remove all its colours from future consideration, and repeat. At any stage with more than `n−components(G)` remaining colours, choosing one representative edge of each colour produces a graph with too many edges to be a forest. A simple cycle in this representative graph is rainbow. Thus one can stop with

```
|U| <= n−components(G),                                  (1.1)
```

where U is the family of unused old cycles. This also covers disconnected graphs and isolated vertices; the empty graph is trivial.

Let F be the union of the chosen rainbow cycles. Because a colour is never reused, F has **exactly one edge from each used colour** and none from an unused colour. The selected cycles are edge-disjoint, although they can share vertices. Hence F is even.

Orient F Eulerianly, obtaining an arc set `vec(F)`. For every used old cycle, orient that entire cycle cyclically so its selected edge has the opposite direction to `vec(F)`. Orient each unused old cycle cyclically in either direction. Call this orientation `T_0`. It is balanced because the old cycles partition all edges.

Now reverse just the selected edges. For an orientation J write

```
b_J(v) = d_J^+(v) − d_J^−(v).
```

The reversal changes the imbalance by `2 b_vec(F)(v)`: the old orientation on the selected edges was the negative of `vec(F)`. Therefore

```
b_T(v) = b_T0(v) + 2 b_vec(F)(v) = 0.                    (1.2)
```

This checks the sign as well as the balance claim.

If the selected edge is `u -> v` in the final orientation, the remainder of its old cycle is also a directed `u`–`v` path. The old cycle now consists of two directed `u`–`v` paths and is not a directed circuit.

**Terminology correction.** For a triangle this is a transitive orientation. For a longer cycle, the precise assertion is that the orientation of its **cycle-edge subgraph** is acyclic, with one source and one sink. It is not an assertion about all chords in the induced graph on the cycle's vertices.

Nothing requires a bound on the number of old cycles changed. This genuinely bypasses the fixed-degree-bounded exchange obstruction in `ResearchHeavy.md`.

### 1.2 The useful exact two-layer reduction

For this refinement, orient each of the selected rainbow cycles `Q_1,...,Q_s` cyclically. This is an allowed Eulerian orientation of F. An arbitrary Eulerian orientation of F need not preserve those particular cycles as directed cycles; that distinction matters if they are to be frozen.

Remove the unused old cycles U as final pieces. For each used colour i let

```
P_i = C_i − e_i,
P   = union_i P_i = G_used − F.
```

Each `P_i` is a simple path oriented in the same endpoint direction as `e_i` in F. Replacing the successive edges of `Q_j` by these paths gives an edge-simple directed closed trail `W_j`. The trails `W_j` partition P, and P is balanced: either sum the path divergences, which equal those of F, or subtract the two balanced orientations `T_used` and `vec(F)`.

Consequently, for **any chosen directed simple-cycle partition** `D_P` of P,

```
U  +  {Q_1,...,Q_s}  +  D_P                              (1.3)
```

is an exact cycle partition of G, of size `|U|+s+|D_P|`.

The danger is exactly located: `W_j` need not be simple. Its internal path vertices can repeat, including repetitions at vertices of `Q_j`. A small number of long rainbow cycles gives no corresponding bound on the cost of splitting the individual expanded trails. Section 3 gives a quadratic counterexample, even when every `Q_j` has length `2n/3`.

### 1.3 A modest but useful extension of the high-Berge-girth partial result

For triangle pieces, continue until **no** rainbow cycle remains, rather than merely stopping at (1.1). The incidence graph between the remaining triangles and graph vertices is then a forest. Indeed, an incidence cycle

```
v_0, C_0, v_1, C_1, ..., v_(k−1), C_(k−1), v_0
```

gives the rainbow graph cycle with edges `v_i v_(i+1)`: every pair of vertices of a triangle is adjacent. Edge-disjoint triangles cannot share two vertices, so `k>=3` and the resulting graph cycle is simple.

Including all n graph-vertex nodes in the incidence graph, the forest identity gives

```
3|U| = n+|U|−components(incidence graph),
2|U| = n−components(incidence graph) <= n−1               (1.4)
```

when `n>=1`. The empty family causes no problem.

More generally, suppose that every undirected cycle with `w_G(C)<c` is one of the designated old cycles, for some `c>0`. Freeze U and use the balanced orientation of `G_used`. No designated used cycle is directed, so every directed simple cycle that remains has weight at least c. Decomposing this orientation and using (0.1) gives

```
number of pieces <= |U| + n_0/(2c).                      (1.5)
```

For a triangle system whose only undirected cycles of length at most R are designated triangles, this yields

```
number of pieces <= (n−1)/2 + m/(R+1).                    (1.6)
```

There are at most `(n−1)/2` exceptional old triangles; every other output cycle has length greater than R. In a `2d`-regular system, `R>=2d` makes this fewer than n pieces. Unlike the earlier matching construction, no divisibility of the triangle multiplicities by three is needed. This is an O(n) count statement with exceptions, not a claim that every cycle is heavy.

The dense obstruction is that non-designated light cycles need not disappear. The next sections address that obstruction rather than assuming it away.

---

## 2. A global phase-packet factorization

### Theorem 2.1 — complete cyclic even-layer packets

Fix `h>=2` and positive integers a,b. Take disjoint classes

```
S_0,L_0,S_1,L_1,...,S_(h−1),L_(h−1),
|S_k|=b,  |L_k|=a,
```

and all arcs in the cyclic order

```
S_k -> L_k -> S_(k+1),                                   (2.1)
```

where k is read modulo h. Call this oriented graph `P_h(a,b)`.

It is balanced and has an **optimal** directed simple-cycle partition with

```
number of cycles = max(a,b),
length of every cycle = 2h min(a,b).                      (2.2)
```

**Proof.** A vertex in `S_k` has in- and out-degree a; a vertex in `L_k` has in- and out-degree b. Every directed cycle follows the layer order and visits each class the same number t of times. Thus its length is `2ht`, with `t<=min(a,b)`. There are `2hab` arcs, so every cycle partition has at least `max(a,b)` cycles.

Rotate the layer order if necessary so `a>=b`. Index `S_k` by `j=0,...,b−1`, and `L_k` by `Z_a`. For each `i in Z_a`, define one cycle by concatenating, in lexicographic order of `(j,k)`, the pairs

```
S_(k,j), L_(k,i+j)       (j=0,...,b−1; k=0,...,h−1).      (2.3)
```

The large-class index is reduced modulo a. At the end of the k-block, the next vertex is `S_(k+1,j)`; at the end of a j-block it is `S_(0,j+1)`, with the last j-block closing to `S_(0,0)`.

Every edge used is present by (2.1). The cycle is simple: it uses distinct vertices in each small class, and `i,i+1,...,i+b−1` are distinct modulo a in each large class. It has length `2hb`.

For fixed k,j, varying i uses every edge from `S_(k,j)` to `L_k` exactly once, and every edge from `L_k` to the prescribed next small-class vertex exactly once. For `k=h−1` the next small index is `j+1 mod b`, which is still a bijection of the small class. Thus the a cycles partition every arc exactly once. They attain the lower bound. □

The common offset i is the **phase**. Independent choices at different layers need not make one long cycle; the synchronized choice (2.3) does.

The even number of layers is part of the theorem. No arbitrary odd-layer Hamilton-factorization claim is being used.

### Corollary 2.2 — amalgamate before paying

Suppose many packets share the same ordered large classes `L_0,...,L_(h−1)` of size a. Packet p has small classes `S_k^(p)` of a common size `b_p`, disjoint from the other packets' small classes. All their complete arc blocks have the orientation (2.1).

Their edge-disjoint union is

```
P_h(a,B),        B=sum_p b_p.
```

It therefore costs exactly `max(a,B)` cycles, rather than

```
sum_p max(a,b_p).                                        (2.4)
```

For example, r packets with `b_p=1` and `r<=a` cost a cycles together but ra separately.

This is an actual amortized global rule: open the common terminal classes once; thereafter adding small-class capacity b increases the certified cost by at most b. Below total capacity a, the number of cycles does not increase at all—the cycles get longer. One must retain the packet as an unclosed edge set until this coupling is performed, instead of irrevocably emitting its local short cycles.

This theorem uses complete, consistently directed arc blocks. It does not assert that arbitrary intersecting path bundles have such a factorization.

---

## 3. A dense period-two obstruction, with a globally optimal repair

It is useful to give a slightly more general family first.

### 3.1 The graph and its old triangle partition

Let `a>=2r>=2`. Take

```
X={x_i : i in Z_a},       Y={y_i : i in Z_a},
A={a_j : 0<=j<r},         B={b_j : 0<=j<r}.
```

All four classes are disjoint. For `s=0,...,2r−1`, put

```
M_s = {x_i y_(i+s) : i in Z_a}.
```

These are distinct perfect matchings between X and Y. Define `G_(a,r)` to have:

* all edges in `M_0,...,M_(2r−1)`;
* all edges between `X union Y` and `A union B`;
* no other edges.

The old triangle partition `D_0` consists, for every i,j, of

```
{x_i, y_(i+2j),   a_j},
{x_i, y_(i+2j+1), b_j}.                                  (3.1)
```

Every XY edge occurs once. Each `a_j` or `b_j` is joined once to every x and every y in these triangles, so all other edges also occur once. In particular,

```
n=2a+2r,        m=6ar,        |D_0|=2ar,
d(x_i)=d(y_i)=4r,             d(a_j)=d(b_j)=2a.            (3.2)
```

The graph is even. Every old triangle has weight

```
1/(2r) + 1/(2a).                                         (3.3)
```

### 3.2 All colours are broken using r long rainbow cycles

For `j=0,...,r−1`, let

```
Q_j = M_(2j) union M_(2j+1).
```

Orient its arcs as

```
x_i -> y_(i+2j) -> x_(i−1).                              (3.4)
```

The successive X-indices decrease by one, so `Q_j` is one Hamilton cycle on `X union Y`, of length `2a`. The `Q_j` are edge-disjoint and rainbow relative to (3.1). Their union F uses exactly one edge of **every** old triangle.

After the prescribed old-cycle orientation and representative reversal, the complementary arc set is

```
P:   X -> A -> Y -> B -> X,                              (3.5)
```

with all four complete arc blocks. Thus P is `P_2(a,r)`. Both F and P are balanced, and the final orientation is

```
T^+ = vec(F) union P.
```

For a triangle using `a_j`, the direct arc and the two-edge path both go `x_i -> y_(i+2j)`. For a triangle using `b_j`, both go `y_(i+2j+1) -> x_i`. All old triangles are transitive, exactly as required.

### 3.3 Exact period two: all old pieces can be replaced by equally bad new ones

Define `D_1` by exchanging the roles of `a_j` and `b_j` in (3.1):

```
{x_i, y_(i+2j),   b_j},
{x_i, y_(i+2j+1), a_j}.                                  (3.6)
```

This is another triangle partition of the same graph. In `T^+`, its triangles are directed:

```
x_i -> y_(i+2j) -> b_j -> x_i,
y_(i+2j+1) -> x_i -> a_j -> y_(i+2j+1).
```

The same XY edges are still one representative from each `D_1` colour, and the same undirected `Q_j` are rainbow. Now choose the **opposite** Eulerian orientation on F. Orienting `D_1` cyclically opposite those representatives gives precisely `T^+`; reversing the representatives produces

```
T^- = (−vec(F)) union P.
```

Every `D_1` triangle is now transitive, and every `D_0` triangle is directed cyclically. Starting from `D_0` again returns to `T^+`.

Thus legal all-colours-used steps give

```
D_0 -> D_1 -> D_0 -> ...                                 (3.7)
```

with `2ar` triangles at every stage. The entire length/weight multiset is unchanged. This defeats automatic strict progress of any symmetric potential depending only on that multiset. It also shows that a former colour can be completely resurrected after one intervening round.

The barrier also survives a rule that stops as soon as at most `n−1` colours remain. In the dense case `a=2r`, `r>=2`, execute just `r−1` of the `Q_j`. There are then `4r<=n−1` unused triangles. Swap the middle labels only for those `r−1` indices and keep the unused triangles fixed. The same two-step reversal returns to `D_0`, still with `4r²` triangle pieces throughout.

**Scope.** This is not a counterexample to a carefully chosen global optimum or to a suitably refined potential. The displayed triangle partitions are very far from minimum cardinality. It disproves a progress claim based solely on breaking all current pieces, even using few, very long rainbow cycles.

### 3.4 Independent expansion and bounded-batch closure force a large cost

The expansion of `Q_j` uses the arc set

```
P_j:  X -> {a_j} -> Y -> {b_j} -> X.
```

Its underlying graph is `K_(2a,2)`. Every directed simple cycle has length four, so **every** cycle partition of `P_j` has exactly a cycles. An explicit one is

```
(x_i, a_j, y_i, b_j),       i in Z_a.
```

Therefore, if the `Q_j` are retained and the expanded trails are closed independently, the total is exactly

```
r + ar.                                                  (3.8)
```

This remains a real obstruction for batches, not just for individual trails. For a set J of b indices, the expanded union is `P_2(a,b)`. Every directed cycle has length at most `4b`, and there are `4ab` arcs. Hence every partition needs at least a cycles, attained by Theorem 2.1.

If the r expansions are assigned to t nonempty independent batches, the retained-F scheme therefore costs exactly `r+at` at best. In particular, batches of size at most B give

```
number of cycles >= r + a ceil(r/B).                     (3.9)
```

Even if each batch is allowed to reopen its Q-edges and repartition its **whole undirected edge set**, it still needs at least a pieces: any one of its middle vertices has degree `2a`, and a simple cycle or singleton piece uses at most two incident edges there. Thus arbitrary undirected repartitioning within independent batches has the lower bound

```
a ceil(r/B).                                             (3.10)
```

The restriction being refuted is independent batch closure. Cycles that mix different batches are exactly the missing resource.

### 3.5 Global coupling already gives n/2 pieces, with no regularity assumption

Amalgamate all `P_j` before closing them. By Theorem 2.1, `P=P_2(a,r)` has a partition into a cycles of length `4r`. Explicitly, for each `i in Z_a`, concatenate

```
a_j, y_(i+j), b_j, x_(i+j),       j=0,...,r−1.            (3.11)
```

The cycle closes from its last X-vertex to `a_0`. Because `r<=a`, it is simple. The proof of Theorem 2.1 verifies exact edge coverage, not just a cover.

Together with the r cycles `Q_j`, this gives

```
a+r = n/2 cycles.                                        (3.12)
```

Their weights in the original graph are

```
w_G(Q_j) = a/(2r),
w_G(C_i from (3.11)) = 1/2 + r/a.                         (3.13)
```

In particular every cycle has weight at least `1/2`, even when `a/r` is unbounded. Their total weight is `a+r=n/2`, as required by (0.1).

This repair changes only the choice of cycle partition inside a fixed balanced orientation. It does not need another orientation flip, extra edges, or a disjointization assertion.

### 3.6 Dense specialization: the same orientation has an optimal Hamilton partition

Set `a=2r`. Then all XY matchings are present and

```
G_(2r,r) = K_(2r,2r,2r),
n=6r,   degree=4r,   |D_0|=|D_1|=4r²,
|Q_j|=4r,   w_G(old triangle)=3/(4r).                     (3.14)
```

Its vertex-connectivity is `4r`: deleting fewer vertices leaves at least two nonempty original parts, which are connected through the complete cross edges; deleting the other two parts isolates the remaining part. Thus this is a dense, maximally connected obstruction, not a separator artefact.

Write `X_0,X_1` and `Y_0,Y_1` for the even/odd-index halves, each of size r. The orientation on F is the complete cyclic four-layer orientation

```
X_0 -> Y_0 -> X_1 -> Y_1 -> X_0.
```

Together with (3.5), all arcs of `T^+` split into the complete blow-ups of these two directed six-cycles:

```
H_0 = (X_0, A, Y_0, X_1, Y_1, B),
H_1 = (X_0, Y_0, B, X_1, A, Y_1).                        (3.15)
```

The twelve ordered class pairs appearing here are distinct and are exactly all ordered class pairs of `T^+`. Each packet is `P_3(r,r)`. By (2.3), each has r directed Hamilton cycles on all `6r` vertices. The two packets therefore give

```
2r = n/3 directed Hamilton cycles.                       (3.16)
```

For an entirely explicit formula, list the six classes of either `H_t` as `L_0,...,L_5`, index each by `Z_r`, and for phase `i in Z_r` concatenate

```
L_(0,j), L_(1,i+j), L_(2,j), L_(3,i+j),
L_(4,j), L_(5,i+j),          j=0,...,r−1.                 (3.17)
```

Indices are modulo r. These are simple Hamilton cycles, and (2.3) proves that they partition that packet's arcs.

Any cycle/edge partition of G needs at least `degree/2=2r` pieces at a vertex. Hence (3.16) is **optimal**, even among undirected cycle/edge partitions. Every Hamilton cycle has weight `6r/(4r)=3/2`.

This single orientation thus supports all of the following:

| Extraction rule | Number of pieces |
|---|---:|
| Select the directed triangle partition `D_1` | `4r² = n²/9` |
| Freeze F, split each expansion separately | `2r²+r = n²/18+n/6` |
| Freeze F, globally amalgamate P | `3r = n/2` |
| Globally factor the two six-layer packets | `2r = n/3`, optimal |

For bounded-batch closure, (3.10) is superlinear whenever `B=o(r)`. Obtaining O(n) by that architecture requires coalescing a linear number of the rainbow expansions in at least one batch. Each expansion already comes from a cycle of length `2n/3`; selecting long rainbow cycles alone does not fix the problem.

The contribution relative to the earlier orientation partial is this **simultaneous obstruction and repair**. It is not a claim that complete multipartite graphs were previously unknown to have linear decompositions.

---

## 4. How much structure does a triangle flip actually impose?

### 4.1 An inverse characterization

Let D be any triangle partition of G and T any balanced orientation of G. In each transitively oriented designated triangle, select the shortcut arc from its source to its sink. Select nothing in a cyclically oriented designated triangle. Let F be the selected arc set.

For a transitive triangle its imbalance vector is twice that of its shortcut. A cyclic triangle contributes zero. Summing over the edge partition gives

```
0 = b_T = 2 b_F.
```

Thus F is balanced and has at most one edge of each old colour. Reversing every selected shortcut makes all designated triangles cyclic. Conversely, reversing them back is exactly the rainbow-flip construction: any directed-cycle partition of F is globally rainbow because F has at most one edge of each old colour.

Therefore **every balanced orientation of a triangle partition has the one-shortcut form**. The number of unselected colours is the number of cyclic designated triangles in T. If all old triangles are transitive, all colours are used and the rainbow selection is certainly maximal.

This does not say that an arbitrary T has at most n unselected colours. The all-transitive case, used next, has zero.

### Theorem 4.2 — every balanced oriented graph embeds in a fully successful output

Let D be a balanced orientation of a simple graph J on N vertices. There is a simple even graph H on at most `2N` vertices, with a triangle partition, and an all-colours-used rainbow flip whose output T:

* makes every old triangle transitive;
* induces exactly D on the original N vertices;
* has its entire selected representative subgraph equal to D.

**Proof.** Properly edge-colour J with at most N colours. This needs no deep edge-colouring theorem: restrict the following colouring of `K_N`. For odd N, use vertices `Z_N` and colour `uv` by `(u+v)/2 mod N`. For even `N>=4`, use `Z_(N−1) union {infinity}`; use the same midpoint colour on finite pairs and colour `u,infinity` by u. At each vertex the colours are distinct. The cases `N<=2` are trivial for a balanced orientation of a simple graph.

Add one vertex `z_c` for each used proper edge-colour. Replace every original arc `u -> v` by the old triangle with edges

```
uv, u z_c, z_c v,
```

retaining uv. These triangles are edge-disjoint: a proper edge-colour class is a matching, so two triangles using the same `z_c` have disjoint original endpoints. No multiple edges are introduced.

Orient the triangle transitively as

```
u -> v,       u -> z_c -> v.                             (4.1)
```

Every new middle vertex has zero imbalance, triangle by triangle. At an original vertex the total imbalance is twice its imbalance in D, hence zero. This gives a balanced orientation T of H.

Choose every original arc uv as the selected representative. Their union is the balanced digraph D. Its directed-cycle partition is a legal rainbow selection using every old triangle colour exactly once. Orienting the old triangles cyclically opposite these representatives and then flipping gives (4.1). There are at most N new vertices and no new original-to-original edges. □

The proper edge-colours used to reuse middle vertices are **not** the piece colours in the rainbow argument: each original edge is its own old triangle piece.

### Consequences and limitations of this barrier

* Being an all-old-triangles-transitive output gives no hereditary restriction that excludes arbitrary Eulerian oriented subgraphs.
* A theorem that blindly freezes the selected F and claims its directed decomposition is automatically cheap would have to address an arbitrary balanced oriented graph, not a specially constrained skeleton.
* Invoking a general O(N) directed-cycle decomposition theorem for every balanced oriented graph would be importing a Bollobás–Scott-type conjectural strengthening, not a result proved here. The local source `/corpus/src/1911.07778/introduction.tex` discusses this directed conjecture separately from the undirected one.

This is an **induced-subgraph universality theorem**, not a claimed reduction of minimum decomposition numbers. Cycles in H may mix through the added middle vertices, and such mixing can make H much easier to decompose. Nor does the theorem rule out choosing F strategically rather than accepting an arbitrary valid selection.

---

## 5. Quantitative obstructions to orientation-only short-cycle control

### 5.1 Complete graphs: a conserved local triangle count

Let `n=2s+1` with `s>=1`, and let T be any Eulerian orientation of `K_n`. It is a regular tournament: every vertex has in- and out-degree s.

Fix v, with out-neighbourhood A and in-neighbourhood B, each of size s. The total out-degree of vertices in A is `s²`; `binom(s,2)` arcs are internal to A and none go from A to v. Hence

```
e_T(A,B) = s²−binom(s,2) = s(s+1)/2.
```

These are exactly the directed triangles `v -> A -> B -> v`. Therefore

```
# directed triangles containing v = (n²−1)/8,
# directed triangles in T          = n(n²−1)/24.          (5.1)
```

For **any** fixed vertex prices `alpha_v`, the additive directed-triangle potential is consequently

```
sum_{directed triangles C} sum_{v in C} alpha_v
   = ((n²−1)/8) sum_v alpha_v,                            (5.2)
```

independent of the balanced orientation. In particular, minimizing such a weighted short-cycle potential cannot detect progress in a complete graph. This sum is over all directed triangles, not over one edge partition; it must not be confused with (0.1).

Every directed triangle has original-degree weight `3/(n−1)`. Thus no balanced orientation of these graphs can make **every** directed cycle uniformly original-degree-heavy.

### 5.2 Every balanced orientation admits a bad extraction

An arc `u -> v` lies in at most s directed triangles, since a third vertex must lie in `N^+(v) intersect N^−(u)`. Take a maximal edge-disjoint family of directed triangles. Each selected triangle meets at most `3s` original directed triangles in an edge. By maximality and (5.1), the number k selected satisfies

```
k >= [n(n²−1)/24]/(3s) = n(n+1)/36.                      (5.3)
```

Removing them preserves balance. The remaining arcs partition into directed simple cycles, so T admits a full cycle partition with at least this many triangle pieces.

This statement holds for **every choice of balanced orientation**, not merely the particular output in Section 3. It rules out any proof that finishes with “take an arbitrary directed-cycle decomposition” and expects O(n).

There is also an adaptive weighted obstruction. Suppose nonnegative arc weights `z_e` satisfy

```
sum_{e in C} z_e >= 1    for every directed simple cycle C.
```

Summing just over the directed triangles and again using that an arc belongs to at most s of them yields

```
sum_e z_e >= [n(n²−1)/24]/s = n(n+1)/12.                  (5.4)
```

Thus even weights chosen **after** seeing the orientation cannot certify all directed cycles by a nonnegative O(n)-mass budget. One must control the chosen partition, or retire many edges in cheaply decomposable packets; changing the positive pricing scheme alone does not evade this obstruction.

These are barriers to universal extraction/charging, not counterexamples to existence of a good partition.

### 5.3 Acyclic dense-cluster orientations require an actual cut certificate

Here is the exact extension condition, useful if one tries to lock an acyclic orientation inside chosen clusters.

**Proposition 5.3.** Let G be even. Orient a subgraph H in any way and leave `R=G−E(H)` unoriented. Write `b_H(S)=sum_{v in S} b_H(v)`. The partial orientation extends to a balanced orientation of G if and only if

```
|b_H(S)| <= e_R(S,V(G)\S)    for every vertex set S.       (5.5)
```

**Proof.** The required out-degree in R is

```
k_v = (d_R(v)−b_H(v))/2.
```

It is integral because G is even and `b_H(v)` has the parity of `d_H(v)`. Also `sum_v k_v=|E(R)|`. An orientation with these out-degrees exists exactly when

```
sum_{v in S} k_v >= e_R(S)       for every S.             (5.6)
```

For completeness, assign each R-edge to its tail using a bipartite integral flow: an edge node has supply one, its two endpoint nodes have capacities `k_v`. The inequalities (5.6) imply Hall's capacity condition for every set of edge nodes, by taking its endpoint set. The singleton and complementary inequalities also give `0<=k_v<=d_R(v)`. Total supply equals total capacity, so the resulting assignment has precisely the desired out-degrees.

Substituting the formula for `k_v` turns (5.6) into `b_H(S)<=e_R(S,V\S)`. Applying it to the complementary set gives the negative inequality. Necessity follows equally from summing balance over S. □

Vertexwise external degree comparisons are not a substitute for all these cuts. Acyclic cluster orientations are permitted when the cut test passes; they are not automatically compatible with Eulerian balance.

There is a sharp quantitative obstruction to the extreme “acyclic backbone plus O(n) exceptional edges” version. If B is an arc set whose deletion makes a regular tournament acyclic, take a topological order of `T−B` and let S be its first s vertices. Balance of T gives exactly `s(s+1)/2` arcs from the complement into S. All must be in B. Hence

```
|B| >= s(s+1)/2 = (n²−1)/8.                              (5.7)
```

This is sharp over balanced orientations: orient `i -> i+d mod n` for `1<=d<=s`. In the natural order `0,...,2s`, there are exactly `s(s+1)/2` backward arcs, and deleting them leaves an acyclic graph.

The refined method below therefore uses **balanced, factorable dense packets**, not an unjustified promise that dense clusters can be made acyclic at linear exceptional-edge cost.

---

## 6. Refined method: paid Eulerian packet transversals

The phase factorization suggests changing what is globally maintained. The object to preserve is not merely a list of broken colours or a hierarchy of separately closed trails. It is a family of **unclosed, compatible Eulerian packets**, with an explicit global factorization and a fixed-original-degree cost certificate.

### 6.1 The degree-share ledger

For any edge subgraph H define

```
rho_G(H) = sum_v d_H(v)/d_G(v).                           (6.1)
```

For edge-disjoint subgraphs, these quantities are additive, regardless of vertex overlap. In particular,

```
sum_i rho_G(H_i) <= n_0.                                 (6.2)
```

For a phase packet `H_i = P_(h_i)(a_i,b_i)`, Theorem 2.1 supplies a partition of cost

```
M_i = max(a_i,b_i).
```

A useful, directly checkable certificate is

```
M_i <= K rho_G(H_i),                                     (6.3)
```

for one absolute K. This is an average degree-share condition, not pointwise degree-normalized resilience. It does not require every output cycle inside a packet to be heavy.

**Why coalescence matters numerically.** In the dense family of Section 3:

* each individual `P_j` has `rho_G(P_j)=4`, but costs `2r`; its efficiency ratio is `r/2` and fails every fixed K;
* the amalgamated P has `rho_G(P)=4r` and costs `2r`, passing with `K=1/2`;
* F has `rho_G(F)=2r` and costs r, also passing with `K=1/2`;
* each of the two six-layer packets (3.15) has `rho_G=3r` and costs r, passing with `K=1/3`.

The degree-share resource is the same before and after amalgamation; only the factorization cost changes. This is exactly the global improvement that a separate-per-rainbow or separate-per-rank account misses.

### Theorem 6.2 — a no-log conditional certificate

Apply the rainbow flip and freeze the unused old cycles U. In the remaining balanced orientation choose pairwise edge-disjoint phase packets `H_i`, and let R be the remaining arc set. Suppose that, for absolute constants `K,c>0`:

1. every packet satisfies (6.3);
2. R has no directed simple cycle of original-degree weight less than c.

Then G has an exact cycle partition with at most

```
|U| + max(K,1/(2c)) n_0                                  (6.4)
```

pieces.

**Proof.** Each packet is balanced, so removing all packets preserves balance of R. Factor each packet by Theorem 2.1. Decompose R into directed simple cycles; by hypothesis they all have weight at least c. By (0.1),

```
number of R-cycles <= rho_G(R)/(2c).
```

Consequently the number of pieces other than U is at most

```
K sum_i rho_G(H_i) + rho_G(R)/(2c)
 <= max(K,1/(2c)) [sum_i rho_G(H_i)+rho_G(R)]
 <= max(K,1/(2c)) n_0.
```

All edges are covered once, because the packets, R and the frozen U are edge-disjoint. □

Condition 2 can equivalently be expressed by saying that the packet union is an **edge transversal of all light directed cycles** in the active orientation. The transversal is allowed to contain quadratically many edges. It is its **decomposition cost**, not its edge count, that is paid linearly. This is how the certificate avoids (5.4) and (5.7).

This module combines the two successful situations:

* in the high-Berge-girth/designated-short-cycle case of Section 1.3, no packets are needed;
* in the dense example, the two packets (3.15) consume the whole active graph, so there is no residual condition to verify. Their ledger alone gives exactly `n/3` pieces.

### 6.3 A concrete global protocol, and the exact missing theorem

The proved protocol is:

1. Use global rainbow flips to remove the designated old short cycles as directed obstructions. Freeze only the O(n) unused old cycles.
2. Keep the expanded path families unclosed. Detect compatible complete even-layer packets and **amalgamate before factorization**, allowing unboundedly many old colours and unbounded vertex overlap.
3. Retire an edge-disjoint packet only with an explicit phase factorization and a uniform cost certificate (6.3). Retiring a balanced packet preserves balance and cannot create a new directed cycle in the residual orientation.
4. When every remaining directed cycle is original-degree-heavy, decompose the residual and use the single fixed-degree ledger (6.4).

There is no per-level or per-scale factor in this accounting. Degrees in (6.1) are frozen in the original graph; they are not recomputed after each removal.

**What has not been proved:** a uniform structural extraction theorem that makes this protocol finish on every graph. More precisely, one would need to choose the representative selection and orientation, and then actually find edge-disjoint, globally coalesced, explicitly factorable packets of uniformly bounded `M_i/rho_G(H_i)` whose union hits every remaining light directed cycle. The complete even-layer packets above are one proved class; this investigation does **not** assert that this restricted class always suffices. More general factorizable dense cores may be necessary.

The outstanding issue has two coupled parts:

* **factorization compatibility:** the short mixed cycles must reveal a globally usable arrangement of arc blocks or path bundles, not merely many pairwise intersections or a dense undirected union;
* **uniform payment:** local copies of a common terminal set must be charged once through a shared packet, or by a genuinely additive degree-share budget, rather than once at every rank or density scale.

A failure of the first is not repaired by declaring all expanded trails to be simple. A failure of the second is not repaired by saying each separate dense cluster has an O(its order) decomposition. Section 3 exhibits both failures with exact formulas. If the method reorients an unretired residual in another round, it must recheck its short-cycle restrictions; (3.7) shows that no-resurrection is not automatic.

Thus the missing step is not a numerical constant, a bounded exchange, or an odd-cover disjointization. It is a **global, paid factorization/extraction statement**. If obtained with absolute K and c, Theorem 6.2 and the parity-forest reduction would yield genuine O(n) edge-disjoint simple cycles/singletons, with no log-star loss. No such universal statement is claimed here.

---

## 7. Targeted verification

All general assertions above have proofs independent of computation. The checker uses integer and exact-rational arithmetic and verifies simplicity and exact edge coverage, not just balance or successful execution.

Run:

```
PYTHONHASHSEED=0 python3 Submission/ResearchOrientationCheck.py
```

### 7.1 Generic flip and inverse/embedding checks

* All **84** nonzero-order even graphs in the NetworkX atlas through order 7 were checked using an actual cycle partition. This is not an enumeration of every partition or every orientation of those graphs.
* **48** generated even graphs, at orders `6,9,12,20,31,48`, were checked for the generic representative-selection bound, both choices of how to Eulerianly orient F, the imbalance identity, and directed-cycle edge partitioning.
* **24** generated triangle systems were checked using maximal incidence-cycle selection, including the exact forest identity (1.4), and **24** inverse-shortcut characterizations were checked.
* The linear-vertex embedding was checked on **48** balanced oriented input graphs. Every output was simple and balanced; all old triangles were transitive; the original orientation was induced; all old colours were used; the order was at most twice the original order.

### 7.2 Phase packets and the dense obstruction/repair

The phase formula was checked for all `1<=a,b<=16` at four layers, and for `1<=a,b<=6` at six, eight and twelve layers: **364 distinct parameter triples** in total.

The family `G_(a,r)` was checked at **29** parameter pairs, including nonregular examples and all dense examples with `r=1,...,12,16,24,32`. Checks include:

* both triangle partitions and the two-step return;
* all-colours-used rainbow selection and all old triangles transitive;
* exact local/batched and globally coupled partitions;
* all degree, count and rational-weight formulas;
* in the dense specialization, the complete tripartite graph identity, the two six-layer arc blocks, and all `2r` Hamilton cycles covering every edge exactly once;
* connectivity computations for the smallest dense cases, supplementary to the general deletion proof.

Selected dense results:

| r | n | Old / period-two triangles | Separate expansions, retaining F | Amalgamated P + F | Optimal Hamilton partition |
|---:|---:|---:|---:|---:|---:|
| 1 | 6 | 4 | 3 | 3 | 2 |
| 2 | 12 | 16 | 10 | 6 | 4 |
| 4 | 24 | 64 | 36 | 12 | 8 |
| 8 | 48 | 256 | 136 | 24 | 16 |
| 16 | 96 | 1024 | 528 | 48 | 32 |
| 32 | 192 | 4096 | 2080 | 96 | 64 |

The last row has **12,288 edges**, with every one covered exactly once in each reported partition.

### 7.3 Universal orientation barriers and cut feasibility

Every labelled regular tournament of orders 3, 5 and 7 was enumerated: respectively **2, 24 and 2640 orientations**. For each, the global and per-vertex directed-triangle identities were verified, a maximal directed-triangle packing was extracted, and the balanced residual was checked and decomposed. The lexicographically ordered triangle greedy procedure used between 4 and 7 triangles at order 7; these finite counts are not needed for the asymptotic lower bound (5.3).

The sharp feedback-arc example (5.7) was checked at every odd order from 3 through 51.

For **320 sampled partial orientations** of `K_3` and `K_5`, every vertex cut was tested and every orientation of the unoriented remainder was exhaustively searched. The cut criterion agreed with actual extendability in every case; 128 samples were extendable.

The checker verifies the specification hash at both its start and its end. All tests passed. The exact constructions and proofs are in this document, rather than depending on temporary scripts or an unrecorded search witness.

---

## 8. Bottom line

The proposed flip is valid and genuinely global. It does not, however, give progress merely by destroying the old circuits: even with zero unused colours and linearly many rainbow cycles of linear length, it can alternate forever between two quadratic triangle partitions.

The refined global operation that succeeds in the explicit obstruction is **phase-synchronized amalgamation before cycle extraction**. The same orientation then has an optimal linear Hamilton partition. A fixed-original-degree packet ledger explains how such amalgamation could remove scale losses, while the universality and complete-graph barriers explain why an orientation-only or arbitrary-extraction argument cannot do so.

**The general O(n) theorem remains open in this work.** The precise new target is a globally compatible, uniformly paid extraction of factorable Eulerian packets that absorbs the mixed short cycles—not another proof that most designated old colours can be broken.
