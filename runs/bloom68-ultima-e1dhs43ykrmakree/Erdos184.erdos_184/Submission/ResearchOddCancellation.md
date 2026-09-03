# Odd-cover cancellation: a rank-exact reservoir reduction and disc-gluing obstructions

## Status and main results

**The unrestricted inequality `c(G) <= k + C r(G)` is not proved, and no counterexample for every constant C is produced.** In particular, this note does not solve the Erdős–Gallai problem. It gives an unconditional, constructive graph reduction, two exact graphic test families, and an explicit account of where polygon-edge gluing fails. None of the failures of restricted procedures below is presented as a disproof of unrestricted rounding.

The main new results relative to the supplied notes are:

1. **An exact odd-reservoir contraction.** Let H have a terminal set W of `2b` leaves and even degrees at all other vertices. Let J add one root adjacent to W. Replace that root by an independent set U of odd size `s=2a+1`, with every possible U–W edge, obtaining R. Then

   ```
   delta = max(0,a+1-b),
   c(R)   = c(J)   + delta,
   c_f(R) = c_f(J) + delta,
   r(R)   = r(J)   + s-1.                                      (A)
   ```

   The reconstruction works for **every** perfect matching of the terminals induced by a cap partition. Each new cycle contains only one real terminal path; vertex repetition is explicitly excluded. Fractional reconstruction does not assume that a degree-feasible terminal distribution is a convex combination of perfect matchings. There is also an explicit signed dual lift valid for **all** cycles.

   Repeated eligible contractions give the single ledger

   ```
   c(G) = c(K) + sum delta_i
        <= c(K) + (r(G)-r(K))/2,                               (B)
   c(G)-c_f(G) = c(K)-c_f(K).
   ```

   Thus this is a genuine smaller-graph reduction, not an optimization objective equivalent to the original problem. In particular, for a proposed linear bound with coefficient at least `1/2`, it suffices to consider graphs with no eligible odd reservoir. Generic graphs need not contain such a reservoir.

2. **Minimum odd covers whose disc-gluing repair is quadratically bad.** For every `t>=1` there is a connected simple even graph G_t with

   ```
   n=10t-1,   m=12t^2+t,   k=o(G_t)=c_f(G_t)=c(G_t)=3t.
   ```

   A specified minimum odd cover of k cycles has just t repeated edges. They form a matching and each occurs three times. Every possible pairing of duplicate copies glues polygons into **discs only**, with

   ```
   boundary trails = 2t,
   exact within-boundary collision debt = t(2t-1).
   ```

   More strongly, even allowing arbitrary temporary increases and arbitrary optimal repartitioning **inside each original edge-overlap component** forces exactly `t(2t+1)` cycles. A global mixed-component partition uses exactly `3t`, and is given explicitly. Therefore genus zero, a matching of repeated edges, only O(n) duplicate copies, and minimum odd-cover cardinality do not justify repairing the gluing components independently.

3. **The exact contraction in (A) need not preserve a cheap odd cover.** There are R_b and their one-root contractions J_b, for every `b>=2`, such that

   ```
   |V(R_b)| = 2b^2+5b-1,
   c(R_b)=c_f(R_b)=c(J_b)=c_f(J_b)=b^2,
   o(R_b)=2b-1,                 o(J_b)=b^2,
   r(R_b)-r(J_b)=2b-2.                                        (C)
   ```

   The displayed minimum odd cover of R_b again has matching repeated-edge support. Thus the odd-cover cost can rise by `(b-1)^2` under a single **cycle-cost-preserving** contraction that removes only `2b-2` units of rank. This rules out charging that rise just to the rank removed by that step. It does not invalidate (A) or the global ledger (B).

   This family also proves the unconditional necessary condition

   ```
   C >= 1/2
   ```

   for any universal inequality `c(G)<=k+C r(G)` valid for every supplied odd cover. The ratio `(c(R_b)-o(R_b))/r(R_b)` tends to `1/2`, not to infinity. An exact signed dual and a separate nonnegative ordinary-cover certificate are supplied.

All proofs are at paper level. No literature-priority claim is made. Only this new file was added to `Submission`; the specification and all 30 pre-existing files were preserved. A self-contained exact checker is embedded at the end.

---

## 0. Conventions and the Fan input

Graphs are finite, simple and undirected. An even graph has even degree at every vertex; disconnected graphs and isolated vertices are allowed. All cycles are vertex-simple, of length at least three. Write

```
c(G)   = minimum number of cycles in an exact edge partition,
o(G)   = minimum number of simple cycles in an odd cover,
c_f(G) = min sum_C x_C,
         subject to sum_{C containing e} x_C=1 for every e, x_C>=0,
r(G)   = |V(G)|-kappa(G).
```

An odd cover is a list of cycles of G, every original edge occurring a positive odd number of times. Repeated list entries are allowed, although two identical entries can be removed from a minimum cover. For a supplied k-cycle odd cover, write

```
mu_e = 1+2a_e,          A=sum_e a_e.
```

A is the number of paired copies to cancel, not the rank. The elementary existence of a cycle partition follows by successively removing simple cycles from a nonempty even graph. Hence all the minima are finite and `o<=c`.

The local survey quotation is exactly:

* `/corpus/src/1110.1144/1110.1144.tex`, lines 324–326, Theorem 3.9 (Fan [14]): every Eulerian graph on n vertices can be covered by at most `floor((n-1)/2)` circuits, each edge an odd number of times.
* `/corpus/src/1310.0632/1310.0632.tex`, line 487, refers to Fan [F03] as proving a **covering** version of Hajós' conjecture. It does not turn the cover into a partition.

The available survey text gives no construction and ends without the cited bibliography. No original proof of this odd-cover theorem was located in the searched local records. Consequently no claim is made here that Fan's particular construction has bounded total excess, matching repeated-edge support, or a useful gluing order. Applied componentwise, the quoted theorem gives `o(G)<=r(G)/2`. No cycle-double-cover assertion is used anywhere below.

The audited fractional bound from the supplied notes is not needed to prove (A)–(C). Nor is unsigned circuit-cone normality, TU of a cycle-incidence matrix, or a general binary-matroid rank inequality assumed.

---

## 1. What polygon-edge gluing really delivers

Start with k disjoint polygonal discs, one for each input cycle. Label their vertices and sides by the corresponding original vertices and edges. At each edge e choose one occurrence to survive and pair the remaining `2a_e` occurrences. Glue each pair of sides by the map preserving the two endpoint labels.

After all gluings, split a vertex of the resulting complex into its different link components. The normalized object is a compact surface, possibly disconnected and nonorientable. Its boundary edges are exactly the surviving original edges, one each. Thus every nonempty boundary component maps to a closed **edge-simple trail** in G. The map need not be injective on vertices.

### Lemma 1.1 — one-shot boundary repair

Let Q range over these boundary trails, and let R_Q be the edge subgraph of its image. Put

```
q   = number of nonempty boundary components,
D_Q = sum_{v in V(R_Q)} (d_{R_Q}(v)/2-1),
D   = sum_Q D_Q.
```

Then

```
c(G) <= q+D.                                                 (1.1)
```

**Proof.** Each R_Q is connected and even. Split its closed edge-simple trail at a repeated vertex. Both resulting trails are nonempty and use disjoint edge sets. At the splitting vertex the sum of passage-excesses decreases by one; at every other vertex shared by the two new trails it decreases by another one. Thus each increase of the trail count by one decreases the total excess by at least one. At most D_Q splits are required before all trails have distinct vertices. Since G is simple, a nonempty closed edge-simple trail has neither one nor two edges. The final pieces are genuine simple cycles. Sum over Q. This is the port-sewing repair from `ResearchInterfaces.md`, specialized to cancelled polygon edges. It is not a new uniform estimate on D. ∎

Equivalently,

```
1+D_Q = |E(R_Q)|-|V(R_Q)|+1 = beta(R_Q).
```

At an original vertex v the total charge is

```
D = sum_v [d_G(v)/2 - number of boundary trails using v].      (1.2)
```

The number of original labels is only n, but a single label can contribute to many different boundary trails. Equation (1.2) therefore is not, by itself, an O(n) bound.

### The surface Euler account

Let h be the number of normalized interior vertices, S the number of surface components, and eta their total Euler genus: `2g` for an orientable component of genus g, and the nonorientable genus otherwise. There are m normalized boundary vertices, because the boundary is a disjoint union of circles with m surviving edges. The normalized cell counts are

```
vertices=m+h,     edges=m+A,     faces=k.
```

Consequently

```
chi = k-A+h = 2S-eta-q,
q   = 2S-eta-k+A-h.                                          (1.3)
```

The interior vertices are the circular link components; interval link components are boundary vertices. Splitting links changes the vertex count, not the numbers of polygon faces or paired/unpaired edges, which proves the cell calculation.

If the odd cover is minimum, no normalized surface component can be closed. Such a component would contain a nonempty subset of the input polygons in which every side is paired internally. Every original edge would then occur evenly in that subset, so deleting the subset would leave a smaller odd cover. This also follows from the familiar fact that the cycle vectors in a minimum odd cover are independent over `F_2`.

Neither the absence of closed components nor genus zero controls D. Section 4 has minimum covers for which **every** normalized component is a disc and D is quadratic in n. Thus topological boundary count and original-label repetition are distinct resources.

---

## 2. A complete reservoir can realize any prescribed terminal matching

The following elementary construction is the engine of the new reduction. It opens all terminals simultaneously, rather than closing path packets independently.

### Lemma 2.1 — complete even bipartite factorization

For `p,q>=1`, the graph `K_(2p,2q)` has a partition into `max(p,q)` simple cycles, each of length `4 min(p,q)`.

**Proof.** Swap the sides if necessary so `p<=q`. Split the smaller side into `X_0,X_1`, each indexed by `j=0,...,p-1`, and the larger into `Y_0,Y_1`, each indexed by `Z_q`. For each `i in Z_q` concatenate

```
X_(0,j), Y_(0,i+j), X_(1,j), Y_(1,i+j)       (j=0,...,p-1),    (2.1)
```

and close cyclically. Indices in Y are modulo q. Within either Y class the p indices are distinct; all smaller-side vertices occur once. Hence these are simple cycles.

At `X_(1,j)` the two incident cycle edges go to `Y_(0,i+j)` and `Y_(1,i+j)`. At `X_(0,j)` the successor is `Y_(0,i+j)` and the predecessor is `Y_(1,i+j-1)` for `j>0`, or `Y_(1,i+p-1)` for `j=0`. Varying i uses every possible neighbor once in each class. Thus the q cycles partition all edges. ∎

The degree lower bound proves the count is optimal. This is the four-layer phase construction, with its full edge and simplicity verification included here.

### Lemma 2.2 — prescribed-matching reservoir

Let `|W|=2b`, `|U|=s=2a+1`, with U and W disjoint. Let M be **any** perfect matching of W. The edges of `K_(U,W)` can be partitioned into

* exactly b simple W–W paths, with endpoint matching M; and
* exactly `delta=max(0,a+1-b)` simple cycles.

All internal vertices of these pieces are in `U union W`. In particular the paths need not avoid terminals belonging to other pairs, but each individual path is simple.

**Proof.** Add a temporary root rho to U and apply Lemma 2.1 to

```
K_({rho} union U, W) = K_(2a+2,2b).
```

Exactly b cycles of its partition use rho, since its degree is `2b`. Remove rho from those cycles. They become b simple W–W paths. Every W vertex is an endpoint exactly once, since every root edge was used exactly once. The other `max(a+1,b)-b=delta` cycles avoid rho.

The resulting endpoint pairs form some perfect matching M_0. Relabel W in the entire reservoir construction by any permutation sending M_0 to M. This changes no available edge of the complete bipartite graph, preserves simplicity and edge-disjointness, and gives the required matching. ∎

This is a constructive simultaneous routing theorem, not a claim that arbitrary interfaces can be summarized by a traffic scalar.

---

## 3. The rank-exact odd-reservoir reduction

Let H be a finite simple graph with a specified set `W`, `|W|=2b>=2`, such that

* every vertex of W has degree exactly one in H;
* every vertex in `I=V(H)\W` has even degree in H.

Components of H disjoint from W, including isolated vertices, are allowed. They remain untouched in all constructions. Define

```
J   = H plus a new root rho and all edges rho-w, w in W;
R_s = H plus a new independent set U, |U|=s=2a+1,
      and all edges u-w, u in U, w in W.
```

Both graphs are simple and even. Set `delta=max(0,a+1-b)`.

### Theorem 3.1 — exact integer contraction and expansion

```
c(R_s) = c(J)+delta.                                         (3.1)
```

Moreover:

* any partition of J with N cycles constructs a partition of R_s with exactly `N+delta` cycles;
* any partition of R_s with N cycles constructs a partition of J with at most `N-delta` cycles.

**Expansion.** In a partition of J, exactly b cycles use rho. Delete rho from them to get b simple terminal paths P_i. Their endpoint pairs form a perfect matching of W. No P_i has a W vertex internally, because W vertices have degree one in H. The other cycles lie wholly in H.

Apply Lemma 2.2 to this endpoint matching. Pair each real H-path P_i with its reservoir path Q_i. Their only common vertices are their two endpoints: the internal vertices of P_i lie in I, whereas those of Q_i lie in `U union W`, and P_i contains no other W vertex. Therefore `P_i union Q_i` is **one simple cycle**, not just an Eulerian trail. Retain all root-free old cycles and all delta reservoir-only cycles. This partitions every real and reservoir edge exactly once and increases the count by delta.

**Contraction.** Start instead with any partition of R_s. Let q be the number of its cycles contained in H, and L the number of all other cycles. Every non-H cycle meets U. Restrict it to H. Its nonempty components are vertex-disjoint simple paths with endpoints in W: a closed component would already be the whole original cycle, and no I vertex can be a switching vertex. A W vertex cannot be internal to a restricted path because it has only one H edge.

Over the whole partition there are exactly b such H-paths, since each of the `2b` H-edges incident with W supplies one endpoint. Cap each path through rho and retain the q H-cycles. This is a partition of J with `q+b` cycles.

At any fixed u in U, the `2b` incident edges force exactly b cycles through u, so `L>=b`. At any fixed w in W, degree `s+1=2a+2` forces exactly `a+1` cycles through w. All of them are non-H cycles, so `L>=a+1`. Thus

```
L >= max(b,a+1) = b+delta,
q+b <= q+L-delta.
```

This gives the asserted contraction and proves both bounds in (3.1). Notice the global count: an individual cycle can split into several capped paths, but the **total** is b, and the same partition already paid for at least `b+delta` non-H cycles. There is no separate n-cost for each split. ∎

### Corollary 3.2 — arbitrary port forests are solved exactly

If H is a forest, every cycle of J uses rho. Hence

```
c(J)=c_f(J)=b,
c(R_s)=c_f(R_s)=max(b,a+1).                                  (3.2)
```

For a direct construction, pair the incident edges at every nonterminal vertex of H. Since H is a forest, the resulting edge-simple trails are simple paths, not closed trails; their endpoints are precisely W. Apply Lemma 2.2. The degree lower bounds at U and W prove optimality.

This permits arbitrarily many paths to share their internal vertices in H, and arbitrary terminal matching. It is not restricted to the threaded cactus/path-chain case. Section 4 uses it to merge cancellation residues from all old components at once.

### Theorem 3.3 — exact fractional value

```
c_f(R_s)=c_f(J)+delta.                                      (3.3)
```

**Lower bound.** Restrict a fractional partition of R_s just as in the contraction proof. Let q and L now be the masses of H-contained and other cycles. The total H-path mass is exactly b, because each terminal's unique H-edge has load one. Capping gives a fractional partition of J of mass `q+b`. The degree equations at a fixed u and a fixed w give `L>=b` and `L>=a+1`. Therefore its original mass `q+L` is at least `c_f(J)+delta`.

**Upper bound, `s<=2b-1`.** Take a fractional partition of J. Its root-using cycle mass is b and each w is an endpoint of real H-paths of total mass one. For each such path, with endpoints x,y, independently use all the following simple reservoir paths with a uniform distribution:

* use all s U vertices in a uniformly random order;
* use a uniformly random ordered choice of `s-1` vertices from `W\{x,y}` internally;
* alternate W and U from x to y.

The two real/reservoir paths meet only at x,y, so every lifted object is a simple cycle. For any fixed w, endpoint mass contributes one reservoir incidence. If `b>1`, the other paths have mass `b-1`, and w is internal with probability `(s-1)/(2b-2)`; their total internal-visit mass is `(s-1)/2`. Thus the total reservoir incidence at w is s. By symmetry of the uniform U order, each of its s reservoir edges has load one. For `b=1`, this regime forces `s=1` and the same conclusion is immediate. The mass is unchanged.

**Upper bound, `s>2b-1`.** For every real H-path use all `2b-2` other terminals internally, and a uniformly random ordered choice of `2b-1` U vertices. A terminal has endpoint mass one and internal mass `b-1`, so its total reservoir incidence is `2b-1`. Each U–W edge therefore has load `(2b-1)/s`.

Fill the uniform deficit `(s-2b+1)/s` by a uniform fractional combination of the length-`4b` cycles of `K_(s,2b)`, each using all W vertices and `2b` distinct U vertices. Such cycles exist since `s>=2b+1`. Their edge-symmetric uniform distribution has edge probability `2/s`. The necessary total additional mass is

```
[(s-2b+1)/s] / (2/s) = (s-2b+1)/2 = delta.
```

All edge equations now hold, with cost `c_f(J)+delta`. These are finite distributions, and hence finite fractional partitions. No perfect-matching-polytope assertion has been used. ∎

### 3.4 A signed dual lift checking every cycle

The dual has unrestricted signed edge weights y and constraints `y(C)<=1` for every simple cycle.

Start with any feasible dual y on J. Its root-edge weights can be normalized to any common value alpha without changing any cap cycle weight or the objective: set `y(rho-w)=alpha` and add `old_y(rho-w)-alpha` to the unique H-edge at w. If an H-edge joins two terminals, add both corrections. A cap cycle contains either both of these edges at w or neither. Denote the modified H weights by y_H.

Then every terminal path P in H satisfies

```
y_H(P) <= 1-2 alpha,                                        (3.4)
```

and all H-cycle inequalities remain valid. In R_s keep y_H and give every U–W edge the common weight z, choosing

```
s<=2b-1:   alpha=1/2,            z=1/(2s);
s> 2b-1:   alpha=(2b-1)/(4b),    z=1/(4b).                    (3.5)
```

Consider any cycle C meeting U. Let u be the number of its U vertices and h the number of its H-path components. Its number of W vertices is exactly

```
|V(C) intersect W| = u+h.                                   (3.6)
```

Indeed its `2h` H-path endpoints have one reservoir incidence each and its other W vertices have two; comparing with the `2u` incidences at U proves (3.6).

In the first regime, (3.4) makes the H-path contribution nonpositive, and

```
y(C) <= 2u/(2s) = u/s <= 1.
```

In the second,

```
y(C) <= h/(2b)+2u/(4b) = (h+u)/(2b) <= 1.
```

Pure reservoir cycles are included by taking `h=0`. H-contained cycles retain their old inequality. Thus **every** simple cycle is checked. Summing edge weights gives exactly `old_y(E(J))+delta`, by (3.5). This explicit certificate agrees with (3.3); it does not assume nonnegative leaf-edge prices.

### 3.5 The single rank ledger and an unconditional irreducible-core reduction

Replacing rho by U increases the order by `s-1` and changes no connected component: all H-components meeting W are joined together in both graphs, and the other components are untouched. Therefore

```
r(R_s)-r(J)=s-1,
0<=delta<= (s-1)/2.                                         (3.7)
```

An **eligible reservoir** in an even simple G is an odd independent set U of size at least three, all of whose vertices have the same nonempty neighbor set W, such that every w in W has exactly one neighbor outside U. Necessarily `|W|=2b` is even. Deleting U and adding one new root adjacent to W is precisely the contraction above. It stays simple and even and strictly reduces rank.

Repeat any eligible contractions until a graph K with no eligible reservoir remains. If step i uses `s_i` vertices and costs delta_i, then

```
r(G)-r(K)=sum_i(s_i-1),
c(G)=c(K)+sum_i delta_i,
c_f(G)=c_f(K)+sum_i delta_i,
0<=sum_i delta_i <= (r(G)-r(K))/2.                            (3.8)
```

Every partition of K lifts constructively. No original-vertex account is restarted at each step. In particular:

* for `B>=1/2`, proving `c(K)<=B r(K)` on the irreducible class proves it for every G, with the **same** B;
* for any `C>=0`, proving `c(K)-c_f(K)<=C r(K)` on that class proves the same fractional additive bound for every G, because the gap in (3.8) is exactly preserved;
* an additive odd-cover bound `c(K)<=k+C r(K)` on that class, together with the quoted componentwise Fan theorem, gives `c(G)<=(C+1/2)r(G)` for all G. Thus it also gives an unrestricted additive bound with constant `C+1/2`.

This is a proved reduction to a genuinely restricted graph class, but not a proof that the irreducible graphs are tractable. One must also not infer that the **supplied** odd cover survives contraction at its original cost. Section 5 disproves even an additive charge just to the rank removed in that assertion.

### 3.6 Regularity-preserving inflation and an essential hypothesis

Let v have positive even degree d in an arbitrary even simple graph Q. Subdivision preserves c and c_f: every cycle uses both edges at a new degree-two vertex or neither, giving a bijection with the old simple cycles and their edge constraints. Subdivide the d incident edges once, making d terminal leaves after v is removed. Replace v by `d-1` independent twins adjacent to those d ports. The resulting graph has

```
c(new)=c(Q),    c_f(new)=c_f(Q),
|V(new)|=|V(Q)|+2d-2.                                       (3.9)
```

If Q is d-regular, so is the new graph: each port has `d-1` reservoir neighbors and one old neighbor. This gives a concrete cost-preserving `K_(d-1,d)` vertex gadget at every even degree, with arbitrary external graph. Subdivision accounts for d of the new rank units; the zero-cost reservoir expansion accounts for the other `d-2`.

The leaf-port hypothesis is indispensable. For example, directly replace one vertex of K5 by three independent twins **without subdividing** its four incident edges. The result is `K7` minus the triangle among the three twins. The other four vertices have degree six, so its cycle-partition number is at least three, whereas `c(K5)=2`. With old vertices `0,1,2,3` and twins `4,5,6`, a three-cycle partition is

```
(0,1,2,3),
(0,2,4,1,5,3,6),
(0,4,3,1,6,2,5).
```

Thus a statement dropping the degree-one condition in H is actually false, not just unsupported by the proof.

---

## 4. Minimum odd covers with quadratically expensive disc-by-disc repair

### 4.1 The graph G_t and its specified minimum odd cover

Fix `t>=1`, put `h=2t`, and use the disjoint vertex sets

```
U = {u_1,...,u_(h-1)},
W = {w_(j,a): j in Z_h, a in {0,1,2}},
{A_i,B_i: 0<=i<t}.
```

Include all U–W edges. For each i add

```
A_i B_i,
A_i w_(2i+1,a),   B_i w_(2i,a)       (a=0,1,2).              (4.1)
```

The graph is simple and connected, with

```
|V|=(2t-1)+6t+2t=10t-1,
|E|=(2t-1)6t+7t=12t^2+t,
d(u)=6t,    d(w)=2t,    d(A_i)=d(B_i)=4.                    (4.2)
```

For a fixed i, set `v_0=A_i`, `v_h=B_i`, and `v_j=u_j` for `1<=j<h`. For every `a in {0,1,2}`, let C_(i,a) traverse

```
v_0, w_(1+2i,a), v_1, w_(2+2i,a), ...,
v_(h-1), w_(h+2i,a), v_h,
```

and close by `B_i A_i`. All W indices are modulo h. These are simple cycles of length `2h+1=4t+1`.

For fixed j and a, the neighbors of u_j used as i varies have indices

```
j+2i,       j+1+2i       (0<=i<t).
```

The first list has one parity and the second the other, so together they are all of `Z_h`, exactly once. Thus every U–W edge belongs to exactly one displayed cycle. Every edge from an endpoint A_i or B_i to W also belongs to exactly one. The only repetitions are

```
mu_(A_i B_i)=3.                                             (4.3)
```

Hence the `3t` displayed cycles are an odd cover, with a matching of t tripled edges and `A=t` cancellation pairs. At any u, degree `6t` forces every cycle cover, and hence every odd cover, to have at least `3t` members. Therefore this cover is **minimum**:

```
o(G_t)=3t.                                                  (4.4)
```

It is also within Fan's numerical bound, since `3t<=floor((10t-2)/2)=5t-1`.

### 4.2 Exact obstruction even after optimal within-component coordination

Define the **edge-overlap graph** of a supplied cover by joining two cycle occurrences when they share an original edge. Each original edge belongs entirely to one component of this graph. Consequently the original graph is partitioned into the edge sets of these components, each itself even.

For the displayed cover of G_t, those components are exactly the t triples

```
{C_(i,0),C_(i,1),C_(i,2)}.
```

Let L_i be the edge union of one triple. It is a chain of h segments, with three internally disjoint length-two branches per segment, together with the closing edge `A_i B_i`.

Every simple cycle of L_i is either:

1. a pair of branches in one segment; or
2. the closing edge and one branch from every segment.

Without the closing edge the junctions separate the chain, so a cycle stays in one segment. A simple cycle using the closing edge must traverse the chain once. This proves the classification.

In any partition of L_i, exactly one cycle uses the closing edge. It consumes one branch in each segment. The two remaining branches in each segment form one local four-cycle. Thus **every** partition has exactly

```
c(L_i)=h+1=2t+1.                                            (4.5)
```

It follows that every procedure which ultimately partitions each original edge-overlap component separately has cost exactly

```
sum_i c(L_i)=t(2t+1).                                       (4.6)
```

This lower bound permits arbitrary operations, arbitrary temporary count increases, new cycles outside the old support, and globally optimal choices **within** each L_i. It is not a bounded-exchange or monotonic-cactusization obstruction.

For any constant C,

```
t(2t+1) > 3t+C(10t-2)
```

for all sufficiently large t. Thus no such component-preserving cancellation method can prove the desired bound from every minimum odd cover.

### 4.3 The polygon surfaces are all discs; the collision debt is exact

At `A_i B_i` one must pair two of its three occurrences and leave the third. The selected pair glues two discs along one side and is again a disc; the third polygon is a separate disc. There are no other paired edges. This holds for **all** `3^t` choices of survivors. Therefore

```
S=q=2t,    eta=0,    h_interior=0,    A=t.                    (4.7)
```

The nontrivial boundary trail in layer i consists of two forward branch paths, one in each direction. It visits every internal junction `u_1,...,u_(h-1)` twice and every other used vertex once. Its repeated-vertex excess is exactly `h-1`. Its image is a chain of h four-cycle blocks, so repairing it separately really requires h simple cycles. The survivor is already simple. Summing gives

```
D=t(h-1)=t(2t-1),
q+D=t(h+1)=t(2t+1).                                         (4.8)
```

The repair bound (1.1) is therefore sharp for these frozen boundaries. Each shared original junction is charged once by each of t different trails. Neither a planar normalized surface nor a forest-shaped face gluing prevents this.

This is stronger than saying that one local cancellation can increase the count. It proves that even optimal full repair within the original edge-overlap components has an unbounded count/rank ratio, despite minimum cover cardinality and linear total excess.

### 4.4 A globally coordinated optimal partition

Keep the t input cycles `C_(i,0)`. All their edges are disjoint. The remaining graph has

* complete bipartite core between U and `{w_(j,1),w_(j,2):j in Z_h}`;
* for each j, the two-edge path `w_(j,1)-z_j-w_(j,2)`, where

  ```
  z_(2i)=B_i,       z_(2i+1)=A_i.
  ```

Its terminal graph is a forest of `2t` two-edge paths. Corollary 3.2, with `|U|=2t-1` and `|W_remaining|=4t`, partitions it into exactly `2t` simple cycles, simultaneously across all layers.

For complete explicitness, for each `j in Z_(2t)` concatenate the following four-vertex blocks for `ell=0,...,t-1`:

```
x_ell, w_(j+ell,1), u_(2ell+1), w_(j+ell-t+1,2),             (4.9)
x_0=z_j,           x_ell=u_(2ell) for ell>0.
```

Close cyclically. These cycles have length `4t`. Every U vertex occurs exactly once, the W indices within either branch class are t distinct residues, and z_j is private to that cycle. They are genuinely simple. The first and last W vertices are `w_(j,1)` and `w_(j,2)`, so the two z_j edges are precisely the required terminal path.

For any fixed U vertex, varying j uses every neighbor in each of the two W classes once; the predecessor/successor offsets in (4.9) are bijections of `Z_(2t)`. Thus the `2t` cycles cover the entire residual exactly once. Together with the retained input cycles they give

```
c(G_t)<=t+2t=3t.
```

The degree bound from (4.2) proves equality, and the same degree equation proves `c_f(G_t)=3t`. This construction reuses no edge, creates no new edge, and does not split a non-simple projected trail and call it a cycle. It changes the allocation of **real edges across different old gluing components**.

In particular, G_t is emphatically **not** a counterexample to unrestricted rounding: it has `c=o=k`. It even has a different minimum odd cover which is already a partition. The conclusion is that minimum cardinality alone does not make a specified odd cover safe for frozen polygon repair; a specially chosen Fan construction could still avoid this example's bad choice.

---

## 5. Exact cycle-cost reduction can destroy odd-cover cheapness

This section both audits the scope of Theorem 3.1 and supplies a sharp necessary asymptotic rounding constant.

### 5.1 Construction

Fix `b>=2`, set `k=2b-1`, and form b disjoint terminal gadgets in H. Gadget i has vertices

```
w_i^-, x_i, y_i, w_i^+,
z_(i,j)       (0<=j<k),
```

and edges

```
w_i^- x_i,       y_i w_i^+,
x_i z_(i,j),     z_(i,j) y_i       (0<=j<k).                 (5.1)
```

Let `W={w_i^-,w_i^+:0<=i<b}`. These are leaves in H. The poles x_i,y_i have degree `k+1=2b`; every z has degree two. Let J_b be the one-root cap of H, and let R_b use an independent complete reservoir

```
U={u_0,...,u_(k-1)},        U complete to W.
```

The graphs are simple, connected and even. Their sizes are

```
|V(H)|=b(k+4)=2b^2+3b,
|V(R_b)|=2b^2+5b-1,
|E(R_b)|=8b^2-2b,
r(R_b)-r(J_b)=k-1=2b-2.                                    (5.2)
```

### 5.2 Exact cap and cycle-partition values

The cap J_b has b articulation blocks sharing only rho. In each block, between x_i and y_i, there are k length-two branches and one return path through `w_i^-,rho,w_i^+`. Pair these `k+1=2b` paths to obtain b cycles. Degree `2b` at a pole forces at least b cycles in any cover of that block. All simple cap cycles lie in one block, so

```
o(J_b)=c(J_b)=c_f(J_b)=b^2.                                 (5.3)
```

For the fractional lower bound the same degree equation gives mass at least b in each block, so no integrality assertion is involved.

Here `s=2b-1` and `a+1=b`, so Theorems 3.1 and 3.3 have `delta=0`:

```
c(R_b)=c_f(R_b)=b^2.                                        (5.4)
```

An explicit partition is obtained by pairing `k-1` branches locally in each gadget, leaving one terminal path per gadget, and then applying Lemma 2.2. It consists of `b(b-1)` local four-cycles and b globally routed cycles of length `4b+2`.

### 5.3 A minimum odd cover of only 2b-1 cycles

For each `j in Z_k`, traverse the following six-vertex blocks for `i=0,...,b-1`, and close cyclically:

```
w_i^-, x_i, z_(i,j), y_i, w_i^+, u_(j+i).                    (5.5)
```

U indices are modulo k. These are simple cycles of length `6b`: the H vertices are private to their gadgets and the b used U indices are distinct because `b<=k`.

Each branch edge in (5.1) is covered exactly once. Each of the `2b` port-arm edges `w_i^-x_i` and `y_iw_i^+` is covered k times. For a fixed connector pair `w_i^+,w_(i+1)^-`, varying j uses every U vertex once; hence every reservoir edge is covered exactly once. This is therefore a k-cycle odd cover, with repeated-edge support a **matching**. Its total number of cancelled pairs is `A=2b(b-1)=O(r(R_b))`.

It is minimum. A cycle using either edge at a degree-two vertex z must traverse that whole branch. A local simple cycle in H uses two branches of one gadget. Any other simple cycle uses at most one branch in each gadget: using two would already close the cycle between x_i and y_i and leave no passage to the rest of the graph. Thus every simple cycle uses at most b branches in total, since `b>=2`. There are `bk` branches to cover. Assign total nonnegative weight `1/b` to each branch path, split equally between its two edges, and zero elsewhere. Every cycle has weight at most one, and total weight is k. Every ordinary cover, hence every odd cover, requires at least k cycles. Consequently

```
o(R_b)=k=2b-1.                                              (5.6)
```

The same certificate shows that the ordinary fractional covering LP (edge loads at least one) has value k; this is **not** the equality-constrained fractional partition value in (5.4).

### 5.4 A signed all-cycle certificate and the precise odd-cover discrepancy

Give weights on R_b as follows:

```
branch edge x_i z_(i,j) or z_(i,j)y_i:       1/4;
port-arm edge w_i^-x_i or y_iw_i^+:       -(b-1)/(4b);
reservoir edge:                            1/(4b).           (5.7)
```

A local two-branch cycle has weight one. Any nonlocal cycle has h terminal H-paths, each of weight

```
1/2 - (b-1)/(2b) = 1/(2b),
```

and u reservoir vertices, contributing another `u/(2b)`. By (3.6), `h+u` is the number of its W vertices and is at most `2b`. Hence its weight is at most one. This proves feasibility for **all** simple cycles.

The total objective is

```
b(2b-1)/2  - (b-1)/2  + (2b-1)/2  = b^2.                  (5.8)
```

Every input cycle in (5.5) is tight: it has `h=u=b`. The total weight of the repeated matching F is

```
y(F)=-(b-1)/2.
```

Since its multiplicity is k, the odd-cover sum is

```
sum_j y(C_j)=y(E)+(k-1)y(F)
            = b^2-(b-1)^2
            =2b-1=k.                                       (5.9)
```

Indeed in **every** optimal partition dual on R_b the displayed odd cover forces

```
y(F) <= -(b-1)/2,
```

because `y(E)=b^2` and each of its k cycles has weight at most one. Thus the negative matching price is unavoidable in aggregate. This is a graphic unit-vector example, not an unsigned cone hole at a nonunit right-hand side.

### 5.5 What the contraction can and cannot charge

Equations (5.3) and (5.6) give

```
o(J_b)-o(R_b)=(b-1)^2,
r(R_b)-r(J_b)=2b-2.                                        (5.10)
```

Their ratio is `(b-1)/2`, which is unbounded. Even if one is allowed to choose the **best** odd cover after contraction, no estimate

```
new odd-cover cost <= old odd-cover cost
                     + C*(rank removed in this contraction)
```

holds for all these instances. This is not merely a failure of transporting the particular list in (5.5). Both odd-cover minima were proved.

On the other hand, the cycle and fractional costs do not change at all. Hence Theorem 3.1 remains a valid exact graph reduction, but a proof starting from a cheap odd cover cannot attach its k-term to every such local reduction without an additional global budget.

Finally,

```
(c(R_b)-o(R_b))/r(R_b)
  = (b-1)^2/(2b^2+5b-2)  -->  1/2.                          (5.11)
```

Thus any universal additive constant must be at least `1/2`. These values remain linear in the **original** rank. They are not an unbounded-ratio counterexample to the requested global inequality, and do not prove that `C=1/2` is sufficient.

---

## 6. Consequences for an unrestricted cancellation proof

The positive theorem and the two obstructions separate three operations which must not be conflated:

1. **Pair equal edge copies and count normalized boundary components.** This is governed by (1.3). In G_t this part is as simple as possible: all components are discs.
2. **Repair repeated original vertices.** If the old edge-overlap components are frozen, G_t forces quadratic cost, even with globally optimal repair inside every component. The successful repair instead opens all their terminal paths and mixes their real edges through one reservoir. Lemma 2.2 and Theorem 3.1 explain exactly why this mixing produces simple cycles.
3. **Maintain the odd-cover objective through a rank reduction.** The reservoir contraction has a perfect ledger for c and c_f, but R_b shows that minimum odd-cover cardinality itself can jump by much more than the local rank decrease.

The unconditional progress is the contraction/reconstruction rule (3.1), its fractional and signed extensions, and the telescoping reduction (3.8). For forest terminal graphs it gives exact globally coordinated cancellation, including an explicit optimum in the quadratic disc-gluing obstruction. This goes beyond rephrasing the target as a minimization over all pairings or over all output partitions.

What is still missing is a theorem handling arbitrary irreducible cores, or a stronger controlled construction of Fan's odd cover. In particular, none of the following has been proved here:

* a universal choice of side pairings whose boundaries can be repaired for `k+O(r)` without cross-component reconnection;
* a universal supply of eligible reservoirs, or a linear bound on what remains after all eligible contractions;
* a rank-cheap transport of a minimum odd cover through the contraction sequence;
* any structural property of the particular cover furnished by Fan's proof beyond the quoted cardinality bound.

The examples disprove some stronger sufficient claims, but do not disprove a fully global cancellation theorem. The generic binary-matroid obstruction, the nonunit cone hole, and a false CDC assertion are not used as substitutes for that missing graphic theorem.

---

## 7. Verification and protected files

The checker below uses Python 3, NetworkX, exact integer edge sets and `fractions.Fraction`. It uses no LP/MILP solver, numerical tolerances, or random tests. All infinite-family conclusions rely on the proofs above, not on the finite checks.

The completed run checked:

| Check | Exact scope |
|---|---:|
| Complete even bipartite factorization | 64 pairs `1<=p,q<=8` |
| Prescribed-matching reservoir routing | 294 matching/size choices, both sides of the threshold |
| Exhaustive terminal matchings | All matchings on 2, 4, 6, 8 terminals at `s=1,3,5,7`: 496 checks |
| G_t families | 19 sizes, `t=1,...,16,20,32,64` |
| All pair choices within their layers | 756 choices; cactus blocks and exact collision debt checked |
| R_b / J_b families | 12 sizes, `b=2,...,12,20` |
| Full R_2 cycle enumeration | 318 cycles; both signed partition and nonnegative cover inequalities checked |
| All even atlas graphs with an edge, through order 7 | 77 graphs, 465 marked nonisolated vertices |
| Cap expansions from those marked vertices | 1,860; every output cycle and edge multiplicity checked |
| Contraction of constructed and greedy partitions | 3,720; cap partition and global count inequality checked |
| One-third K5 fractional support lifts | `s=1,3,5,7`, up to 7,560 labelled fractional cycles |
| Nonmatching fractional terminal data | Two odd triangles of weight `1/2` on six terminals; `s=1,3` |
| Full-cycle signed dual lift tests on additional caps | 3,525 inequalities |
| H-edges joining two terminals | 6 integer/fractional cases; 1,162 full-cycle dual checks, including both endpoint corrections |
| Missing-leaf-hypothesis counterexample | Explicit 3-cycle partition and degree lower bound |

At `t=64`, the graph has 639 vertices and a minimum 192-cycle odd cover; frozen edge-overlap-component repair requires 8,256 cycles, while the explicit global partition has 192. At `b=20`, the second family has 899 vertices and `c=c_f=400`, with minimum odd-cover count 39; its contraction removes 38 rank units but raises that minimum to 400.

All 30 pre-existing `Submission` files were checked byte-for-byte against hashes taken before this work. In particular:

```
Submission/Spec.lean SHA-256:
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

To reproduce, extract the unique Python code block below to a temporary file and run it with `PYTHONDONTWRITEBYTECODE=1 PYTHONHASHSEED=0 python3`. The script writes only its JSON result to standard output and verifies the specification hash.

### Embedded exact checker

```python
#!/usr/bin/env python3
"""Exact checks for ResearchOddCancellation.md; no solver, no protected-file edits."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import factorial, perm
from pathlib import Path
from hashlib import sha256
import json
import networkx as nx


def key(x): return repr(x)
def edge(x,y):
    assert x != y
    return tuple(sorted((x,y), key=key))
def edges(G): return frozenset(edge(x,y) for x,y in G.edges())
def ce(C):
    C=tuple(C)
    assert len(C)>=3 and len(set(C))==len(C), C
    return frozenset(edge(x,y) for x,y in zip(C,C[1:]+C[:1]))
def pe(P):
    P=tuple(P)
    assert len(P)>=2 and len(set(P))==len(P), P
    return frozenset(edge(x,y) for x,y in zip(P,P[1:]))
def graph(es, vs=()):
    G=nx.Graph();G.add_nodes_from(vs);G.add_edges_from(es);return G

def partition(G, D, P=()):
    used=Counter(e for C in D for e in ce(C))
    for p in P:used.update(pe(p))
    assert used==Counter({e:1 for e in edges(G)})

def oddcover(G,D):
    used=Counter(e for C in D for e in ce(C))
    assert set(used)==set(edges(G)) and all(v%2 for v in used.values())
    return used

def fractional(G, D, value):
    used=Counter();mass=F(0)
    for C,z in D:
        assert z>0
        for e in ce(C):used[e]+=z
        mass+=z
    assert used==Counter({e:F(1) for e in edges(G)})
    assert mass==value
    return len(D)

def all_cycles(G):
    vs=sorted(G,key=key);rank={v:i for i,v in enumerate(vs)}
    for s in vs:
        def dfs(P,seen):
            for v in sorted(G[P[-1]],key=key):
                if v==s:
                    if len(P)>=3 and rank[P[1]]<rank[P[-1]]:yield tuple(P)
                elif rank[v]>rank[s] and v not in seen:
                    yield from dfs(P+[v],seen|{v})
        yield from dfs([s],{s})

def greedy_partition(G):
    R=G.copy();D=[]
    while R.number_of_edges():
        C=nx.cycle_basis(R)[0];D.append(tuple(C));R.remove_edges_from(ce(C))
    partition(G,D);return D


def even_bipartite(X,Y):
    """max(|X|,|Y|)/2 simple cycles partition K_(X,Y)."""
    assert len(X)>0 and len(Y)>0 and len(X)%2==len(Y)%2==0
    if len(X)>len(Y):X,Y=Y,X
    p,q=len(X)//2,len(Y)//2
    X0,X1=X[:p],X[p:];Y0,Y1=Y[:q],Y[q:]
    D=[tuple(z for j in range(p) for z in
             (X0[j],Y0[(i+j)%q],X1[j],Y1[(i+j)%q])) for i in range(q)]
    partition(graph(product(X,Y)),D)
    return D


def reservoir_routes(U,W,M):
    """b paths with prescribed matching M, plus delta reservoir-only cycles."""
    rho=('temporary-root',)
    assert rho not in U+W and len(U)%2==1 and len(W)%2==0
    assert Counter(x for pair in M for x in pair)==Counter(W)
    D=even_bipartite([rho]+list(U),list(W));paths=[];extra=[]
    for C in D:
        if rho in C:
            i=C.index(rho);paths.append(C[i+1:]+C[:i])
        else:extra.append(C)
    assert len(paths)==len(M)==len(W)//2
    relabel={}
    for P,(x,y) in zip(paths,M):relabel[P[0]]=x;relabel[P[-1]]=y
    assert set(relabel)==set(W) and set(relabel.values())==set(W)
    paths=[tuple(relabel.get(v,v) for v in P) for P in paths]
    extra=[tuple(relabel.get(v,v) for v in C) for C in extra]
    partition(graph(product(U,W)),extra,paths)
    assert len(extra)==max(0,(len(U)+1-len(W))//2)
    return paths,extra


def cap_split(J,D,rho):
    paths=[];internal=[]
    for C in D:
        if rho in C:
            i=C.index(rho);paths.append(C[i+1:]+C[:i])
        else:internal.append(C)
    H=J.copy();H.remove_node(rho)
    partition(H,internal,paths)
    assert len(paths)==J.degree(rho)//2
    return H,paths,internal


def expand_partition(J,D,rho,s):
    assert s>0 and s%2
    W=list(J[rho]);assert all(J.degree(w)==2 for w in W)
    H,P,internal=cap_split(J,D,rho)
    U=[('reservoir',i) for i in range(s)]
    assert not (set(U)&set(H))
    Q,extra=reservoir_routes(U,W,[(p[0],p[-1]) for p in P])
    out=list(internal)+extra
    for p,q in zip(P,Q):
        assert (p[0],p[-1])==(q[0],q[-1])
        out.append(tuple(p)+tuple(reversed(q[1:-1])))
    R=H.copy();R.add_edges_from(product(U,W))
    partition(R,out)
    delta=max(0,(s+1-len(W))//2)
    assert len(out)==len(D)+delta
    assert len(R)-nx.number_connected_components(R) == \
           len(J)-nx.number_connected_components(J)+s-1
    return R,out,U,W,H


def collapse_partition(R,D,U,W,H,rho):
    h_edges=edges(H);result=[];q=L=0;path_count=0
    for C in D:
        if ce(C)<=h_edges:
            result.append(C);q+=1;continue
        L+=1
        T=graph(ce(C)&h_edges)
        for vs in nx.connected_components(T):
            Q=T.subgraph(vs)
            ends=[v for v in Q if Q.degree(v)==1]
            assert len(ends)==2 and set(ends)<=set(W)
            P=tuple(nx.shortest_path(Q,*ends))
            assert pe(P)==edges(Q) and not (set(P[1:-1])&set(W))
            result.append((rho,)+P);path_count+=1
    J=H.copy();J.add_edges_from((rho,w) for w in W)
    partition(J,result)
    b=len(W)//2;p=(len(U)+1)//2
    assert path_count==b and L>=max(b,p)
    assert len(result)<=len(D)-max(0,p-b)
    return result


def subdivided_cap(J,D,rho):
    W={v:('port',v) for v in J[rho]}
    H=J.copy()
    for v,w in W.items():
        H.remove_edge(rho,v);H.add_edge(rho,w);H.add_edge(w,v)
    out=[]
    for C in D:
        CC=[]
        for x,y in zip(C,C[1:]+C[:1]):
            CC.append(x)
            if x==rho:CC.append(W[y])
            elif y==rho:CC.append(W[x])
        out.append(tuple(CC))
    partition(H,out)
    return H,out


def frozen_family(t):
    h=2*t
    u=lambda j:('u',j)
    w=lambda j,a:('w',j%h,a)
    A=lambda i:('a',i)
    B=lambda i:('b',i)
    layers=[];cover=[]
    for i in range(t):
        Ds=[]
        for a in range(3):
            C=[A(i)]
            for j in range(1,h+1):
                C.append(w(j+2*i,a));C.append(B(i) if j==h else u(j))
            Ds.append(tuple(C));cover.append(tuple(C))
        layers.append(graph(set().union(*(ce(C) for C in Ds))))
    es=[e for L in layers for e in edges(L)]
    assert len(es)==len(set(es))
    G=graph(es);loads=oddcover(G,cover)
    assert len(G)==10*t-1 and G.number_of_edges()==12*t*t+t
    assert max(dict(G.degree()).values())==6*t
    assert {e for e,m in loads.items() if m>1}=={edge(A(i),B(i)) for i in range(t)}
    assert all(m in (1,3) for m in loads.values())
    assert nx.is_matching(G,[e for e,m in loads.items() if m==3])
    D=[cover[3*i] for i in range(t)]
    for i in range(h):
        z=B(i//2) if i%2==0 else A(i//2)
        C=[]
        for j in range(t):
            C.extend((z if j==0 else u(2*j),w(i+j,1),u(2*j+1),w(i+j-t+1,2)))
        D.append(tuple(C))
    partition(G,D);assert len(D)==3*t
    checks=0
    for i,L in enumerate(layers):
        for a,b in combinations(range(3),2):
            paired=ce(cover[3*i+a])^ce(cover[3*i+b])
            R=graph(paired)
            blocks=list(nx.biconnected_component_edges(R))
            assert len(blocks)==h and all(len(Q)==4 for Q in blocks)
            assert R.number_of_edges()-R.number_of_nodes()+1==h
            DQ=sum(d//2-1 for _,d in R.degree())
            assert DQ==h-1
            checks+=1
    return dict(t=t,n=len(G),k=3*t,c=3*t,pairs=t,boundary_count=2*t,
                collision_debt=t*(2*t-1),frozen_min=t*(2*t+1),pairing_checks=checks)


def compression_family(b):
    assert b>=2
    k=2*b-1;rho=('rho',)
    xm=lambda i:('x',i)
    yp=lambda i:('y',i)
    w0=lambda i:('w-',i)
    w1=lambda i:('w+',i)
    z=lambda i,j:('z',i,j)
    U=[('reservoir',j) for j in range(k)]
    H=nx.Graph();W=[];capD=[]
    for i in range(b):
        W.extend((w0(i),w1(i)))
        H.add_edges_from([(w0(i),xm(i)),(yp(i),w1(i))])
        for j in range(k):H.add_edges_from([(xm(i),z(i,j)),(z(i,j),yp(i))])
        for j in range(b-1):capD.append((xm(i),z(i,2*j),yp(i),z(i,2*j+1)))
        capD.append((rho,w0(i),xm(i),z(i,k-1),yp(i),w1(i)))
    J=H.copy();J.add_edges_from((rho,w) for w in W);partition(J,capD)
    R,D,U2,W2,H2=expand_partition(J,capD,rho,k)
    assert U2==U and edges(H2)==edges(H)
    cover=[]
    for j in range(k):
        C=[]
        for i in range(b):C.extend((w0(i),xm(i),z(i,j),yp(i),w1(i),U[(j+i)%k]))
        cover.append(tuple(C))
    loads=oddcover(R,cover)
    repeated={edge(w0(i),xm(i)) for i in range(b)}|{edge(w1(i),yp(i)) for i in range(b)}
    assert {e for e,v in loads.items() if v>1}==repeated
    assert all(loads[e]==k for e in repeated) and nx.is_matching(R,repeated)
    y={e:F(1,4*b) for e in edges(R)}
    for i in range(b):
        for j in range(k):
            y[edge(xm(i),z(i,j))]=F(1,4);y[edge(z(i,j),yp(i))]=F(1,4)
        y[edge(w0(i),xm(i))]=y[edge(w1(i),yp(i))]=-F(b-1,4*b)
    assert sum(y.values(),F(0))==b*b
    assert all(sum((y[e] for e in ce(C)),F(0))==1 for C in D+cover)
    assert len(R)==2*b*b+5*b-1 and R.number_of_edges()==8*b*b-2*b
    assert len(D)==b*b and len(cover)==k
    assert len(R)-len(J)==2*b-2
    positive={e:F(0) for e in edges(R)}
    for i in range(b):
        for j in range(k):
            positive[edge(xm(i),z(i,j))]=positive[edge(z(i,j),yp(i))]=F(1,2*b)
    assert sum(positive.values(),F(0))==k
    blocks=[J.subgraph(vs) for vs in nx.biconnected_components(J)]
    assert len(blocks)==b and all(max(dict(B.degree()).values())==2*b for B in blocks)
    enumerated=0
    if b==2:
        for C in all_cycles(R):
            assert sum((y[e] for e in ce(C)),F(0))<=1
            assert sum((positive[e] for e in ce(C)),F(0))<=1
            enumerated+=1
    return dict(b=b,n=len(R),k=k,c=b*b,cap_odd_min=b*b,
                contracted_rank=2*b-2,cover_count_increase=(b-1)**2,
                all_cycles_dual_checked=enumerated)


def fractional_expand(J,weighted,rho,s):
    W=list(J[rho]);b=len(W)//2
    assert all(J.degree(w)==2 for w in W)
    H=J.copy();H.remove_node(rho);U=[('fu',i) for i in range(s)]
    R=H.copy();R.add_edges_from(product(U,W));out=[]
    for C,lam in weighted:
        if rho not in C:out.append((C,lam));continue
        r=C.index(rho);P=C[r+1:]+C[:r];x,y=P[0],P[-1]
        length=min(s,2*b-1);others=[w for w in W if w not in (x,y)]
        N=perm(s,length)*perm(2*b-2,length-1)
        for us in permutations(U,length):
            for ws in permutations(others,length-1):
                Q=[x]
                for j,u in enumerate(us):
                    Q.append(u);Q.append(ws[j] if j<length-1 else y)
                out.append((P+tuple(reversed(Q[1:-1])),lam/N))
    delta=max(0,(s+1)//2-b)
    if delta:
        N=perm(s,2*b)*factorial(2*b-1)
        for us in permutations(U,2*b):
            for ws0 in permutations(W[1:]):
                ws=(W[0],)+ws0
                C=tuple(z for j in range(2*b) for z in (ws[j],us[j]))
                out.append((C,F(delta,N)))
    value=sum((z for _,z in weighted),F(0))+delta
    fractional(R,out,value)
    return dict(s=s,b=b,cycles=len(out),value=str(value))


def dual_expand(J,y,rho,s):
    W=list(J[rho]);b=len(W)//2
    alpha=F(1,2) if s<=2*b-1 else F(2*b-1,4*b)
    z=F(1,2*s) if s<=2*b-1 else F(1,4*b)
    H=J.copy();H.remove_node(rho)
    yy={e:y[e] for e in edges(H)}
    for w in W:
        ns=list(H[w]);assert len(ns)==1
        yy[edge(w,ns[0])]+=y[edge(rho,w)]-alpha
    U=[('du',i) for i in range(s)]
    R=H.copy();R.add_edges_from(product(U,W))
    yy.update({edge(u,w):z for u in U for w in W})
    assert sum(yy.values(),F(0))==sum(y.values(),F(0))+max(0,(s+1)//2-b)
    checked=0
    for C in all_cycles(R):
        assert sum((yy[e] for e in ce(C)),F(0))<=1
        checked+=1
    return checked


def perfect_matchings(W):
    if not W:
        yield [];return
    x=W[0]
    for i in range(1,len(W)):
        y=W[i];rest=W[1:i]+W[i+1:]
        for M in perfect_matchings(rest):yield [(x,y)]+M


def main():
    result={}
    nonleaf=nx.complete_graph(4);nonleaf.add_edges_from(product(range(4,7),range(4)))
    partition(nonleaf,[(0,1,2,3),(0,2,4,1,5,3,6),(0,4,3,1,6,2,5)])
    assert max(dict(nonleaf.degree()).values())//2==3
    result['nonleaf_port_counterexample_c']=3
    bip=0
    for p in range(1,9):
        for q in range(1,9):
            even_bipartite([('x',i) for i in range(2*p)], [('y',i) for i in range(2*q)])
            bip+=1
    result['complete_bipartite_parameters']=bip
    routing=0
    for b in range(1,7):
        W=[('w',i) for i in range(2*b)]
        for s in range(1,14,2):
            for shift in range(2*b):
                order=W[shift:]+W[:shift]
                M=list(zip(order[::2],order[1::2]))
                reservoir_routes([('u',i) for i in range(s)],W,M);routing+=1
    result['prescribed_matching_route_checks']=routing
    exhaustive=0
    for b in range(1,5):
        W=[('w',i) for i in range(2*b)]
        for M in perfect_matchings(W):
            for s in (1,3,5,7):
                reservoir_routes([('u',i) for i in range(s)],W,M);exhaustive+=1
    result['exhaustive_terminal_matching_checks']=exhaustive
    result['frozen_families']=[frozen_family(t) for t in list(range(1,17))+[20,32,64]]
    result['compression_families']=[compression_family(b) for b in list(range(2,13))+[20]]
    atlas=roots=expansions=collapses=0
    for J in nx.graph_atlas_g():
        if not len(J) or any(d%2 for _,d in J.degree()) or not J.number_of_edges():continue
        atlas+=1;D=greedy_partition(J)
        for rho in J:
            if not J.degree(rho):continue
            roots+=1;K,E=subdivided_cap(J,D,rho)
            for s in (1,3,5,7):
                R,RR,U,W,H=expand_partition(K,E,rho,s);expansions+=1
                collapse_partition(R,RR,U,W,H,rho);collapses+=1
                collapse_partition(R,greedy_partition(R),U,W,H,rho);collapses+=1
    result['atlas']={'graphs':atlas,'marked_vertices':roots,'expansions':expansions,'partition_collapses':collapses}
    # Basic optimal one-third K5 support (individual paths remain identifiable).
    J=nx.complete_graph(5);rho=0
    D=[tuple(map(int,S)) for S in ['01234','01342','01423','02143','02314','03124']]
    K,E=subdivided_cap(J,greedy_partition(J),rho)
    W={v:('port',v) for v in J[rho]};DD=[]
    for C in D:
        CC=[]
        for x,y in zip(C,C[1:]+C[:1]):
            CC.append(x)
            if x==rho:CC.append(W[y])
            elif y==rho:CC.append(W[x])
        DD.append((tuple(CC),F(1,3)))
    fractional(K,DD,F(2))
    result['fractional_K5']=[fractional_expand(K,DD,rho,s) for s in (1,3,5,7)]
    # A degree-feasible endpoint distribution NOT in the perfect-matching polytope.
    rho=('r',);x=('x',);W=[('w',i) for i in range(6)]
    J=graph(list(product([rho,x],W)))
    D=[((rho,W[i],x,W[j]),F(1,2)) for tri in [(0,1,2),(3,4,5)] for i,j in combinations(tri,2)]
    fractional(J,D,F(3))
    result['nonmatching_fractional']=[fractional_expand(J,D,rho,s) for s in (1,3)]
    result['all_cycle_dual_checks']=sum(dual_expand(J,{e:F(1,4) for e in edges(J)},rho,s) for s in (1,3))
    # Also exercise the large-reservoir all-cycle dual, with negative leaf prices.
    W=[('w',i) for i in range(4)];J=graph(list(product([rho,x],W)))
    result['all_cycle_dual_checks']+=sum(dual_expand(J,{e:F(1,4) for e in edges(J)},rho,s) for s in (1,3,5))
    # Leaf-leaf H edges: normalization must add BOTH terminal corrections.
    leaf_cases=[];leaf_duals=0
    for b in (1,2):
        W=[('w',i) for i in range(2*b)];rho=('r',)
        D=[(rho,W[2*i],W[2*i+1]) for i in range(b)]
        J=graph(set().union(*(ce(C) for C in D)))
        for s in (1,3,5):
            R,DD,U,WW,H=expand_partition(J,D,rho,s)
            collapse_partition(R,greedy_partition(R),U,WW,H,rho)
            leaf_cases.append(fractional_expand(J,[(C,F(1)) for C in D],rho,s))
            leaf_duals+=dual_expand(J,{e:F(1,3) for e in edges(J)},rho,s)
    result['leaf_leaf_terminal_cases']=leaf_cases
    result['leaf_leaf_all_cycle_duals']=leaf_duals
    spec=Path('/workspace/leanproject/Submission/Spec.lean')
    result['spec_sha256']=sha256(spec.read_bytes()).hexdigest()
    assert result['spec_sha256']=='429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde'
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
```
