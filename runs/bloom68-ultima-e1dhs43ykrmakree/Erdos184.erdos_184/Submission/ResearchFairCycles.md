# Weight-fair cycle partitions: exact multi-cut constraints and globally fair constructions

## Status — the universal question is still unresolved here

Let

```
W(c): every finite simple 3-connected even graph G has an edge partition
      into simple cycles C with w_G(C) = sum_(v in C) 1/d_G(v) >= c.
```

**This investigation does not prove W(c) for any absolute positive c, and does not construct a 3-connected even family in which every partition has a cycle of weight tending to zero. In particular, W(1/100) remains unresolved by this work.** The requested proof-or-counterexample dichotomy has not been completed. The results below are proved auxiliary results, not a claimed resolution of Erdős–Gallai or a literature-priority claim.

The new results are:

1. **An exact, arbitrary-number-of-cuts optimizer for two coherently intersecting cycles.** Their entire set of simple-cycle partitions is classified. For a globally weight-fair minimum cycle of weight m and a coherently intersecting cycle of weight M>2m, all but exactly one of the latter's inter-contact arcs must be *no heavier* than the corresponding arcs of the minimum cycle. This is a necessary condition in a genuine global lexicographic optimum, not a claim about an arbitrary count optimum.
2. **Sharp necessary conditions at a minimum-weight triangle.** No other old cycle can contain its three vertices. A cycle meeting two vertices has both intervening internal arc weights at most the weight of the missing triangle vertex, and therefore has weight less than 2m. In a regular graph, every such double-contact cycle must be a four-cycle. These conditions expose, but do not resolve, the remaining many-cycle rerouting problem.
3. **The complete global fair-optimal profile of `K_3 join k K_2`.** For every k>=3 it consists of precisely four cycles of weight `3/4+3/(2k+2)` and k-3 cycles of weight `1+3/(2k+2)`. An explicit construction achieves it. The proof optimizes over **all partitions, with no cardinality restriction**. This completes the fair optimization of the known 3/4 test family; it does not lower the previously known upper ceiling 3/4.
4. **A global triangle-orientation theorem without a divisibility assumption.** A triangle partition with bridgeless vertex–triangle incidence admits an Eulerian orientation making every designated triangle transitive. In particular this applies to every triangle partition of a 2-connected graph of minimum degree at least four. A cubic-expansion/perfect-matching proof replaces the degree-divisible-by-six hypothesis in `ResearchHeavy.md`. With an appropriate non-designated-cycle weight or incidence-girth hypothesis, this gives an all-heavy partition, using exchanges of unrestricted size.
5. **Uniformly fair-optimal partitions of an unbounded-degree, nonregular 3-connected family.** A layered permutation construction partitions the cone over a `(2r-1)`-regular, high-girth graph with a perfect matching into N/2 cycles, each of original-degree weight exactly `1+1/N`, where N is the base order. The cycles are simple, every edge and endpoint is accounted for, and the profile is globally optimal. A finite-permutation construction supplies base graphs for every r>=2; thus both minimum degree and degree ratio can be unbounded.

The companion checker is

```
PYTHONDONTWRITEBYTECODE=1 PYTHONHASHSEED=0 \
  python3 Submission/ResearchFairCyclesCheck.py
```

It uses exact rational arithmetic, exhaustive fair optimization on small graphs, explicit edge-partition certificates, and matching algorithms. The family proofs do not depend on testing finitely many parameters. `Spec.lean` and all **26** preexisting Submission files were preserved; only this note and its checker were added.

---

## 1. The actual fair objective and its hereditary property

All graphs are finite, simple and undirected unless an auxiliary multigraph or orientation is expressly introduced. Cycles are simple, and a partition covers every edge **exactly once**. Degrees in `w_G` are frozen at the original G.

It is useful to work more generally with positive vertex weights `lambda(v)`. Give an edge uv weight

```
a(uv) = (lambda(u)+lambda(v))/2.
```

For a path P with distinct endpoints x,y, write

```
a(P) = lambda(x)/2 + sum_(v internal to P) lambda(v) + lambda(y)/2.
```

For a simple cycle this edge sum is exactly `w(C)=sum_(v in C) lambda(v)`. For any partition D of a fixed even edge graph H,

```
sum_(C in D) w(C) = (1/2) sum_v d_H(v) lambda(v).             (1.1)
```

In particular, for `lambda(v)=1/d_G(v)` and H=G, this is half the number of nonisolated vertices. In a 3-connected graph it is n/2.

### 1.1 Definition of lexicographic max–min fairness

Sort the cycle weights of D increasingly, retaining multiplicities. Maximize this finite vector lexicographically over **all** simple-cycle edge partitions. Cardinality is not fixed and is not a primary objective.

There is no prefix-convention ambiguity: two different profiles of partitions of the same graph cannot be a proper-prefix pair, because all weights are positive and their total is fixed by (1.1). A fair optimum exists because there are finitely many partitions.

An exact alternative is to list the distinct weights of all simple cycles as

```
a_1 < ... < a_s,
```

and let `m_i(D)` count cycles of weight a_i. Maximizing the increasing weight profile is equivalent to minimizing

```
(m_1(D),...,m_s(D))
```

lexicographically. If `L=floor(|E(G)|/3)` and the integer B is greater than L, it is also equivalent to minimizing the integer

```
Phi(D) = sum_i m_i(D) B^(s-i).                              (1.2)
```

At the first differing multiplicity, its unit contribution dominates all later contributions, since there are at most L cycles in a partition. Thus no floating-point approximation or informal infinitesimal is required.

### 1.2 Hereditary fairness, with original weights retained

**Lemma 1.1.** If D is globally fair and A is any subfamily, then A is fair on its edge union, using the same original lambda.

**Proof.** Sorted-multiset addition preserves the first differing weight multiplicity. A fair improvement of A therefore remains an improvement after adding the identical multiset of weights from `D\A`. Equation (1.1) gives the fixed sum on the selected union. Replace A to obtain a contradiction. No restriction on the size of A is used. ∎

In particular, if A contains r cycles of globally minimum weight m, and a replacement has no weight below m and fewer than r occurrences of m, the replacement is a genuine strict global improvement. It is not enough merely to produce one heavy replacement cycle or a heavy closed trail.

The finite checker uses exact edge-cover dynamic programming to optimize the **whole** profile. Its states retain the original weights, not residual reciprocal degrees. The hereditary property justifies using the best suffix profile in each state.

---

## 2. Complete multi-cut optimization for coherent intersections

Two edge-disjoint cycles C,D have **coherent intersections** if their common vertices occur in the same cyclic order, up to reversing one cycle. Suppose there are r>=3 common vertices, named in that order

```
x_0,...,x_(r-1).
```

Cut **both** cycles at all r vertices. Let `P_i,Q_i` be their respective `x_i--x_(i+1)` arcs, oriented in that direction, and put

```
a_i=a(P_i),       b_i=a(Q_i),
m=w(C)=sum_i a_i, M=w(D)=sum_i b_i, T=m+M.
```

Assume m<=M. The arc interiors are pairwise disjoint across the two cycles and contain no common vertex. The r cuts are not bounded. This is different from cutting each of three or more old cycles at only two ring connectors.

### Theorem 2.1 — all partitions of this union

Every simple-cycle partition of `C union D` is one of the following:

* **Two spanning circuits:** choose one of `P_i,Q_i` at every gap for the first circuit, and the complementary arc for the second.
* **The r lenses:** for every i, take `P_i union Q_i` as one cycle.

There are exactly `2^(r-1)+1` unordered partitions and `2^r+r` simple cycles in the union. In particular, this classifies arbitrary repartitioning, not just a selected list of two-switches.

**Proof.** Suppress the private internal vertices of the arcs. The result is a cyclic sequence of r junctions with two parallel strands per gap. A simple cycle that uses both strands of one gap is precisely that lens. Every other simple cycle must continue through the next gap at every junction and hence traverse the whole ring, choosing one strand per gap. Once one such spanning circuit is used, the remaining strands form exactly its complementary spanning circuit. If none is used, every gap must be covered by its lens. Distinct strand choices give distinct edge sets, with only global complementation identifying an unordered two-cycle partition. Each lifted circuit is simple because its private interiors and its junctions are distinct. Simplicity of the original graph rules out a lens of length two. ∎

### 2.1 Exact weights and an elementary balancing bound

Set `Delta_i=b_i-a_i`. A spanning replacement indexed by `I subseteq {0,...,r-1}` has the **exact** two weights

```
m + s(I),      M - s(I),       s(I)=sum_(i in I) Delta_i.   (2.1)
```

Its count is two, and its total is T. The lens weights are exactly `a_i+b_i`, with count r and the same total T.

Greedily assign the heavier arc of each pair to the currently lighter total. The discrepancy after the next pair is the absolute difference between the previous discrepancy and `|a_i-b_i|`. Consequently there is a two-cycle partition with

```
min w >= [T-max_i |a_i-b_i|]/2.                            (2.2)
```

Every term in (2.1) and (2.2) is an additive edge weight, with the endpoint halves included. Thus these are also exact original-degree cycle weights after lifting.

The r-lens partition is never fair-optimal. For completeness, let `ell=min_i(a_i+b_i)>0`. Bound (2.2) is at least

```
[T-max_i(a_i+b_i)]/2 >= (r-1)ell/2 >= ell.
```

If the minimum lens is unique, the first inequality gives a strict improvement above ell for both new cycles: after deleting a largest lens, the remaining total is greater than 2ell. If the minimum occurs at least twice, at most one replacement can have weight ell, since T>=3ell. Its minimum multiplicity therefore decreases. This is the paired-arc argument applied to the lens ring, with its exact simplicity already proved above.

It follows that the fair optimum of the entire union has exactly two cycles. Its smaller weight is

```
gamma = max_I min(m+s(I), M-s(I)).                          (2.3)
```

In particular the old pair is fair on its union **if and only if**

```
there is no I with 0 < s(I) < M-m.                         (2.4)
```

When M=m, the interval is empty and the old pair is indeed fair on this union; a two-cycle exchange cannot raise both equal minima while preserving their total.

### Corollary 2.2 — the single expanding gap in a global fair optimum

Let C have globally minimum weight m in a fair partition, and let a coherently intersecting old cycle D have r>=3 contacts and weight M>2m. Then

```
exactly one i has b_i>a_i;
for every other gap, b_i<=a_i.                             (2.5)
```

Conversely, for such a coherent pair with M>2m, condition (2.5) makes that pair fair on its own union.

**Proof.** By Lemma 1.1 and (2.4), every positive Delta_i is at least `M-m`. There cannot be two of them: their sum would be at least `2(M-m)>M`, whereas the sum of all positive Delta_i is at most `sum_i b_i=M`. There is at least one, because `sum_i Delta_i=M-m>0`.

Conversely, with a unique positive Delta, a subset sum omitting it is nonpositive. A subset sum including it is at least the sum of all the Deltas, namely `M-m`, because omitting negative terms only increases the sum. Thus (2.4) holds. ∎

The one expanding D-arc also satisfies

```
sum_(j != i) b_j <= sum_(j != i) a_j < m.                  (2.6)
```

This is a concrete restriction on a **globally** fair partition. A much heavier coherent cycle cannot supply two expanding excursions around the light target: a single arc exchange would already repair that target. It must hide almost all of its extra mass in one gap.

This conclusion does not say that these pairs obstruct all global exchanges. Other cycles can change the arcs or their cyclic order. Noncoherent intersections are not classified by Theorem 2.1.

---

## 3. What global fairness really forces at a light triangle

Let `C=(a,b,c)` be a globally minimum cycle in a fair partition, and write

```
m=lambda(a)+lambda(b)+lambda(c).
```

### Theorem 3.1 — three-contact exclusion and the two-contact inequalities

1. No other old cycle contains all three of a,b,c.
2. Suppose another old cycle D contains a,b but not c. If its two a--b arcs have internal vertex-weight sums u,v, then

   ```
   0<u<=lambda(c),      0<v<=lambda(c),
   lambda(c)<=u+v<=2lambda(c),
   m<=w(D)<=m+lambda(c)<2m.                                (3.1)
   ```

The analogous statements hold for the other two pairs.

**Proof of 1.** Any cyclic order on three common vertices is coherent up to reversal. The corresponding C-arcs are the three single edges. None of the D-arcs can be that same edge, since the partition is edge-disjoint. Thus every D-arc contains an outside vertex, and

```
b_i=a_i+t_i,             t_i>0.
```

Take one D-arc and two C-edges for the first replacement, and the complementary arcs for the second. Their weights are exactly `m+t_i` and `m+t_j+t_k`, both greater than m. They are simple and replace two cycles by two cycles, contradicting fairness.

**Proof of 2.** Neither D-arc is the edge ab, so u,v are positive. Assume u>=v. Replace C,D by

* the cycle consisting of the edge ab and the u-arc of D;
* the other D-arc together with the C-path a--c--b.

These are simple and partition the same edges. Their weights are exactly

```
m+u-lambda(c),           m+v.                              (3.2)
```

If u>lambda(c), both exceed m, a contradiction. Hence u,v<=lambda(c). Since D is not lighter than C, `u+v>=lambda(c)`. The remaining assertions follow by addition; `lambda(c)<m` is strict. ∎

### Original-degree consequences

For `lambda(v)=1/d_G(v)`, every outside vertex x on a two-contact D as above satisfies

```
d_G(x) >= d_G(c).                                         (3.3)
```

It contributes at most lambda(c) to one of the two bounded arcs. If an arc contains at least two outside vertices, each of those contributions is strictly less than lambda(c).

In a d-regular graph, (3.1) forces each a--b arc to have exactly one internal vertex. Thus:

> In a fair partition of a regular graph whose global minimum is a triangle, every old cycle meeting that triangle twice is a four-cycle; no old cycle meets it three times.

More generally any old cycle of weight at least 2m meets the triangle at most once.

### Where the many-incidences argument stops

If m is extremely small, each target vertex belongs to

```
d_G(v)/2 > 1/(2m)
```

old cycles. The inequalities above genuinely exploit global fair optimality, but do **not** bound that number. The incident cycles can still consist of:

* cycles of weight below 2m meeting two target vertices, with very high-degree vertices on their short internal arcs; and
* arbitrarily many cycles meeting the target at only one vertex.

Three-connectivity connects these attachments elsewhere. It does not, by itself, supply a coherent return order or a weight-preserving partition of their whole union. The signed frustration and repeated-visit costs in `ResearchIncidence.md` cannot be dropped here. A proof for an arbitrary light minimum cycle needs to control this larger union, not stop at (3.1).

---

## 4. A complete all-partitions fair solution of the 3/4 test family

Put

```
G_k = K_3 join (k disjoint copies of K_2),      k>=1.
```

The core is a,b,c; outside block i consists of x_i,y_i. Degrees and order are

```
d(a)=d(b)=d(c)=2k+2,       d(x_i)=d(y_i)=4,
n=2k+3.                                                       (4.1)
```

The graph is even. A surviving core vertex connects everything after any two vertex deletions. For k>=2, deleting the three core vertices disconnects the outside blocks, so connectivity is exactly three. For k=1 the graph is K_5.

### Theorem 4.1 — exact full lexicographic optimum

For k>=3 define

```
A_k = 3/4 + 3/(2k+2),       B_k = 1 + 3/(2k+2).
```

The globally fair profile over **all** cycle partitions is

```
(A_k,A_k,A_k,A_k, B_k,...,B_k),
                       k-3 copies of B_k.                 (4.2)
```

It has k+1 cycles. The exceptions are

```
k=1: (5/4,5/4),
k=2: (1,5/4,5/4).                                         (4.3)
```

### 4.1 Upper bound, including the number of minimum-weight cycles

Every partition has q>=k+1 cycles, by the degree of a core vertex. Every outside vertex occurs on precisely two cycles, so the total number of outside-vertex occurrences is 4k.

A cycle with o outside vertices and h core vertices has weight

```
o/4 + h/(2k+2),           0<=h<=3.                         (4.4)
```

For k>=3, any cycle of weight at least A_k has o>=3. If o=3, it must have all three core vertices and its weight is exactly A_k. A cycle heavier than A_k must have o>=4.

If a partition had all weights greater than A_k, it would have at most k cycles from its 4k outside occurrences, contradicting q>=k+1. Thus A_k is a universal bottleneck upper bound.

Now suppose all weights are at least A_k, and let z count cycles of weight exactly A_k. Then

```
4k >= 3z+4(q-z),       z>=4(q-k).                           (4.5)
```

Thus z>=4. A partition with more than k+1 cycles has z>=8 and cannot beat a witness with just four minima. When q=k+1, every cycle contains every core vertex, because each core vertex must occur k+1 times. If also z=4, equality in the outside ledger forces every other cycle to have exactly four outside vertices. Its weight is B_k. Therefore construction of (4.2) proves the entire lexicographic optimum, not just its first coordinate.

### 4.2 Three-port path data

Choose an ordered core pair alpha,beta for one outside block x,y, and let gamma be the remaining core vertex. Its seven edges, including xy but no core edge, split into the three paths

```
alpha--x--y--beta,       beta--x--gamma,       gamma--y--alpha. (4.6)
```

There is one path for each unordered core pair. The first has two outside vertices; the other two have one each. A triple of paths, one per core pair, forms a simple core-spanning cycle whenever their outside interiors are disjoint.

### 4.3 A k=3 base with four cycles of three outside vertices

Use blocks X=(x_X,y_X), Y=(x_Y,y_Y), Z=(x_Z,y_Z), with long pairs respectively ab,bc,ca. The following four cycles partition G_3:

```
a b x_Y y_Y c y_X a,
a y_Y b c x_Z y_Z a,
a x_X y_X b y_Z c a,
a x_Z b x_X c x_Y a.                                     (4.7)
```

In each displayed word the last a only indicates closing the cycle. Every cycle has three core and three outside vertices. Directly from (4.6), every path of each block occurs once and each core edge occurs once. The outside interiors in every word are distinct. Thus all four weights are `A_3=9/8`.

### 4.4 An insertion preserving the exact fair profile

Suppose a partition in three-port path form has precisely four cycles with three outside vertices and all its other cycles have four. Select any three-outside cycle. Since each of its three paths has 0,1 or 2 outside vertices, at least one path P has exactly one. Let its core endpoints be alpha,beta.

Add a fresh outside block, choosing alpha,beta as its long pair in (4.6).

* In the selected old cycle, replace P by the fresh long path. Its outside count increases from three to four.
* Make one additional cycle from P and the fresh two singleton paths. It has three outside vertices.

Both cycles are simple: the fresh vertices are private, and the two fresh singleton paths use distinct vertices. Each old edge is retained once and the seven new block edges are used once. The count increases by exactly one; the number of three-outside cycles stays exactly four. Iteration proves (4.2) for every k>=3.

For k=1 take the two Hamilton cycles

```
a x_1 y_1 b c a,        a y_1 c x_1 b a.
```

For k=2 apply the same insertion at a singleton path in the second cycle. The outside counts become 2,3,3, proving (4.3). For k=2, any partition with minimum at least 1 has at most four cycles by the outside count. Four would all have exactly two outside and all three core vertices, requiring twelve core occurrences when only nine are available. Thus it has three cycles, and counts 2,3,3 are the lexicographic optimum. For k=1 the two equal weights meet the degree/total-weight average bound.

### What this resolves, and what it does not

The old count-optimal partition with a bare core triangle has minimum `3/(2k+2)`, tending to zero. **The fair optimum of the same graph has minimum tending to 3/4, with the same minimum possible cardinality.** This is an actual all-partitions optimization, not another arbitrary bad partition.

The family still rules out only c>3/4 asymptotically. It supplies no vanishing-weight obstruction to W(c).

---

## 5. A global triangle surgery without degree divisibility

A useful positive construction can be made substantially more general than the balanced-middle assignment in `ResearchHeavy.md`.

### Theorem 5.1 — bridgeless incidence suffices

Let T be a triangle edge partition of a simple graph G. Suppose its bipartite vertex–triangle incidence graph I is bridgeless after isolated vertices are discarded. Then G has an Eulerian orientation in which every triangle of T is transitive.

There is no regularity assumption and no requirement that a vertex lie in a multiple of three triangles.

**Proof.** Work in one incidence component. Triangle nodes have degree three. For every graph-vertex node v, let `r_v` be its incidence degree. Bridgelessness implies r_v>=2.

Replace v by a cyclic list of r_v port vertices, attaching its distinct old incidence edges to distinct ports. For r_v=2 use a two-edge parallel digon. Leave triangle nodes unexpanded. Call the resulting auxiliary **multigraph** Q.

Every port has two cycle edges and one incidence edge; every triangle node has its three incidence edges. Thus Q is cubic. It is bridgeless:

* each new internal edge lies on its port cycle, including both edges of a digon;
* an old incidence edge lay on a cycle of I, and that cycle lifts to a cycle of Q by connecting its two used ports inside each expanded vertex.

A bridgeless cubic multigraph has a perfect matching. One standard proof applies Tutte's one-factor theorem: each odd component after deleting a vertex set S has an odd edge boundary; it cannot have boundary one, so it has at least three. These boundaries use at most `3|S|` edges incident with S, yielding Tutte's odd-component inequality. This is the only matching-existence theorem needed at this step.

Take a perfect matching M of Q and its complementary two-factor F. At every triangle node, exactly two incidence edges belong to F. At a port cycle, the number of its external F-edges is even, since every F-degree is two. Thus the selected incidences define a bipartite subgraph J of I satisfying

```
d_J(T)=2 for every triangle T,       d_J(v) even for every v. (5.1)
```

For each triangle, select the graph edge joining its two J-incident vertices. These selected edges form a simple even graph S: at v their number is exactly d_J(v). Orient S Eulerianly. If a selected edge is directed u->v and its triangle's third vertex is z, orient the whole triangle as

```
u->v,       u->z,       z->v.                              (5.2)
```

It is transitive. Its imbalance contribution at u and v is twice that of the selected edge, and its contribution at z is zero. Summing over triangles, the full orientation is balanced at every vertex. All original edges are used exactly once because T is an edge partition. ∎

### 5.1 Why the connectivity hypothesis in the question supplies bridgeless incidence

If G is 2-connected with minimum degree at least four, then every vertex node of I has degree at least two. Suppose an incidence edge vT were a bridge. The side containing v includes another triangle through v and hence includes a graph vertex other than v. The side containing T includes its other two vertices. In G, these two nonempty sides can communicate only through v: all graph edges lie in their designated triangles. Thus v would be a cut vertex, a contradiction.

Consequently Theorem 5.1 applies to **every** triangle partition of a 3-connected even graph. This removes the old degree-divisible-by-six restriction for this orientation construction.

### 5.2 When this really is an all-heavy construction

The orientation is balanced, so repeatedly deleting directed simple cycles partitions its edges. No extracted cycle can be a designated triangle, because those triangles are acyclic. Therefore:

> If every non-designated simple cycle of G has original-degree weight at least c, Theorem 5.1 constructs a partition all of whose weights are at least c.

This is a simultaneous construction, not frozen-weight greedy deletion from an arbitrary orientation: the orientation excludes the entire specified light class before any cycle is removed.

One sufficient hypothesis is incidence girth. Suppose `girth(I)>2R`. A non-designated simple cycle uses at most two edges of any designated triangle; if it uses two, they are consecutive. Compress each such one- or two-edge segment to a two-edge step through its triangle node in I. No triangle node repeats, and no connector vertex repeats. This is an incidence cycle with at most as many triangle nodes as the original cycle has edges. Hence every non-designated cycle has length greater than R. Writing Delta for the original maximum degree gives

```
w_G(C) >= |C|/Delta >= (R+1)/Delta.                        (5.3)
```

For R>=Delta, every extracted cycle has weight greater than one. The count then follows from the exact original-weight total n/2. In particular this extends the positive construction on the high-incidence-girth regular triangle systems in `ResearchHeavy.md` to **every** occurrence degree d>=2, not just d divisible by three.

### Necessary limitation

The orientation theorem alone does not exclude a light cycle made from edges of several designated triangles. It cannot be applied to an arbitrary graph by pretending that all light cycles form one edge-disjoint triangle partition.

The checker deliberately includes Steiner triangle partitions of K_9 and K_27, with occurrence degrees 4 and 13. The new orientation is balanced and every designated triangle is transitive, but other directed triangles remain. These are controls for the missing hypothesis, **not** all-partitions counterexamples: those complete graphs have Hamilton partitions.

The operation can alter transitions in an unbounded number of old triangles. No bounded-cycle or bounded-degree exchange claim is being made.

---

## 6. A layered global construction with a provably optimal uniform weight profile

The next family does not start from a triangle partition. It also handles arbitrarily uneven original degrees.

### Theorem 6.1 — high-girth odd-regular cones

Let H be a simple `(2r-1)`-regular graph on N vertices, r>=2, with a perfect matching. Assume H is 2-connected and has girth at least 2r. Let G be its cone: add an apex z adjacent to every H-vertex.

Then G is simple, even and 3-connected, and it has a partition into exactly N/2 cycles such that

```
each cycle has 2r vertices in H and the apex z,
w_G(C)=1+1/N.                                             (6.1)
```

This uniform profile is the full global fair optimum, and N/2 is also the minimum possible cardinality.

For r=2, the girth assumption can be omitted: the conclusion holds for the cone over every 2-connected cubic simple graph.

### 6.1 Factor permutations

Take a perfect matching M in H. The remaining graph is `(2r-2)`-regular. Orient it Eulerianly, so every indegree and outdegree is r-1.

Its directed edges split into r-1 permutations `sigma_1,...,sigma_(r-1)` of V(H): take a perfect matching in the bipartite tail–head graph, remove it, and repeat. Each remaining bipartite graph is regular of the same degree on both sides; Hall's condition follows by counting edges from any set of left vertices. A permutation here means precisely the arc set

```
{v -> sigma_j(v) : v in V(H)}.
```

Every nonmatching H-edge occurs in one such arc set and in one orientation only.

### 6.2 Assemble all paths at once

Start an arm at every vertex v. At layer j extend its current endpoint x by the edge `x -> sigma_j(x)`. At every layer, the current endpoints are a permutation of V(H), because they are obtained by composing the preceding permutations. Therefore every edge of factor j is used **exactly once** among all the arms at layer j.

For each matching edge uv, concatenate

```
reverse(arm starting at u),   the matching edge uv,
arm starting at v.                                        (6.2)
```

In vertex notation the first arm already ends at u and the second starts at v, so concatenate their vertex lists with the edge uv between them. This produces N/2 edge-simple trails, each with exactly

```
2(r-1)+1=2r-1 edges,       2r vertex occurrences.           (6.3)
```

Together they partition E(H). Their endpoints occur exactly once each, since the final arm endpoints are again a permutation of V(H).

These trails are **simple paths**. A repeated vertex on an edge-simple trail of length 2r-1 would give a closed subtrail containing a simple cycle of length at most 2r-1, contradicting the girth assumption. This is where simplicity is proved, rather than inferred from Eulerianity.

Close every path through z. Every apex edge is used once because every H-vertex was an endpoint once. These are simple cycles, and they partition all of G.

### 6.3 Original weights, count, and global fair optimality

The original degrees in G are

```
d_G(v)=2r for v in H,       d_G(z)=N.
```

Thus (6.3) gives exactly (6.1), not a weight computed in a residual or auxiliary graph. Every partition has at least N/2 cycles by the degree of z. Its total weight is `(N+1)/2`, so its minimum weight is at most

```
[(N+1)/2]/[N/2] = 1+1/N.
```

The constructed partition meets this bound in every coordinate. Any partition attaining this minimum must have exactly N/2 cycles and all weights equal to it. This proves the full fair-optimal profile and count assertion.

Deleting two vertices from G leaves it connected: if z survives it connects all remaining vertices, while if z is deleted, at most one H-vertex is also deleted and H remains connected. Thus G is 3-connected.

### 6.4 The cubic case needs no girth assumption

For r=2 there is just one permutation sigma. The path associated to uv in M is

```
(sigma(u), u, v, sigma(v)).                                (6.4)
```

These four vertices are distinct: sigma has no fixed point; the edge uv is in M, not the permutation factor; and sigma is injective. Thus the path is simple even if H has triangles.

A 2-connected cubic graph is bridgeless and hence has a perfect matching by the cubic matching theorem used in Section 5. Therefore this case applies to every such H, not merely bipartite ones.

### 6.5 Finite base graphs exist for every r, without an unproved high-girth assumption

Here is an explicit finite-permutation existence construction. Fix the odd integer `d=2r-1>=3` and `R>=2r-1`. Let W consist of the empty word and all words of length at most R over d symbols with no equal consecutive symbols.

For symbol i define an involution p_i of W by swapping

```
w <-> wi
```

for every word w of length less than R not ending in i; fix all remaining words. The pairs are disjoint. Applying a reduced word of length at most R in the p_i to the empty word gives its own word index. Thus no nonempty such word is the identity permutation.

Each p_i has exactly

```
1+(d-1)+...+(d-1)^(R-1)
```

transpositions, an odd number because d is odd. Hence all p_i are odd permutations. Let Gamma be the finite permutation group they generate and take its undirected Cayley graph with these d involutions. It is finite, connected, simple and d-regular; distinctness of the generators follows from the no-short-relation property. It is bipartite by permutation sign. A simple graph cycle of length at most R would give a nonempty reduced relation of that length, so its girth exceeds R.

For clarity, every connected d-regular bipartite graph with d>=2 is 2-connected. If deleting a vertex v on the left leaves a component X, and t is the positive number of its edges back to v, degree counting in X gives

```
t=d(|right vertices of X|-|left vertices of X|) >= d.
```

The total available t over all components is d, so there is only one component. Regular bipartite graphs have perfect matchings by Hall. Thus these finite Cayley graphs satisfy every hypothesis of Theorem 6.1.

Taking r unbounded gives minimum degree `2r -> infinity` in the cones. Taking R arbitrarily large also gives arbitrarily large order relative to degree, so the degree ratio need not be bounded. The global construction remains uniform-weight fair-optimal throughout.

This is a positive special family, not a reduction of arbitrary 3-connected even graphs to cones.

---

## 7. A precise single block ledger, conditional on a different weighted lemma

The original-degree statement has not been disproved. Nevertheless a block-aware fallback can be stated without reusing a vertex budget at every attachment.

For an arbitrary even graph, each edge-containing block is even, because every simple cycle lies in one block and an edge partition exists. Root the block–cut forest of each nontrivial component at a chosen graph vertex. For each block B, designate its parent vertex `r_B` (the chosen root in a root block). Give a cycle in B the **different** weight

```
mu_B(C) = sum_(v in C, v != r_B) 1/d_B(v).                  (7.1)
```

The sets `V(B)\{r_B}` partition the non-root graph vertices. Equivalently,

```
sum_B (|V(B)|-1) = |V(G)|-kappa(G).                        (7.2)
```

For any blockwise cycle partitions,

```
sum_B sum_(C in D_B) mu_B(C)
    = (1/2) sum_B (|V(B)|-1)
    = (|V(G)|-kappa(G))/2.                                (7.3)
```

So the following would suffice for a linear count using a **single** ledger:

> Every even 2-connected block, with a specified root vertex, admits a cycle partition with all rooted weights (7.1) at least an absolute c>0.

It would give `c(G)<=(n-kappa(G))/(2c)`. This rooted lemma is **not proved** here. It is not the same as W(c): local block degrees replace original degrees and one vertex's weight is excluded. Likewise, a 2-separator reduction must account for virtual edges and port paths separately; (7.3) alone does not establish such a reduction or preserve original-degree cycle weights.

The point of (7.1)–(7.3) is to make any proposed fallback's payment exact, rather than assigning a fresh full budget to a shared articulation at every level.

---

## 8. Checker coverage and verified results

The checker is self-contained apart from NetworkX. It does not import or edit the previous research checkers. No numerical LP/MILP or floating-point comparison is used.

All tests passed with `PYTHONHASHSEED=0`:

* **192** rationally weighted coherent pairs, with 3 through 10 contacts. **5,952** complete strand assignments check simplicity, edge coverage and exact weights. On **120** of those pairs, exhaustive simple-cycle enumeration and full-profile exact-cover optimization independently verify the complete classification, the strict inferiority of the lens partition, and the single-expanding-gap equivalence when applicable.
* **120** exact weighted triangle/two-contact tests check (3.1)–(3.2) against full fair optima. The supplied triangle-containing pair is itself globally fair in 41 tests, so the tests include the non-improving side of the inequalities, not only favorable exchanges.
* **24** parameters for `G_k`, including every k from 1 through 20 and k=30,50,100,250. The largest graph has **503 vertices**. Every edge, vertex occurrence, degree, cycle weight and profile multiplicity is checked. Independently exhaustive fair search gives:

  | k | exact fair profile | residual DP states |
  |---:|:---|---:|
  | 1 | `(5/4,5/4)` | 24 |
  | 2 | `(1,5/4,5/4)` | 433 |
  | 3 | `(9/8,9/8,9/8,9/8)` | 7,714 |
  | 4 | `(21/20,21/20,21/20,21/20,13/10)` | 144,554 |

* The incidence orientation construction is checked on vertex-triangle systems of the line graphs of K_4, Petersen, Heawood, the dodecahedron and Desargues, on the affine Steiner systems of orders 9 and 27, and on a **39-vertex nonuniform example with degrees 4 and 8** obtained by identifying an independent triple in two line graphs. The auxiliary multigraph is actually checked cubic and bridgeless; the matching is perfect; all selected degrees are even; the final orientation is balanced and every designated triangle is transitive; the extracted simple cycles cover every original edge. For example:

  | triangle system | n | degree | incidence girth | extracted count | minimum original weight |
  |:---|---:|---:|---:|---:|:---|
  | line Petersen | 15 | 4 | 10 | 4 | 5/4 |
  | line Heawood | 21 | 4 | 12 | 6 | 3/2 |
  | line Desargues | 30 | 4 | 12 | 6 | 3/2 |

  These particular counts depend on the matching and extraction choices. The theorem's weight guarantee follows from the incidence girth, not from those choices.

* **Eight cone constructions** check every factor edge, the endpoint permutation, all path and cycle simplicity, and the uniform fair profile. They include nonbipartite cubic bases and the **42-vertex 5-regular incidence graph of the projective plane over F_4**, whose girth is six. The latter cone has n=43, minimum degree six, maximum degree 42, and exactly 21 cycles, all of weight **43/42**. Finite-ball involution checks at `(d,R)=(3,3),(3,5),(5,3),(5,5),(7,4)` verify all permutations, their parity counts, and every reduced word through the promised radius. They check up to 1,814 word states; the full generated groups are not enumerated.
* **All 85 even graphs in the graph atlas through order seven**, including disconnected and edgeless graphs, are solved for their full fair profile. The new triangle and coherent-intersection necessary conditions are checked in those global optima: 8 triangle two-contact cases and 57 coherent-contact cases. Each of the 85 cases also checks the rooted block ledger (7.3), including literal single ownership of every non-root vertex. The 10 three-connected even atlas graphs have smallest optimal bottleneck 1. This upgrades the old bottleneck-only small-graph search to full-profile optimization, but is not evidence of a proved universal constant.

The complete successful output is also retained at `/tmp/ResearchFairCyclesCheck.final.out`. The checker snapshots all other Submission files and verifies that they are unchanged during execution. Independent before/after hashes against the initial inventory confirm that all 26 preexisting files were preserved. The specification hash is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

These are paper-level proofs and exact computational checks, not Lean formalizations.

---

## 9. Exact remaining gap

The new results isolate several genuinely global issues without conflating them:

* A fair optimum is hereditary for arbitrary selected subfamilies, with a fully exact objective. This is stronger than count optimality and stronger than stability under any prescribed exchange size.
* The coherent two-cycle union is now completely solved, including every possible number of cuts and every possible replacement count. An extremely light target can coexist with a much heavier coherent cycle only in the single-expanding-gap pattern.
* At a minimum triangle, a heavy old cycle cannot make two contacts at all. Many double contacts are possible only through other cycles with weights below 2m and high-degree internal vertices. Many one-contact attachments remain possible.
* Neither the single-expanding-gap condition nor the triangle conditions explain how to recombine the **whole** network of attachments in a general 3-connected graph. Large intersections in incompatible cyclic orders, chains of light return arcs, and multiple cuts of many old cycles remain unhandled. Splitting macro trails may produce new cycles below m; a bound on the number of split cycles does not prevent that.
* The matching construction solves the designated-triangle case only when all other possible cycles are heavy. General light cycles are not an edge-disjoint designated class. The cone construction uses an apex and a factor-layer structure absent in a general graph.
* The complete fair solution of `K_3 join kK_2` shows that its light count-optimal triangle cannot serve as a vanishing all-partitions obstruction. Its actual fair bottleneck is asymptotically 3/4, and allowing more cycles cannot improve that profile.

Accordingly, no contradiction has been obtained from a hypothetical globally fair minimum `m<1/100`, and no graph family has been shown to force such minima to zero. The missing step is still a **global, weight-safe recombination or a genuine all-partitions obstruction**, not a better count-only collision bound or another rigid arbitrary partition.

**Bottom line:** the desired yes/no result remains open in this investigation. The new exact optimization theorems, global constructions, complete proofs and reproducible checker are retained here so that the remaining step can be attacked without repeating the previous quantifier and accounting errors.
