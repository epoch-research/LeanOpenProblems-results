# Light-cycle elimination: movable fans, terminal connectivity, and an exact order obstruction

## Status — W(c) is not resolved by this investigation

The target is

> **W(c).** Every finite simple 3-connected even graph G has an edge partition into simple cycles C with `sum_(v in C) 1/d_G(v) >= c`, for some absolute `c>0`.

**I have not proved W(1/100), proved W(c) for any absolute positive c, or constructed a genuine 3-connected family in which every partition has a cycle of weight tending to zero.** In particular the proof-or-counterexample task remains incomplete. No claim about resolving Erdős–Gallai is made.

This note continues the fair-partition approach with the following proved results. The first three concern networks in an arbitrary globally fair partition, rather than a new positive example family.

1. **Deleting a triangle leaves a 2-connected even graph.** If G is simple, even and 3-connected and T is any triangle, then `G-E(T)` is 2-connected. Every 2-separator of this residual graph must separate the surviving triangle terminals; its components and possible intersections with T are sharply restricted. This rules out a residual block-tree explanation for a minimum triangle, but not a long chain of terminal-separating 2-cuts.
2. **Equal-weight fans can be re-paired globally and then absorb an external cycle.** A minimum triangle on edge ab, together with arbitrarily many squares through a,b whose other vertices have the same frozen weight, is a movable packet. The minimum triangle may be moved to any fan vertex and all remaining fan paths may be re-paired, with exactly the same full fair profile. An external cycle avoiding a,b and meeting two fan vertices can then be absorbed into two strictly heavier simple cycles. The outside cycle can originally have only one contact with the old minimum triangle. There is no bound on how many old fan cycles may be re-paired.
3. **Consequences in a regular graph.** For the full fan at any edge of a minimum triangle in a globally fair partition, every external old cycle meets the fan's non-pole vertices at most once. Those vertices are independent in G. An external cycle through a pole and a fan vertex is a square, and an explicit profile-preserving pivot moves the triangle to a different edge. The triangle subfamily is a cactus. These give the global incidence bound `(D+1)n >= 4s(D-1)+5`, where D is the regular degree and s is the odd number of fan vertices. In fact global minimization of the **number of triangles** suffices. For a fan exhausting its poles, this yields a precise terminal-mixing question involving **every** triangle-minimizing partition of the residual graph, even ones with a worse higher-weight profile.
4. **The entire three-terminal, two-contact packet is optimized over all partitions.** For a minimum triangle in a regular graph, all double-contact squares have mutually disjoint interiors. Their union with the triangle is a three-terminal parallel-path network. Its complete fair profile is determined below, allowing every number of spanning cycles and every path pairing. Consequently at least one of the three triangle pairs has no double-contact old cycle.
5. **An exact incompatible-order obstruction, not a W(c) counterexample.** A four-contact union has exactly nine partitions. Its original pair is uniquely globally fair, although the heavier cycle can have two arbitrarily heavy excursions. This disproves an extension of the coherent single-expanding-gap principle to arbitrary cyclic orders. With actual reciprocal degrees its fair minimum is 2, not small; the graph has degree-two vertices and is not 3-connected. Thus this obstruction identifies a real exchange issue without falsely disproving W(c).

The remaining issue is specified in Section 8. In particular, none of these results asserts that fan pivots must eventually improve the profile, that a degree-bounded exchange suffices, or that arbitrary closed trails can be split without creating lighter cycles.

Only this note and `ResearchLightEliminationCheck.py` are added. All 28 preexisting Submission files, including `Spec.lean`, are preserved. The results are paper-level proofs with exact finite checks, not Lean formalizations or claims of literature priority.

---

## 1. Fixed weights and the exact comparison being used

Give every vertex a positive fixed weight `lambda(v)` and let

```
w(C) = sum_(v in V(C)) lambda(v).
```

For an edge uv use the additive weight `(lambda(u)+lambda(v))/2`. Thus a path has half the weight of each endpoint, plus the full weights of its internal vertices. Every cycle's additive edge weight is exactly w(C).

For any partition of a fixed even edge graph H,

```
sum_C w(C) = (1/2) sum_v d_H(v) lambda(v).                 (1.1)
```

The sorted increasing weight profile is maximized lexicographically over **all** simple-cycle edge partitions. Cardinality is not fixed. Positive weights and (1.1) exclude proper-prefix comparisons. A profile improvement on any selected subfamily remains an improvement after adjoining the same unselected cycles: equivalently compare multiplicities at the first weight where they differ. This is hereditary fairness with the original weights retained.

Two consequences used repeatedly are:

* Replacing a selected packet by a partition with exactly the same weight multiset gives another **globally** fair partition if the starting partition was globally fair.
* If all old selected cycles have weight at least m, at least one has weight m, and every new selected cycle is strictly heavier than m, the replacement is a strict global improvement.

No conclusion is inferred merely from count optimality or stability under a restricted move set.

### 1.1 The triangle contact facts, recalled precisely

Let `C=(a,b,c)` have globally minimum weight

```
m = lambda(a)+lambda(b)+lambda(c)
```

in a fair partition.

* No other old cycle contains all three of a,b,c.
* If another old cycle contains a,b but not c, and its two a--b arcs have internal weight sums u,v, then

```
0 < u,v <= lambda(c),
u+v >= lambda(c),
m <= w(D) <= m+lambda(c) < 2m.                            (1.2)
```

These are Theorem 3.1 of `ResearchFairCycles.md`. For clarity, their proof uses exact simple-cycle replacements. In the three-contact case every old non-triangle arc contains an outside vertex; choosing one such arc and the other two triangle edges for one replacement makes both replacement cycles heavier than m. In the two-contact case, the edge ab paired with the arc of internal weight u, and the other arc paired with a--c--b, have weights

```
m+u-lambda(c),           m+v.
```

If `u>lambda(c)`, both exceed m. Interchanging the arcs gives the other bound. The old minimum property gives the bound on u+v.

In a D-regular graph, every vertex has weight `1/D`; hence every double-contact cycle in (1.2) is a square, with one outside vertex on each arc. This conclusion is used only with **actual global fairness**.

---

## 2. A triangle cannot leave a residual articulation network

### Theorem 2.1 — triangle deletion preserves 2-connectivity

Let G be a finite simple 3-connected even graph, and let T be any triangle. Then

```
H = G-E(T)
```

is even and 2-connected. Its minimum degree is at least two.

**Proof.** Since G is 3-connected and even, its minimum degree is at least four. Removing the triangle lowers precisely its three vertex degrees by two, so H is even and has minimum degree at least two.

Every edge cut of an even graph has even cardinality. Vertex-connectivity at least three implies edge-connectivity at least three; parity therefore gives edge-connectivity at least four. Removing the three triangle edges cannot disconnect G, so H is connected.

Suppose that x is a cut vertex of H. Each component K of `H-x` contains a vertex of `V(T)\{x}`: otherwise no removed triangle edge could join K to another component, contradicting connectedness of `G-x`.

In fact K contains at least two such triangle vertices. If its only surviving triangle vertex were t, then K cannot be the singleton `{t}`, since `d_H(t)>=2` and a singleton component of `H-x` would give `d_H(t)<=1`. Thus `K\{t}` is nonempty. Removing x and t from G separates this set from the other components of `H-x`, since all added-back triangle edges incident with K use t. This contradicts 3-connectivity.

There are at most three surviving triangle vertices. Two components would require at least four of them. Hence x cannot be a cut vertex. ∎

This is an assertion about deleting **edges**, not deleting the three vertices. It needs the degree and connectivity hypotheses; the union of a triangle with arbitrary cycles need not have this property.

### Theorem 2.2 — all residual 2-cuts are terminal-separating

Under Theorem 2.1, let S be a two-vertex separator of H. Every component of `H-S` contains a vertex of `V(T)\S`. Consequently:

1. S contains at most one triangle vertex.
2. If S contains one triangle vertex, `H-S` has exactly two components, each containing one of the other two triangle vertices.
3. If S avoids the triangle, `H-S` has either two or three components, each containing at least one triangle vertex.

**Proof.** A component with no surviving triangle terminal has no incident edge among `E(T)\E(G[S])` leading to another component. It would remain a component in `G-S`, contrary to 3-connectivity. The components are vertex-disjoint, so their nonempty terminal sets partition the surviving terminals. There are at least two components. All three conclusions follow. ∎

These theorems do **not** say that H is 3-connected. There may be arbitrarily many distinct 2-cuts separating the same terminal sets. In particular, contracting the whole residual graph to three freely pairable terminals would still discard essential path orders and simplicity constraints.

---

## 3. Globally movable equal-weight fans

Fix distinct poles a,b and an odd set S of other vertices, `|S|=2r+1`. The fan edge set is

```
F = {ab} union {as,bs : s in S}.                          (3.1)
```

Suppose all vertices of S have the same positive frozen weight t. Write `alpha=lambda(a)`, `beta=lambda(b)`. A fan partition consists of one triangle `a b z a`, with `z in S`, and r squares pairing the remaining vertices:

```
a x b y a.
```

Its entire profile is

```
(m, m+t,...,m+t),     m=alpha+beta+t,     r copies of m+t. (3.2)
```

### Lemma 3.1 — arbitrary fan re-pairing preserves global fairness

If this fan partition is a subfamily of a globally fair partition and the triangle has globally minimum weight m, then:

* any chosen vertex of S may replace z as the triangle vertex;
* the remaining vertices of S may be paired in any way;
* the resulting whole partition is still globally fair, with the same full profile.

**Proof.** All such choices are exact simple-cycle partitions of (3.1), with profile (3.2). The rest of the graph is unchanged. ∎

This is not an assumption that one can optimize outside the fair objective. It is an **equality** in that objective. A later use of the triangle contact conditions is made in the re-paired, still globally fair partition.

### Theorem 3.2 — two-contact absorption into a movable fan

Suppose `r>=1` and the hypotheses of Lemma 3.1 hold. Let E be an external old cycle avoiding a,b. Then

```
|V(E) intersect S| <= 1.                                 (3.3)
```

Equivalently, any external old cycle avoiding the poles and meeting at least two fan vertices yields an explicit strict fair improvement, after re-pairing the whole fan if necessary.

**Proof.** All external old cycles have weight at least m.

**Two selected contacts, with a third fan vertex off E.** Choose distinct `x,y in E intersect S` and `z in S\V(E)`. Re-pair the fan so that its triangle is abz and one square is axby. Let R be the x--y arc of E in one direction and T the complementary y--x arc. Replace these three old cycles by

```
Q_1 = a b x R y a,
Q_2 = a z b y T x a.                                     (3.4)
```

Here a path's displayed endpoint is not listed twice. Both cycles are simple: E avoids a,b,z, its two arc interiors are disjoint, and x,y are distinct. They use every edge of the triangle, square and E once. Every replacement contains a,b,x,y, so both have weight at least

```
alpha+beta+2t = m+t > m.
```

All remaining re-paired fan squares are unchanged.

**At least three contacts on E.** Choose three distinct fan contacts x,y,z, named in their cyclic order on E. Re-pair as above, and let `R_xy,R_yz,R_zx` be the three arcs of E. Replace the selected triangle, square and E by

```
Q_1 = a b x R_xy y R_yz z a,
Q_2 = a x reverse(R_zx) z b y a.                          (3.5)
```

The three arc interiors are disjoint, and E avoids a,b. The two cycles are therefore simple and cover exactly the selected edges. Both contain a,b,x,y,z, so both have weight at least `m+2t>m`.

If E has exactly two contacts, the first case applies because `|S|>=3`. Otherwise the second case applies. Each replacement removes at least the old minimum triangle and creates no cycle of weight m or below. Hereditary fairness gives the contradiction. ∎

The proof permits arbitrarily many additional contacts of E with **unselected** fan vertices and other unselected cycles. Those vertices are ordinary private vertices relative to the three selected cycles in (3.5); intersections with unchanged cycles do not violate simplicity. The re-pairing before (3.4) or (3.5) can alter an unbounded number of old squares.

This genuinely reaches some old **one-contact** attachments: a cycle meeting only the old triangle vertex z may meet another fan vertex elsewhere, and hence becomes absorbable after re-pairing.

### Theorem 3.3 — cycles using a pole

Under Lemma 3.1:

* an external cycle containing both poles contains no vertex of S;
* an external cycle containing a but not b and at least two vertices of S forces `beta>t`;
* symmetrically, one containing b but not a and at least two vertices of S forces `alpha>t`.

In particular, if `alpha,beta<=t`, **every external old cycle meets S at most once**, and S is independent in the whole graph.

**Proof.** If a cycle contains a,b and some x in S, move the triangle to abx. This contradicts three-contact exclusion.

Now suppose E contains a,x,y, where x,y are distinct members of S, and avoids b. Move the triangle to abx. The two-contact inequalities say that both a--x arcs of E have internal weight at most beta. One arc contains y. Since the edge ay already belongs to the fan, E cannot use it. The portion of that arc between a and y has at least one internal vertex in addition to y. Consequently that a--x arc has internal weight strictly greater than `lambda(y)=t`, so `beta>t`.

The symmetric assertion follows in the same way. Combining with Theorem 3.2 proves the contact bound when both pole weights are at most t. An edge between two members of S could not be a fan edge; its old cycle would be external and would meet S twice. Thus no such edge exists. ∎

For original-degree weights, the extra assumption in the last assertion is exactly

```
d_G(a),d_G(b) >= d_G(s)   for s in S.
```

It is automatic in a regular graph. It is **not** automatic for an arbitrary nonregular fan, and it has not been silently dropped.

---

## 4. Complete optimization of the double-contact packet

### 4.1 The three-terminal network

Start with a triangle abc. For each pair ij in `{ab,bc,ca}`, add `2r_ij` internally disjoint two-edge i--j paths. All their internal vertices are distinct, including across different pairs. Retain the one direct triangle edge in each pair. Give every vertex the same weight t.

Put

```
R = r_ab+r_bc+r_ca,       s = min(r_ab,r_bc,r_ca).
```

### Theorem 4.1 — full all-partitions fair profile

The lexicographically maximum increasing weight profile is:

```
s=0:  (3t, (4t)^R),

s>=1: ((4t)^(R-3s), (5t)^3, (6t)^(2s-2)).               (4.1)
```

Exponents denote multiplicities; zero multiplicities are omitted. This is optimization over **all** simple-cycle edge partitions, not over a fixed count or a particular pairing convention.

**Classification of all partitions.** The private path interiors have degree two. A simple cycle either uses two paths of the same terminal pair, a *lens*, or one path from each of the three pairs, a *spanning triangle of paths*. Let q be the number of spanning cycles. Every pair has `2r_ij+1` paths, so

```
q is odd,       1 <= q <= 2s+1.                          (4.2)
```

After choosing the q paths on each side and assigning them to spanning cycles, all remaining paths are paired into lenses. These are exactly all partitions. Their total number of cycles and number of lenses are respectively

```
R+(3-q)/2,       L=R+(3-3q)/2.                           (4.3)
```

Every such assignment is simple after lifting because all path interiors are private.

**Proof of optimality when s=0.** Equation (4.2) forces q=1. Every partition has `R+1` cycles and total length `4R+3`, so at least one cycle has length three. The original triangle and R squares attain one three-cycle and all other cycles of length four. Any profile with at least two three-cycles is worse. If there is just one, the fixed count and total length force all the others to have length exactly four. This proves the first line of (4.1).

**Construction when s>=1.** Set `q=2s+1`. On each side select its direct edge and `q-1` of the two-edge paths. Form q spanning cycles, placing the three direct edges on **three different** cycles. This gives three cycles of length five and `q-3=2s-2` cycles of length six. Pair the remaining paths on each side into `R-3s` squares. This proves attainability of the second line.

**Proof of optimality when s>=1.** A lens has length at most four. If a direct edge is used in a lens, that lens has length three, inferior to the constructed profile. Thus in any competing profile with minimum at least four, all direct edges must be in spanning cycles.

If `R-3s>0`, every partition has at least `R-3s` lenses by (4.3), so its minimum is at most four. Taking q smaller than `2s+1` increases the number of lenses by at least three, and hence cannot attain the constructed minimum multiplicity. At q maximal, no spanning cycle may have length four if that multiplicity is to stay minimal. Therefore the three direct edges must occur on different spanning cycles, forcing the displayed profile.

If `R-3s=0`, the construction has minimum five. A smaller q leaves lenses and has minimum at most four. At maximal q there are only spanning cycles. Their three direct edges force some cycle to have length at most five; a profile with minimum five must put them on different cycles. Again (4.1) is forced. ∎

### Corollary 4.2 — at least one double-contact type is absent

Let G be D-regular and let `C=(a,b,c)` be a globally minimum triangle in a fair partition. Among the other old cycles, at least one of the classes

```
contains a,b;       contains b,c;       contains c,a
```

is empty.

**Proof.** Section 1.1 says that every such cycle is a square, with two outside vertices each adjacent to its two triangle contacts. No two of these squares can share an outside vertex: their terminal pairs share a triangle vertex, and sharing an outside vertex would reuse the edge joining these two common vertices. No square contains the third triangle vertex.

Consequently the union of C and **all** its double-contact cycles is exactly the network of Theorem 4.1, with `t=1/D`. If all three classes were nonempty, its fair optimum would have minimum at least `4/D`, whereas the supplied packet has a triangle of weight `3/D`. Hereditary fairness forbids this improvement. ∎

This optimizes the whole double-contact packet at once. It does not discard one-contact cycles or assert that the packet is the entire graph.

---

## 5. Full fans in a regular globally fair partition

Let G be D-regular and let `C=(a,b,c)` be a minimum triangle in a fair partition. Fix the edge ab. Take C and **all** other old cycles containing a,b. By Section 1.1 these are squares with pairwise distinct private vertices. Their union is precisely (3.1), with

```
S = {c} union {the two outside vertices of each such square},
|S|=2r+1=:s,       t=alpha=beta=1/D.                      (5.1)
```

Here s denotes the fan size, not the parameter in Section 4.

### Corollary 5.1 — saturated fan contact constraints

Every external old cycle meets S at most once. The set S is independent in G. An external old cycle containing a pole and a vertex x of S is a square whose other two vertices lie outside `S union {a,b}`.

**Proof.** The first two conclusions follow from Theorems 3.2–3.3. For the last, move the triangle to abx and use (1.2). It is a square. The third triangle vertex cannot belong to it, by three-contact exclusion, and either of its other two vertices in S would reuse a fan edge at the pole. ∎

### Lemma 5.2 — an exact square pivot

Assume `s>=3`. Suppose an external square is

```
E = a p x q a,           x in S.
```

Choose distinct y,z in `S\{x}`. After re-pairing the fan to contain the triangle abz and square axby, the following is a profile-preserving replacement:

```
old: (a,b,z),     (a,x,b,y),     (a,p,x,q);
new: (a,x,p),    (a,b,x,q),     (a,z,b,y).                (5.2)
```

Every other re-paired fan square is unchanged. The new triangle is on the different edge ax.

**Proof.** Corollary 5.1 makes p,q distinct and outside `S union {a,b}`. Thus all six displayed cycles are simple. Listing their edges gives equality of the two unions, with no repeated edge on either side. Both profiles are exactly `(3/D,4/D,4/D)`. The equality principle of Section 1 proves that the resulting whole partition is globally fair. ∎

The pivot allows triangle motion along a chain of squares and fan re-pairings. **It is not a monotone improvement.** Repeating pivots may revisit a previous fair partition. No termination or global-reachability conclusion is being asserted.

### Lemma 5.3 — the triangle subfamily is a cactus

In any globally fair partition with positive vertex weights, the vertex–cycle incidence graph of its triangle subfamily is a forest. If there are tau triangles and their incidence graph has k nonempty components, then

```
2 tau = |union of their vertex sets| - k.                (5.3)
```

In particular, if there is a triangle and the graph has n vertices, `tau<=(n-1)/2`.

**Proof.** Distinct edge-disjoint triangles meet in at most one vertex. If their incidence graph contains a cycle, a shortest incidence cycle gives a clean ring of at least three triangles: its connector vertices are distinct, consecutive triangles share only their connector, and any further intersection would shorten the incidence cycle.

For completeness, a clean ring of cycles has a strict fair improvement. Split each old cycle into its two connector-to-connector arcs of additive weights u_i,v_i. Select one arc per old cycle for each of two new cycles. Clean intersections prove both new cycles simple. Assign the larger arc at each step to the currently lighter total. The final discrepancy is at most `max_i |u_i-v_i|`, so the smaller new weight is at least

```
[sum_i w(C_i)-max_i w(C_i)]/2.
```

If the smallest old weight occurs once, this is strictly greater than that weight; if it occurs at least twice, both new weights are at least that weight and at most one can equal it. In either case the sorted profile strictly improves. This contradicts hereditary fairness.

The forest edge count is `3 tau = (tau+|union V|)-k`, proving (5.3). ∎

### Theorem 5.4 — a global fan incidence bound

In the regular setting of (5.1),

```
(D+1)n >= 4s(D-1)+5.                                    (5.4)
```

If the fan exhausts the degrees of its poles, so `s=D-1`, then

```
n >= ceiling(4D-12+21/(D+1)).                            (5.5)
```

**Proof.** Each vertex of S belongs to `D/2-1` external old cycles. Corollary 5.1 says those occurrences are on distinct cycles as s varies. If Q is the number of external cycles, then

```
Q >= s(D-2)/2.                                         (5.6)
```

The fan has `2s+1` edges, so the total length of the external cycles is

```
Dn/2-(2s+1).                                           (5.7)
```

Let tau_out count their triangles. Every other external cycle has at least four edges. Lemma 5.3, including the one triangle inside the fan, gives `tau_out<=(n-3)/2`. Hence

```
Dn/2-(2s+1) >= 4Q-tau_out
             >= 2s(D-2)-(n-3)/2.
```

Rearranging is (5.4). If the fan exhausts both pole degrees, its degree `s+1` at each pole equals D. Substitution yields (5.5). ∎

This is a necessary condition on **global** fair partitions. It does not give an absolute lower bound on the weight `3/D`: s may be small, and n is not bounded by a constant multiple of D in the target problem. Articulation-based regular completions in the earlier notes remain compatible with these restrictions and can have globally fair light triangles; 3-connectivity is still essential to a hoped-for closure argument.

### Theorem 5.5 — global triangle-count optimality is already enough

In a graph with uniform positive vertex weights, all the triangle contact restrictions, missing-double-contact-type conclusion, fan re-pairings, absorptions, independence conclusion, square pivots, and triangle-forest conclusion above hold if the partition merely **minimizes the number of triangles over all cycle partitions**. Full lexicographic optimality is not needed for these conclusions. The regular fan bound (5.4) also holds for every such triangle-count minimizer.

**Proof.** No simple cycle has fewer than three vertices. In every strict triangle-contact or fan-absorption exchange, the selected old cycles include a triangle and all replacement cycles have length at least four. Thus their number of triangles decreases. A clean ring of triangles replaces at least three triangles by two cycles, each of length at least three, so again its triangle count decreases. Re-pairings and (5.2) preserve the triangle count exactly. For the missing-type conclusion, Theorem 4.1 supplies a replacement without triangles whenever all three types occur. These are global replacements, not stability tests on a prescribed exchange size. The proof of (5.4) uses only these consequences. ∎

The count objective here is **number of triangles**, not number of cycles. An arbitrary minimum-cardinality partition does not satisfy this hypothesis.

### 5.1 An exact residual terminal-mixing formulation for a full fan

This gives a concrete unrestricted outside-network question. Suppose the fan exhausts its poles, `s=D-1`, and put

```
H = G-{a,b}.
```

Then H is simple and even, and

```
d_H(v)=D-2 for v in S,       d_H(v)=D for v outside S.    (5.8)
```

The set S is independent by Corollary 5.1. Three-connectivity of G is equivalent to the following condition on H (with `|S|=D-1>=3`):

```
H is connected, and for every X subseteq V(H) with |X|<=2,
every component of H-X meets S\X.                        (5.9)
```

Indeed, deleting both poles requires H connected. A component in H-X with no surviving terminal has no edge to either surviving pole, proving necessity of the other condition. Conversely, if at least one pole survives a deletion of two vertices, all components of the remaining H connect to that pole through their surviving terminals; if both poles survive they are adjacent. This proves sufficiency as well.

Let `tau(J)` denote the minimum number of triangles in any simple-cycle edge partition of an even graph J. If a globally triangle-minimizing partition of G has this full fan, then

```
tau(G)=1+tau(H),                                         (5.10)
```

and **every** triangle-minimizing partition of H has each cycle meeting S at most once.

To see (5.10), the displayed partition contributes exactly one fan triangle; hereditary triangle-count optimality makes its H restriction attain tau(H). Conversely, any partition attaining tau(H), adjoined to any fan pairing, has the same optimal triangle count in G. Theorem 5.5 and the fan absorber therefore apply to each such partition, proving the universal outside contact restriction.

Thus even outside partitions with a **worse higher-weight profile** cannot be dismissed. If one attaining tau(H) has a cycle through two terminals, (3.4) or (3.5) gives a partition of G with at most tau(H) triangles, contradicting (5.10).

A precise sufficient next lemma would be:

> **Terminal-mixing assertion (unproved).** For even D>=4, let H be simple and even, with an independent terminal set S of size D-1, degrees (5.8), and robustness (5.9). There is a partition attaining tau(H) with some cycle meeting S at least twice.

No proof or counterexample to this auxiliary assertion is obtained here. It would rule out the full-fan case of a regular minimum triangle, but **would not** resolve smaller fans, nonregular graphs, or minimum cycles longer than three. Conversely, failure of this particular sufficient assertion would not automatically disprove W(c). It is not being substituted for W(c).

---

## 6. Four incompatible contacts can trap two heavy excursions

The coherent multi-cut theorem in `ResearchFairCycles.md` cannot be extended by saying that two sufficiently heavy excursions of another cycle always repair a minimum cycle. Here is a complete all-partitions obstruction to that extension.

Take four junctions a,b,c,d. Use two parallel **paths**, not parallel original edges, at each of ab and cd:

```
ab: the direct edge ab and the path a--x--b;
cd: the direct edge cd and the path c--y--d.
```

Add the direct edges bc and da, and two paths `P_bd,P_ca`, whose interiors are private and disjoint from everything else. The graph is simple. Its supplied partition is

```
C = a x b c y d a,
D = a b P_bd d c P_ca a.                                (6.1)
```

The common vertices occur in orders `a,b,c,d` and `a,b,d,c`, which are incompatible up to reversal. Let

```
B = lambda(a)+lambda(b)+lambda(c)+lambda(d),
p=lambda(x)>0,       q=lambda(y)>0,
h=sum internal weights on P_bd,
k=sum internal weights on P_ca,
m=B+p+q,             M=B+h+k.
```

### Theorem 6.1 — exact unique fair optimum

If `M>=m`, the pair (6.1) is the unique fair-optimal partition. Its profile is `(m,M)`. Every other partition has minimum weight strictly below m.

There are exactly nine unordered partitions of this graph and nineteen simple cycles.

**Proof.** Suppress private path interiors, retaining the identity of the eight resulting strands. The junction multigraph is K_4 with an extra parallel strand at ab and at cd. The only two-junction circuits are the ab lens and the cd lens.

If a partition has two cycles, both must visit all four junctions, since every junction has degree four. A Hamilton circuit of this multigraph is of one of three types:

* type C: one ab strand, bc, one cd strand, da;
* type D: one ab strand, bd, one cd strand, ca;
* type X: bc,bd,da,ca.

The complement of type X is the two separate lenses, not one cycle. Thus every two-cycle partition consists of complementary types C and D. There are four choices, according to which of the two strands on each parallel pair is assigned to type C. Their weights are

```
m-i p-j q,         M+i p+j q,          i,j in {0,1}.     (6.2)
```

Only `i=j=0` has minimum at least m.

Every partition with at least three cycles contains a two-junction lens: otherwise its cycles would use at least nine junction-strands when there are only eight. The lens weights are

```
lambda(a)+lambda(b)+p < m,
lambda(c)+lambda(d)+q < m.                              (6.3)
```

This already proves the unique optimum.

For the counts, a three-cycle partition is either the two lenses plus type X, or one lens plus two triangles on the other parallel pair. Each choice of the lens in the latter case has two strand assignments. This gives five three-cycle partitions and four two-cycle partitions. There cannot be four cycles, since that would require four two-junction lenses, and only two exist.

There are two lenses, eight triangles (two strand choices for each of four junction triples), and nine Hamilton circuits (four of type C, four of type D, one of type X). Hence there are nineteen simple cycles. Every suppressed circuit lifts simply, because its path interiors are private. ∎

### Actual reciprocal-degree instance, with its exact limitation

Let both diagonal paths have L edges, `L>=2`. Every junction has degree four and every private vertex has degree two. Thus

```
w_G(C)=2,       w_G(D)=L.                               (6.4)
```

Theorem 6.1 proves the full fair optimum `(2,L)` for every L. When `L>=6`, the two diagonal excursions of D each have internal weight `(L-1)/2>2=m`; both can tend to infinity. Nevertheless no repartition of this entire union improves its minimum.

This is a simple even 2-connected graph, but **not** a 3-connected graph: it has degree-two vertices. More importantly, its minimum fair weight is 2, not `o(1)`. It therefore supplies **no counterexample to W(c)** for a small positive c.

The example isolates why Menger paths or multiple large excursions cannot be converted to a fair improvement merely by ignoring the cyclic order. Conversely, inflating the degrees of its private vertices would introduce new incident cycles whose unrestricted recombination has not been controlled. The unique-optimum proof for the old two-cycle union would then be only hereditary packet information, not a global lower bound in the enlarged graph.

---

## 7. Exact verification and reproduction

Run from `/workspace/leanproject`:

```
PYTHONDONTWRITEBYTECODE=1 PYTHONHASHSEED=0 \
  python3 Submission/ResearchLightEliminationCheck.py
```

The checker is self-contained apart from NetworkX. It neither imports nor modifies an old research checker. The full-profile optimizer is exact-cover dynamic programming on original edge sets, with exact rational weights. Its count recurrence also counts **all** partitions, independently of the maximizing objective.

The checks include:

* arbitrary equal-weight fan re-pairings, two- and three-contact absorptions with long arcs and extra contacts, and exact square-pivot edge identities;
* exhaustive full-profile optimization and enumeration of all partitions on small three-terminal networks, followed by large explicit certificates;
* exact enumeration of all nineteen cycles and all nine partitions of the incompatible four-contact network, with both arbitrary rational weights and actual original reciprocal degrees;
* triangle-edge deletion and the terminal restrictions on residual 2-separators in all relevant atlas graphs and larger generated 3-connected even graphs;
* full fair optimization of every even graph in the graph atlas through order seven, with both unit weights and frozen reciprocal-degree weights. The triangle forest and, for unit weights, all full-fan contact and missing-pair conditions are tested in these genuine global optima.

All checks passed. The final run reported:

| Check | Exact coverage |
|:---|:---|
| Movable fans | 1,980 equal-profile re-pairings; 180 strict absorptions; 18 square pivots |
| Three-terminal optimizer | 26 full fair optima; all 15,400 partitions classified; 6 larger explicit certificates, up to 603 vertices |
| Incompatible four-contact network | 100 rational weightings and 22 original-degree instances; all 9 partitions and 19 cycles per instance |
| Triangle deletion | 889 triangle deletions in 34 simple 3-connected even graphs; 230 actual residual 2-separators checked |
| Global fair optima | 170 instances: all 85 even atlas graphs with each of unit and original-degree weights; 105 whole-fan and 121 external-cycle checks |
| Weaker global objective | All 57 triangle-count-minimizing partitions in the positive-minimum-triangle unit-weight atlas cases; 216 whole-fan checks |
| Terminal connectivity equivalence | 57 three-connected cases and 83 non-three-connected controls |
| Protected files | All 28 preexisting files unchanged |

The full fair atlas optimizations used 17,484 residual DP states; the small three-terminal cases used 1,696. The successful output is retained at `/tmp/ResearchLightEliminationCheck.final.out`. Python syntax and Markdown fence checks also passed. The terminal-connectivity test verifies (5.9), **not** the unproved terminal-mixing assertion.

These finite checks corroborate the proofs; they are not proofs of an unrestricted threshold theorem.

The checker snapshots the 28 preexisting Submission files and verifies that they stay unchanged during execution. An independent before/after inventory checks them against the start of this investigation. The specification SHA-256 is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

---

## 8. Precise remaining step

The results above still leave the following unproved assertions; none is used as an implicit premise.

### 8.1 Even the regular triangle closure is not established

Start with a globally fair partition of a simple 3-connected D-regular graph, and suppose its minimum cycle is a triangle, with `D>300`. Consider all **globally fair partitions with exactly the same full profile** obtainable by fan re-pairings and square pivots, not just one selected local optimum.

The missing closure claim would be that this equivalence class must contain a configuration with a strict fair improvement — for example, a three-contact triangle obstruction, all three double-contact types, or one of the fan absorbers in Section 3 — or that a different unrestricted packet improvement exists.

**No proof of that claim is given.** Three-connectivity, and even the stronger residual information in Section 2, does not by itself prove it. External cycles can still make one fan contact apiece and connect to each other in complicated overlapping packets. Pivots can change the controlling edge and can cycle; their profile equality is not a termination argument. Theorem 5.4 is not a contradiction when the graph is large.

This is a sharply identified first barrier, not a claimed equivalence between the particular fan move set and all possible improvements. A full proof might need a packet which no sequence of these pivots exposes. Section 5.1 gives an even more concrete sufficient subproblem when a fan exhausts its poles: terminal mixing in a triangle-count-minimizing partition of H under (5.8)–(5.9). That auxiliary assertion is also unproved, and is expressly weaker in scope than W(c).

### 8.2 What would still be needed after regular triangles

Even resolving 8.1 would not prove W(c). One must also handle:

* nonregular weights, where a two-contact arc may contain several high-degree vertices and equal-profile triangle moves are not available;
* minimum cycles of length four and greater;
* arbitrary incompatible cyclic orders, including the exact obstruction of Section 6;
* chains and branching networks of light cycles requiring many cuts of many old cycles;
* every simple cycle produced by the final repartition, not merely two heavy routed trails or a controlled count of small split-off cycles.

The exact global target remains: for a hypothetical globally fair minimum `m<1/100`, find a subfamily A and a simple-cycle partition of **its exact edge union**, with original degrees frozen, such that no new cycle has weight below m and the multiplicity of m strictly decreases. Alternatively, construct a simple 3-connected even family and prove, over **every** partition, that some cycle has weight tending to zero.

Neither conclusion has been obtained here. In particular, the incompatible-order example, an arbitrary bad decomposition, and any degree-bounded exchange obstruction do not have the required all-partitions 3-connected quantifier.

**Bottom line:** the task is still unresolved. The new network-level fan exchanges, exact three-terminal optimizer, residual connectivity theorem, global necessary bound, and fully classified order obstruction are retained as proved progress, with the missing global elimination step explicit.
