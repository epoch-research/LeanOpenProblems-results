# Heavy-cycle decompositions: verified progress and exchange barriers

## Status and main conclusions

**No absolute positive c is established for either proposed existence lemma, and no family refuting all positive c is obtained here. In particular, this is not a proof or disproof of the Erdős–Gallai conjecture.** The case of a small constant such as `c = 1/10` remains unresolved by this investigation.

There are, however, two rigorous asymptotic auxiliary counterexamples and a positive exchange result:

1. **Minimum cardinality does not force minimum weight or minimum length.** There are 3-connected even simple graphs with minimum degree tending to infinity and an *exactly minimum-cardinality* cycle partition containing a triangle of original-degree weight tending to zero. The other cycles in that same partition all have weight greater than 1. This invalidates choosing an arbitrary minimum-cardinality partition and claiming its cycles must be heavy.
2. **No bounded-cycle-exchange repair lemma works, even at maximum possible vertex-connectivity.** For every exchange bound `r` and arbitrarily large degrees `2d`, there is a finite simple `2d`-regular graph with vertex-connectivity `2d` and a triangle partition which cannot be changed at all by repartitioning the edges of at most `r` existing cycles. Its cycle weights are `3/(2d)`, and its number of cycles is `nd/3`, not uniformly O(n). The bound `r` can even be any prescribed function of the degree: choose the construction's other parameter afterwards.
3. **The second obstruction is not a counterexample to the existence lemma.** For an infinite subfamily, a separate, explicit matching-and-orientation argument gives a partition in which *every* cycle has original-degree weight greater than 1 and the number of cycles is less than `n/2`. Thus the distinction between a globally good partition and a locally immovable bad partition is certified, not conjectural.
4. **A valid weighted clean-ring exchange is available.** If `r ≥ 3` cycles meet in a clean cyclic necklace, their edges can be repartitioned into two simple cycles with a quantitative lower bound on both weights. This gives a genuine lexicographic shortest-cycle improvement, but clean-ring size cannot be bounded in terms of the degree alone.

The closest corpus paper explicitly identifies simultaneous selection of inverse-degree-heavy cycles as a possible way past its logarithmic loss. Other superficially relevant results concern vertex partitions, paths, locally self-avoiding tours, or numbers of cycles, rather than the required minimum weight of every cycle.

`Submission/Spec.lean` was only read. Its SHA-256, checked before and after the research, is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

The existing `ResearchPackets.md` and `ResearchPacketsCheck.py` were not edited.

---

## 1. Exact formulation and accounting

All graphs below are finite, simple, and undirected unless an orientation is explicitly introduced. A cycle is simple. A cycle partition is an **edge partition**, not a cover and not a vertex partition. Degrees in the weight are always those of the original graph under discussion:

```
w_G(C) = sum_{v in V(C)} 1/d_G(v).
```

For a nonempty even graph with no isolated vertices and any cycle partition D,

```
sum_{C in D} w_G(C)
  = sum_v (number of cycles of D containing v)/d_G(v)
  = sum_v (d_G(v)/2)/d_G(v)
  = n/2.                                                   (1.1)
```

With isolated vertices, replace n by the number of nonisolated vertices.

The two targets are:

* **W(c):** every 3-connected even simple graph has a cycle partition with `w_G(C) ≥ c` for every cycle.
* **L(c):** every 3-connected even simple graph of minimum degree δ has a cycle partition with `|C| ≥ cδ` for every cycle.

W(c) gives at most `n/(2c)` cycles. Also W(c) implies L(c), since

```
w_G(C) ≤ |C|/δ.
```

Conversely, L(c) only gives

```
w_G(C) ≥ |C|/Δ ≥ cδ/Δ,
|D| ≤ |E(G)|/(cδ) ≤ nΔ/(2cδ).                              (1.2)
```

Thus it suffices for regular graphs, and more generally for a uniformly bounded ratio `Δ/δ`, but it does not supply the original-degree weighted statement in general.

The articulation and 2-separator count reduction described in the question is compatible with pursuing W(c) on 3-connected pieces: the relevant charge is the sum of the piece orders. One should not additionally assume that local reciprocal degrees remain the original graph's reciprocal degrees after gluing. The count reduction and a weight-preservation assertion are different claims. No new separator reduction is needed for the counterexamples below: their connectivity is checked directly.

---

## 2. Corpus findings: what is and is not supplied

The search used `/corpus/metadata.jsonl`, title/abstract searches, and targeted full-text searches of 283 source files from 219 graph-related candidates. This is a report of the local sources actually inspected, not a claim to have exhausted all later literature. The source directory for the specification's Bucić–Montgomery reference `2211.07689` was not present locally.

### 2.1 The closest inverse-degree paper

**Charlotte Knierim, Maxime Larcher, Anders Martinsson, Andreas Noever, _Long Cycles, Heavy Cycles and Cycle Decompositions in Digraphs_, arXiv:1911.07778.**

Relevant local files:

* `/corpus/src/1911.07778/preliminaries.tex`, lemma `small_decomp_existence`;
* `/corpus/src/1911.07778/easy_version.tex`;
* `/corpus/src/1911.07778/weighted_general.tex`;
* `/corpus/src/1911.07778/conclusion.tex`, especially lines 5–9.

Their inverse-out-degree weight is directly analogous to the proposed weight. Their decomposition lemma uses **current** out-degrees in each residual graph. Its exact accounting is a harmonic sum at each vertex, producing the logarithm. They obtain an O(n log Δ) cycle decomposition of Eulerian digraphs, not an original-degree all-heavy partition.

The conclusion explicitly suggests that finding the cycles simultaneously rather than iteratively might remove the logarithmic factor. So the general direction has a close precedent; the missing simultaneous assertion is not already established by that paper.

### 2.2 Bondy–Fan gives the single heavy cycle particularly cleanly

The preceding paper states the following Bondy–Fan theorem in `introduction.tex`, lines 49–53:

> A 2-edge-connected graph on n vertices with nonnegative edge weights has a cycle of weight at least `2W/(n−1)`, where W is the total edge weight.

Set

```
a(uv) = (1/d_G(u) + 1/d_G(v))/2.
```

Then

```
a(C) = w_G(C),             a(E(G)) = n/2.
```

Consequently, in a nontrivial connected even graph,

```
max_C w_G(C) ≥ n/(n−1) > 1.                                (2.1)
```

A connected even graph has no bridge, so the theorem applies. This supplies a cited route to the single-cycle observation in the question, without any partition conclusion.

On an even residual H, keeping the original weights instead gives

```
a(E(H)) = (1/2) sum_v d_H(v)/d_G(v).
```

On a connected nontrivial component with h vertices, Bondy–Fan therefore only guarantees a cycle of weight at least

```
(sum_{v in component} d_H(v)/d_G(v))/(h−1).                  (2.2)
```

There is no uniform lower bound when the remaining degree fractions are small. Section 3 gives an exact high-minimum-degree example where many original-weight-heavy cycles can be removed, leaving a very light triangle.

An arbitrary-edge-weight strengthening of the form “every cycle in some partition has weight at least a constant times W/n” is false even for complete even graphs: put all positive weight on one edge of `K_{2s+1}`, with `s ≥ 2`. Every partition has at least s cycles, and at most one can use that edge. This observation does **not** refute reciprocal-degree weights, or a version with extra local weight-normalization assumptions.

### 2.3 Long cycles leading to few pieces: CFS

**David Conlon, Jacob Fox, Benny Sudakov, _Cycle packing_, arXiv:1310.0632.**

Source: `/corpus/src/1310.0632/1310.0632.tex`.

* Lines 28–30 state the O(n log log d) cycle/edge result.
* Lines 41–45 give O(α^−12 n) pieces when `δ(G) ≥ αn`.
* Lines 200–207 give a useful precise hereditary long-cycle condition: if every subgraph with m ≥ 2n edges has a cycle of length at least

  ```
  α (m/n) log²(m/n),
  ```

  then `6α^−1 n` cycles and edges suffice.

The extra logarithmic factor in the available cycle length makes the charges over density scales summable. This is a different sufficient mechanism from requiring every cycle in the final partition to be long. The dense result's dependence on α cannot be read as a universal constant for arbitrary minimum degree δ.

### 2.4 Dense cycle decompositions control count, not minimum cycle length

**António Girão, Bertille Granet, Daniela Kühn, Deryk Osthus, _Path and cycle decompositions of dense graphs_, arXiv:1911.05501.**

Source: `/corpus/src/1911.05501/Introduction.tex`, theorem `n/2`, lines 117–122, and the subsequent Δ/2 theorem.

For fixed positive density and sufficiently large order, an Eulerian graph of linear minimum degree has a decomposition into at most `n/2 + εn` cycles. Stronger density/quasirandomness hypotheses give a bound near `Δ/2`. These statements do not say that every cycle in the chosen decomposition has length Ω(δ), or constant reciprocal-degree mass.

Section 3 below shows why a count-optimality assertion alone cannot be used to infer such a minimum-weight statement.

### 2.5 Two important near misses

**Vytautas Gruslys, Shoham Letzter, _Cycle partitions of regular graphs_, arXiv:1808.00851.**

Source: `/corpus/src/1808.00851/path-partition-v7.tex`, theorem `main`, lines 120–124. For `d ≥ αn`, it partitions **V(G)** into at most `n/(d+1)` cycles. It is not an edge decomposition and cannot be substituted for L(c).

**Tien-Nam Le, _Locally self-avoiding eulerian tours_, arXiv:1611.07486.**

Source: `/corpus/src/1611.07486/1611.07486.tex`, conjecture at lines 27–29, theorem at lines 40–44, and corollary at lines 65–68.

For each fixed ℓ there is a degree threshold d_ℓ such that every even connected graph of minimum degree at least d_ℓ has an Euler tour with no short *consecutive subcycle* of length at most ℓ. Cutting it into consecutive chunks gives long **paths**. It does not give an edge partition into long simple cycles: after a loop is removed, formerly nonconsecutive edges become consecutive. Nor does the theorem state a linear bound on d_ℓ.

Indeed, for unrestricted even graphs the articulation-triangle construction from the question, with sufficiently large odd cliques attached at its three vertices, has high minimum degree and a compulsory triangle in every cycle partition. It still satisfies the locally-self-avoiding-tour theorem. Thus the general inference from that tour theorem to an all-long cycle partition is demonstrably invalid.

### 2.6 Further relevant sources

* **Andrea Jiménez, Yoshiko Wakabayashi, _On path-cycle decompositions of triangle-free graphs_, arXiv:1402.3741.** `/corpus/src/1402.3741/Gallai-3jun2015.tex`. This really studies minimum-length-constrained decompositions, but its pieces may be paths and the main length threshold is 4 under triangle-free/odd-distance hypotheses. It does not establish L(c).
* **Irene Heinrich, Manuel Streicher, _Cycle Decompositions and Constructive Characterizations_, arXiv:1708.09141.** `/corpus/src/1708.09141/heinrichStreicherCycleDecompositionsAndConstructiveCharacterizations.tex`. It characterizes graphs whose cycle-decomposition cardinality is unique, using the existence of two edge-disjoint cycles sharing at least three vertices. This is useful context for exchange arguments, not an all-heavy partition theorem.
* **Ashwin Ganesan, _Cayley graphs and symmetric interconnection networks_, arXiv:1703.08109.** `/corpus/src/1703.08109/RMSlecturenotesv7.tex`, lines 1030–1036. It states and proves the Watkins theorem that a finite connected edge-transitive graph has vertex-connectivity equal to its minimum degree. This standard theorem is the connectivity input in Section 4. The same fact is independently stated in `/corpus/src/1006.5129/1006.5129.tex`, lines 39–44.

No inspected source supplied W(c) or L(c) with an absolute positive c.

---

## 3. Iteration I: an exactly count-optimal partition can contain an arbitrarily light triangle

### Proposition 3.1

There are 3-connected even simple graphs G with `δ(G) → ∞` and minimum-cardinality cycle partitions D for which

```
min_{C in D} |C|/δ(G) → 0,
min_{C in D} w_G(C) → 0.
```

This refutes the assertion about **an arbitrary count-minimizing partition**, not the existence of a different all-heavy partition.

### Construction

Let k ≥ 2 and let t ≥ 2 be even. Take a core triangle on `a,b,c`, take k vertex-disjoint copies `B_i` of `K_t`, and join every vertex of every B_i to all three core vertices. Thus

```
G = K_3 join (k disjoint copies of K_t),
n = kt + 3,
d(v) = t+2       for v outside the core,
d(a)=d(b)=d(c) = kt+2.                                     (3.1)
```

All degrees are even. Deleting at most two vertices leaves a core vertex which is adjacent to every remaining outside vertex, so G remains connected. Deleting all three core vertices separates the k cliques. Hence

```
κ(G)=3,                 δ(G)=t+2.
```

The fact that t can tend to infinity is important: this is not just a bounded-minimum-degree extension of the known kK₂ example.

### The exact partition

Decompose each `K_t`, for t = 2m, into m Hamilton paths

```
P_{i,j} : x_{i,j} ... y_{i,j},      j=0,...,m−1,
```

such that every vertex is an endpoint of exactly one path. This is the usual Hamilton-path form of Walecki's decomposition. One completely explicit formula, on vertices modulo 2m, is

```
P_j = j, j−1, j+1, j−2, j+2, ..., j−(m−1), j+(m−1), j−m.
```

For completeness, the consecutive pairs of P_j are precisely the unordered pairs whose endpoint sum is `2j−1` or `2j` modulo 2m. There are respectively m and m−1 such non-loop pairs. As j varies these sum classes partition all pairs, proving the edge decomposition; the endpoint pairs are `{j,j+m}`, proving the endpoint assertion.

For indices i modulo k, take the cycles

```
C_{i,j} = a P_{i,j} b x_{i+1,j} c y_{i+1,j} a,             (3.2)
```

and also take the core triangle `abc`.

Each cycle in (3.2) is simple: its Hamilton path is in B_i and its two extra outside vertices are in the distinct clique B_{i+1}.

The edge-partition check is exact:

* Inside B_i, all edges occur once among the P_{i,j}.
* A vertex x_{i,j} uses its edge to a as a path endpoint; as the singleton in a previous-clique cycle, it uses its edges to b and c.
* A vertex y_{i,j} similarly uses its edge to b as an endpoint, and its edges to c and a as a singleton.
* Only `abc` uses core-core edges.

There are exactly

```
q = kt/2 + 1
```

cycles. Every partition needs at least `d(a)/2 = kt/2+1` cycles, since a simple cycle uses at most two edges at a. Thus this partition has **minimum possible cardinality**, in fact `(n−1)/2`.

### Weights and limiting behavior

The core triangle has

```
|abc|/δ(G) = 3/(t+2),
w_G(abc) = 3/(kt+2).                                      (3.3)
```

Each other cycle has t+2 outside vertices and all three core vertices, so

```
|C_{i,j}| = t+5,
w_G(C_{i,j}) = 1 + 3/(kt+2) > 1.                          (3.4)
```

Letting t tend to infinity, even with k fixed at 2, proves Proposition 3.1.

It also gives a precise frozen-weight greedy failure: remove all cycles (3.2), each of weight greater than 1 in the original degrees. The residual graph is the triangle (3.3), whose original-degree weight is arbitrarily small. This is not an O(n)-count obstruction—the displayed partition is already optimal—but it prevents an induction from treating every residual graph as if its current heavy-cycle theorem supplied original-degree mass.

**What this does not refute:** minimizing cardinality *and then* optimizing the shortest cycle, or W(c), or L(c). The quantifier “some optimal partition is bad” must not be replaced by “every partition is bad.”

The known upper obstruction on c is also recovered correctly, with its original quantifier. For t=2, every partition has at least k+1 cycles and a total of 4k outside-vertex occurrences. Some cycle has at most three outside vertices, so its weight is at most `3/4 + 3/(2k+2)`. Letting k grow rules out W(c) for c>3/4. For general t, the same pigeonhole argument only gives an outside count at most t+1 and weight at most

```
(t+1)/(t+2) + 3/(kt+2).
```

As t increases this bound approaches 1, not 0. Merely enlarging the attached cliques therefore does not amplify the known all-partitions obstruction to refute small c.

---

## 4. Iteration II: arbitrarily large exchange barriers in maximally connected regular graphs

The next construction rules out a bounded repair mechanism much more decisively than a two-cycle example.

### Theorem 4.1 — immovable light triangle partitions

For every positive integer r and every sufficiently large positive integer d, there is a finite connected simple graph G and a triangle partition T such that

```
δ(G)=Δ(G)=κ(G)=2d,
|T| = nd/3,
w_G(Triangle) = 3/(2d),                                   (4.1)
```

and the following holds:

> For any subfamily of at most r triangles of T, the union of its edges has exactly one simple-cycle partition: those same triangles.

Thus no exchange using at most r existing cycles can change this partition, even if the exchange may introduce an arbitrary number of replacement cycles and need not improve any particular objective.

The finite group in the proof is explicitly constructed using permutations of a finite set; no unproved residual-finiteness assertion or probabilistic connectivity assertion is needed. The only imported connectivity theorem is Watkins' theorem quoted in Section 2.6.

### 4.1 Finite permutations with no short reduced relations

Fix an integer R ≥ max(r, 3). Start with the reduced-word notation for the free product of d cyclic groups of order 3:

```
F = <a_1,...,a_d | a_i^3=1>.
```

A reduced word has syllables `a_i` or `a_i²`, with different indices on consecutive syllables. Let W be the finite set of reduced words of syllable length at most R, including the empty word.

For each i, define a permutation p_i of W as follows. For every word w of length less than R whose last index is not i, including the empty word, cycle the triple

```
w -> w a_i -> w a_i² -> w.
```

These triples are disjoint. Fix the remaining words, which are precisely the words of length R whose last index is not i. Therefore p_i is a permutation of order 3.

Let Γ be the finite permutation group generated by the p_i. Regard the permutations as acting on the right, so multiplication follows the written sequence of applications.

**Short-relation property.** No nonempty reduced word of syllable length at most R in the p_i is the identity permutation. To see this, apply it to the empty word. Every successive prefix lies in W, and the permutations perform exactly the corresponding reduced-word multiplication. The empty word is sent to that nonempty reduced word.

This also ensures that the `2d` permutations `p_i,p_i²` are all distinct, once R ≥ 2.

### 4.2 Cayley graph and triangle incidence girth

Let

```
G = Cay(Γ, {p_i,p_i² : 1≤i≤d}).
```

It is a finite connected simple `2d`-regular graph. For each i, the cosets

```
g <p_i> = {g, g p_i, g p_i²}
```

are triangles. Every edge belongs to exactly one of these triangles. They give the partition T. Every vertex is in exactly d triangles, so `3|T|=nd`.

Let B be the bipartite incidence graph whose two classes are the vertices of G and the triangles of T. Its degrees are d on the first side and 3 on the second.

Suppose B had a cycle involving k triangle nodes, with k ≤ R. Following its successive vertex-to-vertex steps gives a relation

```
p_{i_1}^{ε_1} p_{i_2}^{ε_2} ... p_{i_k}^{ε_k} = 1,
ε_j in {1,2}.
```

Consecutive indices differ: distinct cosets of the same order-3 subgroup cannot meet. Thus this is a nonempty reduced word of syllable length k, contradicting the short-relation property. Consequently

```
girth(B) > 2R.                                            (4.2)
```

In particular, the triangles meet pairwise in at most one vertex.

There is another consequence needed later:

> Every simple cycle of G of length at most R is one of the designated triangles.

Indeed, a simple cycle other than a designated triangle uses either one edge or a consecutive two-edge path in each triangle it visits. It cannot use two separated edge segments of the same triangle, since those edges share a vertex. Compressing each such segment to the incidence step through its triangle produces an incidence cycle with at most as many triangle nodes as the original cycle had edges. This contradicts (4.2).

### 4.3 Connectivity is maximal, not merely three

Permuting the generator indices, and independently replacing any a_i by a_i², permutes W and conjugates the p_i to the corresponding relabelled or inverted generators. These conjugations preserve Γ. Hence the stabilizer of the identity in the resulting Cayley graph acts transitively on its `2d` neighbors. Together with translations of Γ, this makes G arc-transitive and therefore edge-transitive.

The finite connected edge-transitive connectivity theorem gives

```
κ(G)=δ(G)=2d.                                             (4.3)
```

Thus neither articulations, 2-separators, nor even a small fixed vertex separator explain this obstruction.

### 4.4 Why every small exchange is literally impossible

Take at most r designated triangles. Their incidence graph is a forest, because an incidence cycle in it would involve at most r ≤ R triangle nodes. Equivalently, their union is a cactus whose cycle blocks are exactly the chosen triangles. Its only simple cycles are those triangles.

Every edge must be covered, so its only cycle partition is the original one. This proves the exchange assertion.

For any proposed positive heavy threshold c, choose d with `3/(2d)<c`. All the cycles are then light, and yet none can be repaired by an r-cycle exchange. Also

```
|T|/n = d/3 -> infinity.
```

So a uniformly bounded exchange search is not even guaranteed to reach an O(n)-piece decomposition from an arbitrary initial cycle partition.

More strongly, suppose an exchange bound is prescribed as some finite function `r(δ)`, or a function of δ and Δ. Fix a sufficiently large d first and then choose `R ≥ r(2d)` (respectively `R ≥ r(2d,2d)`). The same proof defeats that bound. The order n is allowed to become very large.

**Scope:** this refutes a repair lemma starting from an arbitrary partition. It does not refute a proof that begins with a globally optimized partition, uses exchanges whose sizes depend on the graph, or constructs the target partition by a different method.

---

## 5. Iteration III: the exchange-barrier family nevertheless has an all-heavy partition

This closes a possible logical loophole in using Theorem 4.1 as a purported counterexample to W(c).

### Lemma 5.1 — a balanced transitive orientation of regular triangle systems

Suppose the edges of a simple graph are partitioned into triangles and every vertex lies in exactly `3a` of those triangles. There is an Eulerian orientation of the graph in which every designated triangle is transitively oriented.

**Proof.** Assign to each triangle one of its vertices as its middle vertex, so that every graph vertex is assigned exactly a times. This is a capacitated matching problem, and Hall's condition holds. For any set U of triangle nodes,

```
3|U| ≤ 3a |N(U)|,
```

so `|U| ≤ a|N(U)|`. Replace each graph vertex by a clones and apply ordinary Hall. There are exactly an triangles and an clones, so all capacities are filled.

In each triangle select the edge joining its two non-middle vertices. The selected edges form a simple graph F. A vertex is in `3a` triangles and is the middle in a, so

```
d_F(v)=2a.
```

Orient F Eulerianly, component by component. If its selected edge in a triangle is oriented `u -> v` and the middle is m, orient the whole triangle as

```
u -> v,       u -> m,       m -> v.                        (5.1)
```

This is transitive. At every vertex the outdegree-minus-indegree contribution in the full graph is twice its contribution in F; middle occurrences contribute zero. Hence the full orientation is Eulerian. □

### Corollary 5.2 — all cycles can have weight greater than 1

In Section 4 take

```
d=3a,                 R ≥ max(r,2d).
```

Apply Lemma 5.1. Every undirected cycle of length at most R is a designated triangle, and no designated triangle is directed cyclically. Thus every directed simple cycle in the orientation has length greater than R.

A finite balanced digraph has an edge partition into directed simple cycles: repeatedly remove a directed cycle, preserving balance. Applied here and then forgetting orientations, this yields a cycle partition D_good with

```
|C| ≥ R+1,
w_G(C) = |C|/(2d) ≥ (R+1)/(2d) > 1,
|D_good| ≤ nd/(R+1) < n/2.                                (5.2)
```

Compare this with the immovable triangle partition:

```
D_bad:  n d/3 cycles, every weight 3/(2d);
D_good: fewer than n/2 cycles, every weight greater than 1.
```

Both statements hold for the **same maximally connected regular graph**. For any fixed positive c and any bounded or degree-dependent exchange size, choose d sufficiently large and then R sufficiently large. Taking R also larger than 2dc makes the good partition exceed the particular threshold c. This produces a completely verified failure of that local repair principle while simultaneously certifying a good partition.

The orientation argument is specific to this triangle-system structure. It does not orient an arbitrary graph so that all its directed cycles are long, and it is not a proof of L(c) for general graphs.

### 5.3 A nonregular weighted sufficient condition

Regularity is not essential to Lemma 5.1. If vertex v belongs to `3a_v` designated triangles, with integer a_v, use a_v clones of v. Hall follows from `3|U| ≤ sum_{v in N(U)} 3a_v`, and the selected graph has even degrees `2a_v`. The same balanced transitive orientation follows. Equivalently, this applies to triangle-partitioned graphs whose degrees are all divisible by 6.

Consequently, if in such a graph **every cycle of original-degree weight less than c is one of the designated triangles**, the resulting directed-cycle partition proves W(c) for that graph. This is a genuine weighted sufficient condition with no bounded degree-ratio assumption. The unproved issue in general is obtaining that special structure of the light cycles, not the orientation once the structure is supplied.

---

## 6. A valid weighted shortest-cycle exchange: clean rings

Here is a positive local statement with its exact simplicity and weight requirements.

### Lemma 6.1 — paired-arc balancing

Let `C_1,...,C_s`, with s ≥ 3, be edge-disjoint cycles forming a clean cyclic necklace:

* C_i and C_{i+1} meet in one vertex x_i, with indices modulo s;
* the x_i are distinct;
* there are no other intersections between different cycles.

For s=3 this means each pair meets in its designated distinct connector. Give the edges arbitrary nonnegative additive weights. Split C_i into its two `x_{i−1}`–`x_i` arcs with weights a_i,b_i, and put

```
T = sum_i (a_i+b_i),
D = max_i |a_i−b_i|.
```

The union has a partition into two simple cycles Q_1,Q_2 satisfying

```
min(w(Q_1), w(Q_2)) ≥ (T−D)/2
                    ≥ (T−max_i w(C_i))/2.                 (6.1)
```

**Proof.** Choose one arc from each C_i for Q_1 and the complementary arcs for Q_2. The clean-ring hypothesis ensures that both are simple cycles and that they partition all selected edges. To balance their weights, process the arc pairs one at a time, assigning the heavier arc to the currently lighter total. If the current discrepancy is z and the new pair difference is b−a ≥ 0, the new discrepancy is `|z−(b−a)|`. Induction bounds the final discrepancy by D. Their total is T, proving (6.1). □

### Consequence for a global shortest-cycle objective

Suppose all selected cycles have weight at least m>0, and at least one has weight exactly m. Then, for s ≥ 3, both replacement cycles have weight at least m.

* If there is exactly one old cycle of weight m, the other selected cycles have larger weight. The last bound in (6.1) is then strictly greater than m, so neither replacement has weight m.
* If at least two old cycles have weight m, at most one replacement can have weight m, since their total is at least `3m`.

Thus the number of globally minimum-weight cycles decreases, without creating a lighter cycle. This is a genuine lexicographic improvement. Using unit edge weights gives the corresponding shortest-length improvement. Using

```
a(uv) = (1/d_G(u)+1/d_G(v))/2
```

gives the original-degree vertex-weight version exactly.

### Why this still does not prove W(c) or L(c)

A general cycle partition need not have clean intersections. The hypothesis cannot be replaced just by “the union is Eulerian,” since splitting an Eulerian closed trail may create many small simple cycles.

Furthermore, after a clean-ring exchange the two new cycles share *all* the ring connectors. Thus the linear-intersection hypothesis is not preserved by iteration. A global shortest-cycle proof must address these larger intersections, not silently reapply the lemma.

In the family of Section 4, the initial incidence graph has no cycle of bounded size. A shortest incidence cycle does give a clean ring, but its number of old cycles is greater than R. The positive exchange and the negative bounded-exchange theorem therefore fit together: the needed exchange can exist while being arbitrarily large relative to any prescribed degree-only bound.

---

## 7. Verification and finite experiments

The theorems above are proved for the entire parameter families. The following computations were supplementary checks, not substitutes for the asymptotic proofs.

### 7.1 Exact finite bottleneck search

For a finite graph, all simple cycles were enumerated once. A candidate threshold w was tested by exact-cover backtracking on edge bitmasks, restricted to cycles of original-degree weight at least w. All weights were rational. Binary search over the finite set of cycle weights computed

```
max_{cycle partitions D} min_{C in D} w_G(C).
```

Results:

* All **10** 3-connected even graphs in the NetworkX graph atlas, through order 7, were checked. The smallest optimum was **1**.
* **36** additional generated even 3-connected graphs of orders 8 and 9 were checked. The smallest optimum in that sample was **25/24**.
* Every returned witness was independently checked against the saved graph6 graph: simple cycles, no repeated or missing edges, and the claimed minimum rational weight.

These small searches neither improve nor challenge the known asymptotic `3/4` upper obstruction. In particular they are not evidence that an untested small constant is proved.

### 7.2 The high-minimum-degree count-optimal family

The explicit Hamilton-path and cycle formulas of Section 3 were checked for all 24 pairs

```
k in {2,3,4,7},       t in {2,4,6,10,20,40}.
```

Checks included exact edge coverage, cycle simplicity, all degree formulas, the count `Δ/2`, every weight, and the total weight `n/2`. Vertex-connectivity was also computed for the cases of order at most 45; the direct deletion argument proves it for all parameters.

### 7.3 Finite-ball permutation checks

The finite permutation construction was tested at

| d | R | size of W | nonempty reduced words checked |
|---:|---:|---:|---:|
| 2 | 2 | 13 | 12 |
| 2 | 5 | 125 | 124 |
| 3 | 3 | 127 | 126 |
| 3 | 5 | 2047 | 2046 |
| 5 | 3 | 731 | 730 |

For each instance, every p_i was checked to be a permutation with cube equal to the identity. Applying every reduced word in W to the empty word gave its own word index. Generator relabelling and generator inversion were checked to conjugate the permutations as claimed.

### 7.4 A fully generated 2520-vertex example

For d=3 and the radius-1 permutation construction, the generated group has order 2520. Although radius 1 only promises avoidance of relations of syllable length 1, the actual triangle-incidence graph in this example has girth **16**. Consequently its 2520-triangle partition is immutable under exchanges of at most **7** original cycles.

The complete graph and triangle partition were generated and checked. The matching construction of Lemma 5.1 produced an Eulerian orientation; all designated triangles were checked to be transitive, and all actual graph triangles were checked to be designated ones.

With `PYTHONHASHSEED=0`, the resulting directed-cycle extraction gave:

```
n = 2520,       degree = 6,       number of edges = 7560,
number of good cycles = 185,
minimum good cycle length = 8,
maximum good cycle length = 140,
minimum good cycle weight = 8/6 = 4/3,
sum of good cycle weights = 1260 = n/2.
```

The extracted cycles were checked to partition all edges exactly. The girth computation can be rooted at the identity vertex because translations act transitively on the graph-vertex side of the incidence graph.

The graph's maximal vertex-connectivity follows from the symmetry proof and Watkins' theorem; a large all-pairs connectivity computation was not used as a replacement for that proof.

### 7.5 Weighted balancing checks

The paired-arc greedy balancing inequality and the strict decrease in the number of minimum-weight cycles were tested on **10,800** exact-rational instances, with ring sizes 3 through 11. All checks passed.

### 7.6 Reproduction artifacts

The research scripts and results are retained in this workspace at:

* `/tmp/heavy_search.py` — exhaustive cycle enumeration and exact-cover bottleneck search;
* `/tmp/heavy_atlas_results.json` and `/tmp/heavy_random_results.json` — graphs, optimum values, and witness partitions;
* `/tmp/heavy_verify.py` — Section 3 formulas, finite permutations, and the fully generated matching/orientation example;
* `/tmp/heavy_verify_results.json` — the latter checks' output;
* `/tmp/heavy_metadata.json`, `/tmp/heavy_graph_sources.json`, and `/tmp/heavy_text_hits.txt` — bibliography/search records.

The main structural checker is run as

```
PYTHONHASHSEED=0 python3 /tmp/heavy_verify.py
```

Its SHA-256 is

```
6e550950e2f462cbbcee195ae2801b6e3c5a054ff4cf3e94cd75607ef90511ac
```

These temporary artifacts are supplementary. The definitions, constructions, and proofs needed for the mathematical conclusions are all given above, rather than relying on temporary files remaining available.

---

## 8. What remains, and what the next proof would need

### Established negative conclusions

* An arbitrary minimum-cardinality partition need not have even one uniform positive lower bound on its smallest original-degree weight or its smallest length divided by δ.
* From an arbitrary partition, no bound on the number of cycles used by a successful light-cycle repair can depend only on δ and Δ. This remains false when `κ=δ=Δ` and all degrees tend to infinity.
* Single-heavy-cycle existence, dense count bounds, vertex-cycle partitions, and locally self-avoiding Euler tours do not by themselves establish simultaneous heaviness.

### Established positive tools

* The reciprocal-degree edge-weight conversion makes the single-cycle Bondy–Fan theorem and the clean-ring exchange directly applicable.
* The weighted clean-ring lemma is a correct global-shortest-cycle improvement when its exact intersection hypothesis holds.
* Regular triangle systems with every vertex in a multiple of three triangles admit the balanced transitive orientation of Lemma 5.1. When the only short cycles are those designated triangles, this yields an all-long decomposition.

### Still unresolved

Neither a proof of W(c) or L(c), nor a family forcing `min_C w_G(C) -> 0` **in every partition**, was obtained. The known `c > 3/4` obstruction remains a restriction on possible constants, not a refutation of every positive c.

A viable shortest-cycle argument now has a more precise remaining burden:

1. handle partitions in which the short cycle meets other cycles in multiple vertices;
2. allow exchange regions of unbounded size, rather than postulating a two-, three-, or degree-bounded-cycle repair;
3. control the simplicity and weights of all replacement cycles, not just the weight of an Eulerian union;
4. either establish a global structural contradiction for a light cycle in a genuinely lexicographically optimized partition, or provide a different simultaneous construction.

The new examples do not kill the original heavy-cycle route. They decisively rule out two natural shortcuts, and the all-heavy orientation of the exchange-barrier family demonstrates that those shortcuts can fail even when the desired conclusion is strongly true.
