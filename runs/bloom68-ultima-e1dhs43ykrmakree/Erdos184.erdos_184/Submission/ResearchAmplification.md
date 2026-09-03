# Amplifying integral obstructions: shared-coordinate cancellation and clone repairs

## Status

**No disproof of Erdős–Gallai is obtained.** No family with an unbounded minimum cycle/singleton count divided by its order is constructed. Arbitrary asymmetric shared-vertex transition systems remain unresolved. A concrete fully shared Petersen-layer amplification is, however, constructed and then **globally repaired**, ruling it out rigorously.

These are new results relative to the saved research notes, not claims of literature priority. They are paper-level proofs, not Lean formalizations. `Spec.lean` and all 21 preexisting Submission files were preserved.

The main results are:

1. **A genuine shared-vertex amplification attempt fails by global cancellation.** For `k>=2`, the simple graph `A_k` places k edge-disjoint copies of `R_(14^(k-1))` on exactly the same `14^k` vertices. It has degree `4k` and `c_f=2k`. Combining the individually minimum layer partitions costs `k(14^(k-1)+2)`, whose count/order ratio tends to infinity. But an explicit mixed-coordinate repair gives

   ```
   c(A_k) <= 2k + [14^k+3*12^k-4*11^k]/6 <= 14^k/3.
   ```

   This is an actual simple-cycle partition. The proof globally regroups the residual triangles using an elementary torus construction. More generally it proves a Cartesian-power theorem for uniform cycle factors, and in particular

   ```
   c(R_t^{square k}) < (5/12)(14t)^k                 [all t>=2, k>=1].
   ```

   Thus letting both the ring size and the number of Cartesian factors grow does not amplify the minimum ratio either.

2. **The Petersen-ring gap disappears under complete even cloning.** For every `t>=2, s>=1`,

   ```
   |V(R_t[2s])| = 28ts,
   c(R_t[2s]) = c_f(R_t[2s]) = 4s.
   ```

   The partition consists of **4s Hamilton cycles**; `c/n=1/(7t)`. Degree certifies the optimum against all partitions. The same repair works for any edge-disjoint shared-vertex overlay of the relevant four-Hamilton double covers; in particular `c(A_k[2s])=c_f(A_k[2s])=4ks`.

3. **An exact binary phase calculation.** For a labelled cycle double cover with q occurrences, form the multigraph J recording which two occurrences cover each edge. The exact optimum in the matching-lift construction on two clones is

   ```
   q + epsilon,
   epsilon = number of components K of J with |E(K)| != |V(K)| (mod 2).
   ```

   A parity-orientation algorithm constructs actual simple cycles. The Petersen systems have `epsilon=0`. **A positive epsilon is not a lower bound for unrestricted partitions:** an explicit odd-cycle example is repaired more cheaply by turns between clone fibres.

4. **Uniform cloning cannot amplify the ratio.** For every even simple G and integer `a>=1`,

   ```
   c(G[a]) <= a c(G).
   ```

   A self-contained Hamilton decomposition of `C_l[a]` for every `l>=3, a>=1` proves this. After division by order, no loss constant accumulates over repeated uniform blow-ups.

5. **Even twin fibres have a base-independent bound.** Every independent-set blow-up H with positive even fibre sizes satisfies `c(H)<=|V(H)|/2`, including nonuniform fibres and arbitrary base graphs. This uses the classical Lovász path/cycle theorem and explicit two-clone factorizations of paths and cycles.

6. **Complete transition libraries cannot amplify via line graphs.** Every even simple line graph satisfies `c(G)<=r(G)`. Every line graph, even or not, has a cycle/singleton partition of size at most `2|V(G)|`. More precise constructive component counts are proved below; no bounded-host-degree assumption is made.

The checker is `ResearchAmplificationCheck.py`. It uses exact edge-set identities and finite exhaustive checks, not random counterexample search or numerical optimization. The Cartesian repairs are proved constructively; no external Hamilton-decomposition theorem for products is assumed.

---

## 0. Conventions and the exact target

Graphs are finite, simple and undirected. A cycle is simple, with length at least three. All partitions are **edge partitions**. Write

```
p(G) = minimum number of simple cycles and singleton edges in a partition;
c(G) = minimum number of simple cycles in a partition, when G is even;
c_f(G) = minimum exact fractional cycle-partition mass, when G is even;
r(G) = |V(G)| - number_of_components(G), including isolated components.
```

Empty edge sets have cost zero. For a positive integer a, `G[a]` has vertex set `V(G) x Z_a`, no edges inside any fibre, and all a² edges between the fibres of u and v whenever `uv in E(G)`. In particular, **this is a complete independent-set blow-up, not a graph cover, an arbitrary partial blow-up, or a multigraph of parallel edges.** It is simple; `d_(G[a])(v,i)=a d_G(v)`.

### Lemma 0.1 — singleton edges do not help on an even graph

For an even graph, `p(G)=c(G)` exactly, not just up to constants.

**Proof.** In any cycle/singleton partition, the singleton remainder is even, since deleting the cycle pieces preserves all degree parities. If it has s edges, decompose it into simple cycles; there are at most `s/3` such cycles. Replacing the singleton pieces cannot increase the count, and strictly decreases it if `s>0`. Conversely every cycle partition is allowed in p. ∎

Thus the exact pure-cycle optima below also answer the cycle/singleton question for these graphs. The general parity-forest reduction from the previous notes still handles non-even graphs.

The audited inequality `c_f(G)<=r(G)` from `ResearchFractional.md` is not strengthened by an integrality assertion here. In fact none of the new upper constructions requires it. It explains why a linear edge-price certificate valid for all cycles cannot itself prove the desired superlinear lower bound: such a certificate is bounded by `c_f<=r`.

---

## 1. Binary clone phases: an exact solvable constraint system

A **labelled cycle double cover** is a list `C_1,...,C_q` of simple cycles of a graph G such that every edge occurs exactly twice. Repeated cycles are allowed as distinct list occurrences. G need not be even for this section; `G[2]` is always even.

Form a loopless multigraph J on `{1,...,q}`. An original edge e is one labelled edge of J, joining the two occurrences containing e. Parallel edges in J are allowed. They are bookkeeping edges, not parallel edges in the graph being decomposed. Every node i of J has degree `|C_i|`, so J has no isolated nodes unless the cover is empty.

Over each original edge `uv`, the four edges in `G[2]` split into exactly two perfect matchings:

```
parallel: {(u,0)(v,0), (u,1)(v,1)};
crossed:  {(u,0)(v,1), (u,1)(v,0)}.                         (1.1)
```

Give one matching to each of the two occurrences containing e. For each `C_i`, its assigned matchings form a 2-regular graph on the two clones of `V(C_i)`. Call this a **matching lift**. All these matching lifts together partition every edge of `G[2]`.

### Theorem 1.1 — exact matching-lift cost

Let

```
epsilon(J) = #{connected components K of J:
                 |E(K)| not congruent to |V(K)| modulo 2}.
```

The minimum total number of simple cycle components of all the matching lifts is exactly

```
q + epsilon(J).                                             (1.2)
```

In particular,

```
c(G[2]) <= q + epsilon(J).                                  (1.3)
```

**Proof.** Orient a bookkeeping edge of J toward the occurrence receiving its crossed matching. At occurrence i, one turn around the old cycle switches the clone bit exactly `indegree_J(i)` times. Therefore its matching lift is:

* one simple cycle of length `2|C_i|` if the indegree is odd;
* two simple cycles, each of length `|C_i|`, if the indegree is even.

This is a precise monodromy calculation: the old vertices are distinct, and a clone is revisited only after either one or two full turns. All resulting cycles have length at least three. The total cost is consequently

```
q + #{nodes of even indegree}.                              (1.4)
```

In any connected component K, the sum of the indegrees is `|E(K)|`. Making every indegree odd requires `|E(K)|=|V(K)| (mod 2)`. If these parities differ, at least one node must have even indegree.

These conditions are sufficient with exactly that many exceptional nodes. Prescribe odd indegree at every node, except prescribe even indegree at one chosen node of each deficient component. The sum of the prescribed parities now equals the edge-count parity componentwise. Take a spanning tree, orient every non-tree edge arbitrarily, and process tree leaves toward the root. There is a unique choice for the parent edge that supplies the prescribed parity at each processed leaf. The last root equation follows from the component parity. This constructs an orientation with zero or one even-indegree node per component, as required.

Together with (1.4), this proves the exact restricted optimum and the unrestricted upper bound. ∎

This construction coordinates choices over arbitrarily many original vertices; it does not prescribe independent matchings at those vertices and hope they sew simply. The returned objects are already connected, 2-regular simple subgraphs on labelled clones.

### Corollary 1.2 — Hamilton double covers with compatible parity

Suppose every `C_i` is Hamilton, and every component of J has compatible parity. Then `G[2]` has a Hamilton decomposition with exactly q cycles, and

```
c(G[2]) = c_f(G[2]) = q.                                   (1.5)
```

**Proof.** A Hamilton double cover with q occurrences forces G to be q-regular: at each vertex it supplies `2q` cycle incidences, which cover each incident edge twice. Thus `G[2]` is `2q`-regular. Theorem 1.1 supplies q Hamilton cycles. Every simple cycle uses at most two edges at any fixed vertex, so every integral partition and every exact fractional partition has cost at least q. ∎

This degree certificate is valid for **every** simple cycle, including cycles absent from the double cover and cycles that do not project to old cycles.

---

## 2. The Petersen ring loses its entire gap

Use the graph and four Hamilton cycles already specified and proved in `ResearchRounding.md`, Sections 5–6. For reference:

```
R_t: 14t vertices, 28t edges, degree 4;
c(R_t)=t+2,                    c_f(R_t)=2;
four Hamilton cycles, each original edge occurring in exactly two.  (2.1)
```

The construction takes t copies of `L(Petersen)-root`, joins the two right ports of one copy to the two left ports of the next, and uses the four seed paths in the prior note. Nothing about the previous global lower bound is replaced by an algorithmic/local-optimum assertion here.

### Theorem 2.1 — exact doubling repair

For every `t>=2`, `R_t[2]` has a partition into four Hamilton cycles. Hence

```
|V(R_t[2])|=28t,              c(R_t[2])=c_f(R_t[2])=4.       (2.2)
```

**Proof.** The double-cover multigraph J has four nodes, all of degree `14t`, and no loops or isolated nodes. Thus its component node counts are either 4, or 2 and 2. In a component on k nodes,

```
|E(K)| = 14t k/2 = 7tk.
```

Both k and this edge count are even. Every component therefore passes the parity test of Theorem 1.1. Its algorithm constructs four Hamilton cycles on the clones. Degree eight proves the lower bound four for both c and `c_f`. ∎

No enumeration of all cycles of the large graph is needed for this lower bound. The upper certificate is an explicit exact partition, constructed by the spanning-tree parity procedure of Section 1.

### Shared-colour version

Let `b>=1`, and let G be the edge-disjoint union of b spanning 4-regular graphs on a common **even** number N of vertices. Suppose each of these graphs has a double cover by four Hamilton cycles. Their vertex labellings and overlap patterns are arbitrary; only their edge sets must be disjoint.

The concatenated double cover has `4b` occurrences. Its bookkeeping multigraph is the disjoint union of the four-node systems above, because an original edge belongs to exactly one input layer. Thus

```
G[2] has 4b Hamilton cycles,
c(G[2])=c_f(G[2])=4b.                                       (2.3)
```

In particular, this applies to any edge-disjoint superposition of relabelled Petersen rings on the same even vertex set, if such a superposition is the input. **No alignment of the layers' old transition choices is required.** The phase equations, not the old gadget count, determine the repair.

This does not assert that the original un-cloned superposition has a cheap partition. Projecting the new Hamilton cycles back would cover old edges with multiplicity and revisit original vertices. Dividing that cover is exactly an integral-rounding issue, not a valid reverse implication.

### A fully shared, algebraic Petersen-layer family

The shared-colour hypothesis can be realized with an arbitrarily large number of **genuine Petersen-ring layers**, not merely layers that already have Hamilton decompositions.

For `k>=2`, put `T=14^(k-1)` and use the same `N=14^k` vertices `Z_14^k` for every layer. For each coordinate i, make a copy of `R_T` as follows. A block label `b in {0,...,T-1}` is written in base 14 in the other `k-1` coordinates, in their fixed order. The internal vertex label `v in {1,...,14}` becomes coordinate `v-1` in position i. This is a bijection from `V(R_T)` to the common vertex set. Let `A_k` be the union of these k relabelled rings.

**The layers are edge-disjoint.** An internal block edge changes only its layer coordinate i. A connector, oriented from block b to block `b+1`, changes coordinate i by `-2 (mod 14)`, because its port pair is `3 -> 1` or `4 -> 2`. In each other coordinate it changes by 0 or `+1 (mod 14)`, with at least one `+1`: these are exactly the base-14 increment/carry rules, including wraparound. Thus a connector changes at least two coordinates and cannot equal any internal edge. Connectors in layers i and j cannot coincide, even with opposite directions: in coordinate i their changes would require `-2` to equal one of `0,+1,-1 (mod 14)`. Internal edges in different layers are plainly distinct. This proves simplicity and edge-disjointness for all k.

Consequently the following are rigorous:

```
|V(A_k)|=14^k,                  d(A_k)=4k,
c_f(A_k)=2k,
there is a supplied partition with k(14^(k-1)+2) cycles,
c(A_k[2s])=c_f(A_k[2s])=4ks       [every s>=1].             (2.4)
```

The fractional equality follows from the combined `4k` Hamilton double-cover occurrences and the degree lower bound. The supplied integral partition is the union of the proved minimum partitions of the individual layers. The clone equality follows from (2.3) and Section 3.

The ratio `k/14 + 2k/14^k` is the count/order ratio of that **supplied partition**, not a lower bound for `c(A_k)/14^k`. In fact Section 2A gives an explicit global repair with at most `14^k/3` cycles, **without cloning**. Thus this fully shared construction is decisively not a disproof.

One can already locate the failure of the old lower-bound proof. A former 14-vertex punctured-Petersen block now has exactly

```
4 + 56(k-1)
```

boundary edges: four from its own ring and four edges at each of its 14 vertices from every other layer. Those other-layer edges all leave the block by the coordinate argument above. Its crossing traffic is no longer limited to two paths. The global repair below identifies an actual recombination, rather than relying only on this failure of a proof.

Section 3 proves the even-clone extensions used in (2.4).

---

## 2A. A global Cartesian repair of the shared obstruction

Write `G^{square k}` for a Cartesian power: its vertices are k-tuples, and an edge changes exactly one coordinate along an edge of G. This is different from the complete independent blow-up `G[a]`.

### Lemma 2.2 — an explicit two-Hamilton-cycle torus

If `l>=3`, `m>=3`, `l` divides m and `gcd(m,l-1)=1`, then `C_m square C_l` has a Hamilton decomposition into two cycles.

**Proof.** Use vertices `(x,y) in Z_m x Z_l`. Orient every horizontal edge by `x -> x+1` and every vertical edge by `y -> y+1`. The phase `x+y (mod l)` is well-defined because l divides m. In colour 0, choose the horizontal outgoing edge at phases `0,...,l-2` and the vertical outgoing edge at phase `l-1`. Colour 1 uses the other outgoing edge.

Each colour has indegree one as well as outdegree one: the two possible predecessors of `(x,y)` both have phase `x+y-1`, so precisely the predecessor in the selected direction sends an edge of that colour into `(x,y)`. The two factors partition all oriented edges, hence all undirected edges.

Every step increases phase by one. After l steps, colour 0 translates by `(l-1,1)` and colour 1 by `(1,l-1)`. Each translation has order m: the hypotheses imply

```
ord(l-1 in Z_m)=m,    ord(1 in Z_m)=m,    and l divides m.
```

A return must take a multiple of l steps by phase, and then a multiple of m such blocks by translation. Thus each colour has one orbit of length lm, exactly the number of vertices. Both are actual Hamilton cycles. ∎

In particular the lemma applies to `m=l^r` for every `r>=1`, with **no parity restriction** on l.

### Lemma 2.3 — a paid partition of every cycle power

For every `l>=3` and `j>=1`, `C_l^{square j}` has a partition containing a Hamilton cycle and having exactly

```
q_j(l) = (l^(j-1)+l-2)/(l-1) <= l^(j-1)                  (2A.1)
```

cycles. Except in small cases, this is a constructed count, not a minimum claim.

**Proof.** At `j=1` use the single cycle. Suppose the preceding partition has a distinguished Hamilton cycle H, of length `m=l^(j-1)`. In the next Cartesian power, keep the l copies of every other old cycle. The l copies of H, together with **all** new-coordinate edges, form exactly `C_m square C_l`, since H spans the preceding vertex set. Replace this whole torus by the two Hamilton cycles of Lemma 2.2. Therefore

```
q_1=1,                   q_j=l(q_(j-1)-1)+2.
```

Solving this recurrence gives (2A.1), and the two new torus cycles retain the required distinguished Hamilton cycle. The pieces outside the torus and inside it partition disjoint edge sets. No closed trail is being counted as simple. ∎

This already rules out naive coordinate-by-coordinate amplification of one cycle: its old `j l^(j-1)` coordinate cycles globally recombine into `q_j(l)=O(l^j)` cycles with a constant independent of j.

### Theorem 2.4 — uniform cycle-factor Cartesian packets

Let `a>=0`, `b>=1`, `l>=3` and `k>=1`. Let F consist of b vertex-disjoint l-cycles and a isolated vertices, so its order is `n_0=a+bl`. Then `F^{square k}` has a cycle partition of the following exact constructed size:

```
S_k(a,b,l)
 = [n_0^k + l(l-2)(a+b)^k - (l-1)^2 a^k] / [l(l-1)]
 <= (n_0^k-a^k)/l.                                      (2A.2)
```

**Proof.** A component with j active coordinates chooses those coordinates, one of the b old cycles in each, and one of the a isolated vertices in every other coordinate. There are

```
binom(k,j) b^j a^(k-j)
```

such components, each isomorphic to `C_l^{square j}`. The j=0 components are isolated and cost zero. Apply Lemma 2.3 to every other component. Summing its exact count gives

```
sum_(j=1)^k binom(k,j)b^j a^(k-j)
    [l^(j-1)+l-2]/(l-1),
```

which is (2A.2) by two binomial expansions. The inequality follows from `q_j(l)<=l^(j-1)`. ∎

More generally, suppose an even graph G on `n_0` vertices has an edge partition into spanning subgraphs `F_1,...,F_p`, where `F_i` consists of vertex-disjoint cycles of a common length `l_i` and `a_i` isolated vertices. Multiplicities of cycles within each `F_i` are unrestricted. The edge sets of `F_i^{square k}` partition `G^{square k}`: a Cartesian edge belongs to the unique factor containing its changing-coordinate base edge. Consequently

```
c(G^{square k})
 <= sum_i S_k(a_i,b_i,l_i)
 <= sum_i (n_0^k-a_i^k)/l_i
 <= n_0^k sum_i 1/l_i.                                   (2A.3)
```

The charge is once per cycle **factor/type**, not once per coordinate or once per cycle component of a factor. The factors may overlap arbitrarily in vertices. Choosing one factor per old cycle proves an O(order) bound for all Cartesian powers of any fixed even base. A uniform bound across changing bases needs control of `sum_i 1/l_i`; this is supplied in the next application, not assumed universally.

### Corollary 2.5 — all Cartesian powers of the Petersen rings are uniformly linear

For every `t>=2` and `k>=1`,

```
c(R_t^{square k})
 <= [1/(14t)+1/(11t)+1/3] (14t)^k
 <= (383/924)(14t)^k < (5/12)(14t)^k.                     (2A.4)
```

**Proof.** The prior minimum partition consists of one `14t`-cycle, one `11t`-cycle, and t vertex-disjoint triangles. These give three factors:

```
F_1: one C_(14t),              a_1=0;
F_2: one C_(11t),              a_2=3t;
F_3: t disjoint C_3,           a_3=11t.
```

Apply (2A.3). The coefficient is largest at `t=2`, where it equals `383/924<5/12`. ∎

Thus this is uniform in **both** the original ring size and the number of Cartesian factors. Allowing the Petersen obstruction parameter to grow along with the degree does not evade the bound.

### Theorem 2.6 — explicit global repair of the fully shared family A_k

The graph `A_k` of Section 2 has a partition with exactly

```
Q_k = 2k + [14^k+3*12^k-4*11^k]/6
```

cycles. For every `k>=2`,

```
p(A_k)=c(A_k) <= Q_k <= 14^k/3.                            (2A.5)
```

**Proof.** Keep the two long cycles from the documented minimum partition of each of the k layers, for a total of `2k` cycles. In each layer the remaining pieces are exactly the triangles on the old labels `{1,7,9}`, which become the coordinate alphabet `{0,6,8}`. All their other coordinates are arbitrary.

The entire remaining edge graph is therefore exactly `F^{square k}`, where F is the triangle on `{0,6,8}` and eleven isolated states on the other elements of `Z_14`. This is an edge identity, not only an incidence analogy. In one coordinate, a remaining edge is precisely an edge of that triangle; all other coordinates stay fixed. Its connected components with j active triangle coordinates are the `binom(k,j)11^(k-j)` copies of `C_3^{square j}` described above.

Apply Theorem 2.4 with `a=11,b=1,l=3`. Its output count is

```
S_k(11,1,3)=[14^k+3*12^k-4*11^k]/6.
```

The retained long cycles use no edges of this remainder, and the new component cycles are simple by Lemma 2.3. This proves the exact constructed count Q_k. Finally,

```
Q_k <= 2k+(14^k-11^k)/3 <= 14^k/3,
```

because `11^k>=6k` for `k>=2` (indeed for `k>=1`). ∎

For the **same graphs**, the old separately optimal layer partitions have count/order ratio

```
k/14+2k/14^k -> infinity,
```

whereas the displayed repaired partition has ratio

```
Q_k/14^k -> 1/6.
```

The exact minimum `c(A_k)` is not identified, and could be much smaller than Q_k; its fractional value is exactly `2k`. But the explicit linear upper bound already excludes every superlinear lower-bound claim for this family. This is a genuine global, mixed-coordinate cancellation of an integral obstruction replicated on the same old vertices, not a bounded-port substitution, a numerical counterexample search, or an assertion that a bad local algorithm will improve.

---

## 3. Complete cycle blow-ups always Hamilton-decompose

### Lemma 3.1 — all clone multiplicities

For every `l>=3` and `a>=1`, `C_l[a]` has a partition into a Hamilton cycles. In particular,

```
c(C_l[a])=c_f(C_l[a])=a.                                   (3.1)
```

**Proof, first case: l even.** Label the base vertices cyclically `v_0,...,v_(l-1)` and each fibre by `Z_a`. For each `j in Z_a`, put a perfect matching on link i with shift `b_(i,j)`:

```
(v_i,x) -- (v_(i+1), x+b_(i,j)),
b_(i,j) = j for even i, -j for odd i,
```

and add 1 to `b_(0,j)`. On each link, its a shifts are a permutation of `Z_a`, so the a proposed factors partition that complete bipartite link. The sum of the shifts around the base cycle is 1. Therefore following a factor once around increases the clone coordinate by 1, and a turns visit all clones. Each factor is one Hamilton cycle, not a collection of shorter cycles.

**Second case: l odd and a odd.** On the first three links use shifts

```
j, j, 1-2j,
```

and on the remaining, even number of links use cancelling pairs `j,-j`. All link-shift lists are permutations, since 2 is invertible modulo a. Again the total shift is 1, proving the assertion. For `a=1` this is simply the original cycle.

**Third case: l odd and a even.** First construct two Hamilton cycles in `C_l[2]`, without using constant-direction matching lifts. At base vertex `v_1`, make the following two colours:

* colour h uses both edges from `(v_1,h)` to the two clones of `v_0`;
* the same colour uses both edges from `(v_1,1-h)` to the two clones of `v_2`;
* along the outside base path `v_2,v_3,...,v_(l-1),v_0`, colour 0 uses the parallel matching on each link and colour 1 the crossed matching.

The two colours partition all edges. For a fixed colour, the outside path lifts to two disjoint paths covering all outside clones. Its two endpoints at one end are joined through one clone of `v_1`, and its two endpoints at the other end through the other clone. The result is one Hamilton cycle on all `2l` vertices. Both colours have this property. In fact this construction works for even l too.

Write `a=2b`. Blow up each of these two Hamilton cycles by b. Their lengths `2l` are even, so the first case decomposes each blow-up into b Hamilton cycles. The two edge sets partition

```
(C_l[2])[b] = C_l[2b]
```

under the explicit clone identification `(v,h,x) -> (v,hb+x)`. This gives a Hamilton cycles in total.

In all cases, degree `2a` supplies the lower bound a, including the fractional lower bound. ∎

The odd-l/even-a case is essential. It would be incorrect to claim that arbitrary modular shift choices make all lifts Hamilton. The turns through different clones explicitly overcome a possible matching-lift parity obstruction.

### Theorem 3.2 — no uniform-blow-up amplification

If G is even, then for every `a>=1`,

```
c(G[a]) <= a c(G).                                         (3.2)
```

**Proof.** Take a minimum cycle partition of G. The complete blow-ups of its cycles are edge-disjoint and partition `G[a]`, even though their vertex supports may overlap arbitrarily. Apply Lemma 3.1 to each cycle. This creates exactly a replacement cycles for each old cycle. ∎

For `|V(G)|>0`, dividing by `a|V(G)|` proves monotonicity of the count/order ratio. This holds for changing, dense base graphs, not just bounded-degree fixed templates. Any succession of uniform independent blow-ups is one blow-up, since `(G[a])[b]` is `G[ab]`. No product of loss constants is hidden in the recursion.

This theorem does **not** cover adding new edges inside clone fibres, selectively deleting cross-fibre edges, or arbitrary unions with unrelated new edge layers.

### Corollary 3.3 — exact even-clone Petersen values

Apply Lemma 3.1 to the four Hamilton cycles of `R_t[2]` and use `(R_t[2])[s]=R_t[2s]`. There are `4s` Hamilton cycles, and the graph has degree `8s`. Therefore

```
|V|=28ts,     |E|=112ts²,
p=c=c_f=4s,   c/|V|=1/(7t).                                (3.3)
```

Similarly, the graph G in the shared-colour version (2.3) satisfies

```
c(G[2s])=c_f(G[2s])=4bs.                                   (3.4)
```

As G is simple and `4b`-regular, `4b<=N-1`. The ratio in (3.4) is `2b/N<1/2`, even if b grows and the old vertices are reused by every layer.

---

## 4. Even twin fibres: a bound independent of the base obstruction

The preceding monotonicity theorem charges a cycles per old **cycle**, so it depends on `c(G)`. A different construction removes that dependence for even clone fibres.

### Lemma 4.1 — two-clone paths

For a simple path P of k edges:

* if `k=1`, `P[2]` is one 4-cycle;
* if `k>=2`, `P[2]` partitions into two simple cycles, each of length `2k`.

**Proof.** Write `P=(v_0,...,v_k)`. Colour h uses `(v_0,h)` at the first endpoint and `(v_k,h)` at the last. Join each of these endpoint clones to both clones in the adjacent internal fibre. Between successive internal fibres use the parallel matching in colour 0 and the crossed matching in colour 1. In each colour the internal matching chains are two vertex-disjoint paths. The chosen endpoint clones close them into one simple cycle. The other endpoint clones belong to the other colour. All four edges of every original link are used once. ∎

Internal fibres are used wholly in each output cycle. The two unused endpoint clones in one colour are used by the other, so no vertex multiplicity is being concealed.

### External input — the actual Lovász theorem

The classical theorem used here says:

> Every finite simple graph on h vertices has an edge partition into at most `floor(h/2)` simple paths and simple cycles.

This is the **path/cycle** theorem, not the still stronger path-only conjecture and not Erdős–Gallai's cycle/singleton assertion. It is stated explicitly in the local source

```
/corpus/src/1402.3741/Gallai-3jun2015.tex, lines 26–50,
Andrea Jiménez and Yoshiko Wakabayashi,
On path-cycle decompositions of triangle-free graphs.
```

Lines 26–33 specify exact edge decompositions; lines 48–50 state the Lovász bound. Its 1968 original proof is not rederived here. This is the only extra external theorem needed for Theorem 4.2; the binary-phase, Cartesian-product, uniform-cycle-blow-up and line-graph constructions have their own proofs in this note.

### Theorem 4.2 — paired false twins preclude a disproof

For every simple graph B on h vertices, even or not,

```
c(B[2]) <= 2 floor(h/2) <= h.                              (4.1)
```

More generally, if H is a blow-up of any simple base graph with positive **even** fibre sizes, then

```
c(H) <= |V(H)|/2.                                         (4.2)
```

**Proof.** Apply the Lovász theorem to B. Lift each path using Lemma 4.1 and each cycle using the two-clone construction in Lemma 3.1. Each old piece costs at most two cycles, and its blow-up uses exactly its own original links. The lifted edge sets therefore partition `B[2]`. This proves (4.1).

For nonuniform fibre sizes `2a_v`, first replace v by `a_v` independent vertices and retain complete adjacency on base links, producing a simple graph B. Then H is exactly `B[2]`. Its order is `2|V(B)|`, proving (4.2). ∎

Equivalently, the theorem applies to any graph admitting a partition into pairs of nonadjacent vertices with identical open neighborhoods. Between two such pairs there are either all four edges or none, so the graph is `B[2]`.

The bound is asymptotically sharp for this class: let B be `K_h` with h odd. Its usual Hamilton decomposition lifts to `h-1` Hamilton cycles of `B[2]`. Degree `2(h-1)` proves this optimum, and `(h-1)/(2h)` tends to `1/2`.

This is a uniform obstruction to clone-preserving degree-scale amplification. It still applies when the quotient B changes with the scale or contains arbitrarily many overlaid colours; no bound on its own integral optimum is required. Deleting the completed clone adjacencies can destroy the hypothesis. There is no claim that arbitrary partial blow-ups inherit (4.2).

---

## 5. Complete transition libraries: all Eulerian line graphs are linear

A natural encoding uses a host graph X: its edges are the states, and two states can transition whenever their host edges meet. If every transition at a host vertex is allowed, the encoded graph is exactly `L(X)`.

Let `N=|E(X)|=|V(L(X))|`. For each host vertex v, its incident edges induce a clique `K_(d_X(v))` in the line graph. These cliques partition the **edges** of the line graph, because two distinct edges of a simple X share at most one endpoint. The fact that every state is incident with only its two host endpoints is a single global incidence account; host degrees need not be bounded.

### A self-contained clique ingredient

The Walecki constructions give:

```
K_(2k+1):            k Hamilton cycles;
K_(2k) minus M:      k-1 Hamilton cycles, for any perfect matching M. (5.1)
```

Here is an explicit verification if these facts are not taken as standard. For odd order, label vertices by infinity and `Z_(2k)`. For `t=0,...,k-1` take

```
(infinity, t, t-1, t+1, ..., t-(k-1), t+(k-1), t-k).
```

The finite edges have alternating sums `2t-1,2t` modulo `2k`, filling those two nonloop pair classes. The infinity-neighbors are t and `t-k`; these cover every finite vertex once.

For even order, use infinity and `Z_(2k-1)`. For `t=0,...,k-2` take

```
(infinity, t, t-1, t+1, ..., t-(k-1), t+(k-1)).
```

Again the two finite sum classes are filled. The omitted finite sum class is `2k-3`, leaving a matching on all finite vertices except `2k-2`; the omitted infinity edge ends at that exceptional vertex. Thus the remainder is a perfect matching. Relabel the vertices to map it to any prescribed M. The cases `K_1` and `K_2 minus M` have no cycles.

### Theorem 5.1 — exact constructive counts for even line graphs

Assume `L(X)` is even. For each nontrivial connected component Y of X, put `m_Y=|E(Y)|`, `h_Y=|V(Y)|`. Then all its host degrees have the same parity, and there is a cycle partition of `L(X)` with exactly

```
sum over all-odd Y:   (m_Y - h_Y/2)
  + sum over all-even Y: (m_Y - h_Y + 1)                    (5.2)
```

cycles. Consequently

```
c(L(X)) <= r(L(X)) <= N.                                  (5.3)
```

**Proof.** At a line-graph vertex corresponding to `uv`, its degree is

```
d_X(u)+d_X(v)-2.
```

Evenness implies that the two host degrees have the same parity. Connectivity propagates the parity throughout each nontrivial host component.

For an all-odd component, decompose each host-vertex clique independently by (5.1). Their edge sets are disjoint and exhaustive. The number is

```
sum_v (d_Y(v)-1)/2 = m_Y-h_Y/2.
```

For an all-even component Y, choose an Euler tour of Y. Its cyclic list of edges is a Hamilton cycle H of `L(Y)`: every edge-state occurs exactly once, and successive states share the host vertex where the tour transitions. Since Y is simple and has positive even degrees, it has at least three edges; H is a genuine simple cycle.

At each host vertex v, the Euler tour pairs its incident edges into a perfect matching `M_v` of its transition clique. These are precisely the H-edges inside that clique. Remove H. The remaining graph is the edge-disjoint union of `K_(d_Y(v)) minus M_v`. Apply (5.1) separately to these residual cliques. Including H, the count is

```
1 + sum_v (d_Y(v)-2)/2 = m_Y-h_Y+1.
```

This proves the actual partition (5.2). A nontrivial all-odd component has `h_Y>=2`, so its count is at most `m_Y-1`; an all-even one has `h_Y>=3`, with count at most `m_Y-2`. Each nontrivial host component gives exactly one connected line-graph component, even for a lone host edge, whose line graph is an isolated vertex with cost zero. Summing gives (5.3). Isolated host vertices give no line-graph vertices and are ignored. ∎

Formula (5.2) is a **constructed count**, not a claim of global optimality. For example it is not the optimal three-cycle partition of `L(Petersen)`. Only the upper bound is needed for the impossibility of this amplification route.

### Corollary 5.2 — non-even line graphs also cannot refute the target

For arbitrary simple X, let h be its number of nonisolated vertices. Then

```
p(L(X)) <= 2N-h <= 2N.                                    (5.4)
```

**Proof.** In an odd-order transition clique, use its Hamilton decomposition. In an even-order clique, use the Hamilton decomposition after removing a perfect matching and retain the matching edges as singletons. A host vertex of odd degree d costs `(d-1)/2` pieces; one of positive even degree d costs `(d-2)/2+d/2=d-1`. Each costs at most `d-1`. Summing over nonisolated host vertices gives `2N-h`, and the transition cliques partition line-graph edges. ∎

Thus an arbitrarily complicated input, arbitrarily high host degrees, or many iterations ending in a full line-graph operation cannot produce unbounded `p/n`.

### Where restricted transitions escape this theorem

Deleting allowed transitions from the cliques is not covered. In fact arbitrary restrictions are universal: let X be a star with N edges. Its line graph is `K_N`. Keeping an arbitrary set of transitions at the centre realizes **any** simple graph on N states. Thus a claim about all restricted-transition encodings would already contain the entire original problem.

The no-go result is for complete transition libraries (and any other class separately proved to have a suitable local decomposition), not for arbitrary forbidden-transition systems. General nonregular binary-matroid circuit obstructions still do not transfer to a graphic representation just by calling these states transitions.

---

## 6. An exact warning about turning a phase defect into a lower bound

It is tempting to view `epsilon(J)>0` in Theorem 1.1 as an encoded integral obstruction. It is genuine **within its defined lift class**, but it is not generally a graph obstruction.

Take `G=C_l` with l odd, and double-cover it by two copies of its one cycle. J has two nodes and l parallel bookkeeping edges. Therefore `epsilon=1`, and every matching-lift partition has at least three cycles. Theorem 1.1 attains three.

Nevertheless the star-turn construction in Lemma 3.1 gives **two Hamilton cycles** in `C_l[2]`, and degree four proves the actual optimum is two. For `l=3`, writing `ia=(i,0)` and `ib=(i,1)`, one explicit partition is

```
(1a, 0a, 2a, 1b, 2b, 0b),
(1b, 0a, 2b, 1a, 2a, 0b).                                (6.1)
```

These two cycles cover all edges of `K_(2,2,2)` once. They use turns of the form

```
(u,0) -- (v,h) -- (u,1),
```

which are simple on the clones but backtrack after projection to the old graph. Such a turn was absent from the matching-lift model.

This is a small, exact demonstration of the quantifier danger in the proposed direction: even a correct algebraic incompatibility calculation may only constrain a chosen transition class. Mixed/projection-backtracking cycles can globally cure it. Any disproof must account for those cycles too, not assume that every new cycle inherits a single colour or a nonbacktracking old projection.

---

## 7. What is ruled out, and what remains unresolved

The following routes are now explicitly excluded by the proved constructions:

* **the fully shared coordinate Petersen overlays A_k:** their separately optimal layers give a superlinear supplied count, but the explicit global partition has at most `|V(A_k)|/3` cycles;
* **Cartesian powers of the Petersen rings:** the bound is less than `5n/12`, uniformly even when both the ring size and exponent grow; more general uniform cycle-factor packets satisfy (2A.3);
* **uniform complete cloning of an even obstruction:** the ratio cannot increase at all, at any clone multiplicity;
* **complete even clone fibres, including nonuniform ones and shared-colour quotients:** the graph has `c<=n/2` regardless of the quotient's unknown optimum;
* **the supplied Petersen rings followed by even complete cloning:** the entire additive gap disappears, with the exact values (3.3), not merely a constant bound;
* **a last full line-graph/complete-transition operation:** `p<=2n`, and `c<=r` if the output is even;
* **a proposed lower bound using only the binary matching-lift phase equations:** (6.1) shows that the restricted optimum may exceed the actual one.

These do not rule out arbitrary asymmetrically relabelled or nonseparable edge-disjoint overlays directly on the old vertex set, partial clone matchings with no paired-twin structure, restricted transition graphs, or recursively added fibre-internal edges. No construction in those remaining classes with a superlinear global minimum is established here. No universal additive-rank rounding theorem is proved either.

A successful amplification would have to preserve an obstruction after allowing unrestricted colour changes and simple turns at reused vertices, while avoiding the Cartesian residual regrouping, the complete-clone repairs, and a merely bounded-degree construction. The exact phase theorem isolates one class where these global choices can be coordinated and the old gadget-by-gadget lower count cannot be inherited.

---

## 8. Verification and protected files

Run:

```
python3 Submission/ResearchAmplificationCheck.py
```

The script uses Python 3 and NetworkX only. **The full checker passed.** Its exact verification totals are:

* **150 path templates and 560 complete cycle blow-ups**, including both parity cases and the even-clone/odd-base-cycle construction;
* **760 labelled loopless multigraphs and all 118,000 of their orientations**, verifying the parity-orientation optimum independently of its constructive algorithm;
* cycle-double-cover lifts and the explicit scope warning: odd base cycles have restricted lift cost three but actual two-Hamilton-cycle partitions;
* **all 209 unlabelled graphs through order six**, with exact path/cycle partitions and checked paired-clone partitions; all **31 even inputs** also satisfy the independently optimized `p=c` check, and give **155 uniform partition lifts**;
* **21 two-Hamilton torus constructions, 24 cycle-power partitions, and 17 partial uniform-cycle-factor powers**, checked against independently generated Cartesian-product edge sets;
* **five Cartesian powers of Petersen rings**, including `R_2^{square 3}` on 21,952 vertices with an exact partition into 3,670 cycles (an upper witness, not a minimum claim);
* **58 nonuniform even-fibre instances**;
* **36 even-clone Petersen graphs**, through `R_101[10]` on 14,140 vertices, whose 20 Hamilton cycles meet the degree lower bound exactly;
* the fully shared overlays **A_2 and A_3**, their exact triangle-grid remainder identities, uncloned global repairs, all claimed boundary counts, and five even-clone Hamilton partitions;
* **all 1,253 graph-atlas hosts through order seven**, including **147 Eulerian line graphs**; clique constructions through order 41, four line-graph iterations, and seven equality examples for asymptotic sharpness of the paired-twin bound.

For the shared-vertex test, the concrete upper witnesses are:

| Graph | Order | Fractional optimum | Separate layer count | Global repair count | Double-clone optimum |
|---|---:|---:|---:|---:|---:|
| `A_2` | 196 | 4 | 32 | 28 | 8 on 392 vertices |
| `A_3` | 2744 | 6 | 594 | 440 | 12 on 5488 vertices |

The separate and global-repair columns are **partition counts**, not claims to equal `c(A_k)`. The fractional and double-clone columns are actual optima, with degree lower certificates valid for all cycles.

The checker does not use finite verification as a substitute for the general proofs. In particular, optimum claims for the large blow-ups use the universal degree certificate, not enumeration or a solver-reported optimum. The Lovász theorem is an explicitly identified external input; finite checks do not purport to prove it.

The specification SHA-256 is unchanged:

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

**Outcome:** an explicit global repair of a fully shared Petersen-layer amplification, a uniform bound for all Cartesian powers of the rings, and exact clone/complete-transition impossibility results. The required disproof and unbounded minimum count/order family remain unestablished.
