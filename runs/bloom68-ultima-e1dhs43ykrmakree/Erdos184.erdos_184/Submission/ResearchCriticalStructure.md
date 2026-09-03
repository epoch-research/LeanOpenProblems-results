# Genuine critical structure: the cost-three case, with a complete finite reduction

## Outcome and limits

**The requested universal Erdős–Gallai argument remains unresolved.** This note proves no absolute constant for all critical graphs and supplies no genuine critical counterexample to fixed count. Accordingly, **`Spec.lean` is unchanged**.

There is a scoped structural advance beyond the previously established cost-two case:

> **Theorem (computer-assisted).** Every finite even simple graph that is genuinely **3-critical** has exactly three cycles in **every** simple-cycle edge partition.

The proof also works for loopless multigraphs, with a parallel pair counted as a core cycle. It consists of paper-level reductions followed by a small, self-contained exhaustive calculation whose completeness is proved below. It is **not a Lean formalization**, and no literature-priority claim is made.

The main ingredients are:

1. **A genuine all-restriction consequence:** if a connected non-cycle graph `F` is `q`-critical, then for every simple cycle `C`,
   \[
   Q(F-V(C))\le q-2.                                      \tag{0.1}
   \]
   Here `F-V(C)` need not be even; `Q` still maximizes over its even edge restrictions. This is not the assertion about `c(F-E(C))` obtained from a single cycle deletion.
2. **A cycle-rank lemma:** any graph containing no two edge-disjoint simple cycles has cycle-space dimension at most **four**.
3. A non-fixed 3-critical graph would reduce to a connected loopless **4-regular core** of order `n` and girth `g` satisfying
   \[
   n\le 2g+3.                                             \tag{0.2}
   \]
   Moore bounds then leave only parallel-edge cores on at most seven vertices, simple cores on at most nine vertices, and triangle-free simple cores on ten or eleven vertices.
4. A completeness-justified generator produces **780 core presentations**, with possible isomorphic repetitions. The checker audits **all 506,296 even restrictions**, counting those repetitions, and reconstructs minimum and maximum partitions for every restriction. All **125** non-fixed full-cost-three presentations have an explicitly extracted **proper, genuinely 3-critical, fixed-count restriction**. None is misidentified as critical itself.

Consequently the user's structural candidate is proved **when `c(G)<=3`**: if such an even graph has two edge-disjoint cycles sharing at least three vertices, it has a proper even restriction `H` with `c(H)>=c(G)`. Any genuine counterexample to the universal critical-fixed-count assertion must have **critical cost at least four**.

Only these files were created:

* `Submission/ResearchCriticalStructure.md` — this report;
* `ResearchCriticalStructureCheck.py` — the self-contained standard-library checker at the repository root.

No old example is promoted to criticality. The supplied `S` and `L(Petersen)` remain noncritical. Neither their cycle-deletion certificates nor a generic signed-state-extension assertion is used in this proof.

---

## 1. Definitions and elementary critical reductions

All cycles are **vertex-simple**. In auxiliary loopless multigraphs, distinct parallel edges have distinct identities and two parallel edges form a cycle. For an even edge set `W`, let

\[
 c(W)=\min_{\mathcal D\text{ partition of }W}|\mathcal D|,
 \qquad
 \nu(W)=\max_{\mathcal D\text{ partition of }W}|\mathcal D|.
\]

The empty set has both costs zero. For **any** graph `X`, even or not, define

\[
 Q(X)=\max_{W\subseteq E(X),\ W\text{ even}}c(W).
\]

An even nonempty graph `F` is `q`-critical when

\[
 c(F)=q,\qquad
 c(W)<q\quad\text{for EVERY proper even }W\subsetneq E(F). \tag{1.1}
\]

Properness means proper **edge** support, not deletion of an isolated vertex.

### 1.1 Facts used in the reduction

For completeness, the needed low-cost and separator facts have short proofs.

* A 1-critical graph is a cycle.
* A 2-critical graph has `nu=2`: otherwise, the union of two members of a partition with at least three members is a proper even restriction of cost exactly two. The union cannot be one simple cycle, whether its two cycles meet or are vertex-disjoint.
* If `F` is `q`-critical and `d_F(v)=2q`, **every cycle contains `v`**. Otherwise deleting a cycle avoiding `v` leaves a proper even restriction whose degree at `v` still forces cost at least `q`. Every partition therefore has exactly `q` cycles, by counting incidences at `v`.
* At an articulation or disjoint union, both `c` and `nu` add: a simple cycle belongs to a single block. In an even graph, every nonempty block is even. Criticality passes to the blocks, since replacing a block by a proper even restriction of at least its old cost would contradict (1.1) after restoring the other blocks.
* Suppressing degree-two paths preserves `c`, `nu`, and **all-restriction criticality**. An even restriction uses an entire such path or none of it; simple cycles and their partitions correspond bijectively. Subdivision is the inverse correspondence.

In particular, a **non-fixed** 3-critical graph cannot have more than one nonempty block: then each block would be critical of cost at most two and hence fixed-count, making their sum fixed-count. Nor can it have a degree-six vertex. After discarding isolates, it has one cyclic block, degrees two and four, and at least one degree-four vertex. Suppressing its degree-two paths gives a connected 4-regular core. The core is loopless: a suppressed loop would come from a cycle attached at a single branch vertex, contradicting the one-block condition. Its cost and criticality remain exactly three.

Thus a non-fixed 3-critical counterexample gives a **connected loopless quartic 3-critical core**. No assumption about arbitrary minors or retaining old cycles is involved. The stronger previously supplied two-edge and vertex-edge separator reductions are not needed for this particular cost-three proof.

---

## 2. A vertex-deletion consequence of genuine criticality

### Lemma 2.1

Let `F` be connected, even, nonempty, and not a single cycle. If `F` is `q`-critical, then for every simple cycle `C` in `F`,

\[
 \boxed{Q(F-V(C))\le q-2.}                              \tag{2.1}
\]

**Proof.** Let `W` be any even edge restriction of `F-V(C)`. Its vertex support is disjoint from `C`, so

\[
 c(W\mathbin{\dot\cup} C)=c(W)+1.
\]

This union is proper in `F`. Indeed, if it were all of `F`, connectedness would force `W` empty and `F=C`, which was excluded. Equivalently, some edge incident with `V(C)` but not in `C` is omitted. Applying (1.1) gives `c(W)+1<=q-1`. Maximize over **all** such `W`. ∎

In a quartic graph properness is especially transparent: every vertex of `C` has two incident edges missing from `C union W`.

For `q=3`, (2.1) implies that `F-V(C)` contains **no two edge-disjoint simple cycles**. If it contained `A,B`, their union would be an even restriction of cost two. Alternatively, `C union A union B` would be a proper even restriction of cost exactly three, since `C` is vertex-disjoint from the other two cycles. `A` and `B` are allowed to share vertices.

This is exactly where the full critical hypothesis is used. The cycles `A,B` are arbitrary cycles in a vertex-deleted graph, not surviving members of a supplied minimum partition. There is no reoptimization/retention assumption.

---

## 3. No two edge-disjoint cycles implies cycle rank at most four

For any graph `X`, including a disconnected or non-even graph, put

\[
 \beta(X)=|E(X)|-|V(X)|+\kappa(X),
\]

where isolated vertices count as components. This is cycle-space **dimension**, not graphic matroid rank.

### Lemma 3.1

If `X` has no two edge-disjoint simple cycles, then

\[
 \boxed{\beta(X)\le4.}                                  \tag{3.1}
\]

**Proof.** There is at most one component containing a cycle. Discard forest components, remove leaves, and suppress degree-two vertices. These operations preserve `beta` and the existence of two edge-disjoint cycles. A component that is just a cycle has `beta=1`, so suppose for contradiction that `beta>=5`.

The resulting connected core `J` has minimum degree at least three; loops and parallel edges are allowed at this stage. In this temporary suppressed core, a loop is a one-edge cycle, corresponding to a cycle before suppression. Removing the edges of **any** cycle `D` leaves a forest, since a cycle in the remainder would be edge-disjoint from `D`. If that forest has `k>=1` components, then

\[
 |E(J)|-|D|=|V(J)|-k,
 \qquad
 \beta(J)=|D|-k+1\le |D|.
\]

Consequently the girth `g` of `J` satisfies `g>=beta>=5`; in particular `J` is simple. Minimum degree three gives

\[
 |V(J)|\le 2\beta(J)-2.                                 \tag{3.2}
\]

The elementary breadth-first-tree Moore bounds for minimum degree three are

\[
 |V(J)|\ge
 \begin{cases}
  3\cdot2^r-2,&g=2r+1,\\
  2^{r+1}-2,&g=2r.
 \end{cases}                                             \tag{3.3}
\]

The first comes from a radius-`r` tree rooted at a vertex; the second from the two depth-`r-1` trees rooted at the ends of an edge. Any identifications prohibited by these tree counts would create a shorter cycle. For every `g>=5`, (3.3) is at least `2g`: check `g=5,6`, and increasing `r` increases the exponential expression by more than the corresponding increase four in `2g`.

Thus `|V(J)|>=2g>=2beta`, contradicting (3.2). ∎

The constant four is needed: `K_{3,3}` has `beta=4` and no two edge-disjoint cycles. Its degree three prevents two edge-disjoint cycles from sharing a vertex, while its six vertices and girth four prevent two vertex-disjoint cycles. The checker independently enumerates its fifteen cycles and verifies the assertion.

---

## 4. The finite bound on a quartic 3-critical core

### Proposition 4.1

Let `K` be a connected loopless 4-regular 3-critical graph. If it has `n` vertices and girth `g`, then

\[
 \boxed{n\le 2g+3.}                                    \tag{4.1}
\]

**Proof.** Take a shortest cycle `C` of length `g` and let `X=K-V(C)`. Lemmas 2.1 and 3.1 give `beta(X)<=4`.

The quartic graph `K` has `2n` edges. Write `e_C` for the number of edges with both ends in `V(C)`; certainly `e_C>=g`, even when parallel edges occur. Counting edges removed with `V(C)` gives

\[
 |E(X)|=2n-4g+e_C\ge2n-3g.
\]

If `n>g`, `X` has `n-g` vertices and at least one component, including any isolates. Hence

\[
 4\ge\beta(X)\ge (2n-3g)-(n-g)+1=n-2g+1,
\]

which proves (4.1). If `n=g`, (4.1) is immediate. ∎

### Corollary 4.2 — exhaustive finite cases

Every such core occurs in at least one of the following finite classes:

* connected loopless quartic multigraphs on **2–7 vertices**;
* connected quartic **simple** graphs on **5–9 vertices**;
* connected quartic **triangle-free simple** graphs on **10 or 11 vertices**.

**Proof.** A parallel pair gives `g=2`, hence `n<=7`. Without parallel edges the core is simple. For minimum degree four, the same breadth-first counting gives

\[
 n\ge
 \begin{cases}
  2\cdot3^r-1,&g=2r+1,\\
  3^r-1,&g=2r.
 \end{cases}                                             \tag{4.2}
\]

For `g>=5` these bounds exceed `2g+3`: at `g=5,6` they give respectively `17>13` and `26>15`, and the differences increase with `r`. Thus `g=3` or `4`. Formula (4.1) gives `n<=9` or `n<=11`, respectively. A quartic simple graph has at least five vertices. ∎

This is a bound on **all possible critical cores**, not an inference from the largest graph searched. Subdivision may make the original simple graph arbitrarily large, but does not escape the core bound.

---

## 5. Complete finite calculation and why its enumeration is exhaustive

### Proposition 5.1 — checked finite statement

In the classes of Corollary 4.2:

1. All simple graphs in the specified classes have `c=2`.
2. Every full-cost-three multigraph with `nu>3` has a proper even restriction of cost at least three.
3. The sole isomorphism type of quartic 3-critical core is the four-vertex graph with two disjoint triple-edge bundles, joined by two single edges into a connected graph. It has `c=nu=3` and maximum proper restriction cost two.

The stronger third description is not needed to rule out non-fixed cores. In the generated presentations its representative has edges

```
02, 02, 02, 03, 12, 13, 13, 13.
```

It is a two-edge splice of two four-path cores, not an irreducible 4-edge-connected exception.

### 5.1 A self-contained generator, not an assumed graph catalog

`quartic_cores` builds the upper triangle of a symmetric adjacency matrix row by row. Its entries are nonnegative integers at most `M`, its diagonal is zero, and each row must sum to four. Use `M=4` for multigraphs and `M=1` for simple graphs. Every loopless quartic multigraph satisfies this multiplicity cap.

Besides necessary degree/capacity checks, the only symmetry pruning is:

> When two consecutive future vertices have identical adjacency entries to all previously completed rows, their entries in the current row must be nonincreasing.

**Completeness proof.** In each isomorphism class choose a labeling that lexicographically maximizes the row-major upper-triangular adjacency string. Suppose future vertices `j<k` have identical adjacency to the vertices before the current row `i`, but `a_ij<a_ik`. Swapping `j,k` leaves all completed rows unchanged and increases the current row at its first changed entry, a contradiction. Therefore every lexicographically maximal labeling passes the generator's pruning. Checking consecutive equal-prefix vertices suffices for the implemented constraint; in particular it never excludes this maximal labeling.

Every entry value allowed by the remaining degree, multiplicity cap, and preceding equal-prefix entry is tried. A completed row has degree exactly four. The capacity check `remaining_degree<=M*(remaining_other_vertices)` is necessary for any completion. At the last row all degrees must be four, and a direct traversal checks connectivity. In the triangle-free cases an edge is forbidden exactly when it would close a triangle with an earlier vertex; every triangle would be detected when its second-smallest vertex's row is processed.

Thus every needed isomorphism class is represented. **Uniqueness is not asserted or needed.** No nauty output, stored isomorphism list, random sampling, or prior research checker is a premise of the delivered calculation.

### 5.2 Exact all-restriction calculation

For each generated graph, the checker:

1. Eliminates its binary incidence columns while retaining their relation words, obtaining a cycle-space basis.
2. Checks the dimension independently using `m-n+kappa`, enumerates the full basis span, and checks parity of every word. At `m<=12` it additionally compares against parity tests on **all** `2^m` edge subsets.
3. Enumerates all vertex-simple cycles by DFS with distinct edge identities. Independently, among **all even words**, it identifies the connected nonempty 2-regular supports and requires the two cycle lists to agree.
4. Computes both extrema for **every word**. For a nonempty even word `W`, let `e` be its least edge. Then
   \[
   c(W)=1+\min_{C\subseteq W,\ e\in C}c(W\setminus C),
   \quad
   \nu(W)=1+\max_{C\subseteq W,\ e\in C}\nu(W\setminus C). \tag{5.1}
   \]
   Every partition has a unique member containing `e`, so these are exhaustive recurrences. Dependencies have fewer edges. Actual attaining minimum and maximum partitions are reconstructed and checked for every word.
5. Computes `max_{W proper} c(W)` directly from the complete table. For each rejected non-fixed full-cost-three candidate, it also extracts a minimum-edge proper word with cost at least three, checks its cost is exactly three, checks **all** its proper even subwords have cost below three, and checks its maximum partition size is three.

The last step supplies genuine proper critical witnesses, rather than testing only cycle complements. No numerical optimization or rounding tolerance occurs.

### 5.3 Complete output totals

Counts below are **orderly presentations, potentially isomorphic**, not counts of distinct isomorphism classes.

| Core class | `n` | Presentations | Even restrictions audited | Non-fixed full-cost-three presentations rejected | Fixed-count-three critical presentations |
|---|---:|---:|---:|---:|---:|
| multigraph, `M=4` | 2 | 1 | 8 | 0 | 0 |
| multigraph, `M=4` | 3 | 1 | 16 | 0 | 0 |
| multigraph, `M=4` | 4 | 3 | 96 | 0 | 1 |
| multigraph, `M=4` | 5 | 12 | 768 | 3 | 0 |
| multigraph, `M=4` | 6 | 59 | 7,552 | 17 | 0 |
| multigraph, `M=4` | 7 | 364 | 93,184 | 105 | 0 |
| simple | 5 | 1 | 64 | 0 | 0 |
| simple | 6 | 1 | 128 | 0 | 0 |
| simple | 7 | 6 | 1,536 | 0 | 0 |
| simple | 8 | 35 | 17,920 | 0 | 0 |
| simple | 9 | 268 | 274,432 | 0 | 0 |
| triangle-free simple | 10 | 4 | 8,192 | 0 | 0 |
| triangle-free simple | 11 | 25 | 102,400 | 0 | 0 |
| **Total** | | **780** | **506,296** | **125** | **1** |

Every connected quartic core of order `n` has cycle dimension `n+1`, so each presentation contributes exactly `2^(n+1)` restrictions. The largest table has only 4,096 words. The printed output includes a SHA-256 digest of the graph list and all per-graph minimum/maximum restriction transcripts for each row.

These bounded calculations, together with the proved finite reduction and proved generator coverage, establish Proposition 5.1. They are a **computer-assisted finite proof**, not a purported paper-only Hamilton-decomposition theorem.

---

## 6. The cost-three theorem and the exact structural consequence

### Theorem 6.1

Every genuinely 3-critical finite even simple graph has `c=nu=3`.

**Proof.** If a 3-critical graph were non-fixed, Section 1 would give a connected loopless quartic 3-critical core. Corollary 4.2 places that core in the exhaustive finite calculation. Proposition 5.1 says that every critical cost-three core there is fixed-count. Subdivision preserves both partition extrema, giving a contradiction. ∎

The same argument starts from an arbitrary loopless multigraph, so the theorem is valid for those cores as well.

### Corollary 6.2 — the user's candidate through cost three

Let `G` be even with `c(G)<=3`. If it has two edge-disjoint simple cycles sharing at least three vertices, then

\[
 \exists\ W\subsetneq E(G),\quad W\text{ even},\quad c(W)\ge c(G).
                                                               \tag{6.1}
\]

**Proof.** The two-cycle expansion lemma makes their union non-fixed, and completing partitions with a partition of the even complement makes `G` non-fixed. For clarity, the expansion lemma can be seen by taking, in each cycle, a path between two common vertices avoiding a third common vertex. The two paths form a nonempty even subgraph, while the complementary even subgraph still has degree four at the third vertex. There is therefore a partition of the two-cycle union into at least three cycles, versus its original two.

If (6.1) were false, `G` would be genuinely `c(G)`-critical. Costs one and two are fixed-count by Section 1, and cost three is fixed-count by Theorem 6.1. Contradiction. ∎

In particular a counterexample to critical fixed count must have `q>=4`. This conclusion does **not** assume that the relevant two cycles belong to a chosen minimum partition.

The existing fixed-count graphic theorem additionally gives `cf(F)=p(F)=Q(F)=3` for a 3-critical `F`. This uses the already established fixed-count-to-fractional implication from `ResearchCriticalGraphic.md`, not a generic signed-state extension theorem. The new proof above only requires integral partition counts.

---

## 7. What remains missing for a universal bound

Lemma 2.1 holds for arbitrary `q`, but the small cycle-rank collapse used here is specific to the residual bound `Q<=1`. At the next critical cost it gives only

\[
 Q(F-V(C))\le2,
\]

which does not imply absence of two edge-disjoint cycles and does not imply `beta<=4`. For example the octahedral graph has `Q=2` and `beta=7`; its complete restriction table occurs in the simple six-vertex check. Consequently neither (4.1) with the same constant nor the finite list can simply be reused for `q>=4`.

The supplied secondary-potential tactic is not completed here. From a three-cycle expansion, criticality guarantees reoptimization of a complement, but no proved argument controls the lengths or the retained identities of the replacement cycles. This note supplies no lexicographic improvement theorem, no vertex-token allocation, and no universal critical average-degree or fractional-mean estimate.

There is an exact algorithmic recurrence useful for further critical searches. For every even `W`,

\[
 Q(W)=\max\left(c(W),\max_{C\subseteq W\text{ cycle}} Q(W\setminus C)\right),
                                                               \tag{7.1}
\]

and `W` is critical exactly when

\[
 c(W)>\max_{C\subseteq W\text{ cycle}}Q(W\setminus C).             \tag{7.2}
\]

Indeed, any proper even restriction `U` omits the edges of at least one cycle in the nonempty even complement `W\U`, so `U` is contained in one of the displayed cycle complements. **The quantity in (7.2) is hereditary `Q`, not `c` of that complement.** Also, unlike (5.1), the maximum in (7.1) must range over all contained cycles, not just cycles through a fixed edge. The optional-input checker implements this recurrence and audits all critical subrestrictions of the supplied graph. It is an exact finite diagnostic, not a general bound.

Thus the main requested universal result is still open in this investigation. There is no proved finite universal `C`, and no genuine non-fixed critical counterexample is claimed. The completed result is the all-size, cost-three theorem, with a rigorously bounded exhaustive core calculation.

---

## 8. Reproduction, controls, and file preservation

Run from the project root:

```sh
PYTHONHASHSEED=0 python3 -B ResearchCriticalStructureCheck.py
```

The default run uses **only the Python standard library**, reads no graph catalog, writes no files, and finishes with

```
ALL EXACT CHECKS PASSED
```

Two complete runs with `PYTHONHASHSEED=0` and `17` produced byte-identical output. The default stdout SHA-256 was

```
e2d0597b504f859f12e521df5c381cc535560b814fdbf9e5e762a74142c71328
```

As a separate verification, the isomorphism-class sets from the delivered generator were compared with independent `nauty-geng` / `nauty-multig` generation in **all thirteen** finite classes. Canonical sets agreed exactly. For multigraphs, comparison used the simple subdivision of every edge; original degree-four vertices and new degree-two vertices distinguish the two parts. This supplemental check is not a dependency of the default checker or its completeness proof. Syntax and optional-input checks also passed without creating bytecode files.

Additional independent controls include:

* literal cycle enumeration in `K_{3,3}`, checking sharpness of Lemma 3.1;
* the complete 64-word `K5` table, checking (7.1) against direct containment maxima and correctly reporting **not critical**;
* a simple subdivision of the positive four-vertex core: it has 8 vertices and 12 edges, and **all 32** even restrictions are checked. Its full cost and maximum count are three, and its maximum proper cost is two. The full even-word bijection with the core is verified. This is only a positive-control test, not the main structural advance.

The default check protects all **243 pre-existing non-cache project files outside `.lake`** using the same combined fingerprint computed before work:

```
40b4de36f0f5259f515157c6b897fae3611145bef9f190341d30146d6c99b104
```

The specification's unchanged SHA-256 is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

Both allowed new files are excluded from that pre-existing-file fingerprint. No other project file was intentionally written, including bytecode caches.

### Source scope

The previously supplied fixed-count source was checked at

```
/corpus/src/1708.09141/heinrichStreicherCycleDecompositionsAndConstructiveCharacterizations.tex
```

Its two-cycle expansion lemma and its equivalence between fixed count and the exclusion of edge-disjoint cycles meeting in more than two vertices are consistent with the argument above. It does **not** assert criticality implies fixed count. No such universal assertion has been imported from it. The vertex-deletion/rank/finite-core proof given here stands separately; the source is needed only for the recalled broader fixed-count consequences, not for the exhaustive criticality tests.
