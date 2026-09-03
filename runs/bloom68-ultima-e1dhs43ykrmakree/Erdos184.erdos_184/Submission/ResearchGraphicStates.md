# Graphic signed-state extension is false: an explicit K5 obstruction

## Outcome and scope

**The proposed universal signed-extension statement is false, already for the even simple graph `K5`.** The counterexample is not merely an arbitrary signed function: it is a **nonnegative normalized additive state** on all even edge subsets. It has no representation by edge prices, even when those prices may have either sign. A strictly positive variant is available as well.

The failure is certified in two ways:

* a short paper proof, using an explicit seven-cycle incidence identity;
* a complete exact audit of **all 64 even restrictions**, their **104 cycle partitions** in total, and **279 ordered disjoint pairs**. The space of additive functions has dimension **17**, whereas the space represented by edge prices has dimension **10**. Thus the relation-space defect is exactly **7**.

**This stops the proposed universal extension route.** No finite universal `K` with `cf(F) >= c(F)/K` for genuinely `q`-critical graphic `F` is proved or refuted here. The example itself is **not critical**, and it has `c(K5)=cf(K5)=2`. Neither Erdős–Gallai nor Hajós is proved or disproved.

Only these two files were created:

* `Submission/ResearchGraphicStates.md` — this report;
* `ResearchGraphicStatesCheck.py` — the exact, standard-library checker at the project root.

No specification or pre-existing research file was edited. These are paper-level and exact finite results, not a Lean formalization or a literature-priority claim.

---

## 1. The extension question and its relation-space formulation

Let `G=(V,E)` be a finite simple graph whose vertex degrees are all even. Let

\[
 Z=\{F\subseteq E:\text{every degree in }(V,F)\text{ is even}\}.
\]

The atoms of this concrete logic are the edge sets of vertex-simple cycles. Every word in `Z` is an edge-disjoint union of such atoms. An additive function is a map `m:Z -> R` satisfying

\[
 m(A\cup B)=m(A)+m(B)\qquad(A,B\in Z,\ A\cap B=\varnothing).
\]

In particular `m(empty)=0`. A state additionally has `m(F)>=0` and `m(E)=1`. Signed edge-price extension asks for real numbers `y_e`, **without sign restrictions**, such that

\[
 m(F)=\sum_{e\in F}y_e\qquad(F\in Z).                 \tag{1.1}
\]

Let `C` be the set of all simple cycles, and let `A` be the `E x C` matrix with columns `1_C`. For every `W in Z`, take the differences

\[
 \mathbf1_{\mathcal D}-\mathbf1_{\mathcal D'}
 \quad\text{for actual simple-cycle partitions }
 \mathcal D,\mathcal D'\text{ of the same }W.
\]

Let `R` be their real linear span in `R^C`. Here each partition covers an actual **0/1 restriction**, not a multiset of edges. Always `R subseteq ker A`.

An assignment of values to the atoms extends additively to `Z` if and only if it annihilates `R`: define the value of a word by summing over a partition; partition relations make this well-defined, and concatenating partitions proves additivity. It comes from edge prices if and only if it lies in `im A^T = (ker A)^perp`. Consequently the universal extension assertion on this graph is precisely

\[
 R=\ker A.                                          \tag{1.2}
\]

Sections 2–3 give an explicit failure of (1.2), without relying on computed ranks.

---

## 2. A state on every even restriction of K5

Label the vertices `0,1,2,3,4`, with indices read modulo five. Let

\[
\begin{aligned}
 P&=(0\,1\,2\,3\,4\,0),\\
 D&=(0\,2\,4\,1\,3\,0).
\end{aligned}
\]

These are complementary Hamilton cycles. Explicitly,

\[
\begin{aligned}
 E(P)&=\{01,12,23,34,04\},\\
 E(D)&=\{02,24,14,13,03\},\\
 E&=E(P)\mathbin{\dot\cup}E(D).
\end{aligned}
\]

We identify each cycle with its edge set. For any `epsilon` with `|epsilon|<=1/2`, define, on **every** `F in Z`,

\[
 m_\varepsilon(F)=\frac{|F|}{10}
             +\varepsilon\bigl(\mathbf1_{\{F=P\}}
                              -\mathbf1_{\{F=D\}}\bigr).       \tag{2.1}
\]

For the main example take `epsilon=1/2`. Thus only two values differ from the uniform edge-count state:

\[
 m(P)=1,\qquad m(D)=0;
 \qquad m(F)=|F|/10\quad(F\notin\{P,D\}).             \tag{2.2}
\]

### Proposition 2.1 — all disjoint-union additivity equations hold

For every `|epsilon|<=1/2`, (2.1) is a nonnegative normalized additive state on `Z`.

**Proof.** The function `F -> |F|/10` is additive. It remains to check

\[
 h(F)=\mathbf1_{\{F=P\}}-\mathbf1_{\{F=D\}}.
\]

A simple cycle has no proper nonempty even edge subset. Therefore:

* If an even set is disjoint from `P`, it is either empty or `D`, because it is an even subset of `E\P=D`.
* Similarly, the only even sets disjoint from `D` are empty and `P`.
* A union of two nonempty disjoint even sets cannot be `P` or `D`, since these are atoms.

Now take disjoint `A,B in Z`. If one is empty, additivity of `h` is immediate. If one is `P` or `D` and the other is nonempty, the pair is exactly `P,D`; their `h`-values cancel, and `h(E)=0`. In every remaining case, `A`, `B`, and `A union B` are all outside `{P,D}`, so all three `h`-values are zero. This exhausts **all** disjoint even pairs.

Finally `m_epsilon(E)=1`, and the only altered values are `1/2+epsilon` and `1/2-epsilon`. They are in `[0,1]`; so are all unaltered values. ∎

This argument does not infer additivity merely from a selected collection of full partitions. It proves the defining equation for arbitrary disjoint even restrictions. Also, choosing `epsilon=1/4` gives a **faithful state**: `0<m(F)<1` for every proper nonempty even `F`. The obstruction below applies to every nonzero `epsilon`, including this strictly positive example.

---

## 3. A real cycle relation that the state violates

For `i=0,...,4`, let `T_i` be the triangle with vertices `{i,i+1,i+2}`. These five triangles are

\[
 012,\quad123,\quad234,\quad340,\quad401.
\]

Each edge of `P` belongs to exactly two of these triangles; each edge of `D` belongs to exactly one. Hence the following equality holds over the integers, and in particular over the reals:

\[
 \boxed{\ \sum_{i=0}^4\mathbf1_{T_i}
                 =2\mathbf1_P+\mathbf1_D.\ }         \tag{3.1}
\]

If edge prices represented `m_epsilon`, applying their linear functional to (3.1) would give

\[
 \sum_{i=0}^4m_\varepsilon(T_i)
       =2m_\varepsilon(P)+m_\varepsilon(D).           \tag{3.2}
\]

But (2.1) gives

\[
 \sum_{i=0}^4m_\varepsilon(T_i)=5\cdot\frac3{10}
                              =\frac32,
 \qquad
 2m_\varepsilon(P)+m_\varepsilon(D)
       =2\left(\frac12+\varepsilon\right)
           +\left(\frac12-\varepsilon\right)
       =\frac32+\varepsilon.                        \tag{3.3}
\]

This is a contradiction whenever `epsilon!=0`. In the main example the two sides are **`3/2` and `2`**. No positivity assumption on the hypothetical `y_e` was used.

Thus, in cycle-coordinate notation,

\[
 r=\sum_{i=0}^4 e_{T_i}-2e_P-e_D
 \quad\text{satisfies}\quad
 Ar=0,\qquad m_\varepsilon\cdot r=-\varepsilon\ne0.   \tag{3.4}
\]

Proposition 2.1 shows that `m_epsilon` annihilates every actual partition difference of every even restriction. Therefore (3.4) proves directly that

\[
 r\in\ker A\setminus R.
\]

The multiplicity-two load on the edges of `P` in (3.1) is precisely what is missing from disjoint-union additivity on 0/1 restrictions. Hahn–Banach cannot repair this: the proposed linear functional already assigns inconsistent values to a genuine real incidence relation.

---

## 4. Complete audit and the exact seven-dimensional defect

### 4.1 All 64 words, not just full partitions

`K5` has ten edges and binary cycle-space dimension `10-5+1=6`. Its even restrictions are completely classified as follows.

| Edge count | Number of words | Type | Partitions per word |
|---:|---:|---|---:|
| 0 | 1 | empty | 1 (empty partition) |
| 3 | 10 | triangle | 1 |
| 4 | 15 | quadrilateral | 1 |
| 5 | 12 | Hamilton cycle | 1 |
| 6 | 15 | two triangles sharing one vertex | 1 |
| 7 | 10 | `K5` minus a triangle: `K_{2,3}` plus the edge joining its two degree-four vertices | 3 |
| 10 | 1 | `K5` | 21 |

The six-edge words are complements of quadrilaterals; each is a figure eight with its unique two-triangle partition. In a seven-edge word, the three partitions choose one of the three length-two terminal paths to make a triangle with the terminal edge; the other two paths form a quadrilateral.

The full partitions consist of:

* **6** complementary pairs of Hamilton cycles;
* **15** partitions of type `triangle + triangle + quadrilateral`, one for each quadrilateral, whose complement has a unique two-triangle partition.

There are no other possible full length patterns: all simple cycles have lengths between three and five, and the total edge count is ten. The table contains **104 partitions in total**. Direct enumeration also gives **279 ordered pairs `(A,B)` of disjoint even words**, including pairs involving the empty set.

The checker independently obtains the words by parity tests on all `2^10` edge subsets and by the span of six fundamental cycles. It obtains the atoms both by support minimality among the 64 words and by vertex-simple DFS. It enumerates partitions by choosing the unique cycle containing the least remaining edge and recurring on its complement. Thus it covers every unordered partition once, not just minimum partitions or an old decomposition's subunions.

### 4.2 Full-restriction relations really do suffice here — with a proof

There is a useful general observation for an **even ambient graph**. If `D1,D2` partition the same even `W`, fix any cycle partition `B` of `E\W`, which is also even. Then

\[
 \mathbf1_{\mathcal D_1}-\mathbf1_{\mathcal D_2}
  =\mathbf1_{\mathcal D_1\cup\mathcal B}
    -\mathbf1_{\mathcal D_2\cup\mathcal B}.           \tag{4.1}
\]

The right side is a difference of full partitions. Hence the span of full partition differences equals `R`. This is a completion-and-cancellation argument, not an assumption that checking full partitions always substitutes for checking restrictions in other questions. In particular it says nothing about `q`-criticality. **The checker nevertheless generates the relations from all 64 restrictions separately**, as requested.

### 4.3 Exact dimensions, also justified without a computer

The checker finds:

| Matrix or space | Size / dimension |
|---|---:|
| Simple cycles | 37 |
| Incidence matrix `A` | `10 x 37`, rank **10** |
| `ker A` | **27** |
| Full partition-difference rows | 20 rows, rank **20** |
| All-restriction partition-difference rows | 40 rows, rank **20** |
| Additive functions, `R^perp` | **17** |
| Edge-price-representable functions, `im A^T` | **10** |
| Quotient `ker A / R` | **7** |

Here one partition is fixed as a reference for each word; differences from that reference span all differences for the word. Thus the 40 rows are `104-64`, not an incomplete selection. All ranks use exact rational elimination; for integer matrices these are also the real ranks. Adding the explicit relation (3.4) raises the row rank from 20 to 21.

For a paper verification of the two ranks:

**Rank of the incidence matrix.** The ten triangle columns alone have rank ten. Indeed, suppose edge prices give sum zero on every triangle. Put `a_i=y_{0i}` for `i=1,2,3,4`. The triangles through zero force `y_{ij}=-a_i-a_j` for `i,j!=0`. The four triangles avoiding zero then force every three-term sum of the four `a_i` to be zero. Subtracting these equations makes all `a_i` equal, and a three-term equation makes their common value zero. All edge prices vanish. Thus the triangle matrix is nonsingular and `rank A=10`.

**Rank of the partition relations.** Choose one Hamilton-pair partition as reference. Each of the 15 triangle-triangle-quadrilateral partitions contains a distinct quadrilateral, which appears in none of the other full partitions. Its difference row therefore has a private coordinate. The other five Hamilton-pair partitions likewise each have private Hamilton-cycle coordinates, because each Hamilton cycle has a unique complementary Hamilton cycle. The 20 difference rows are independent. By (4.1) they generate all restriction relations, so `dim R=20`.

Equivalently, every additive function on this `K5` logic can be parametrized by:

1. arbitrary values on the **10 triangles**;
2. an arbitrary total value `s=m(E)`;
3. an arbitrary value on one Hamilton cycle in each of the **6 complementary pairs**.

The other Hamilton-cycle value in each pair is `s` minus the chosen value. The value on each quadrilateral is `s` minus the values of the two triangles in its complement. These assignments give total `s` on every full partition and, by (4.1), well-defined additive values on every word. This gives exactly `10+1+6=17` parameters. Edge prices occupy only a ten-dimensional subspace.

---

## 5. What this does and does not say about critical restrictions

Recall the genuine hypothesis from `Submission/ResearchCriticalGraphic.md`:

\[
 c(F)=q,\qquad c(W)<q
       \quad\text{for EVERY proper even }W\subsetneq F.         \tag{5.1}
\]

The graph in this report is not such a restriction:

* `P,D` partition `K5`, so `c(K5)<=2`; its degree-four vertices force at least two cycles. Hence `c(K5)=2`.
* All cycles have at most five edges. The uniform dual price `y_e=1/5` is feasible for exact fractional partition cost and has total value two. Together with the two-cycle partition this gives **`cf(K5)=2`**.
* The proper even restriction consisting of triangles `012` and `034` has cost two: it has the displayed two-cycle partition, and its shared vertex has degree four. Therefore the strict inequality in (5.1) fails.

In fact the complete table shows that the maximum integer cost of a proper even restriction is two, while the full graph also has three-cycle partitions. None of this is a critical fractional gap.

Accordingly:

* The universal graphic **signed-state-extension premise is disproved**.
* A proposed proof that builds an abstract additive state and then invokes universal signed extension is invalid unless it separately verifies the missing real relations for the particular state it builds.
* This counterexample does **not** rule out extension on a narrower class of genuinely critical graphs, nor construction of a special edge-representable state on those graphs. Neither is proved here.
* It does **not** refute the finite-`K` critical bound, nor establish any such `K`. The independent graphic `cf <= rank` input is unchanged, but no new rounding step is supplied to combine with it.

As requested, the route stops at the graphic counterexample. There is no random graph catalog, unrelated gadget construction, or unsupported critical-state/Hahn–Banach assertion.

---

## 6. Literature scope and verification

The supplied local source is Anna De Simone, Mirko Navara, and Pavel Pták, *Extending states on finite concrete logics*, arXiv:math-ph/0311012, at

```
/corpus/src/math-ph_0311012/math-ph0311012.tex
```

It defines signed measures, states, and difference-closed concrete logics in exactly the relevant sense. Its theorem labelled `ext-even` treats the logic of **all even-cardinality subsets of an even-cardinality set**. That is not the graphic logic here: an even-degree edge set in `K5` can have odd cardinality, including triangles and Hamilton cycles. Its non-extension examples for other difference-closed logics motivate checking the relations but are not used as a substitute for a graphic example. The `K5` proof above is self-contained; no claim is made that this example or its dimension calculation is new in the literature.

Run from the project root:

```sh
PYTHONHASHSEED=0 python3 ResearchGraphicStatesCheck.py
```

The checker uses only the Python standard library and exact integers/rationals. It writes no files and checks:

* the actual even simple graph, all 64 words, all 37 atoms, all 104 partitions, and all 279 ordered disjoint pairs;
* all state equations and bounds for `epsilon=1/2`, and strict positivity on proper nonempty words for `epsilon=1/4`;
* every relation row against the edge-incidence matrix and the state;
* both matrix ranks, the explicit violated incidence identity, and the rank increase when that missing relation is adjoined;
* the exact primal/dual certificates for `cf(K5)=2` and the proper cost-two bowtie witness against criticality;
* unchanged protected-file hashes during execution and the specification hash.

The delivered checker passed with distinct hash seeds. A separate independent frozenset-based verification also reconstructed all 64 words, checked all 279 disjoint pairs, and checked (3.1) edge by edge, obtaining the same contradictory state evaluations `3/2` and `2`.

The pre-work fingerprint of all **239 pre-existing project files outside `.lake`**, excluding only the two permitted new paths, was

```
cdc119b949d1b55cefffa89ccbf1d5d595ce810c27ca08de1a7d806c8511d062
```

It remained unchanged. The protected `Submission/Spec.lean` SHA-256 is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

The universal-claim status is therefore precise: **graphic signed extension is false; the genuine critical finite-constant bound and Erdős–Gallai remain unresolved by this route.**
