# Simultaneous 2-factorizations: regular obstructions and a linear cut-defect budget

## Status and main results

**Neither the general Erdős–Gallai O(n) theorem nor the proposed O(n) total-component 2-factorization theorem for arbitrary even-regular simple graphs is proved here. No counterexample to the latter count theorem is obtained.** In particular, the bound `r+n` is not established or refuted.

The unrestricted **all-long** strengthening is, however, decisively false even for regular graphs of arbitrarily large degree. The investigation also gives a fixed-original-degree way to handle low cuts, a usable weaker simultaneous target, and an unconditional dense-piece consequence.

1. **Every factor can be forced to be short.** For every `r>=2` there is a connected simple `2r`-regular graph `W_r` with

   ```
   n=(2r+1)^2,
   minimum cycle-partition size
     = minimum total components in a 2-factorization
     = r(2r+1).
   ```

   **Every spanning 2-factor contains a triangle.** In every 2-factorization, all `r` factors contain a triangle, and the same vertex lies on a triangle in every factor. Nevertheless the displayed minimum total count is less than `n/2`. A second, denser example has `n=6r+6`, a compulsory triangle, and exact minimum count `3r+1`.

2. **An exact regular-completion and factor-gluing lemma.** An arbitrary even graph of maximum degree at most `2r` can be retained as a forced cycle core of a regular graph by explicit Walecki lobes. Both the unrestricted cycle count and the minimum total factor-component count satisfy exact additive formulas. Color compatibility at articulation vertices is proved, rather than assumed.

3. **Regularity pays for low-cut defects linearly.** If a `D`-regular simple graph is split into its cycle blocks, the total number of missing factor slots is at most

   ```
   (3/4)(n-(D+1)c),
   ```

   where `c` is the number of connected components. The coefficient `3/4` in the coarser bound `(3/4)n` is asymptotically sharp. For recursive separations of order two, a connected graph has at most

   ```
   t <= 1 + 3(n-D-1)/(D-3)                              [D>3]
   ```

   nondegenerate terminal pieces. Their aggregate degree deficit is O(n), not O(nD). Parity repair, auxiliary edges, and restoration of **simple** cycles are accounted for explicitly.

4. **Dense bounded-order pieces really are resolved.** Using the verified Conlon–Fox–Sudakov dense theorem, if those terminal pieces have order at most `K D` for a fixed `K`, then the original regular graph has an `O(K^12 n)` **simple-cycle partition**. Low-degree peeling is paid by the fixed deficit budget, and there is no logarithmic number of density rounds. This is not asserted to produce a 2-factorization.

5. **A weaker simultaneous criterion allows short components.** Match short factor-components to vertex tokens and missing factor slots. If suitable local partial factorizations satisfy this Hall condition, then block gluing gives a genuine 2-factorization with at most `6n` total components. After general 2-vertex separations, the same condition on the 3-connected terminal pieces gives at most `10n` simple cycles. The universal existence of the Hall-certified local factorizations is the missing assertion; the implication and all its accounting are proved.

6. **The earlier high-Berge-girth obstruction has good factorizations, not merely good partitions.** Its balanced high-directed-girth orientation can be factorized simultaneously. In the checked 2520-vertex example, this yields **three 2-factors with 4 components each: 12 simple cycles in total**, with minimum length 9. Thus this prior local-exchange barrier is not a counterexample to the factorization target either.

The new results here are research lemmas and constructions, not a claim of priority over uninspected literature. `Submission/Spec.lean` and the previous research notes were not edited. The specification hash is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

---

## 0. Conventions and the count that matters

Graphs are finite, simple and undirected unless auxiliary multiedges or an orientation are explicitly introduced. Put

```
D=2r,                  m=rn=Dn/2.
```

A 2-factor is spanning and 2-regular. A 2-factorization has exactly `r` factors, but its cost is

```
q(F)=sum_{i=1}^r number_of_cycle_components(F_i),          (0.1)
```

**not** the number `r` of factors. Write `f_2(G)` for the minimum of (0.1) when G is `2r`-regular.

For an even graph H with maximum degree at most `2r`, a **partial r-factorization** means an edge coloring with colors `1,...,r` such that every color has degree either 0 or 2 at every vertex. Its nonempty components are cycles; isolated vertices and empty color classes do not count. Write `Q_r(H)` for its minimum total cycle count, and `c(H)` for the minimum count in an unrestricted simple-cycle partition. Thus `Q_r(G)=f_2(G)` for a `2r`-regular G, but equality between `Q_r(H)` and `c(H)` is not assumed in general.

For a threshold `L=alpha D`, an all-long 2-factorization would have

```
q(F) <= m/L = n/(2 alpha).
```

By contrast, a hypothetical per-step guarantee of cycles of length proportional to the **current** remaining regular degree only gives an estimate proportional to

```
n sum_{s=1}^r 1/s.
```

Nothing below uses that estimate. `D` is fixed at the degree of the original regular graph throughout the cut and deficit accounting.

---

## 1. Literature audit: relevant results and non-results

The search used `/corpus/metadata.jsonl`, targeted title/abstract filters, and full-text searches in **638 candidate source directories, containing 802 relevant-format text files**. The candidate filters were deliberately broad and included false positives. This is a statement about the local corpus searched, not an exhaustive claim about later literature.

### 1.1 Petersen and Tutte do not bound the total components

* **Petersen:** every positive even-regular graph has a 2-factor. An explicit local statement is `/corpus/src/1401.4159/1factrevision.tex`, theorem `petersen`, around lines 685–690. Iteration gives a 2-factorization, not an O(n) bound on (0.1).
* **Tutte's 2-factor criterion:** see `/corpus/src/1404.6299/Vizing_2-factor.tex`, theorem `tutte's theorem`, around lines 285–293. It decides existence of a 2-factor. It does not impose a girth or total-component constraint. Section 2 below gives the elementary orientation/matching construction needed for the partial version used here.

### 1.2 Jackson: one Hamilton cycle under dense 2-connectivity

The Jackson theorem quoted explicitly in `/corpus/src/1706.04334/partial-3-trees.tex`, theorem `thm:jackson`, lines 1843–1847, is:

> Every 2-connected k-regular graph with at most 3k vertices is Hamiltonian.

It is a single-cycle theorem. Deleting its Hamilton cycle need not preserve 2-connectivity, and its degree-to-order hypothesis deteriorates. It does not provide a coordinated factorization at the original degree scale.

### 1.3 A genuine simultaneous theorem in the very dense range

**Béla Csaba, Daniela Kühn, Allan Lo, Deryk Osthus, Andrew Treglown, _Proof of the 1-factorization and Hamilton Decomposition Conjectures_, arXiv:1401.4159.**

`1factrevision.tex`, theorem `HCDthm`, around lines 173–180, states that for sufficiently large order, every D-regular graph with `D>=floor(n/2)` has a decomposition into Hamilton cycles and at most one perfect matching. For even D, this is exactly `r` Hamilton cycles, so total component count equals factor count in this particular theorem. The density hypothesis cannot be discarded.

### 1.4 Long-girth factorization titles require care

* **Italo J. Dejter, _Tight factorizations of girth-g-regular graphs_, arXiv:2102.06956.** `/corpus/src/2102.06956/ho012822.tex`, introduction, especially lines 32–63. Its “tight” factorization is a **1-factorization** with a rainbow condition on the graph's girth cycles; the studied degree/girth/chromatic-index parameters coincide. It is not a theorem giving arbitrary regular graphs 2-factors with components of length proportional to the degree.
* **Felix Joos, Marcus Kühn, Bjarne Schülke, _Decomposing hypergraphs into cycle factors_, arXiv:2104.06333.** `/corpus/src/2104.06333/hamdecomp_arXiv.tex`, theorems `simple2 min_deg` and `main`, around lines 98–129. These are **approximate** packings under dense codegree/intersection hypotheses. The input factors can have sufficiently large fixed girth `L`, depending on fixed parameters. This is neither an exact arbitrary-degree decomposition nor the required fixed-original-degree statement.
* **Vytautas Gruslys, Shoham Letzter, _Cycle partitions of regular graphs_, arXiv:1808.00851.** `/corpus/src/1808.00851/path-partition-v7.tex`, theorem `main`, around lines 120–124, partitions **V(G)** into few cycles in the dense range. It is not an edge factorization.

### 1.5 Minimum-component objectives really occur, but without the proposed bound

* **Andrei V. Nikolaev, Egor V. Klimov, _Finding a second Hamiltonian decomposition of a 4-regular multigraph by integer linear programming_, arXiv:2201.03846.** `/corpus/src/2201.03846/KlimovNikolaev2022.tex`, around line 471, explicitly minimizes the **total number of connected components in two 2-factors**. This is genuinely the relevant type of objective, but the paper develops exact algorithms/heuristics for degree four, not a uniform arbitrary-degree O(n) theorem. Degree four already has a trivial linear count bound.
* **M. Abreu, D. Labbate, J. Sheehan, _Pseudo and Strongly Pseudo 2-Factor Isomorphic Regular Graphs_, arXiv:1002.1033.** `/corpus/src/1002.1033/1002.1033.tex`. Its restrictions on invariant component-count parity in high-degree regular graphs do not give a quantitative minimum total component count over a whole factorization.
* **Irene Heinrich, Manuel Streicher, _Cycle Decompositions and Constructive Characterizations_, arXiv:1708.09141.** The paper characterizes uniqueness of the cardinality of unrestricted cycle decompositions. It does not supply a resolvable minimum-component theorem.

### 1.6 The applicable dense theorem, and the explicit simultaneous gap

* **David Conlon, Jacob Fox, Benny Sudakov, _Cycle packing_, arXiv:1310.0632.** `/corpus/src/1310.0632/1310.0632.tex`, theorem `EGlargemin`, around lines 41–45: minimum degree at least `eta h` gives `O(eta^-12 h)` cycles and singleton edges. Theorem 4.3 below uses this theorem with a fixed eta and converts the final even remainder into cycles. It does not claim a factorization from the dense theorem.
* **António Girão, Bertille Granet, Daniela Kühn, Deryk Osthus, _Path and cycle decompositions of dense graphs_, arXiv:1911.05501.** Its dense Eulerian count results do not assert that all output cycles have length proportional to the original degree, or that their cycles can be grouped into exactly r spanning 2-factors.
* **Charlotte Knierim, Maxime Larcher, Anders Martinsson, Andreas Noever, _Long Cycles, Heavy Cycles and Cycle Decompositions in Digraphs_, arXiv:1911.07778.** `conclusion.tex` explicitly proposes finding cycles simultaneously as a possible way to remove its logarithmic loss. Its proved decomposition accounting uses current degrees and harmonic sums, not an original-degree simultaneous assertion.

**Audit conclusion:** no inspected source supplied the requested arbitrary-degree `f_2(G)<=C n` or `f_2(G)<=r+n` theorem. In particular, no factor-count statement has been substituted for a cycle-count statement.

---

## 2. Partial factorizations and exact articulation gluing

### Lemma 2.1 — partial r-factorizations exist

Every even loopless multigraph H with maximum degree at most `D=2r` has a partial r-factorization. In a simple graph its nonempty components are simple cycles of length at least three.

**Proof.** Orient each nontrivial connected component Eulerianly, giving

```
d^+(v)=d^-(v)=d_H(v)/2.
```

Add

```
ell_H(v)=r-d_H(v)/2                                    (2.1)
```

dummy directed loops at v. Split each vertex into a left and a right copy, and replace an arc `u->v` by a bipartite edge `u_L v_R`. This is an r-regular bipartite multigraph. Hall's theorem supplies a perfect matching; removal preserves regularity, so all edges can be partitioned into r perfect matchings.

Each matching pulls back to a directed cycle cover. Delete the dummy loops. At each vertex and in each color the remaining degree is 0 or 2. All non-loop components are directed simple cycles. In a simple oriented graph a directed 2-cycle cannot occur, since there is only one orientation of an undirected edge. Auxiliary parallel edges can give length-two cycles; these are allowed until the auxiliary edges are restored. □

Exactly `ell_H(v)` colors are absent at v. These are **missing factor slots**, not extra cycle components.

### Lemma 2.2 — component-optimal block factorizations glue simultaneously

Let G be a `2r`-regular simple graph and let `B_1,...,B_b` be its blocks. Then

```
f_2(G)=sum_j Q_r(B_j).                                  (2.2)
```

More generally, arbitrary prescribed partial r-factorizations of the blocks can be glued by blockwise color permutations without changing any of their cycles or their total count.

**Proof.** An even graph has no bridges. Its blocks are even: the parity of the edges from a cut vertex into any component on the other side follows from the degree sum in that component. Every simple cycle lies in one block.

For the upper bound root each block-cut tree. At a cut vertex v, block B uses `d_B(v)/2` colors. These sizes sum to r over all incident blocks. After the parent block is colored, partition the unused colors into subsets of the required sizes for the child blocks. A permutation of a child block's entire palette sends its used-color set at v to its allocated subset. There is only one already constrained cut vertex for that child block; proceed down the tree.

At each original vertex every color now has degree exactly two. A color is used by only one incident block at a cut vertex, so all component cycles remain exactly the local cycles. This produces a genuine r-factorization with their summed count. Conversely, restricting a global factorization to a block gives a partial r-factorization, because each global component lies in a block. This proves the lower bound and (2.2). □

This is a simultaneous color-gluing statement. It is **not** valid with the same proof for pieces meeting in two vertices; see Section 5.

---

## 3. Explicit regular counterexamples to all-long factors

### 3.1 A Walecki lobe with prescribed missing root slots

On private vertices `Z_(2r) union {infinity}`, use the Hamilton cycles, for `i=0,...,r-1`,

```
C_i = (infinity, i, i-1, i+1, i-2, i+2, ...,
       i-(r-1), i+(r-1), i-r, infinity),                 (3.1)
```

with finite labels modulo `2r`.

These partition `K_(2r+1)`: finite edges in `C_i` have endpoint sum `2i-1` or `2i` modulo `2r`, and the infinity edges cover the two finite endpoints `i,i-r`.

The antipodal matching

```
M={ {x,x+r}: x=0,...,r-1 }
```

is rainbow across these cycles. Indeed, the edge indexed by x lies in color

```
i = x + ceil(r/2)  (mod r).                             (3.2)
```

Fix `0<=k<r`. Choose the matching edge in each of `r-k` of the Hamilton cycles and subdivide all these chosen edges by **one new common root z**. Their endpoints are distinct, so the resulting graph is simple. Call it `L_(r,k)`.

Every private vertex still has degree `2r`, while

```
d(z)=2(r-k).
```

Its edges are partitioned into exactly r simple cycles:

* `r-k` cycles of length `2r+2`, containing z;
* k cycles of length `2r+1`, not containing z.

Thus this lobe has exactly k missing factor slots at its root and none at its private vertices. It is 2-connected: for `r>=2`, deleting the root leaves a clique minus a matching, while deleting one private vertex leaves the root with a neighbor and the remaining private graph connected. The `r=1,k=0` case is the 4-cycle and is checked directly. In particular, root degree two is allowed.

### Theorem 3.1 — exact regular completion of an even cycle core

Let H be any even simple graph on N vertices with maximum degree at most `2r`. Put

```
S={v: d_H(v)<2r}.
```

For each `v in S`, attach a private copy of `L_(r,d_H(v)/2)` by identifying its root with v. Do nothing at vertices of degree `2r`. The resulting simple graph G is `2r`-regular, has

```
|V(G)|=N+(2r+1)|S|,                                    (3.3)
c(G)=r|S|+c(H),                                        (3.4)
f_2(G)=r|S|+Q_r(H).                                    (3.5)
```

**Proof.** The degree assertion follows from the root-degree formula. Every simple cycle of G lies wholly in H or wholly in one attached lobe: a cycle cannot leave and re-enter a lobe through its sole attachment vertex without repeating that vertex.

Each lobe needs at least r cycles in any cycle partition, since a private vertex has degree `2r`. Its construction supplies exactly r. This proves (3.4).

For (3.5), restrict any global factorization to the core and the lobes to get the lower bound. Conversely, choose an optimal partial r-factorization of H. At v it uses `k=d_H(v)/2` colors. Permute the lobe's r colors so that precisely those k colors are the ones absent at its root. Its root-using cycles fill all other colors at v. Do this independently for every attached lobe. All original vertices and all private vertices then have degree two in every color, without changing any cycles. □

If every vertex is deficient, (3.3) becomes `n=(2r+2)N`. Since `Q_r(H)<=e(H)/3`, this explicit family already satisfies

```
f_2(G) <= rN+(r-1)N/3 < (2/3)n.                        (3.6)
```

The regularization preserves an arbitrary even cycle core, but incurs `Theta(r)` vertices per deficient vertex. It is **not** a linear-vertex reduction from general even graphs to the regular case.

### 3.2 A dense regular graph with a compulsory triangle

Take `H=K_3` and `r>=2`. Then `S=V(H)` and `Q_r(H)=c(H)=1`. Theorem 3.1 gives

```
n=6r+6,                  f_2(G)=c(G)=3r+1.              (3.7)
```

The core triangle occurs in **every** cycle partition. One explicit factorization has:

* one factor consisting of that triangle and three private `(2r+1)`-cycles;
* `r-1` factors, each consisting of three `(2r+2)`-cycles.

This is a simple regular graph of degree about one third of its order, not a bounded-degree example. Its dense lobes do not remove the obstruction at the articulation vertices.

### 3.3 A triangle in every factor, not just a bounded number of bad factors

Take H to be a windmill of r triangles with common center x and otherwise disjoint vertices. Then

```
|V(H)|=2r+1,        d_H(x)=2r,        d_H(v)=2 for v!=x.
```

For `r>=2`, attach the lobes only to the `2r` noncentral vertices. Call the result `W_r`. All core triangles are compulsory, so `c(H)=Q_r(H)=r`; in a partial r-factorization they have distinct colors at x. Therefore

```
|V(W_r)|=(2r+1)^2,
f_2(W_r)=c(W_r)=2r^2+r=r(2r+1)<|V(W_r)|/2.             (3.8)
```

Every spanning 2-factor contains x. The component through x must be one of the core triangles, because no simple cycle can enter an attached lobe and leave it again. Thus **every spanning 2-factor of W_r contains a triangle**, irrespective of whether it was selected as part of a factorization.

Consequences, with their exact quantifiers:

* For every positive c, taking `r>3/c` refutes “every `2r`-regular simple graph has a 2-factorization with every component of length at least `c r`.”
* Even “there is one such all-long 2-factor” fails for unrestricted regular graphs.
* One cannot repair the statement by allowing only an absolute number of factors to be bad: all r factors of `W_r` are bad.
* One cannot demand an absolute bound on the number of short factor-components through each original vertex: x is on r compulsory triangles.
* These examples **do not** refute the total-count target: their exact optimum is linear.
* Their connectivity is one. They do **not** refute an all-long assertion after a valid 2-connected or 3-connected reduction, or the 3-connected original-degree-heavy-cycle conjecture in `ResearchHeavy.md`.

The compulsory triangles have original-degree weight `3/(2r)`, tending to zero. This does not change the prior `c>3/4` obstruction for the differently quantified 3-connected weighted target.

---

## 4. Low cuts have a linear fixed-degree budget

### 4.1 The elementary density envelope

For every simple graph J on `h>=3` vertices with maximum degree at most D,

```
2e(J) <= (D+3)h-3(D+1).                                (4.1)
```

For `3<=h<=D+1`, subtracting `h(h-1)` from the right side gives

```
(h-3)(D+1-h)>=0.
```

For `h>=D+1`, use `2e(J)<=Dh`, and the remaining difference is `3(h-D-1)>=0`. This simple convex-envelope inequality drives both ledgers below.

### Theorem 4.1 — sharp linear block-defect budget

Let G be a simple D-regular even graph with n vertices, c connected components and b blocks. Then

```
2Db <= 3n-(D+3)c,                                      (4.2)
sum_B sum_{v in B} (D-d_B(v)) = D(b-c),                 (4.3)
sum_B sum_{v in B} ell_B(v)
    = D(b-c)/2
    <= (3/4)(n-(D+1)c).                                (4.4)
```

**Proof.** All blocks have at least three vertices, and the block-cut forest identity is

```
sum_B (|B|-1)=n-c.
```

Sum (4.1) over blocks, using `sum e(B)=Dn/2`, to obtain (4.2). Also `sum |B|=n+b-c`, and summing the deficits gives (4.3). Divide by two and substitute (4.2) to get (4.4). □

In particular, all blocks of order at most `D/2+1` together have at most `(3/4)n` edges. Indeed, in such a block

```
e(B)<=D|B|/4 <= D|B|/2-e(B)=sum_v ell_B(v).
```

Their entire cycle cost can be paid linearly, without any lower bound on their cycle lengths.

**Sharpness of the coefficient.** Let the core be a chain of t triangles, with `2t+1` vertices and maximum degree four, and attach the lobes of Theorem 3.1 at every core vertex, with `D>=6`. Then

```
n=(D+2)(2t+1),       b=3t+1,
sum ell = 3Dt/2.
```

The ratio `(sum ell)/n` approaches `3/4` as t and then D tend to infinity. Alternatively, the windmill completion `W_r` itself has `b=3r` and `sum ell=r(3r-1)`, whose ratio to `(2r+1)^2` also tends to `3/4`. Thus the missing slots are genuinely a linear-sized resource; they cannot simply be ignored, and the coarser coefficient `3/4` cannot be uniformly reduced.

### Theorem 4.2 — the 2-separator ledger and parity-preserving reconstruction

Let G be connected, simple, even and D-regular, with `D>3`. Recursively split along separating sets of two vertices, always keeping both child orders at least three. Cuts of order zero or one can be padded to order two, retaining a nonempty interior on each side. Stop when a piece has order three or its underlying simple graph is 3-connected.

At each split, partition the existing edges between the children, assigning any pole-pole edges to one side. If both poles are odd in a child, add a virtual edge between them to **each** child. Let t be the number of terminal pieces and p the number of splits requiring this parity repair. Let `H_j^+` denote the augmented terminal multigraphs, and `H_j` their real-edge subgraphs, on the same vertex sets. Then

```
sum_j (|H_j|-2)=n-2,                                   (4.5)
t <= 1+3(n-D-1)/(D-3),                                 (4.6)
number of virtual edges = 2p <= 2(t-1),                 (4.7)
Delta_real := sum_j sum_v (D-d_{H_j}(v))=2D(t-1),        (4.8)
Delta_aug  := sum_j sum_v (D-d_{H_j^+}(v))
           =2D(t-1)-4p.                                (4.9)
```

All augmented pieces are even and have maximum degree at most D. In particular their total number of missing factor slots is

```
Lambda = Delta_aug/2 = D(t-1)-2p = O(n).                (4.10)
```

For `D>=6`, the useful coarse bounds are

```
sum_j |H_j| <= 3n,
Lambda <= Delta_real/2 <= 6n.
```

**Proof of the degree/parity claims.** All non-pole vertices keep their degree at a split. The two possible odd vertices in a child must have the same parity, by the degree sum. The parent is even, so the parity is the same in both children. Add the two virtual edges exactly when required.

At a pole with an odd child degree, both child degrees before repair are positive odd integers. Adding one to either is at most their sum, which is the parent degree. Thus the maximum degree never exceeds the fixed original D. Parallel edges are possible and are marked virtual; no loops are introduced.

Equation (4.5) follows by induction on the split tree. Real edges still partition E(G), so summing (4.1) for the **simple real-edge graphs** gives

```
Dn <= (D+3)(n+2(t-1))-3(D+1)t,
```

which rearranges to (4.6). Degree sums give (4.8)–(4.9). Notice that applying (4.1) to augmented multigraphs instead would be invalid; it is simplicity of the real-edge graphs that is used. □

**Reconstruction of cycles.** Suppose each augmented leaf has a simple-cycle partition, allowing cycles of length two made possible by auxiliary parallel edges. At a repaired split, delete the paired virtual edges from the two cycles containing them. This leaves two simple pole-to-pole paths whose interiors lie on opposite sides of the separator. Their union is a simple cycle. Replace the two old cycles by this one. Unrepaired splits simply keep both partitions.

Consequently the reconstructed partition has exactly

```
q_original = sum_j q_j - p.                            (4.11)
```

At the end all virtual edges have disappeared. The original graph is simple, so no length-two cycle remains. This is an edge partition into genuine simple cycles, not a partition into closed trails.

The ordinary bound `t=O(n)` would only pay `O(nD)` missing slots. Equation (4.6), using regularity, is the essential improvement. There is no charge once per cut depth or degree scale.

### 4.3 Deficit-paid low-degree peeling

Here the real-edge graph H need not be even. Assume only `Delta(H)<=D`, and define

```
Delta(H;D)=sum_v (D-d_H(v)).
```

Repeatedly delete a vertex of **current** degree less than `D/4`, where D remains fixed. Let R be the deleted vertices and let M be the number of edges deleted. Then

```
M <= Delta(H;D)/2,                 |R| <= 2 Delta(H;D)/D. (4.12)
```

**Proof.** Count each deleted edge when its first endpoint is deleted. Thus

```
M=e_H(R)+e_H(R,V(H)\R) <= D|R|/4.
```

Writing `Delta_R=sum_{v in R}(D-d_H(v))`,

```
Delta_R = D|R|-2e_H(R)-e_H(R,V(H)\R)
        >= D|R|-2M
        >= D|R|/2.
```

Combine the inequalities. □

This is not a harmonic current-degree argument: the deletion threshold is a fixed fraction of the original D, and every deleted edge is charged to a fixed deficit. More generally a threshold `theta D`, for `theta<1/2`, costs at most `theta Delta/(1-2theta)` edges.

### Theorem 4.3 — bounded-order dense terminal pieces give genuine O(n)

Fix `K>=1`. Suppose the terminal pieces in Theorem 4.2 all have order at most `K D`. Then G has an `O(K^12 n)` **simple-cycle partition**, with a constant independent of D and of the number or depth of cuts.

**Proof.** In each simple real-edge graph `H_j`, perform the peeling of Section 4.3. The remaining graph is empty or has minimum degree at least `D/4` and order at most `K D`. Hence its minimum degree is at least `1/(4K)` times its own order.

Apply CFS theorem `EGlargemin` with `eta=1/(4K)`. Let `A_K=O(K^12)` be its linear constant. Keep all the cycles it produces. In leaf j, the edges not yet covered consist of peeled edges, CFS singleton edges, and all virtual edges. This remainder is even because `H_j^+` was even and only whole cycles have been removed. Decompose the remainder into multigraph simple cycles, using at most half its edge count.

If `c_j+s_j<=A_K |H_j|` is the dense decomposition's cost and `M_j<=Delta(H_j;D)/2` is the peeling cost, the leaf's cycle count is at most

```
c_j+(s_j+M_j+a_j)/2
 <= A_K |H_j|+Delta(H_j;D)/4+a_j/2,
```

where `a_j` is its number of virtual edges. Summing and using (4.11) cancels the `sum a_j/2=p` term exactly:

```
q_original <= A_K sum_j |H_j| + Delta_real/4
           <= (3A_K+3)n                 [D>=6].         (4.13)
```

Degree at most four is already trivially linear. □

This resolves a definite class with arbitrarily many dense pieces and low cuts. It does not assume that every terminal piece is regular, and it does not assert that arbitrary regular graphs have only such bounded-order pieces. **Large 3-connected pieces with unbounded `|H_j|/D` remain outside this consequence.** The dense theorem's cycles also need not be factor-colorable, so (4.13) is not a theorem about `f_2(G)`.

---

## 5. Factor colors across two vertices: a real compatibility issue

### 5.1 Exact palette-profile condition

Suppose two even pieces meet exactly in `u,v`, and their degrees at each pole sum to `2r`. In a partial r-factorization of the first piece let its used-color sets at u and v have sizes a,b and intersection size s. If the second piece's intersection size is t, a whole-side permutation of its palette makes the two sides compatible **if and only if**

```
t = r-a-b+s.                                           (5.1)
```

Indeed, the second side's sets must become the complements of the first side's two sets. The intersection of those complements has the size on the right. Conversely, matching the sizes of the four membership cells gives a permutation. Degrees determine a and b but do not determine s and t.

### 5.2 Explicit failure, even though a global repair is excellent

Use poles `u=0,v=1`. Give the left piece the two color-components

```
L_0=(0,2,4,1,3,5),       L_1=(2,3,4,5),
```

and the right piece

```
R_0=(0,6,7,8,9),         R_1=(1,8,6,9,7).
```

Their edge-disjoint union is a simple 4-regular graph on ten vertices. Every interior vertex has degree four in its own piece; each pole has degree two in each piece.

On the left, both poles use the same color, so `a=b=s=1`. On the right they use different colors, so `t=0`. Equation (5.1) requires `t=1`. No palette permutation works. In fact the old four component cycles cannot be colored with two colors at all: each pair within a side intersects, and `L_0,R_0,R_1` give a triangle in the cycle-intersection graph.

Nevertheless the whole graph has this Hamilton decomposition:

```
(0,2,3,5,4,1,7,6,8,9),
(0,5,2,4,3,1,8,7,9,6).
```

So the obstruction is to **retaining and merely relabeling locally chosen components**, not to the existence of a good global factorization. It is why Theorem 4.2's reconstruction is stated for cycle partitions rather than silently claimed to preserve r factor colors.

### 5.3 A clean positive closure: regular two-edge sums

Let G be obtained from disjoint simple `2r`-regular graphs `G_1,G_2` by deleting edges `u_1v_1,u_2v_2` and adding `u_1u_2,v_1v_2`. Then

```
f_2(G)=f_2(G_1)+f_2(G_2)-1.                            (5.2)
```

For the upper bound align the colors of the deleted edges. Splice their two component cycles into one across the new cut. All other cycles and colors remain intact.

For the reverse inequality, a factor meets the two-edge cut in zero or two edges. The cut edges therefore belong to a single component cycle in one factor. Cutting it and restoring the two old edges produces factorizations of `G_1,G_2`, increasing the total component count by exactly one. This proves equality.

Iteration over any tree of these sums gives the summed optimum minus the number of joins. If the original components all had length at least L, the new spliced cycle has length `l_1+l_2-2>=L` for `L>=3`. Thus this particular low-cut operation preserves both a total-count bound and an all-long bound. General 2-vertex overlap is different, as the preceding example shows.

---

## 6. A weaker simultaneous target: Hall-certified short components

The counterexamples show that demanding no short components, only finitely many bad factors, or bounded short-component load at every original vertex is too strong. A **global assignment of short components to vertex resources** survives these examples.

Fix the original `D=2r` and take, for concreteness,

```
L=D/8=r/4.
```

For an even augmented piece H of maximum degree D, let A be its marked virtual edges, let F be a partial r-factorization, and let

```
ell(v)=r-d_H(v)/2,           capacity(v)=1+ell(v).       (6.1)
```

Let S be the component cycles of F that have length less than L and use **no** edge of A. These are cycles in the simple real-edge graph.

### Definition — the short-component Hall certificate

Require a matching assigning every `C in S` to a distinct token at one of its vertices, where v has `1+ell(v)` tokens. Equivalently, for every subfamily T of S,

```
|T| <= sum_{v in union_{C in T} V(C)} (1+ell(v)).         (6.2)
```

The tokens consist of one ordinary vertex token plus the missing factor slots. They are an accounting device: assigning a cycle to a missing slot does **not** purport to recolor the cycle into its missing color. Hall's theorem makes the condition a concrete finite matching certificate.

For an original regular graph with no cuts, `ell=0`: the condition asks for **distinct vertex representatives for the chosen short factor-components**, not the absence of short components. It immediately gives `q(F)<=5n`, because long components cost at most `m/L=4n` and short ones at most n.

### 6.1 Useful sufficient versions

* One may omit the ordinary vertex token and demand a matching into capacities `ell(v)` alone; this is stronger, but will be satisfied in the explicit forced-triangle examples after block splitting.
* If every short nonvirtual component contains a vertex of degree at most `D/2` **in this fixed piece**, the missing-slot-only condition follows. Choose such a vertex for each short cycle. At v there are at most `d_H(v)/2` component occurrences in the entire partial factorization, and

  ```
  d_H(v)/2 <= r-d_H(v)/2=ell(v).
  ```

  All cycles assigned to v fit its slots.
* Let J be the simple graph formed by the short nonvirtual component edges. The hereditary inequality

  ```
  e_J(U) <= 3 sum_{v in U} (1+ell(v))     for every U    (6.3)
  ```

  suffices for (6.2), since the cycles of any subfamily contribute at least three edge-disjoint edges each inside their union. Thus a weighted sparsity certificate for the **chosen short-component edge set** is another sufficient stopping rule. It does not require the entire graph to be sparse.

The windmill example explains why vertexwise bounded bad-factor load would be needlessly restrictive: its r short cycles through x can instead be matched to r different noncentral vertices.

### Theorem 6.1 — block certificates imply a true 6n factorization

Suppose each block B of a simple `D=2r`-regular graph G has a partial r-factorization satisfying (6.2), with no virtual edges. Then G has an r-factorization with at most `6n` total simple-cycle components.

**Proof.** Apply Lemma 2.2, retaining every local cycle. With b blocks and c connected components,

```
q <= sum_B e(B)/L + sum_B sum_v (1+ell_B(v))
  = 4n + (n+b-c) + D(b-c)/2
  = 5n + (D+2)(b-c)/2.
```

Theorem 4.1 bounds the last term by

```
[3(D+2)/(4D)] [n-(D+1)c] <= n       when D>=6.
```

For `D=2,4`, any factorization has at most `Dn/6<=2n/3` components. □

If missing slots alone suffice, the corresponding bound is less than `4.75n`, hence at most `5n`.

### Theorem 6.2 — 3-connected terminal certificates imply a 10n cycle partition

Use Theorem 4.2's augmented terminal pieces. Suppose each underlying 3-connected terminal piece has a partial r-factorization satisfying (6.2), ignoring its virtual-edge-containing cycles. Then G has a partition into at most `10n` simple cycles.

Order-three terminal pieces need no extra hypothesis: there is at most one component avoiding virtual edges, namely the real triangle, and it can use one ordinary vertex token.

**Proof.** Work first in a connected component and assume `D>=16`. Write `h_j=|H_j|`, with t leaves and p parity repairs. Count long cycles by edges, short nonvirtual cycles by their matched tokens, and all remaining cycles by a virtual edge. The augmented leaves have `m+2p` edges and

```
sum_j sum_v ell(v)=D(t-1)-2p.
```

After reconstruction, subtract p by (4.11). Therefore

```
q_original
 <= (m+2p)/L + sum_j h_j + D(t-1)-2p + 2p - p
  = 5n + (D+2)(t-1) + p(16/D-1)
 <= 5n + (D+2)(t-1)
 <= 5n + [3(D+2)/(D-3)](n-D-1)
 < 10n.                                                (6.4)
```

For `D>=16`, `3(D+2)/(D-3)<=54/13<5`. Smaller even D is already bounded-degree and has a cycle count at most `Dn/6<3n`. Sum over connected components. □

**Important limitation:** Theorem 6.2 gives a cycle partition, not necessarily a global 2-factorization. Section 5 exhibits the palette issue that must be solved to upgrade it. Theorem 6.1 really does give a factorization.

### What is the missing simultaneous assertion?

A concrete next target is:

> For fixed absolute alpha and b, choose a partial r-factorization in each relevant high-connectivity, maximum-`2r` piece so that the components shorter than `alpha(2r)` and avoiding marked auxiliary edges have a Hall assignment into capacities `b+r-d(v)/2`.

Here `alpha=1/8,b=1` are specific plausible test parameters, not proved constants. This assertion is strictly less demanding than all-long factors: short cycles, short cycles in every factor, and high short-cycle load at some vertices are allowed.

It is not supplied by Petersen, by single-factor length estimates, or merely by declaring a factorization component-optimal. **No proof of this universal existence assertion is claimed.** The work above supplies a correct fixed-degree implication, a linear cut budget, and explicit families where the certificate succeeds despite unavoidable short cycles.

For an inclusion-minimal Hall obstruction with positive token capacities, no vertex of its union belongs to only one of its cycles: deleting that cycle would retain a Hall violation after losing the private vertex's token. Its excess is exactly one once such private vertices are excluded. This gives a definite global obstruction to study, but not a bounded-size exchange region. The high-Berge-girth examples are compatible with arbitrarily large required trades.

---

## 7. The high-Berge-girth exchange barrier admits good simultaneous factors

The prior notes prove the following for an infinite subfamily of the Cayley triangle systems: G is simple `2d`-regular, every vertex lies in `d=3a` designated triangles, and there is a balanced orientation in which every designated triangle is transitive. If every undirected cycle of length at most R is designated, this orientation has no directed cycle of length at most R.

There is an immediate **factorization upgrade**. The oriented graph has indegree and outdegree d at every vertex. Split it into a d-regular bipartite graph and take a 1-factorization, as in Lemma 2.1 but without dummy loops. Pulling back gives d spanning directed cycle covers. Hence the undirected graph has a genuine 2-factorization with

```
every component length >= R+1,
total component count <= nd/(R+1).                     (7.1)
```

Taking `R>=2d` gives fewer than `n/2` components. Degrees here are the original degrees; no iteration through shrinking degrees is involved.

This uses the prior orientation construction and strengthens its conclusion from a cycle partition to a resolvable one. It does not claim that the orientation construction is new, or that arbitrary graphs admit such orientations.

### A fully checked simultaneous example

For the 2520-vertex degree-six Cayley graph in `ResearchHeavy.md`, the triangle-incidence graph has girth 16. Its old partition has 2520 triangles and is immutable under exchanges of at most seven of them. It is already a bad **2-factorization**: the triangle cosets for each of the three generators form a spanning factor with 840 components.

The reproducible matching/orientation/factorization construction in `ResearchFactorsCheck.py`, with `PYTHONHASHSEED=0`, gives the following three spanning 2-factors:

| Factor | Component lengths | Components |
|---|---|---:|
| 1 | 9, 30, 77, 2404 | 4 |
| 2 | 9, 12, 105, 2394 | 4 |
| 3 | 9, 71, 1142, 1298 | 4 |

Each row sums to 2520. All **7560 edges** occur exactly once. The total is **12 simple cycles**, not “three cycles because there are three factors.” The smallest original-degree cycle weight is `9/6=3/2`.

The small minimum length here is a property of this finite witness; the general unbounded-length statement is (7.1) with the original construction's parameter R chosen afterwards.

### Why this does not replace the general simultaneous problem

Every balanced orientation of a complete odd graph has a directed triangle: a tournament with no directed triangle is transitive and cannot be balanced. Nevertheless the complete graph has a Hamilton decomposition. Thus even maximally connected regular graphs can require selecting good factors **despite** the presence of many other short directed cycles. Requiring the whole orientation to have large directed girth is too strong for the dense case.

The Hall criterion deliberately concerns only the selected factor-components, not all directed cycles of an orientation. A global factor-selection or refactorization argument is still needed there.

---

## 8. Verification and reproduction

The general claims above have proofs independent of the computations. The computations test constructions, color compatibility, degree/edge accounting, and simplicity, rather than using a search failure as a theorem.

Run:

```
PYTHONHASHSEED=0 python3 Submission/ResearchFactorsCheck.py
```

The checker writes its detailed numerical report to `/tmp/ResearchFactorsCheck.json`. It verifies the specification SHA-256 at the beginning and end.

Verified checks:

* **17** triangle-core regular completions, `r=2,...,16,20,32`: exact regularity, simplicity, edge coverage by r spanning factors, count `3r+1`, the single compulsory-triangle witness, and 2-connectivity of each lobe.
* **9** windmill completions, through `r=32`, where `n=4225`, degree is 64 and there are 135200 edges: every returned factor has one core triangle, every factor covers all vertices once, and the total is `r(2r+1)`.
* **7** triangle-chain completions and **3** other even cores: the general construction and block-deficit formulas.
* **19** separator/virtual-edge reconstruction instances, including trees of regular two-edge sums, forced-triangle completions, and selected regular graphs: exact leaf order identities, real-edge coverage, parity repairs, maximum degree preservation, deficit formulas, and the cycle-count change `q=sum q_j-p`.
* **20900** parameter pairs checking the density envelope, supplementary to its two-line proof.
* **60** deficit-paid peeling instances: exact deleted-edge counts, the `Delta/2` edge bound, and the fixed-threshold minimum degree of the remainder.
* **4** explicit missing-slot-only Hall certificates, including an 1122-vertex degree-64 example with eight unavoidable short core cycles and 768 available missing-slot tokens across blocks.
* The ten-vertex two-pole palette obstruction and the two displayed Hamilton cycles repairing it globally.
* The entire 2520-vertex Cayley example, including the incidence girth, balance, transitive designated triangles, all three spanning factors, all twelve component lengths, and exact edge coverage.

The checker does **not** assert that its generic partial-factorization algorithm always returns a Hall-certified factorization. Nor does it infer a universal constant from a sample of small regular graphs.

Search records were retained in `/tmp/factors_metadata.json`, `/tmp/factors_scanned.json`, `/tmp/factors_all_hits.txt`, and `/tmp/factors_relevant_hits.txt`. The proofs and references needed for the conclusions are in this document, rather than depending on those temporary files.

---

## 9. Bottom line and the remaining burden

The most important negative correction is stronger than an arbitrary bad minimum decomposition: **there are high-degree regular graphs in which every spanning 2-factor is forced to contain a triangle.** Still, their exact optimal total component count is linear. The all-long strengthening is therefore not the right unrestricted formulation.

The useful positive replacement is a **globally chargeable short-component exception**, not a current-degree length bound and not a bounded number of bad factors. Missing slots created by cuts have a proved linear budget. A Hall assignment can additionally spread short-cycle charges away from a highly loaded vertex. Dense bounded-order terminal pieces can already be handled unconditionally by the deficit-paid dense theorem.

What remains is genuinely simultaneous and global:

1. on large high-connectivity pieces, produce factorizations satisfying a short-component Hall/sparsity certificate, or some comparably strong original-degree count certificate;
2. if the conclusion must remain a global r-factorization after 2-vertex cuts, repair the two-pole palette profiles, rather than just summing local cycle counts;
3. allow unbounded trades: the earlier degree-dependent bounded-piece obstruction remains valid, while its good 12-component factorization demonstrates that global refactorization can succeed dramatically.

**No unrestricted O(n) factorization theorem is claimed.** The completed outcome is a clear regular refutation of the all-long target, exact factorization-compatible counterexample constructions, a linear fixed-degree cut/defect ledger, a proved dense-piece consequence, and a weaker explicit simultaneous criterion whose universal existence remains open in this work.
