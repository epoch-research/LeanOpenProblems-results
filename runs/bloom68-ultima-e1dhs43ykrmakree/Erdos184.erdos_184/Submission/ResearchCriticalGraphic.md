# Graphic critical restrictions: exact reductions, a Hajós consequence, and an extension-property obstruction

## Status and precise conclusions

**Neither universal graphic inequality `c(G) <= p(G)` or `c(G) <= 2 p(G)` is proved or refuted here.** In particular, no graph with `c>p` is claimed. The results below are proved structural reductions and a completely certified counterexample to replacing criticality by its single-circuit consequence. They do not fill either placeholder in `Spec.lean`.

The main conclusions are:

1. **The proposed equality on critical graphs has an exact structural reformulation.** For finite even graphic graphs, the following universal statements are equivalent:
   - `c(G) <= p(G)`;
   - `p(G)=Q(G)`, where `Q(G)=max_even H subseteq G c(H)`;
   - every inclusion-minimal `c`-critical graph satisfies `cf(F)=c(F)`;
   - every such critical graph has **the same number of cycles in every cycle partition**.

   The last equivalence uses the genuine graphic classification of Heinrich–Streicher, not a binary-matroid assertion. Consequently **a universal `c<=p` theorem would imply the full Hajós bound `c(G)<=floor(r(G)/2)`**, not merely the linear Erdős–Gallai bound. This is a conditional implication, not a proof of either conjecture.

2. **There is a solver-free fractional certificate for any prospective critical counterexample.** Suppose every circuit of `F` extends to a minimum `q`-partition, and `F` has another partition of size `s>q`. Then
   \[
   c_f(F)\leq \frac{s(q-1)}{s-1}<q.
   \]
   If `F` is actually `q`-critical, the same upper bound holds for **`p(F)`**, because every proper even restriction has integer cost at most `q-1`. Thus finding a critical graph with a nonconstant partition count would automatically refute `c<=p`; a numerical LP search is unnecessary.

3. **Exact criticality reductions are proved.** Criticality passes in both directions through articulation sums, two-edge splices, and vertex-edge splices. The last two operations satisfy `c=c1+c2-1` and `cf=cf1+cf2-1`; there is also an exact two-state formula for `p` and `Q`. A minimal counterexample to the equality target can therefore be reduced, after series suppression, to a loopless, 2.5-connected, 4-edge-connected even multigraph with `c>Delta/2`. Multigraphs here are only a reduction device: subdivision preserves all four invariants and yields actual simple graphs. The unshifted factor-two target requires more care and is **not** automatically reduced by the same scalar argument.

4. **The low-critical-number case is completely classified.** A critical graph with `c=2` is exactly two vertex-disjoint cycles, a figure eight, or a subdivision of four parallel terminal paths. In each case `cf=p=c=2`. More generally, if a critical graph has `c=Delta/2`, every cycle passes through a maximum-degree vertex and `cf=c`.

5. **A concrete graphic obstruction to the single-circuit shortcut:** an explicitly specified **simple graph `S` on 16 vertices and 30 edges** has
   \[
   \boxed{c(S)=4,\quad c_f(S)=3,\quad Q(S)=p(S)=6,\quad \nu(S)=10.}
   \]
   Nevertheless **every one of its 1,058 simple cycles extends to a minimum four-cycle partition**: `c(S\C)=3` for every cycle `C`. All **32,768 even restrictions** are checked, not just old partition subunions or circuit complements. This refutes both “all circuits extend minimum partitions implies `cf=c`” and “checking all single-circuit deletions establishes criticality.” It is emphatically **not** a counterexample with a genuinely critical whole graph.

6. **The old Petersen examples do not supply the missing counterexample.** A complete audit of all **65,536 even restrictions** of `L(Petersen)` gives `Q=p=7`, although its whole values are `c=3, cf=2`. For the old rings `R_t`, an explicit proper cactus restriction proves `p(R_t)>=6t`, whereas `c(R_t)=t+2`. No full-ring exhaustive enumeration is claimed.

New deliverables are this report and **`ResearchCriticalGraphicCheck.py`**, which uses only the Python standard library and exact rational arithmetic. All 41 pre-existing files in `Submission/` and `newSubmission/`, including the specification, were protected by a pre-work hash manifest and left unchanged. These are paper-level and exact finite computational results, not Lean formalizations or literature-priority claims.

---

## 1. Definitions and the exact critical hypothesis

All graph partitions in this note are partitions into **vertex-simple cycles**. An even graph need not be connected; isolated vertices do not affect any invariant. Put

\[
\begin{aligned}
c(F)&=\min\{|\mathcal D|:\mathcal D\text{ is an actual edge-disjoint cycle partition of }F\},\\
\nu(F)&=\max\{|\mathcal D|:\mathcal D\text{ is such a partition}\},\\
c_f(F)&=\min\Bigl\{\sum_Cx_C:x_C\geq0,\ \sum_{C\ni e}x_C=1\ (e\in E(F))\Bigr\},\\
p(G)&=\max_{H\subseteq G,\ H\text{ even}}c_f(H),\\
Q(G)&=\max_{H\subseteq G,\ H\text{ even}}c(H).
\end{aligned}
\]

The empty graph has value zero. The fractional program uses exact loads, not covers. Its dual prices are unrestricted in sign. Always `cf(F)<=c(F)` and `p(G)<=Q(G)`.

A nonempty even graph `F` is **`q`-critical** here if

\[
c(F)=q,\qquad c(W)\leq q-1
\quad\text{for every proper even }W\subsetneq F.       \tag{1.1}
\]

Thus `Q(F)=q`. Choosing a minimum-edge restriction attaining `Q(G)` gives precisely this hypothesis. Conversely any graph satisfying (1.1) can be considered with ambient graph `G=F`.

For every circuit `C` of a critical `F`,

\[
c(F\setminus C)=q-1.                                  \tag{1.2}
\]

The upper bound is (1.1); a smaller value would give a partition of `F` with fewer than `q` cycles after reinserting `C`. Hence every circuit extends a minimum partition. **The converse to this deduction is false even for simple graphs**, as Section 6 certifies.

---

## 2. An exact fractional subtraction lemma

The following statement works for binary matroids as well as graphs.

### Lemma 2.1 — minimum extensions versus a larger partition

Suppose `c(F)=q` and every circuit of `F` belongs to a minimum `q`-partition. Let `P` be any partition of `F` into `s>q` circuits. For each `C in P`, choose a minimum partition `D_C` containing `C`. In the vector space indexed by all circuits, set

\[
 x=\frac{\sum_{C\in P}\mathbf1_{D_C}-\mathbf1_P}{s-1}.
                                                               \tag{2.1}
\]

Every coordinate is nonnegative: a circuit in `P` is present in its own chosen extension, and no other coordinate is subtracted. The numerator has edge load `s-1` everywhere, since it is `s` full partitions minus one full partition. Thus `x` is an exact fractional partition and

\[
\boxed{c_f(F)\leq\frac{sq-s}{s-1}
       =\frac{s(q-1)}{s-1}
       =q-\frac{s-q}{s-1}<q.}                          \tag{2.2}
\]

There is no sampling, repeated unit capacity, or claim that subtraction produces an integral partition. The displayed nonnegative coefficients are the certificate. ∎

### Corollary 2.2 — what a genuine critical counterexample would certify

If `F` is `q`-critical and `nu(F)>=s>q`, then

\[
 p(F)\leq\max\{q-1,c_f(F)\}
       \leq\frac{s(q-1)}{s-1}<q=c(F).                 \tag{2.3}
\]

The first inequality accounts for **every** even restriction using criticality. If only `nu(F)>=s` is specified, apply (2.2) to a maximum partition: the function `t(q-1)/(t-1)` is nonincreasing for `t>1`. No assertion that the partition-count range is an interval is needed. For example, a genuinely critical graph with `c=3` and a four-cycle partition would have `p<=8/3`.

Conversely, under the minimum-extension hypothesis, `cf(F)=q` forces `nu(F)=q`. The dual gives another proof: an optimal dual of value `q` is tight on every member of every minimum partition. Since every circuit occurs in one, **all** circuits have price exactly one, so every partition has `q` members.

This is not a theorem that all critical graphs have constant partition count. It explains exactly why that missing structural assertion is consequential.

---

## 3. Fixed decomposition counts: the genuine graphic ingredient

### 3.1 Local literature theorem actually available

Heinrich–Streicher, *Cycle Decompositions and Constructive Characterizations*, arXiv:1708.09141, prove the following for connected loopless Eulerian multigraphs. These statements are equivalent:

1. `c(F)=nu(F)`;
2. no two edge-disjoint simple cycles of `F` share more than two vertices;
3. `F` is constructed from even multiedges using vertex identification and vertex-edge identification.

An **even multiedge** has two vertices joined by `2r` parallel edges. In a vertex-edge identification, take disjoint even graphs with marked edges `u_i v_i`, delete the two edges, identify `v_1` with `v_2`, and add `u_1u_2`. The local source gives the definition at lines 251–254 and the equivalence at lines 652–668. It also deduces treewidth at most two. Apply the statement componentwise for disconnected graphs.

This is a theorem about all **simple-cycle** partitions, unlike some “circuit partition” literature involving closed trails. It does not assume, or assert, the criticality implication missing here.

### 3.2 Fractional costs under the construction

Vertex identification adds both `c` and `cf`: a simple cycle cannot pass through both sides of an articulation.

For vertex-edge identification, and also for the two-edge splice defined in Section 5,

\[
 c(F)=c(F_1)+c(F_2)-1,\qquad
 c_f(F)=c_f(F_1)+c_f(F_2)-1.                            \tag{3.1}
\]

Here is a direct exact fractional proof, including its signed dual.

* In a fractional partition of `F_i`, the cycles through the marked edge have total mass one. Couple these two mass-one collections by product coefficients. Gluing the marked cycles produces simple crossing cycles; all nonmarked cycles are retained. The new total mass is `cf(F1)+cf(F2)-1`.
* Conversely, let `y_i` be optimal signed duals. Retain their prices off the marked edges. Give the new connector edge, or the pair of connector edges in total, price
  \[
  y_1(e_1)+y_2(e_2)-1.
  \]
  A crossing cycle caps to cycles `C_1,C_2` and has price `y_1(C_1)+y_2(C_2)-1<=1`. Local cycles retain their old inequalities. The objective is `cf(F1)+cf(F2)-1`.

Every gluing uses vertex-disjoint interiors, so the new crossing objects are genuinely simple cycles. Negative connector prices are allowed and sometimes necessary. The integral correspondence glues the unique marked cycle from each partition, giving the first identity in (3.1).

On an even multiedge, every circuit has two edges. Price every edge `1/2`: every circuit is tight and the total price is `r=c`. These duals propagate through the construction: at a crossing cycle, `1+1-1=1`. Consequently:

### Theorem 3.1 — fixed graphic count implies exact fractional count

If an even graph satisfies `c(F)=nu(F)=q`, then

\[
 c_f(F)=p(F)=Q(F)=q.                                   \tag{3.2}
\]

In fact, there are signed edge prices with **every circuit priced exactly one**. Restricting the same prices to any even `W` proves `cf(W)=c(W)=nu(W)` there.

Also, fixed count implies criticality: concatenate partitions of a proper nonempty `W` and of its nonempty complement. Their total count is `q`, and the complement costs at least one. This last observation holds for binary matroids too; the fractional conclusion does not. The synchronized binary examples and `R10` are not exceptions to a graphic theorem.

### 3.3 Exact equivalence of the universal equality targets

For the class of finite even simple graphs, the following are equivalent:

\[
\begin{array}{ll}
\text{(A)}&c(G)\leq p(G)\quad\text{for every }G;\\
\text{(B)}&Q(G)=p(G)\quad\text{for every }G;\\
\text{(C)}&c_f(F)=c(F)\quad\text{for every critical }F;\\
\text{(D)}&\nu(F)=c(F)\quad\text{for every critical }F.
\end{array}                                                    \tag{3.3}
\]

**Proof.** Under (A), every even `H subseteq G` has `c(H)<=p(H)<=p(G)`, so `Q(G)<=p(G)`; the reverse inequality always holds. If (B) holds, a critical `F` of cost `q` has `p(F)=q`, whereas every proper restriction has fractional cost at most `q-1`. Thus `cf(F)=q`. Conversely, under (C), select a critical restriction attaining `Q(G)`: then `p(G)>=cf(F)=Q(G)`. Lemma 2.1 proves (C) implies (D), and Theorem 3.1 proves (D) implies (C). ∎

Thus the graphic equality route is equivalent to saying that **every critical graph belongs to the Heinrich–Streicher constructive class**. No such assertion is imported from their paper.

### 3.4 Why `c<=p` would imply full Hajós

For completeness, the relevant bound on the constructive class has a short direct proof. For a connected loopless multigraph `J`, let

\[
 \mu(J)=|E(J)|-\#\{\text{unordered adjacent vertex pairs of }J\},
\]

the number of extra parallel edges. Every graph in the fixed-count class satisfies

\[
 c(J)\leq\frac{|V(J)|+\mu(J)-1}{2}.                    \tag{3.4}
\]

For a `2r`-multiedge, the right side is `(2+(2r-1)-1)/2=r`. Vertex identification adds `c` and `mu` and reduces the sum of vertex counts by one, preserving the inequality. For vertex-edge identification,

\[
\begin{split}
c&=c_1+c_2-1,\qquad n=n_1+n_2-1,\\
\mu&=\mu_1+\mu_2-a_1-a_2,\qquad a_i\in\{0,1\},
\end{split}
\]

where `a_i=1` exactly when the deleted edge had a parallel mate. The new connector is not parallel to an existing edge. Since `a_1+a_2<=2`, adding the two inductive bounds and subtracting one proves (3.4).

For simple graphs `mu=0`; adding over components gives `c(F)<=r(F)/2`, where `r(F)=|V(F)|-kappa(F)` counts isolated components as usual. Under any of (3.3), choose a critical restriction attaining `Q(G)`. It has fixed count, hence

\[
 c(G)\leq Q(G)=c(F)\leq\frac{r(F)}2\leq\frac{r(G)}2.
                                                               \tag{3.5}
\]

Integer rounding gives the usual Hajós bound. This argument does **not** use the previously proved `cf<=rank` bound, and does not claim the equality target is equivalent to Hajós in the reverse direction.

---

## 4. Completely proved small-critical cases

### 4.1 Critical cost two

A `2`-critical graph cannot have a partition into three or more cycles. The union of any two members of such a partition would be a proper even restriction of cost exactly two: two edge-disjoint cycles cannot have their union be one simple cycle.

Thus `nu=2`. In a two-cycle partition the cycles share at most two vertices. To see the obstruction to three common vertices directly, let the two cycles contain distinct common vertices `a,b,z`. In each cycle take an `a`–`b` path avoiding `z`. Their union is a nonempty even graph, while its complement in the two-cycle union still has degree four at `z`. Decomposing the former needs at least one cycle, and the latter at least two.

There are therefore exactly three possibilities, up to subdivisions and isolated vertices:

* two vertex-disjoint cycles;
* two cycles meeting at one vertex;
* two cycles meeting at exactly two vertices: four internally disjoint paths between those vertices.

Conversely these three forms have exactly two cycles in every partition and are critical. Fractional equality is immediate. For the last two forms price each edge incident with a common degree-four vertex `1/2`, and all other edges zero. For disjoint cycles price one edge in each component one. This proves `cf=p=2` without invoking the general classification.

A `1`-critical graph is simply a cycle.

### 4.2 Saturation of the vertex degree bound

Suppose `F` is critical with `c(F)=q` and `d(v)=2q`. If a cycle avoided `v`, deleting it would leave a proper even graph still requiring at least `d(v)/2=q` cycles. Hence every cycle contains `v`.

The exact edge-load equations at `v` now force the total fractional mass to be `q`. Every integral partition also has exactly `q` cycles. In particular,

\[
 c(F)=\Delta(F)/2\quad\Longrightarrow\quad c_f(F)=c(F).
                                                               \tag{4.1}
\]

Any critical counterexample to the equality target must have `c(F)>Delta(F)/2`.

---

## 5. Exact separator reductions, including the hereditary invariant

### 5.1 Operations and marked states

Take disjoint nonempty even graphs `F_i` with marked edges `e_i=u_iv_i`.

* A **two-edge splice** deletes `e_1,e_2` and adds `u_1u_2,v_1v_2`.
* A **vertex-edge splice** deletes `e_1,e_2`, identifies `v_1,v_2`, and adds `u_1u_2`.

For `b in {0,1}`, define

\[
 p_i^b=\max\{c_f(W):W\subseteq F_i\text{ even},\ \mathbf1_{e_i\in W}=b\},
                                                               \tag{5.1}
\]

and define `Q_i^b` with `c` instead of `cf`. The empty restriction is allowed in state zero.

For **either** splice,

\[
\boxed{
\begin{aligned}
p(F)&=\max\{p_1^0+p_2^0,\ p_1^1+p_2^1-1\},\\
Q(F)&=\max\{Q_1^0+Q_2^0,\ Q_1^1+Q_2^1-1\}.
\end{aligned}}                                                \tag{5.2}
\]

**Complete restriction classification.** An even restriction either avoids all connectors or uses them. In the first case its two traces are even restrictions avoiding the marked edges, and its costs add. In the second case cap each trace with its marked edge. Both capped traces are even and contain the mark; every crossing cycle caps to one circuit in each side. Formula (3.1) applies to these restrictions, giving the subtraction of one. Conversely any pair of restrictions in the same marked state constructs an even restriction of the splice. This covers all even restrictions, not merely ones arising from supplied minimum partitions. ∎

### 5.2 Criticality is equivalent on the pieces

Let `q_i=c(F_i)` and `q=q_1+q_2-1`. Then

\[
\boxed{F\text{ is }q\text{-critical}
\quad\Longleftrightarrow\quad
F_i\text{ is }q_i\text{-critical for both }i.}           \tag{5.3}
\]

**Forward direction.** Let `W_1` be a proper even restriction of `F_1`.

* If it contains `e_1`, splice it to the whole `F_2`. This is a proper even restriction of `F` of cost `c(W_1)+q_2-1`, forcing `c(W_1)<=q_1-1`.
* If it avoids `e_1`, take a minimum partition of `F_2` and let `C_2` be its marked cycle. The residual `F_2\C_2` has cost exactly `q_2-1`. Its union with `W_1`, without connectors, is proper and has cost `c(W_1)+q_2-1`. Again criticality gives the required bound.

The same argument applies to side two; empty restrictions cause no difficulty.

**Reverse direction.** In an inactive restriction both traces omit their marked edges, so its cost is at most `(q_1-1)+(q_2-1)=q-1`. In a proper active restriction at least one capped trace is proper; its cost, after subtracting one for the splice, is again at most `q-1`. The full cost is `q`. ∎

For a disjoint or articulation sum, `c,cf,p,Q` all add, and the sum is critical if and only if all nonempty pieces are critical. The proof is the same replacement argument without a connector.

Subdivision gives a bijection on circuits and on all even restrictions: every degree-two path is used wholly or not at all. It preserves `c,nu,cf,p,Q` and criticality. No rank theorem is being applied to the suppressed multigraph.

### 5.3 A precise irreducible target for the equality question

The gap `c-cf` adds at both splice operations. The range gap `nu-c` also adds. Therefore, if a critical equality counterexample exists, a smaller critical equality counterexample occurs in some nontrivial piece of any of these separations.

Discard isolated vertices, reduce articulation blocks, and suppress degree-two paths. Nontrivial two-edge separations and vertex-edge separations can then be capped as above. Pieces which are just cycles cause only series operations and have zero gap. Choosing a counterexample of minimum cycle-space dimension, and then minimum core size, gives an irreducible counterexample with:

* no articulation;
* minimum degree at least four;
* no two-edge cut (hence 4-edge-connectivity, since every cut of an even graph is even);
* no pair `(v,e)` whose deletion disconnects it: **2.5-connectivity**;
* `c>Delta/2` and `nu>c>=3`.

Parallel edges in the core are allowed. Subdividing them restores an actual simple graph and the same critical/fractional data. Loops would be separate cycle blocks and cannot be the nonzero-gap atom.

This is a reduction, **not** a proof that no such atom exists. Nor does it say that criticality is preserved by arbitrary minors.

### 5.4 Why the unshifted factor-two target needs marked information

For a marked even graph, `p^0>=p^1-1`: delete a marked cycle from a state-one maximizing restriction and use `cf(W)<=1+cf(W\C)`. Thus (5.2) implies

\[
 p(F)\geq p(F_1)+p(F_2)-1.                              \tag{5.4}
\]

This alone does not propagate the unshifted hypothesis `c_i<=2p_i`: its lower bound would lose an extra unit. The **conditional** shifted hypothesis `c_i<=2p_i-1` is splice-stable, since

\[
 c(F)\leq2(p_1+p_2)-3\leq2p(F)-1.
\]

No universal shifted inequality is asserted. A factor-two induction must keep suitable marked-state estimates, or supply an additional argument; it cannot simply reuse the equality-gap reduction.

For any fixed `K>=1`, the universal assertion `c<=Kp` is equivalent to its assertion on all critical graphs, by choosing a critical restriction attaining `Q`. This logical reduction does not supply the missing estimate on the irreducible critical pieces.

---

## 6. A fully certified simple counterexample to the extension shortcut

### 6.1 Actual simple graph

On original vertices `0,...,6`, let

```
D = (03, 04, 05, 13, 15, 16, 24, 25, 26),
T = (34, 36, 46).
```

For the `j`th pair `uv` of `D`, indexed from zero, put in the three edges

```
uv,  u--(7+j),  (7+j)--v.
```

Also put in the three edges of `T`. This defines a **simple** graph `S` with 16 vertices and 30 edges. Vertices `0,...,6` have degree six; vertices `7,...,15` have degree two.

For compact certificates only, suppress those nine degree-two vertices. The resulting seven-vertex multigraph `J` has two copies of every pair in `D` and one copy of each pair in `T`. Its edge indices are:

| Core indices | Endpoints |
|---|---|
| 0,1 | 03 |
| 2,3 | 04 |
| 4,5 | 05 |
| 6,7 | 13 |
| 8,9 | 15 |
| 10,11 | 16 |
| 12,13 | 24 |
| 14,15 | 25 |
| 16,17 | 26 |
| 18 | 34 |
| 19 | 36 |
| 20 | 46 |

The even-indexed copy is the direct edge; the next copy is the two-edge path. Every integer mask below refers to this table and is lifted to the actual simple graph by the checker.

### 6.2 Integral optimum four: an analytic lower bound

A four-cycle partition of the actual simple graph is

```
(0,3,1,12,6,4,2,5)
(0,4,13,2,14,5,11,1,6,3,7)
(0,8,4,3,10,1,5,9)
(2,6,15).
```

The corresponding core masks are `1071185, 566790, 262568, 196608`.

For the lower bound, a hypothetical three-cycle partition of `J` would consist of three Hamilton cycles: every original vertex has degree six and must belong to all three cycles. The bipartite graph with edge set `D` has parts `{0,1,2}` and `{3,4,5,6}`. Every Hamilton cycle of `J` uses six edges across these parts and exactly one edge of `T`.

Add a vertex `w` to the simple graph with edges `D` and join it to `3,4,6`. The result is the cube, a cubic bipartite graph on `4+4` vertices. Replace the `T`-edge `xy` of a Hamilton cycle by `x-w-y`; this gives a Hamilton cycle of the cube. Its complement is a perfect matching.

In a supposed three-cycle partition of `J`, each `T`-edge is used once and each underlying `D`-edge twice. Therefore the three complementary perfect matchings just constructed partition the cube's edges. The union of every two of these matchings would be Hamiltonian.

This is impossible by a short sign argument. Represent the three perfect matchings of a `4+4` bipartite graph by permutations `pi_1,pi_2,pi_3`. A Hamiltonian union of matchings `i,j` means `pi_i^{-1}pi_j` is a four-cycle, so `sign(pi_i) sign(pi_j)=-1`. Multiplying this for the three pairs gives `1=-1`.

Thus `c(J)>=4`, and subdivision gives `c(S)=4`.

### 6.3 Exact fractional value three

The following six actual simple cycles cover every edge exactly twice:

```
(0,4,13,2,5,1,12,6,3,7)
(0,4,3,10,1,12,6,2,14,5)
(0,5,1,3,6,15,2,4,8)
(0,7,3,10,1,6,4,13,2,14,5,9)
(0,3,1,11,5,2,15,6,4,8)
(0,3,4,2,6,1,11,5,9).
```

Give each coefficient `1/2`. Their core masks are

```
551174, 362644, 659800, 1090722, 1196617, 333345.
```

This is a fractional partition of cost three. Price every edge incident with vertex `0` by `1/2`, and all other edges zero. Every simple cycle has price zero or one, while the total price is three. Hence `cf(S)=3` exactly.

### 6.4 All cycles extend minimum partitions, but criticality fails badly

The complete circuit list has 1,058 members. The checker verifies and reconstructs a three-cycle partition of `S\C` for **each** one. The analytic bound `c(S)=4` supplies the matching lower bound. Consequently

\[
 c(S\setminus C)=3\quad\text{for every simple cycle }C.          \tag{6.1}
\]

Nevertheless the complete cycle space has dimension `30-16+1=15`, and its **32,768** even restrictions have this integer-cost distribution:

| `c(W)` | Number of even restrictions |
|---:|---:|
| 0 | 1 |
| 1 | 1,058 |
| 2 | 14,876 |
| 3 | 13,047 |
| 4 | 3,172 |
| 5 | 564 |
| 6 | 50 |

Thus `Q(S)=6`, not four. An explicit proper witness takes the doubled edges

```
03, 04, 05, 13, 16, 24.
```

These underlying pairs form a tree. In the simple graph they are the six triangles with new vertices `7,8,9,10,12,13`, forming a cactus. Its only circuits are those six triangles, so its exact fractional value is six. The core support mask is `15615`.

Every even restriction has `cf(W)<=c(W)<=6`, and this witness has `cf=6`. Therefore

\[
 \boxed{Q(S)=p(S)=6.}                                   \tag{6.2}
\]

This is an all-even-restriction upper certificate, not an inference from a few selected subgraphs. The witness itself is a critical restriction with `cf=c=6`.

The nine triangles arising from all doubled pairs, together with the triangle on `3,4,6`, form a ten-cycle partition. Since `S` has 30 edges and is simple, no partition has more than ten cycles. Applying Lemma 2.1 to this ten-part partition and its four-part extensions gives an additional exact fractional certificate of value `10/3`; the six-cycle half-cover improves it to three.

For the mark `34`, the checker also certifies the exact marked maxima

\[
 (p^0,p^1)=(Q^0,Q^1)=(6,5).
\]

Both upper bounds use every even restriction in the corresponding state; exact all-circuit-tight signed duals certify attaining witnesses. This illustrates why marked states in (5.2) need not have their larger value in the state containing the mark.

Vertex-identifying `t` disjoint copies gives connected simple graphs with

```
c=4t, cf=3t, Q=p=6t,
c(G\C)=4t-1 for EVERY circuit C.
```

These identities follow by direct-sum cycle behavior, not by enumerating an exponentially larger graph. They show that the extension shortcut can miss an arbitrarily large additive gap. They still do **not** refute either hereditary target.

---

## 7. The Petersen hereditary calculation

Use the standard Petersen graph with outer cycle `0,...,4`, spokes `i(i+5)`, and inner edges `(5+i)(5+(i+2 mod 5))`. Label its line-graph vertices by the lexicographically ordered Petersen edges, as in the earlier rounding report.

The old four-Hamilton-cycle half-cover and the old three-cycle partition are rechecked independently. Thus the known whole values remain

\[
 c(L(P))=3,\qquad c_f(L(P))=2.
\]

The new complete-restriction calculation gives

\[
 \boxed{Q(L(P))=p(L(P))=7.}                             \tag{7.1}
\]

The lower witness consists of the vertex triangles corresponding to Petersen vertices

```
{0,1,2,3,5,6,9}.
```

They induce a tree in the Petersen graph, so their line-graph triangles form a seven-cycle cactus. The checker independently verifies that these are the only contained circuits. For the upper bound it computes `c(W)<=7` for every one of the `2^16=65,536` even restrictions, so automatically `cf(W)<=7` for all of them. Thus this is a certificate of the actual hereditary maximum.

For the old ring `R_t`, each block is `L(P)` with line-graph vertex `0`, representing Petersen edge `01`, deleted. In each block use the six vertex triangles corresponding to

```
{2,3,4,5,6,7}.
```

They avoid the deleted vertex. Their intersection graph is a forest (edges `23,27,34,57`, with vertex `6` isolated), so the restriction is a six-cycle **cactus forest with two components** on the 14 block vertices. Omit all ring connectors and take these restrictions in every block. By additivity,

\[
 p(R_t)\geq6t>t+2=c(R_t)\qquad(t\geq2).                 \tag{7.2}
\]

The whole-ring equality `c(R_t)=t+2` is the prior proved result, not newly inferred from sampling. Only the explicit hereditary lower bound is asserted here; no value of `Q(R_t)` or exact `p(R_t)` is claimed. In particular these rings are not `c`-critical and are not low-`p` examples.

---

## 8. Local literature search and the cycle-polytope issue

The locally available sources relevant to this investigation were:

1. **Irene Heinrich and Manuel Streicher**, *Cycle Decompositions and Constructive Characterizations*, arXiv:1708.09141. Local file:
   `/corpus/src/1708.09141/heinrichStreicherCycleDecompositionsAndConstructiveCharacterizations.tex`.
   Lines 317–369 give the `c,nu` splice identities; lines 626–668 give the two-cycle obstruction and fixed-count characterization. This is the substantive structural theorem used in Section 3.

2. **Irene Heinrich, Till Heller, Eva Schmidt, and Manuel Streicher**, *2.5-Connectivity: Unique Components, Critical Graphs, and Applications*, arXiv:2003.01498. Local file:
   `/corpus/src/2003.01498/twoFiveConnectivity.tex`.
   The application at lines 827–856 reduces extremal cycle decomposition and Hajós to 2.5-connected components. Importantly, their “critical 2.5-connected” condition, defined at lines 581–583, means **every edge deletion destroys 2.5-connectivity**. It is not (1.1), so its critical-graph classification cannot simply be applied to this problem.

3. **Irene Heinrich and Sven O. Krumke**, *Minimum Cycle Decomposition: A Constructive Characterization for Graphs of Treewidth Two with Node Degrees Two and Four*, arXiv:1701.05516. Local file:
   `/corpus/src/1701.05516/CyclePaper.tex`.
   This supplies double-ear constructions and exact low-treewidth decomposition algorithms, not a theorem about all minimal `c`-critical restrictions. The prior series-parallel fractional rounding result is consistent with it.

4. **Lorenzo Traldi**, *Circuit partitions and signed interlacement in 4-regular graphs*, arXiv:1607.04233. Its introductory definition explicitly uses “circuit” for a **closed trail**, possibly repeating vertices, and “minimal circuit” for a closed path. Its circuit-partition/interlacement machinery therefore does not, by itself, give the required minimum **simple-cycle** count. An Euler circuit of a connected even graph cannot be counted as one of our cycles.

5. **João Gouveia, Monique Laurent, Pablo A. Parrilo, and Rekha Thomas**, *A new semidefinite programming hierarchy for cycles in binary matroids and cuts in graphs*, arXiv:0907.4518, Mathematical Programming 133 (2012), 203–225. Local file:
   `/corpus/src/0907.4518/0907.4518.tex`, especially lines 1125–1160. It quotes the Barahona–Grötschel characterization: the binary cycle polytope is given by the cocycle parity inequalities precisely in the stated excluded-minor class; graphic matroids belong to that class.

6. **Tim Römer and Sara Saeedi Madani**, *Cycle algebras and polytopes of matroids*, arXiv:2105.00185. Local file:
   `/corpus/src/2105.00185/2105.00185.tex`, lines 34–38 and 173–177. It explicitly identifies the graphic cycle polytope with the **Eulerian subgraph polytope**, not the hull of individual simple cycles.

In zero-one coordinates the graphic polytope statement concerns

\[
 P_G=\operatorname{conv}\{\mathbf1_H:H\subseteq G\text{ even}\}.
\]

It has the box constraints and the cut-parity inequalities

\[
 z(A)-z(D\setminus A)\leq |A|-1
 \quad(D\text{ a cut},\ A\subseteq D,\ |A|\text{ odd}).             \tag{8.1}
\]

In contrast, exact fractional circuit cost is the gauge of

\[
 B_G=\operatorname{conv}\bigl(\{0\}\cup\{\mathbf1_C:C\text{ a simple cycle}\}\bigr).
\]

The prior identity `p(G)=min{lambda:P_G subseteq lambda B_G}` remains valid. Describing `P_G` does not establish that an integral point has a low-cost **disjoint** decomposition into vertices of `B_G`. The graph `S` has the graphic parity-polytope property and every-circuit minimum extension, but still has `cf<c`. An argument from these two facts alone to integral cost equality is therefore concretely false. A successful proof must use the full all-restriction critical hypothesis in an additional way.

No local source found here supplied that additional theorem. This is a bounded local literature audit, not a claim of exhaustive literature coverage or a priority claim for the reductions.

---

## 9. Exact verification and scope

Run

```
PYTHONHASHSEED=0 python3 Submission/ResearchCriticalGraphicCheck.py
```

Optionally dump the full restriction certificates into a **new** directory outside the protected research folders:

```
python3 Submission/ResearchCriticalGraphicCheck.py \
  --dump-restrictions /tmp/critical-graphic-certificates
```

An optional `--graph-json FILE` accepts an additional actual even simple graph, for example `{"n": 3, "edges": [[0,1], [1,2], [2,0]]}`. The checker enumerates it completely, selects a minimum-edge restriction attaining `Q`, and verifies criticality over **all** of that restriction's even subgraphs. If the selected restriction has fixed count, an exact all-circuit-tight dual certifies `p=Q` on that input. If it has nonconstant count, (2.1) instead supplies a rational primal and a hereditary upper bound strictly below its integer cost, certifying a counterexample **on the extracted restriction**. This is a per-input diagnostic, not an assertion that the second case cannot occur. Its cycle-space dimension is capped at 20; running time is exponential.

The checker does not import prior checkers or require NetworkX, SciPy, SymPy, or an LP/MILP solver. Numerical optimization was used during discovery, in particular to locate a compact half-cover, but never as a final certificate; the delivered certificates are checked exactly.

Its independent checks include:

* verification of the actual simple edge lists and even degrees;
* binary incidence elimination producing an independent kernel basis of dimension `m-n+kappa`;
* enumeration of the entire kernel, with distinctness and evenness checks, proving that **all** even restrictions are present;
* enumeration of simple cycles by vertex-simple DFS, independently compared with the connected 2-regular words in that entire kernel;
* exact minimum **and maximum** partition DPs for every word;
* explicit reconstruction of all 1,058 minimum cycle extensions in `S`;
* rational exact-load primal checks and signed dual inequalities against **all contained cycles**, not merely the displayed supports;
* cactus witnesses attaining `p=6` in `S` and `p=7` in `L(P)`; every restriction's integer upper bound certifies the corresponding hereditary upper bound;
* exact all-circuit-tight signed duals for the small critical gluing examples and for the marked-state witnesses;
* the literal coefficient construction (2.1), yielding the additional `10/3` primal;
* unchanged protected-file hashes during execution and the prescribed specification hash.

For a nonzero even word `W`, let `e` be its first used edge. The exhaustive recurrence is

\[
\begin{aligned}
c(W)&=1+\min_{C\subseteq W,\ e\in C}c(W\setminus C),\\
\nu(W)&=1+\max_{C\subseteq W,\ e\in C}\nu(W\setminus C).
\end{aligned}
\]

Every partition has exactly one member containing `e`, so this covers all partitions. It is not a heuristic upper bound. Each recursive support is smaller and belongs to the fully enumerated cycle space. The optional JSONL files record every word, both costs, and the chosen first cycles; deterministic transcript hashes are also printed.

The final checker passed with distinct hash seeds, both in its default mode and with the additional `K5` input and certificate export. A separate read-back verifier independently recognized the circuits and checked both exhaustive recurrences in all **98,642 exported restriction records** (the two main graphs, eight gluing fixtures, and `K5`). Invalid non-even, nonsimple, and looped inputs were rejected; the empty case and the dimension cap were also checked. The final pre-work manifest comparison confirmed all 41 old files unchanged.

The protected specification SHA-256 is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

Only the named new report and checker are deliverables. Small graph searches were diagnostics for finding the explicit obstruction, not evidence used to promote a finite absence of critical gaps into a theorem. No minimality-by-order claim is made about `S`.

---

## 10. What remains open after these reductions

The equality question has been sharpened to a concrete structural alternative:

> Does there exist an even graphic `q`-critical graph with a partition into more than `q` simple cycles?

If yes, (2.1) and a complete criticality certificate immediately give a correct counterexample to `c<=p`. If no, Heinrich–Streicher plus the elementary fractional gluing proof give `c<=p`, and indeed the full Hajós bound. Neither alternative is established in this report.

For the factor-two question, the exact marked formula (5.2) is a useful interface, but no theorem proves `p(F)>=c(F)/2` on the irreducible critical pieces. The single-circuit extension property is strictly weaker than criticality and cannot be substituted for it, even when checked for every actual simple cycle. The new counterexample certifies that failure completely while leaving the genuine hereditary targets unresolved.
