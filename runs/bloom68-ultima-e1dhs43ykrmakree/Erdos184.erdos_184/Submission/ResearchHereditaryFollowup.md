# Hereditary fractional follow-up: global-minimum retention fails, even at four

## Status and precise new conclusions

The universal binary-matroid question

\[
 c(M)\ \leq\ K\,p(M),\qquad
 p(M):=\max_{F\in Z(M)}c_f(M|F),                         \tag{0.1}
\]

**remains unresolved in this report.** No unbounded actual `c/p` family, universal constant, or graphic Erdős–Gallai proof is claimed. The results below are genuine counterexamples to the proposed retention/one-step routes and exact positive theorems for a new binary family, not a sampling gap mislabeled as a counterexample to (0.1).

The new family `M(H,n)` synchronizes complementary clique-cut codes along an arbitrary connected simple bookkeeping graph `H`. Write `q=|V(H)|`, `h=|E(H)|`. For `h>=2`, `n>=8`, `4|n`, it has the following properties.

1. **Global optimum and actual hereditary maximum, exactly:**
   \[
   \boxed{c(M(H,n))=q,\qquad p(M(H,n))=h.}                \tag{0.2}
   \]
   Every circuit, every full-ground-set partition, and the integer optimum of **every** Eulerian restriction are classified below. Every Eulerian restriction has an explicit exact-load fractional primal. In fact, every Eulerian restriction of this family satisfies the **actual hereditary factor-two bound**, and that hereditary factor is sharp within the class.

2. **No constant selection guarantee from a specified global minimum partition.** For `H=K_q`, `n=4q^2`, a displayed partition `D` is globally minimum, `|D|=q`, but
   \[
   \boxed{\max_{\mathcal A\subseteq D}
       c_f\!\left(\bigcup\mathcal A\right)<2.}           \tag{0.3}
   \]
   Thus no finite constant works for uniform-half retention, exchangeable retention, or **any adaptive/nonexchangeable/deterministic selection restricted to subunions of this supplied `D`**. This refutes a guarantee for an arbitrary supplied minimum partition; it does not refute a theorem allowed to replace it with a different minimum partition.

3. **Uniform-half `K=4` fails even if the minimum partition is optimally chosen.** For `M(K_9,256)`, **every globally minimum partition** `D` has nine circuits and satisfies
   \[
   \mathbb E_{\text{independent }1/2}\,
      c_f\!\left(\bigcup\mathcal A\right)
      \leq\frac{9207}{4096}<\frac94,
   \qquad \frac94-\frac{9207}{4096}=\frac9{4096}.        \tag{0.4}
   \]
   More generally, for `M(K_q,4q^2)`, even after optimizing **both** the globally minimum partition and an arbitrary exchangeable retention law,
   \[
   \sup_{D\text{ minimum},\;\mu\text{ exchangeable}}
       \frac{\mathbb E_\mu c_f(\bigcup\mathcal A)}q
       \longrightarrow\frac18.                         \tag{0.5}
   \]
   Consequently this stronger exchangeable approach cannot establish a denominator `K<8`. For the particular vertex partition in item 2, the ratio tends to zero instead.

4. **A concrete refutation of the suggested one-step inequality.** A binary matroid on 480 elements has
   \[
   c(M)=6>
   c_f(M)+\max_{C\text{ circuit}}c_f(M\setminus C).
                                                                  \tag{0.6}
   \]
   Exact rational upper certificates bound the right side by `136/23<6`. This is a direct sum of two explicitly defined connected-family instances; see Section 9.

5. **A further theorem about recursive kernel coupling.** If the independent local kernels are replaced by `K tensor U_0`, where `K` is an Eulerian outer binary code with actual circuit-partition number `t`, then the new integral optimum is at most `t+1`. If `dim U_0>=t`, its actual hereditary maximum is at least `t`, so the new matroid satisfies `c<=p+1<=2p`. An exact 280-element audit also exhibits collapse of the displayed five-part partition to an actual two-part global minimum. See Section 10.

The large witness in (0.2) lies **outside** the old-partition subunion cube in (0.3). Indeed, for that dense family, `c/p=2/(q-1)`, which tends to **zero**, not infinity. Section 6 also rules out a hidden counterexample obtained simply by taking one of its Eulerian restrictions.

These are paper-level results, not Lean formalizations or literature-priority claims. The companion file is **`ResearchHereditaryFollowupCheck.py`**, using only the Python standard library and exact arithmetic. Neither the earlier research files nor `Spec.lean` is changed.

---

## 1. Definitions and conventions

A finite binary matroid is specified by a binary cycle space `Z <= F_2^E`. Its circuits are the support-minimal nonzero words. We identify words with their supports. Assume `E in Z`; thus the matroid is Eulerian. For any `F in Z`, set

\[
\begin{split}
c(F)&=\min\{|\mathcal D|:\mathcal D\text{ is a disjoint circuit partition of }F\},\\
c_f(F)&=\min\left\{\sum_C x_C:
  \sum_{C\ni e}x_C=1\quad(e\in F),\quad x_C\geq0,
  \quad C\subseteq F\text{ a circuit}\right\},\\
p(M|F)&=\max\{c_f(W):W\in Z,\;W\subseteq F\}.
\end{split}                                                       \tag{1.1}
\]

The empty restriction has both costs zero. These are **exact partitions**, not fractional covers or odd covers. The LP dual has unrestricted signed element prices; we do not clip them or assume a nonnegative optimal dual. The explicit certificates below are exact primal load equations and, where a lower bound is needed, exact dual certificates.

If `D` is globally minimum, every subunion has integer optimum equal to the number of retained circuits. The construction below respects this necessary condition: it has `c(union A)=|A|` for every `A subseteq D`, although its fractional values remain small.

---

## 2. The base block and its two independent labels

Fix an even `n>=6` for this section. Let `B=E(K_n)`, `m=binom(n,2)`, and

\[
 Z_n=\operatorname{Cut}(K_n)+\langle 1_B\rangle.
                                                                  \tag{2.1}
\]

Write `delta(T)` for the cut of a shore `T subseteq [n]`, with vertices numbered `0,...,n-1`.

### Lemma 2.1: the proper-word antichain

For `n>=5`, every nonempty proper word of `Z_n` is a circuit. Every partition of `B` into nonempty proper base words has exactly two pieces.

**Proof.** Nontrivial cuts form an antichain. For example, if `delta(S) subseteq delta(T)`, then `S` is constant on each of the two shores of `T`, so either `S` is trivial or the cuts coincide. Consequently complements of nontrivial cuts also form an antichain.

Two nontrivial cuts cannot be disjoint: if every edge across `S` has both endpoints on the same side of `T`, all vertices must be on the same side of `T`. Thus no nontrivial cut is contained in the complement of another nontrivial cut.

Conversely, the complement of a nontrivial cut cannot be contained in another cut when `n>=5`. Such containment would say that two cuts cover `K_n`. Give each vertex its two shore-membership bits. Two vertices with the same bits have their edge in neither cut; four bit patterns cannot distinguish five vertices.

These observations exclude every strict containment between nonempty proper words of (2.1). Also `1_B` is not a cut, and the complement of any nonempty proper base word is another such word. After the first part of a partition of `B`, its complement is a circuit, so there can be exactly one remaining part. ∎

Because `n` is even, parity of a shore is unchanged by taking its complement. Define

\[
 U_0=\{\delta(T):|T|\text{ even}\},\qquad
 A=\delta(\{0\}),\qquad B'=1_B+A.
                                                                  \tag{2.2}
\]

The even-cut space has dimension `n-2`; one basis is

\[
 \delta(\{0,i\}),\qquad 1\leq i\leq n-2.                \tag{2.3}
\]

Indeed, the even-shore space has dimension `n-1` and the cut map has the one-dimensional kernel `{empty,[n]}` on it. The `n-1` pairs `{0,i}` generate that space, with their only cut relation being their total sum; deleting one gives (2.3).

Every base word has a **unique** expression

\[
 z=sA+tB'+u,\qquad s,t\in\mathbb F_2,\quad u\in U_0.     \tag{2.4}
\]

The two-bit quotient label `pi(z)=(s,t)` has the following meanings:

| label | words |
|---|---|
| `00` | even cuts, including zero |
| `10` | odd cuts |
| `01` | complements of odd cuts |
| `11` | complements of even cuts, including the full block |

In particular, all `10` and `01` words are proper nonzero circuits. The only non-circuit `11` word is the full block. Every nonzero `00` word is a circuit.

---

## 3. Synchronization along an arbitrary graph

Let `H=(V,L)` be a connected simple graph with `q=|V|`, `h=|L|>=2`. Orient each edge arbitrarily, once and for all. For every oriented edge `uv`, take a disjoint copy `B_uv` of the base block. Define

\[
 Z(H,n)=\left\{z:
   z|_{B_{uv}}=x_uA+x_vB'+u_{uv},\quad
   x\in\mathbb F_2^V,\quad u_{uv}\in U_0\right\}.
                                                                  \tag{3.1}
\]

This is an explicit binary row-space presentation of a matroid, denoted `M(H,n)`. If an ordinary column representation is wanted, take any basis of `Z(H,n)^perp` as the rows of a parity-check matrix; its kernel is exactly (3.1). The checker independently performs this conversion.

There is no isolated vertex. Applying `pi` to each block recovers all endpoint bits `x_v`; subsequently it recovers every `u_uv`. Thus the parameterization is injective, and

\[
 |E(M)|=hm,\qquad
 \dim Z(H,n)=h(n-2)+q,\qquad
 r(M)=hm-h(n-2)-q.                                      \tag{3.2}
\]

### 3.1 The displayed partition

For `v in V`, let `D_v` have trace `A` on a block where `v` is the first endpoint, trace `B'` where it is the second endpoint, and trace zero elsewhere. These are words of (3.1). On every block the two incident `D_v` have complementary traces, so

\[
 D=\{D_v:v\in V\}\quad\text{is a disjoint partition of }E.
                                                                  \tag{3.3}
\]

The next classification shows that each `D_v` is a circuit. It will then be proved that (3.3) is **globally minimum**, not just irreducible under a selected set of exchanges.

### 3.2 Complete circuit classification

There are exactly two types of circuits.

* **Local circuits:** a nonzero even cut in one block, zero in all others.
* **Vertex-set circuits:** choose a nonempty `T subseteq V` with `H[T]` connected. Put zero on blocks not incident with `T`. On every incident block `uv`, put a proper base word with label `(1_T(u),1_T(v))`. In particular, on an edge internal to `T`, the trace is the complement of a **nonzero** even cut, not the full block.

**Proof.** A word with a full block contains a proper local circuit and is not a circuit. If a word has a nonzero `00` trace, it contains the corresponding local circuit; it is minimal only when that is the whole word.

For any other nonzero candidate, write `T={v:x_v=1}`. Its nonzero traces are exactly those incident with `T`, and all are proper. If `H[T]` is disconnected, keeping the traces incident with one component gives a nonzero proper subcycle; no edge joins two such components, so this restriction is consistent with (3.1).

Conversely, suppose `H[T]` is connected and all the prescribed traces are proper. Any contained cycle must use each trace either wholly or not at all, by Lemma 2.1. Its vertex set `R` is contained in `T`. On each edge internal to `T`, including one endpoint in `R` forces both endpoints into `R`, because the only available nonzero trace has label `11`. Connectivity implies `R` is either empty or all of `T`. An empty `R` cannot give a nonzero contained word, since there is no nonzero `00` trace. With `R=T`, every incident trace is forced, so the contained word is the original one. ∎

These matroids are also **simple and connected**. Every nonzero proper base word has at least `n-1>=5` elements: cuts have this property, and a cut complement has at least `m-n^2/4=n(n-2)/4>=n-1` elements for `n>=6`. Thus there are no circuits of size one or two. For connectedness, any two ground elements belong to one vertex-set circuit on `V`: in each relevant block choose a two-vertex shore avoiding the endpoints of those elements. At most four endpoints need be avoided, so `n>=6` suffices. The corresponding pair-cut complement contains the specified elements; choose arbitrary pair-cut complements on the other blocks. Section 3.2 makes the resulting word a circuit.

### 3.3 Classification of all full-ground-set partitions

In any circuit partition of `E`, each block is partitioned into exactly two proper base words, by Lemma 2.1. Their labels sum to `11`. Hence each graph vertex belongs to exactly one vertex-set circuit. The vertex sets of those circuits form a partition `Pcal` of `V` into connected induced subsets.

If both endpoints of a graph edge belong to one part, its block uses one `11` vertex-set trace and its complementary `00` local circuit. If the endpoints belong to different parts, its block uses the two complementary `10` and `01` vertex-set traces and no local circuit. Consequently the partition size is exactly

\[
 |\mathcal P|+\sum_{T\in\mathcal P}|L(H[T])|
   =q+\sum_{T\in\mathcal P}
           \bigl(|L(H[T])|-|T|+1\bigr).                 \tag{3.4}
\]

Every connected vertex partition is realizable: use `A,B'` on crossing edges, and an even cut and its complement on each internal edge. Connectivity makes each proposed vertex-set word a circuit by Section 3.2.

Each summand in (3.4) is nonnegative. The singleton partition gives the displayed `D`, proving

\[
 \boxed{c(E)=q.}                                        \tag{3.5}
\]

Moreover, a full partition is minimum **if and only if every `H[T]` is a tree**. The maximum full partition size is `h+1`, attained by one vertex-set circuit on `V` and one local circuit per graph edge. To see that no larger size is possible, contract the parts in (3.4): connectedness leaves at least `|Pcal|-1` crossing edges, and the cost is at most `|Pcal|+h-(|Pcal|-1)=h+1`.

For `H=K_q`, all minimum partitions therefore correspond to a matching: their vertex parts have size one or two. A matching with `t` edges gives `q-t` vertex-set circuits and `t` local circuits, totaling `q`. The traces may vary, but this structural description applies to **all** minimum partitions.

---

## 4. Every Eulerian restriction: exact integer optimum

Let `F in Z(H,n)` have vertex pattern `S={v:x_v=1}`. Its blocks fall into the following exhaustive classes.

* `P subseteq L(H[S])`: full blocks.
* `Q subseteq L(H[V\S])`: nonzero even-cut blocks outside `S`.
* Every other block incident with `S` has a proper nonzero trace, called frozen.
* Remaining blocks are zero.

Let

\[
 J=(S,L(H[S])\setminus P),\quad k(J)=\operatorname{cc}(J),
 \quad k_0=\operatorname{cc}(H[S]),                       \tag{4.1}
\]

where isolated vertices of `S` count as components and the empty graph has zero components. Let `P_in` be the edges of `P` whose endpoints are in the same component of `J`.

### Theorem 4.1

For every binary word `F`, including zero and the full word,

\[
 \boxed{c(F)=|Q|+k(J)+|P_{\rm in}|.}                    \tag{4.2}
\]

The largest size of an exact circuit partition of `F` is

\[
 \boxed{c_{\max}(F)=|Q|+k_0+|P|.}                       \tag{4.3}
\]

**Proof.** Every `Q` block is forced to be its single local circuit. In any remaining partition, each vertex of `S` belongs to exactly one vertex-set circuit, by the same block-label argument as in Section 3.3. No vertex outside `S` can occur. A frozen internal edge has its indivisible `11` trace, so its endpoints must lie in the same vertex part. Thus these parts are connected unions of components of `J`.

For such a partition `Rcal` of `S`, the exact cost is

\[
 |Q|+|\mathcal R|+
   |\{e\in P:e\text{ has both endpoints in one part of }\mathcal R\}|.
                                                                  \tag{4.4}
\]

Every such partition is realizable, fixing frozen traces, splitting a full crossing block into complementary `10,01` traces, and splitting a full internal block into a proper `11` trace and a local even cut.

The finest choice, the components of `J`, realizes (4.2). Merging `r` components of `J` into a connected part removes `r-1` vertex parts but requires at least `r-1` additional internal `P` edges connecting them. The edges of `P_in` are already internal before any merge. Therefore no merging lowers (4.4), proving minimality.

For the maximum, merge parts along an edge of `H[S]` whenever they are in the same component of that graph. Such a crossing edge must belong to `P`. Merging reduces the number of parts by one and adds at least one internal `P` edge, so it does not decrease (4.4). The coarsest partition, the components of `H[S]`, gives (4.3). ∎

For the old subunion

\[
 F_S=\bigcup_{v\in S}D_v,
\]

we have `P=L(H[S])`, `Q=empty`, and `J` is edgeless. Thus

\[
 c(F_S)=|S|.                                            \tag{4.5}
\]

This independently checks the global-optimality inheritance required by the question.

A further useful consequence, for connected `H`, is

\[
 \max_{F\in Z(H,n)}c(F)=\max(q,h),                      \tag{4.6}
\]

and every proper `F` has `c(F)<=h`. For `empty != S != V`, each component of `H[S]` has a distinct boundary edge, so `k_0<=|delta_H(S)|`; (4.3) is at most

\[
 |L(H[V\setminus S])|+|\delta_H(S)|+|L(H[S])|=h.
\]

For `S=V`, a proper `F` has `|P|<=h-1`, so (4.3) is at most `h`; for `S=empty`, its value is `|Q|<=h`. Equality `h` is attained by taking one nonzero even cut in every block, and equality `q` is attained by the full word.

---

## 5. Exact-load fractional certificates on the entire family

Now impose the main parameters `n>=8`, `4|n`. Define

\[
 m=\binom n2,\quad a=2(n-2),\quad U=\frac{n^2}{4},\quad
 \beta=\frac aU=\frac{8(n-2)}{n^2},\quad
 \alpha=\frac m{m-a}.                                  \tag{5.1}
\]

Then `0<beta<=1` and `1<alpha<=7/4<2`.

Two elementary symmetric distributions supply the certificates.

* Uniformly choose a two-vertex shore. Its even cut has size `a`, and each element of a block is included with probability `a/m`.
* Uniformly choose an `n/2`-vertex shore. Its cut is even because `4|n`, has size `U`, and includes each element with probability `U/m`.

Repeated descriptions of the same balanced cut are simply accumulated as repeated contributions to its coefficient; this is legitimate in an LP primal.

### 5.1 A fractional primal for every word

For each component `T` of `H[S]`, use total mass one on vertex-set circuits with vertex set `T`. Keep all frozen traces fixed. Independently on each full block in `P` internal to `T`, choose the **complement of a uniformly random two-vertex cut**. All these are circuits by Section 3.2.

Every frozen element gets load exactly one. On each full block the load is `1-a/m`. Fill the missing load using local balanced-even-cut circuits with total coefficient `beta` on that block. Indeed,

\[
 (1-a/m)+\beta(U/m)=1.                                 \tag{5.2}
\]

Finally use every forced `Q` circuit with coefficient one. This proves, for **every** `F`, including the full word,

\[
 \boxed{c_f(F)\leq |Q|+k_0+\beta|P|.}                  \tag{5.3}
\]

If `S` is empty, the construction consists just of the `Q` circuits and is optimal.

The `Q` circuits are also forced in every fractional partition: they are the only circuits available on their blocks, and no other contained circuit uses those elements. Hence they contribute exactly `|Q|`, additively. Since every fractional partition of a nonempty set has total coefficient at least one,

\[
 c_f(F)\geq |Q|+\boldsymbol 1_{S\ne\varnothing}.        \tag{5.4}
\]

No claim that (5.3) is always optimal is needed or made.

### 5.2 A better full-word certificate

For `F=E`, use only vertex-set circuits with vertex set `V`. Choose independently a pair-cut complement on each block, and give this product distribution total mass `alpha`. Every element receives load

\[
 \alpha(1-a/m)=1,
\]

so

\[
 \boxed{c_f(E)\leq\alpha<2.}                            \tag{5.5}
\]

Unlike the integer optimum (3.5), the right side is independent of the number of graph vertices. We do not identify it with the exact value of `c_f(E)`.

### 5.3 The actual hereditary maximum, exactly

For proper `F`, (5.3), `beta<=1`, and the argument proving (4.6) give `c_f(F)<=h`. For the full word, (5.5) gives `c_f(E)<2<=h`. Thus **all** Eulerian restrictions have been bounded, not merely old subunions.

For the reverse inequality, choose a nonzero even cut independently in each of the `h` blocks and let `W` be their union. It has vertex pattern zero. The circuit classification shows that its **only** contained circuits are the chosen `h` local cuts. They form a disjoint partition. A dual with price one on one element of each cut and zero elsewhere has value `h` and every circuit price at most one. Therefore

\[
 c_f(W)=h,
\qquad\boxed{p(M(H,n))=h.}                              \tag{5.6}
\]

This proves (0.2), with the genuine hereditary maximum checked over the whole cycle space.

---

## 6. Every Eulerian restriction satisfies the actual factor-two target

The construction cannot hide a bad `c/p` ratio in one of its restrictions. For a word `F` with data `S,P,Q,k_0`, two explicit subrestrictions give independent exact lower witnesses.

1. **Local witness.** In each full `P` block, select one nonzero even cut; retain the original `Q` cuts; put zero elsewhere. This is a subcycle of `F` with vertex pattern zero. Its only circuits are the selected `|P|+|Q|` disjoint local circuits. Its fractional value is exactly `|P|+|Q|`.

2. **Frozen-component witness.** Replace each full `P` trace of `F` by the proper complement of a nonzero even cut, leaving all other traces unchanged. This is another subcycle of `F`, now with no full blocks. Its only circuits are one vertex-set circuit for each component of `H[S]`, together with the `Q` circuits. To see uniqueness, every internal edge of `H[S]` now has a frozen `11` trace; any nonzero contained vertex pattern is a union of entire components, and a circuit can use only one component. Its fractional value is exactly `k_0+|Q|`.

Both exact values have the same elementary primal/dual certificates as in Section 5.3. Consequently

\[
 p(M|F)\geq |Q|+\max(|P|,k_0).                           \tag{6.1}
\]

The maximum-partition formula (4.3) now yields

\[
 \begin{split}
 c(F)&\leq |Q|+|P|+k_0\\
     &\leq 2\bigl(|Q|+\max(|P|,k_0)\bigr)
      \leq 2p(M|F).
 \end{split}                                                       \tag{6.2}
\]

This is a **full hereditary factor-two theorem for this class**, not for arbitrary binary matroids. The proof uses actual subrestrictions not confined to a preselected circuit partition. It also works for the even-`n` variant in Section 11.2.

### 6.1 The hereditary factor two is sharp within this class

Orient `P_3` as `0->1->2`, take `M(P_3,n)`, and let `F` have its first block full and its second block equal to a fixed proper `11` trace `R` (for example, the complement of a two-vertex even cut). Its entire supported cycle space is

\[
 \{(\delta(T),0):T\subseteq[n]\}
 \;\cup\;
 \{(1_B+\delta(T),R):T\subseteq[n]\}.
\]

Indeed, the second trace must be zero or all of `R`, by Lemma 2.1; these alternatives force `x_1=x_2=0` or `x_1=x_2=1`, respectively, while `x_0` permits both cut parities in the first block. Every proper nonzero word in this displayed space is a circuit, again by the base antichain. Thus `c(F)=2` and its hereditary maximum equals its full fractional value.

Put `gamma=(n-1)/U=4(n-1)/n^2`. Give coefficient `1/n` to each of the `n` circuits `(1_B+delta({v}),R)`. The first-block missing load is `(n-1)/m`; fill it by local balanced cuts of total coefficient `gamma`. This is an exact primal of value `1+gamma`.

For a matching signed dual, put price `1/U` on every first-block element, price `1-(m-(n-1))/U` on one element of `R`, and zero on its other elements. Every local cut has size at most `U`, and every global circuit's first trace is a nontrivial-cut complement of size at most `m-(n-1)`. Thus every circuit has price at most one, and the total price is `1+gamma`. The anchor price is negative for the stated parameters; no nonnegative-dual assumption is being made. Consequently

\[
 \boxed{c(F)=2,\qquad p(M|F)=c_f(F)=1+\frac{4(n-1)}{n^2},
 \qquad \frac{c(F)}{p(M|F)}\longrightarrow2.}            \tag{6.3}
\]

The checker independently enumerates all 256 supported words and all 254 circuits in this restriction at `n=8`, verifies `c=2`, and checks the exact primal/dual value `23/16`, including the negative anchor price `-5/16`. This does not improve the already known universal lower threshold from the prior note; it establishes sharpness of the new class theorem itself.

---

## 7. A supplied global minimum can have no valuable subunion at all

Take `H=K_q`, `q>=3`, and the singleton/vertex partition `D` from (3.3). Every nonempty induced `H[S]` is connected. For `0<|S|<q`, (5.3) gives

\[
 c_f(F_S)\leq 1+\beta\binom{|S|}{2},
\qquad c_f(E)\leq\alpha.                               \tag{7.1}
\]

Choose `n=4q^2`. Then

\[
 \beta=\frac2{q^2}-\frac1{q^4}<\frac2{q^2}.
\]

For every proper nonempty `S`,

\[
 c_f(F_S)
  <1+\frac{(q-1)(q-2)}{q^2}<2.
\]

The empty word has value zero, and the full word has value at most `alpha<2`. Thus (0.3) holds. Simultaneously, `c(F_S)=|S|` and `c(E)=q` by Sections 3–4.

For any finite proposed constant `K`, take `q>2K`. Every subunion of this genuinely globally minimum `D` then has fractional value **strictly less than `|D|/K`**. Taking an expectation cannot change that obstruction, regardless of the distribution or how structurally/adaptively the subset was selected.

This excludes a strategy restricted to the vertices of the cube generated by a supplied minimum partition. In the cycle-polytope/gauge language, the gauge is uniformly below two on this cube, while its monotone corner-to-corner circuit distance is `q`. Binary symmetry does not rescue a proof that only queries that cube.

It does **not** exclude querying the other cycle-polytope vertices. Here

\[
 p(M)=\binom q2,\qquad \frac{c(M)}{p(M)}=\frac2{q-1}.    \tag{7.2}
\]

The local witness of Section 5.3 is outside the cube: its recovered vertex pattern is zero but the word is nonzero, whereas the only old subunion with vertex pattern zero is the empty set.

### 7.1 An explicit finite uniform-half counterexample

For independent half-retention of the vertex partition, summing (7.1) by subset size gives

\[
 \mathbb E c_f(F_S)
 \leq \frac{2^q-2+\beta\binom q2(2^{q-2}-1)+\alpha}{2^q}.
                                                                  \tag{7.3}
\]

Indeed, a fixed graph edge is internal to `2^{q-2}` subsets; subtract the full subset when using the proper-subset formula.

For `q=5,n=64`,

\[
 h=10,\quad m=2016,\quad
 \beta=\frac{31}{256},\quad\alpha=\frac{504}{473}.
\]

The matroid has 20,160 elements, cycle dimension 625, and rank 19,535. Its exact integral optimum is 5 and actual hereditary maximum is 10. The exact upper certificate in (7.3) is

\[
 \mathbb E c_f(F_S)\leq\frac{2394037}{1937408}
       <\frac54,
\qquad
 \frac54-\frac{2394037}{1937408}
       =\frac{27723}{1937408}>0.                        \tag{7.4}
\]

With `q=5,n=192`, there is the stronger deterministic failure

\[
 \max_{S\subseteq V}c_f(F_S)\leq\frac{479}{384}<\frac54.
                                                                  \tag{7.5}
\]

These are rational **upper certificates below the conjectured lower bound**; exact fractional optimization on the large instances is unnecessary.

### 7.2 Quantifier guardrail: replacing the partition is different

For `K_q`, choose a maximum matching and a corresponding minimum partition from Section 3.3. Select all its local circuits, and, if `q` is odd, also its single remaining singleton vertex circuit. Their union has no other contained circuits: the local blocks have pattern `00`, and the singleton's frozen traces preclude adding any other vertex pattern. This is a direct sum of `ceil(q/2)` circuits, so it has exact fractional value `ceil(q/2)`.

Thus the same family admits another minimum partition with a valuable **nonexchangeably chosen** subunion. The no-constant result (0.3) is not a claim that all minimum partitions are bad for every selection rule.

---

## 8. Half retention at four fails for **every** minimum partition

The ambiguity about which global minimum is used can be removed for the specific uniform-half claim.

Fix any minimum partition of `M(K_q,n)`. It corresponds to a matching of size `t`, `0<=t<=floor(q/2)`. There are `q-t` vertex-set circuits (one per matched pair or unmatched singleton), and `t` local circuits (one on each matched-pair block).

After retaining each of its `q` circuits independently with probability `1/2`, use the restriction data `S,P,Q` of Section 4.

* A `Q` block occurs precisely when the local circuit of a matched pair is retained and its vertex-set circuit is not. Thus `E|Q|=t/4`.
* `S` is nonempty precisely when at least one of the `q-t` vertex-set circuits is retained. Thus `Pr(S nonempty)=1-2^{-(q-t)}`.
* Every block is partitioned into two circuits of the fixed full partition. It is full after retention precisely when both are retained. Thus `E|P|=h/4`, independently of the matching and of all the chosen traces.

Since a nonempty `K_q[S]` is connected, (5.3)–(5.4) give the rigorous two-sided bound

\[
 \frac t4+1-2^{-(q-t)}
 \ \leq\ \mathbb E c_f(F)
 \ \leq\ \frac t4+1-2^{-(q-t)}+\frac{\beta h}{4}.         \tag{8.1}
\]

The general certificate (5.3), rather than its special full-word improvement, is used here, so there is no exception for retaining all circuits.

### 8.1 A strict finite counterexample for all global minima

Set `q=9`, `n=256`, `h=36`. Then `beta=127/4096`. The upper expression in (8.1) increases for `t=0,...,4`, so its maximum is

\[
 1+\frac{31}{32}+9\frac{127}{4096}
     =\frac{9207}{4096}<\frac94.                        \tag{8.2}
\]

The matroid has 1,175,040 elements, cycle dimension 9,153, rank 1,165,887, `c=9`, and `p=36`. **Every** minimum partition satisfies (0.4), regardless of trace choices. Thus merely optimizing the minimum partition does not make the uniform-half `K=4` assertion true.

### 8.2 Even optimizing an exchangeable law has limiting ratio one eighth

An exchangeable law on subfamilies of a fixed `q`-part partition is a mixture of uniform fixed-cardinality laws. Conditional on retaining `r` circuits, for any one matched pair's local/global circuit pair,

\[
 \Pr(\text{local retained, global omitted})
   =\frac{r(q-r)}{q(q-1)}
   \leq\frac{q}{4(q-1)}.                               \tag{8.3}
\]

Therefore, for any exchangeable law and any minimum partition,

\[
 \mathbb E c_f(F)
   \leq\frac{tq}{4(q-1)}+1+\beta h.                    \tag{8.4}
\]

Take `n=4q^2`. Then `beta h<1`, and `t<=floor(q/2)`. Dividing (8.4) by `q` gives an upper bound tending to `1/8`, uniformly over both choices being optimized.

For the reverse limiting bound, use a maximum-matching minimum partition and independent half-retention. The forced `Q` circuits alone give expected fractional value at least `floor(q/2)/4`, by (5.4). Dividing by `q` tends to `1/8`. This proves (0.5).

This rules out an exchangeable proof with any denominator `K<8` even if a favorable global minimum is selected first. It neither proves a retention theorem at eight nor supplies a counterexample to the actual hereditary target (0.1).

---

## 9. The proposed one-step inequality is explicitly false

Consider

\[
 N=M(P_3,16),\qquad M=N\oplus N.
\]

For `N`, `q=3`, `h=2`, `m=120`, `a=28`, and `alpha=30/23`. The preceding theorems give

\[
 c(N)=3,\quad p(N)=2,\quad c_f(N)\leq\frac{30}{23},
 \quad c_f(N|F)\leq2\quad\text{for every proper Eulerian }F.
                                                                  \tag{9.1}
\]

For direct sums, circuits stay in one summand and both the integral and fractional exact-partition costs add. The hereditary maximum adds as well, since maximizing restrictions can be chosen independently.

Every circuit `C` of `M` is in one of the two summands. Its complement leaves the other summand intact and a proper Eulerian restriction in the affected one. Consequently

\[
 c(M)=6,\quad p(M)=4,\quad c_f(M)\leq\frac{60}{23},
 \quad
 \max_C c_f(M\setminus C)\leq\frac{30}{23}+2=\frac{76}{23}.
\]

Thus

\[
 c_f(M)+\max_C c_f(M\setminus C)
    \leq\frac{136}{23}<\frac{138}{23}=c(M).              \tag{9.2}
\]

The matroid is explicitly binary and Eulerian by (3.1) and direct sum. Its ground set has `2*2*120=480` elements, cycle dimension `2*(2*14+3)=62`, and rank 418. In particular, the one-step inequality cannot be used as a general lemma in this approach. Its failure here does not conflict with the hereditary target: `c(M)=6<=2p(M)=8`.

---

## 10. A rigorous obstruction to tensor-coupling the local kernels

A natural next attempt is to couple the independent edge-local kernels by a second binary code, so that the `h`-circuit witness in Section 5.3 is no longer available. There is a precise obstruction to this particular recursive operation when the inner even-cut kernel is large enough.

Let `K <= F_2^L` be any Eulerian binary cycle space on the bookkeeping edges, so `1_L in K`, and let

\[
 t=c_K(L)
\]

be its **actual** minimum full circuit partition size. Replace the independent `U_0` variables in (3.1) by their tensor-coupled subspace:

\[
 Z_{H,K,n}=\langle D_v:v\in V\rangle+(K\otimes U_0).
                                                                  \tag{10.1}
\]

Here `a tensor u` has trace `u` on the blocks indexed by `supp(a)` and zero elsewhere. Equivalently, after choosing a basis of `U_0`, each of its coefficient vectors across the `h` blocks must be a word of `K`. This is a subcode of `Z(H,n)` containing all `D_v` and the full word. The quotient labels still make its dimension exactly `q+(n-2)dim K`.

### Theorem 10.1

For every connected simple `H` with `h>=2`, every such Eulerian `K`, and every even `n>=6`,

\[
 c(Z_{H,K,n})\leq\min(q,t+1).                            \tag{10.2}
\]

If in addition `n-2>=t`, then

\[
 p(Z_{H,K,n})\geq t,\qquad
 \boxed{c(Z_{H,K,n})\leq p(Z_{H,K,n})+1\leq2p(Z_{H,K,n}).}
                                                                  \tag{10.3}
\]

In particular, shrinking the independent kernels in this tensor-product fashion cannot yield an unbounded ratio, or violate the factor-two target, when the inner cut space has at least `t` independent directions. If `q>t+1`, the displayed `q`-part vertex partition ceases to be globally minimum outright.

**Proof of the integral upper bound.** Fix a minimum circuit partition `A_1,...,A_t` of `L` in `K` and a nonzero `u in U_0`. The word `W=1_L tensor u` belongs to (10.1). Its restriction is precisely the code `K` with each coordinate replaced by the support of `u`: by the proper-word antichain, every contained nonzero block trace must equal `u`, and all quotient labels are zero. Thus `A_i tensor u` are circuits and partition `W`.

The complement `E\W` has a proper `11` trace on every block. It is the vertex-set circuit on `V` in the larger code `Z(H,n)`, so remains a circuit in the subcode (10.1). This gives a `(t+1)`-circuit partition of the full ground set. Each `D_v` likewise remains a circuit, giving the alternative upper bound `q`.

**Proof of the hereditary lower bound.** Choose linearly independent nonzero words `u_1,...,u_t in U_0`, possible when `n-2>=t`. They are all base circuits. Consider the colored word

\[
 W_{\rm col}=\sum_{i=1}^t A_i\otimes u_i.               \tag{10.4}
\]

It belongs to `K tensor U_0` and has a nonzero proper even-cut trace on every block. Any codeword contained in it has, on a block in `A_i`, either trace zero or trace `u_i`, by Lemma 2.1. Its quotient labels are zero, so it lies in `K tensor U_0`.

For each `i`, apply a linear functional on `U_0` taking value one at `u_i` and zero at the other `u_j`. The resulting block-indicator word belongs to `K` and is supported in `A_i`. Since `A_i` is a circuit of `K`, that indicator is either zero or all of `A_i`. Therefore the entire supported subcode of (10.4) consists exactly of the unions of the `t` disjoint circuits `A_i tensor u_i`. Its exact fractional value is `t`. The one-anchor-per-piece dual certifies this value, proving (10.3). ∎

The fractional upper certificates of Section 5 are **not** being reused after coupling: their independent block choices need not belong to (10.1). Theorem 10.1 instead uses an integral upper certificate and an actual hereditary lower witness.

The same argument works with **any** family of `t` disjoint circuits of `K`, not necessarily a minimum full partition, whenever `t<=dim U_0`. In particular it can expose an integral outer decomposition that was fractionally cheap before the tensor coupling. No independence of the supports in the old outer partition cube is being presumed; it is created by the independent `u_i` labels.

### 10.2 An exact finite kernel-coupling audit

Take `H=K_5`, outer code `K=Cut(K_5)+<1>`, and inner parameter `n=8`. The outer code has `c_K(L)=2`, `p(K)=5/3`. Its 32 words and 30 circuits are independently enumerated by the checker; equal coefficients `1/3` on the five star complements and uniform element prices `1/6` certify the full fractional value. Every proper nonzero outer word is a circuit.

The coupled code (10.1) has 280 elements, cycle dimension 35, and rank 245. The two-colored witness (10.4) has exactly four supported codewords and exactly two circuits, proving `p>=2`: the outer fractional value `5/3` has not been preserved by this attempt to suppress the local witnesses. The generic proof constructs a three-circuit full partition, already disproving global optimality of the displayed five-circuit partition.

In fact, this finite coupled example has **actual global minimum two**. Here is a fully reproducible complementary-pair certificate. Order the ten bookkeeping edges lexicographically. Order the five outer basis rows as the stars at `0,1,2,3`, followed by the full word. Order the six inner basis rows as `delta({0,i})`, `i=1,...,6`. Use the thirty tensor rows in inner-major order followed by `D_0,...,D_4`. Take the binary row-sum with message mask

```text
0x75d1031a5
```

(bits numbered from zero in this 35-row order), and take its complement. The checker computes the supported-subcode dimension of each as **one**, equivalently rank 34 for the generator-column constraints outside either support. Thus both are circuits. The full word is not a circuit since it properly contains `D_0`, proving `c=2` exactly. This is exact binary Gaussian elimination, not an LP estimate or a claim inferred from failure of a search.

The whole `2^35`-word code is not enumerated, and no exact value of its full hereditary maximum is claimed; the certified lower bound `p>=2` already proves `c<=p` for this instance. The general theorem (10.3) uses the actual hereditary maximum through a lower witness and supplies the full constant bound for its stated class without needing an upper enumeration of that maximum.

This does not eliminate more complicated recursive couplings, nor the regime `t>n-2`. It does show why simply substituting another low-fractional Eulerian binary code into the independent-kernel slots is not a justified amplification argument: global minimum can collapse, and independently colored local restrictions can increase the hereditary denominator.

---

## 11. Independent exact verification and its scope

Run from `/workspace/leanproject`:

```sh
python3 Submission/ResearchHereditaryFollowupCheck.py
```

Only the standard library is used. There is no numerical LP tolerance and no random sampling.

### 11.1 Small instances are exhaustively audited from the row spaces

The checker does **not** take the circuit classification or integer formulas as inputs to its reconstruction.

1. It enumerates the complete binary row space.
2. It independently constructs an ordinary binary column representation, verifies its rank, checks that its total column sum is zero, and checks that its kernel is precisely the enumerated cycle space.
3. For each word `F`, it computes the dimension of the subcode supported in `F`. Explicitly, if `g_e` is the generator-matrix column at `e`, the message vectors of this subcode satisfy `dot(g_e,x)=0` for every `e notin F`. A nonzero `F` is a circuit exactly when this kernel has dimension one. This independently determines **all circuits**.
4. It enumerates each supported subcode and hence every circuit contained in each word. Integer dynamic programming, anchored at the first used element, determines both minimum and maximum exact partition sizes for every word. These are compared with (4.2)–(4.3).
5. It expands the product-distribution fractional primal for every word, checks that every support is an independently identified contained circuit, and verifies every load equation with exact rational arithmetic. Thus every word receives a certified fractional upper bound at most `h`.
6. It checks the exact `h`-circuit hereditary witness against **all** its contained circuits, establishing `p=h` rather than merely an upper estimate.
7. For **every** word, it constructs and verifies both exact subrestriction witnesses from Section 6, checking the hereditary factor-two conclusion throughout the instance.
8. In the `K_3` instance, it independently enumerates **all** globally minimum partitions and checks their matching structure and the exact generic-primal expectation identity used in (8.1).

The audited instances and results are:

| bookkeeping graph | `n` | elements | cycle dimension | all words | all circuits | `c(E)` | maximum full partition | exact `p` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `P_3` | 8 | 56 | 15 | 32,768 | 16,383 | 3 | 3 | 2 |
| `K_3` | 6 | 45 | 15 | 32,768 | 15,708 | 3 | 4 | 3 |
| `P_4` | 6 | 45 | 16 | 65,536 | 15,484 | 4 | 4 | 3 |

The `K_3,n=6` case has exactly 15,616 minimum partitions: 4,096 with matching size zero and 11,520 with matching size one. The cyclic bookkeeping graph is important: it checks a case where **not every** full partition is globally minimum.

### 11.2 Why the `n=6` audit is legitimate

All structural and integer results in Sections 2–4 and the hereditary witnesses in Section 6 require only even `n>=6`. For the fractional construction with general even `n`, let `b` be the largest even integer at most `n/2`, and replace `U` by `b(n-b)`. Use uniformly chosen `b`-vertex shores in the filling distribution. Then `U>=2(n-2)=a`, so `beta<=1`, and the same proof works.

At `n=6`, `b=2`, `U=a=8`, `beta=1`, `alpha=15/7`. The proof of exact `p=h` remains valid whenever `h>=alpha`, hence for the two three-edge graphs in the table. This variant permits exhaustive cyclic examples without enumerating millions of higher-dimensional words. It is not being used for the large retention counterexamples, all of which satisfy the main `4|n`, `n>=8` conditions.

### 11.3 Large instances: certificate identities, not gigantic enumerations

For `(q,n)=(5,64),(5,192),(9,256)`, the checker verifies the exact rational certificate equations, dimensions, strict inequalities, and expectation formulas. It also checks the asymptotic formula inequalities at every integer `3<=q<=64` with `n=4q^2`, and the elementary exchangeable probabilities for every cardinality at those sizes. The proofs in Sections 7–8, not these finite tests, establish the statements for all `q`.

It would be incorrect to describe this as an enumeration of `2^625` words, much less `2^9153` words. The large instances are certified by the fully proved structural classification and explicit primal distributions. The strict upper bounds already refute the claimed lower bounds; no exact fractional optimum for those large old subunions is asserted.

The checker also verifies the exact `136/23<6` arithmetic and binary-code parameters of the one-step counterexample. For Section 10, it enumerates the 32-word outer code and uses exact supported-subcode ranks in the 35-dimensional coupled code: all four words of the two-colored lower witness, each circuit in the generic three-part upper certificate, and the complementary pair certifying the actual global minimum two are checked. This is explicitly distinguished from complete enumeration of that larger code. Its final success line is:

```text
ALL EXACT CHECKS PASSED
```

---

## 12. What this does and does not leave open

* **Refuted:** uniform-half retention with denominator four for a genuine global minimum, even when the minimum partition can be chosen optimally.
* **Refuted more strongly, with a different quantifier:** every constant selection theorem confined to the subunions of an arbitrary supplied global minimum. Adaptive, nonexchangeable choices do not save that formulation.
* **Sharpened barrier:** optimizing a global minimum and any exchangeable law has limiting best ratio `1/8` on this new family.
* **Refuted:** the proposed universal one-step inequality `c(E)<=cf(E)+max_C cf(E\C)`.
* **Proved:** complete circuit and integer-partition classifications for `M(H,n)`, exact actual `c=q,p=h`, and the factor-two target for **all Eulerian restrictions** of the family.
* **Proved for an additional coupling class:** replacing the local kernels by `K tensor U_0` gives `c<=p+1<=2p` whenever `dim U_0>=c_K(L)`. Thus that natural large-inner-kernel recursive operation does not produce an unbounded actual ratio.
* **Not resolved:** the existence of any universal binary `K` in (0.1), or an unbounded actual `c/p` counterexample. The known lower threshold `K>=2` from the prior note is unaffected.

The independent local even-cut kernels are decisive in both directions: they make the fractional refilling cost small, but they also supply the large off-cube hereditary witness `p=h`. Synchronizing more vertex labels along a dense graph destroys the proposed retention argument without destroying that witness. The tensor-coupling theorem in Section 10 gives a further rigorous obstruction: local coloring can recover an integral outer partition as an exact fractional hereditary witness, while the proposed new minimum can collapse. Any other attempted recursive amplification must control these witnesses **and simultaneously reprove the whole-family global minimum and all-restriction bounds**; this report does not assume that such a modification works.
