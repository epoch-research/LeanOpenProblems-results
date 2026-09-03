# Optimal minimum-partition retention: a counterexample for every finite constant

## Status and new result

**The unrestricted optimized-minimum retention statement is false for finite Eulerian binary matroids, for every finite denominator `K`.** This note gives a complete structural counterexample, not another bad supplied partition.

There are connected, simple, Eulerian binary matroids `N_q`, with `c(N_q)=q`, such that

\[
\boxed{\quad
 \text{for EVERY globally minimum partition }\mathcal D
 \text{ and EVERY }\varnothing\ne\mathcal A\subseteq\mathcal D,
 \qquad
 1\le c_f\!\left(\bigcup\mathcal A\right)<1+\frac1q.
 \quad}                                                        \tag{0.1}
\]

Consequently

\[
 \sup_{\mathcal D\text{ minimum},\;\mu\text{ any retention law}}
 \frac{\mathbb E_\mu c_f(\bigcup\mathcal A)}q\longrightarrow0.     \tag{0.2}
\]

The law may be exchangeable, nonexchangeable, adaptive, or deterministic. It may depend on the chosen partition and all its circuit traces. Allowing a randomized choice of minimum partition also cannot help. In particular, neither lexicographic optimization of sorted circuit lengths nor direct optimization of the fractional retention objective rescues a universal constant.

**What is not resolved:** no counterexample to `c<=Kp`, no graphic counterexample, and no refutation of the **critical-only** retention statement is claimed. In fact, these examples have

\[
 c(N_q)=q,\qquad p(N_q)=Q(N_q)=q(q-1),\qquad
 \frac{c(N_q)}{p(N_q)}=\frac1{q-1},                         \tag{0.3}
\]

where `Q=max_even F c(F)`. They are not critical. A proof restricted to genuine critical restrictions could still yield the desired hereditary bound and the graphic Erdős–Gallai consequence.

The single construction studied here is the previous clique synchronization code with **two independent blocks per bookkeeping edge**. This small change is decisive: a two-vertex merger now costs two local circuits, not one. We prove that *all* nonsingleton vertex parts strictly increase the partition count. This removes the matching-based alternative minima responsible for the previous limiting ratio `1/8`.

The only new files are this report and **`ResearchOptimalRetentionCheck.py` at the repository root**. All proofs are at paper level, with exact finite checks, not Lean formalizations or literature-priority claims. No specification was edited.

---

## 1. Exact partition conventions

A binary matroid is specified by its cycle space `Z <= F_2^E`. Its circuits are the support-minimal nonzero words. Assume `1_E in Z`. For a cycle `F`,

\[
\begin{aligned}
 c(F)&=\min\{|\mathcal D|:\mathcal D\text{ is a disjoint circuit partition of }F\},\\
 c_f(F)&=\min\left\{\sum_C x_C:
   x_C\ge0,\quad \sum_{C\ni e}x_C=1\ (e\in F),
   \quad C\subseteq F\text{ a circuit}\right\},\\
 p(M)&=\max_{F\in Z}c_f(F),\qquad Q(M)=\max_{F\in Z}c(F).
\end{aligned}                                                     \tag{1.1}
\]

The empty restriction has both costs zero. Dual prices are unrestricted in sign. The counterexample uses **exact-load primal upper certificates**, not covers, odd covers, or assumed nonnegative dual optima.

For any globally minimum partition `D` and `A subseteq D`,

\[
 c\!\left(\bigcup\mathcal A\right)=|\mathcal A|.                  \tag{1.2}
\]

Otherwise replacing `A` would shorten the full partition. Our examples satisfy (1.2) throughout; their integer/fractional discrepancy on these subunions is real.

---

## 2. The binary block, recalled with its proof

Let `n>=8`, `4|n`, and put `B=E(K_n)`, `m=binom(n,2)`. Binary addition of supports means symmetric difference. Define

\[
 Z_0=\operatorname{Cut}(K_n)+\langle 1_B\rangle.
\]

### Lemma 2.1 — proper-word antichain

Every nonempty proper word of `Z_0` is a circuit. Every partition of `B` into nonempty proper base words has exactly two parts.

**Proof.** Nontrivial cuts form an antichain: if `delta(S) subseteq delta(T)`, then `S` is constant on each shore of `T`, so the cuts coincide. Their complements consequently also form an antichain.

Two nontrivial cuts cannot be disjoint. If every edge across a nontrivial `S` has its endpoints on the same side of `T`, the complete bipartite graph across `S` forces `T` to be constant. This also excludes a cut contained in a proper cut complement.

Conversely, a proper cut complement cannot be contained in a cut: that would make two cuts cover `K_n`. Label each vertex by its two shore-membership bits. With `n>=5`, two vertices have the same label, and their edge lies in neither cut. This is a contradiction.

Thus all nonempty proper words are support-minimal. The complement of the first part of a partition of `B` is another such word, hence a circuit; there is exactly one remaining part. ∎

Since `n` is even, the parity of a shore is unchanged by complementation. Set

\[
 U_0=\{\delta(T):|T|\text{ even}\},\qquad
 A=\delta(\{0\}),\qquad A^c=1_B+A.
\]

The dimension of `U_0` is `n-2`; a basis is `delta({0,i})`, `1<=i<=n-2`. Every base word has a unique expression

\[
 z=sA+tA^c+w,\qquad s,t\in\mathbb F_2,\quad w\in U_0.             \tag{2.1}
\]

Write `pi(z)=(s,t)`. Its four fibers are:

| Label | Base words |
|---|---|
| `00` | even cuts, including zero |
| `10` | odd cuts |
| `01` | complements of odd cuts |
| `11` | complements of even cuts, including `B` |

Every `10` or `01` word is nonempty and proper. The sole nonproper `11` word is `B`.

---

## 3. The doubled-clique code

Let `q>=2`, `V=[q]`. For **each unordered pair** `u<v`, take **two disjoint copies** `B_uv^(0), B_uv^(1)` of the base block. The number of blocks is

\[
 h=2\binom q2=q(q-1).
\]

Define the cycle space

\[
 Z^{(2)}_{q,n}=
 \left\{z:
 z|_{B_{uv}^{(b)}}=x_uA+x_vA^c+w_{uv}^{(b)},
 \quad x\in\mathbb F_2^V,\quad
 w_{uv}^{(b)}\in U_0\text{ independently}\right\}.                \tag{3.1}
\]

Call its binary matroid `N(q,n)`. This definition does not require a multigraph to be the target graph: the bookkeeping object has parallel edges, but **the constructed object is a binary matroid**. Taking any basis of `(Z^(2)_(q,n))^perp` as the rows of a parity-check matrix gives an ordinary binary column representation.

The quotient labels recover every vertex bit `x_v`, and then every local kernel word. Therefore

\[
 |E|=hm,\qquad \dim Z^{(2)}_{q,n}=h(n-2)+q,\qquad
 r(N(q,n))=hm-h(n-2)-q.                                      \tag{3.2}
\]

Setting all vertex bits to one and all kernel words to zero gives `1_E`, so the matroid is Eulerian. The canonical vertex word `D_v` has trace `A` when `v` is the first endpoint, `A^c` when it is the second endpoint, and zero otherwise. These words partition `E`.

### Lemma 3.1 — complete circuit classification

The circuits are exactly:

1. **Local circuits:** one nonzero even cut in one block, zero in all other blocks.
2. **Vertex-set circuits:** choose a nonempty `T subseteq V`; put zero on blocks disjoint from `T`; on every incident block use a **proper** base word with label `(1_T(u),1_T(v))`.

In particular, an internal block of a vertex-set circuit uses a proper complement of a nonzero even cut, not the full block.

**Proof.** A word with a full block contains a proper local circuit and is not minimal. A word with a nonzero `00` trace contains that local circuit, so it can be minimal only when that is its whole support. This proves that every other possible circuit has the form in item 2.

Conversely, consider a word of item 2 and a cycle contained in it. By Lemma 2.1, each trace of the contained cycle is either zero or the entire available proper trace. Its vertex pattern is some `R subseteq T`. On every internal block the available label is `11`, so including one endpoint in `R` forces the other endpoint. The clique on `T` is connected, including when `T` is a singleton. Hence `R` is empty or all of `T`. In the first case no nonzero trace is available with label `00`, so the contained cycle is zero. In the second every nonzero trace is forced. The word is a circuit. ∎

In particular the canonical `D_v` are circuits.

These matroids are **simple and connected**. Each nonzero proper base word has at least `n-1` elements: a cut has that property, and a cut complement has at least `n(n-2)/4>=n-1` elements. Thus there are no matroid loops or two-element circuits. For connectedness, any two ground elements lie in one vertex-set circuit on `T=V`: in each relevant block choose a two-vertex shore avoiding the endpoints of the specified base edges, and use its cut complement. There are enough unused vertices because `n>=8`; other blocks can use arbitrary pair-cut complements. Lemma 3.1 applies. **No graphic realization is asserted.**

---

## 4. All full partitions, and why every minimum is bad

### Theorem 4.1 — exact all-partition count formula

Every circuit partition of the full ground set determines a set partition `Pcal` of `V` and has size

\[
\boxed{
 |\mathcal D|
  =|\mathcal P|+2\sum_{T\in\mathcal P}\binom{|T|}{2}
  =q+\sum_{T\in\mathcal P}(|T|-1)^2.
}                                                               \tag{4.1}
\]

Every set partition of `V` is realizable. Consequently

\[
 \boxed{c(N(q,n))=q,}
\]

and **every** globally minimum partition consists of one singleton vertex-set circuit for each vertex, and **no local circuits**.

**Proof.** In any full circuit partition, each block is partitioned into nonempty proper base traces. By Lemma 2.1 there are exactly two complementary traces. Their quotient labels are either `10,01` or `11,00`.

Fix a vertex `v` and any incident block. Exactly one of the two traces has its `v`-bit equal to one. Since every vertex-set circuit containing `v` uses that block, exactly one vertex-set circuit contains `v`. Thus the vertex sets of the nonlocal circuits form a set partition `Pcal` of `V`.

If both endpoints of a bookkeeping pair lie in one part `T`, each of its **two** blocks uses a `11` trace from that part's circuit and a complementary `00` local circuit. If the endpoints lie in different parts, each block uses complementary `10,01` traces and no local circuit. This gives the first equality in (4.1). The second follows by summing

\[
 1+s(s-1)=s+(s-1)^2
\]

over the part sizes `s`.

Conversely, for any set partition, split every internal block into a nonzero even cut and its complement; split every crossing block into an odd cut and its complement. The proposed vertex-set words are circuits by Lemma 3.1, and the cuts on internal blocks are local circuits. They give a full partition of the displayed size.

Every square in (4.1) is nonnegative and vanishes exactly for a singleton part. The canonical singleton partition attains `q`, proving all assertions. ∎

An arbitrary minimum can still choose its traces freely. On each block choose any `10` word for the first endpoint and give its complement to the second endpoint. All choices are independent. There are exactly

\[
 2^{h(n-2)}                                                     \tag{4.2}
\]

unordered minimum partitions: the singleton vertex labels distinguish their members uniquely. The next bound is uniform over **all** these choices, not just the canonical `A,A^c` traces.

**Difference from the single-block construction.** With one block per pair, a two-vertex part plus its one local circuit still costs two and can appear in a minimum. With two blocks, it costs three. Formula (4.1) rules out all larger mergers as well, not merely pairwise exchanges.

---

## 5. A low exact fractional certificate for every minimum subunion

Put

\[
 a=2(n-2),\qquad U=\frac{n^2}{4},\qquad
 \beta=\frac aU=\frac{8(n-2)}{n^2},\qquad
 \alpha=\frac m{m-a}<2.                                      \tag{5.1}
\]

Here `0<beta<=1`. A uniform two-vertex shore has cut size `a` and includes each base edge with probability `a/m`. A uniform `n/2`-vertex shore has cut size `U` and includes each base edge with probability `U/m`. Both are even shores because `4|n`.

Fix **any** globally minimum partition `D`. By Theorem 4.1 index its circuits as `D'_v`, according to their singleton vertex sets. For `S subseteq V`, let

\[
 F_S=\bigcup_{v\in S}D'_v,\qquad s=|S|.
\]

Every block is now:

* full if both endpoints are in `S`;
* the original proper, frozen `10` or `01` trace if exactly one is in `S`;
* zero if neither is in `S`.

There are exactly `s(s-1)` full blocks.

### Theorem 5.1 — uniform pointwise bound

For `S` nonempty,

\[
\boxed{
 c(F_S)=s,\qquad 1\le c_f(F_S)\le1+\beta s(s-1).
}                                                               \tag{5.2}
\]

Also `c_f(E)<=alpha`.

**Proof of the fractional certificate.** For each two-vertex shore `R` in the base `K_n`, make a vertex-set circuit `Gamma_R` on `T=S`:

* keep every frozen trace exactly as supplied by the chosen minimum;
* replace each full block by `B\delta(R)`;
* use zero elsewhere.

These are circuits by Lemma 3.1. The *same* shore `R` may be used on every full block; only marginal loads matter, so independence across blocks is unnecessary. Give each of the `m` shore choices coefficient `1/m`. Repeated circuits, if any, have their coefficients added.

Each frozen element receives load exactly one. On each full block the load is `1-a/m`. In that block add local balanced-even-cut circuits with **total coefficient `beta`**, uniformly over all `n/2`-vertex shores. Every element then has total load

\[
 \left(1-\frac am\right)+\beta\frac Um=1.                       \tag{5.3}
\]

Shore complements describe the same balanced cut, but accumulating their coefficients is legitimate. The total coefficient is `1+beta s(s-1)`, with no loads outside `F_S`.

The integer assertion is (1.2), since `D` is globally minimum. Every exact fractional partition of a nonempty set has total mass at least one, by its load equation at any one element.

For the full-word improvement, use vertex-set circuits on `V`, with a pair-cut complement on every block, and give their uniform distribution total coefficient `alpha`. Each edge load is `alpha(1-a/m)=1`. This proves `c_f(E)<=alpha`. ∎

No claim that the upper bounds in (5.2) are exact fractional optima is needed. Upper certificates suffice to contradict the proposed lower guarantee.

---

## 6. No finite denominator survives optimization

Set

\[
 N_q=N(q,8q^3).
\]

Then `beta<1/q^3`. Uniformly over all minima and all nonempty subunions,

\[
 c_f(F_S)\le1+\beta q(q-1)
 <1+\frac{q-1}{q^2}<1+\frac1q,                            \tag{6.1}
\]

which proves (0.1). For any proposed finite `K>0`, take an integer `q>max(2,2K)`. The right side of (6.1) is less than `q/K`. Every subunion, including the empty one, then has cost below the proposed expected-value lower bound. **Taking any expectation or optimizing the partition cannot change this pointwise obstruction.**

For independent half-retention, `s` has distribution `Bin(q,1/2)` and

\[
\boxed{
 1-2^{-q}\le\mathbb E c_f(F_S)
 \le1-2^{-q}+\frac{\beta q(q-1)}4.
}                                                               \tag{6.2}
\]

The lower bound uses only nonemptiness; the upper uses `E[s(s-1)]=q(q-1)/4`. These bounds hold for *every* minimum, so all their half-retention expectations tend to **one**, not to a positive fraction of `q`.

Even after optimizing an arbitrary exchangeable law, the unnormalized optimal expectation tends to one: retaining exactly one circuit gives value one, while (6.1) is a uniform upper bound. The same statement holds if arbitrary laws are allowed. Thus the optimized ratio tends to **zero**, strengthening the old one-eighth obstruction to failure of every finite denominator.

### A finite counterexample to `q/8` for every minimum and every law

Take

\[
 q=9,\qquad n=5832=8\cdot9^3,\qquad h=72.
\]

Then

\[
 \max_{\mathcal D\text{ minimum},\;\mathcal A\subseteq\mathcal D}
 c_f(\bigcup\mathcal A)
 \le 1+\beta h
 =\frac{64879}{59049}
 <\frac98,
\]

with strict gap `12409/472392`. This explicitly includes the best lexicographic minimum, the best fractional-objective minimum, and any optimized exchangeable retention law.

This finite binary matroid has 1,224,230,112 elements and cycle dimension 419,769. Those parameters and rational certificates are checked algebraically; its enormous cycle space is **not** claimed to have been enumerated.

---

## 7. The actual hereditary invariant and the criticality limitation

For completeness, the construction's genuine hereditary maximum can be determined, not just lower-bounded outside the minimum-partition cubes.

Let `F` be any cycle of `N(q,n)` and let `S` be its recovered vertex pattern. Let `P` be its full blocks, and let `R` be its nonzero `00` blocks. Every other nonzero block incident with `S` is a frozen proper trace, including possible internal `11` traces. Blocks of `R` lie entirely outside `S`.

If `S` is nonempty, repeat the certificate of Section 5 with vertex set **all of `S`**, fixing every frozen trace, replacing full traces by pair-cut complements, and adding the forced local circuit on each `R` block. Lemma 3.1 still applies because every nonempty clique on `S` is connected. It gives

\[
 c_f(F)\le |R|+1+\beta|P|.                                  \tag{7.1}
\]

If `S` is empty, the only contained circuits are exactly the `|R|` local cuts, and `c_f(F)=c(F)=|R|`.

For `empty != S != V`, at least two boundary blocks are neither in `R` nor in `P`. Therefore `|R|+|P|<=h-2`, so (7.1) is at most `h-1`. For `S=V` and `F` proper, `R` is empty and `|P|<=h-1`, so (7.1) is at most `h`. The full word has fractional value at most `alpha<2<=h`. This bounds **every** Eulerian restriction by `h`.

For equality, choose one nonzero even cut in every block and let `W` be their union. Its vertex pattern is zero, and its only contained circuits are these `h` disjoint local cuts. They give an exact primal of cost `h`. Give price one to one element of each cut and zero to its other elements: this is a dual of value `h`, valid on **all circuits of `N|W`**. Thus

\[
 \boxed{p(N(q,n))=h.}                                          \tag{7.2}
\]

Likewise `Q=h`: on a proper restriction with nonempty `S`, one vertex-set circuit on `S`, one matching local cut per full block, and the `R` circuits form an integral partition of size `1+|P|+|R|<=h`. The empty-pattern case costs at most `h`, the full word costs `q<=h`, and `c(W)=h`.

This also locates the exact scope of the counterexample:

* `W` lies outside **every** minimum-partition subunion cube. A subunion has recovered vertex pattern `S`, so the only such subunion with pattern zero is empty; `W` is nonempty with pattern zero.
* `W` is an `h`-critical restriction: it is a direct sum of `h` circuits, and each proper cycle in it uses fewer of them. Its half-retention fractional expectation is exactly `h/2`.
* The full matroid is not `q`-critical. More strongly, for any local circuit `C`,
  \[
    c(E\setminus C)=q.
  \]
  Indeed, no minimum full partition contains `C`, so the residual cannot have cost `q-1`. Merging its two endpoint vertices, and adding the local circuit in each of their two blocks, gives a `(q+1)`-partition containing `C`; deleting `C` gives the matching upper bound.

Thus the universal **global-minimum retention** claim has a complete negative answer in the binary class, but reducing first to a maximum-`Q` critical restriction remains a genuinely different route. The construction does not refute that route, `c<=Kp`, or graphic Erdős–Gallai.

---

## 8. Exact verification and its limits

Run from the repository root:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 ResearchOptimalRetentionCheck.py --check-workspace
```

The checker uses only the Python standard library and exact rational arithmetic. It writes no files.

1. **Independent base audit.** It reconstructs all 256 binary base words at `n=8`, identifies all 254 circuits by supported-code dimension, and checks that every full partition has two parts.
2. **Complete doubled-block audit, `q=2,n=8`.** From the actual 56-element, dimension-14 row space it reconstructs **all 16,384 words and all 12,287 circuits**. An anchored exact partition DP gives the full partition histogram
   \[
   4096\text{ partitions of size }2,\qquad3969\text{ of size }3.
   \]
   It independently enumerates **all 4,096 global minima**, verifies that each has singleton vertex sets and no local circuit, and checks every subunion's integer cost. It also verifies exact-load fractional primals for **every Eulerian restriction**, plus the exact `p=2` local witness and its dual.
3. **Three-vertex check, `q=3,n=8`.** It tests all 152 trace categories: zero/full/proper choices in labels `00,11`, and representative proper traces in labels `10,01`. Circuit status is checked by binary linear algebra, and representative fractional certificates are expanded and checked edge by edge. The category multiplicities sum to `2^39`; **this is not an enumeration of `2^39` individual words**. Lemma 2.1 explains the category reduction: a proper trace admits only itself or zero as a supported base subword, independent of its cut size. All five vertex-set partition types are explicitly realized; their costs have type histogram `{3:1, 4:3, 7:1}`. This is not mislabeled as an independent enumeration of all large-instance minimum partitions.
4. **Exact large-parameter identities.** For `q=2,...,64`, `n=8q^3`, it checks the edge-load identities, pointwise bounds, the exact binomial expectation identity, and the strict finite `q=9` bound above. The proof for arbitrary `q` is in Sections 2–7, not inferred from this finite range.
5. **Protected files.** The optional workspace check confirms the pre-work aggregate hash of all 241 pre-existing non-cache files, excluding only the two permitted new files. The unchanged specification SHA-256 is
   ```text
   429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
   ```

**Complete proof status:** the all-optimized-minima, all-laws counterexample is proved. The critical-only retention and universal hereditary constant questions remain open in this work.
