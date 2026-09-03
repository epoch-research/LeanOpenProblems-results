# Cube block amplification: an exact lift and a capacitated positive theorem

## Status and main result

**Neither `R(Q_d)=O(2^d)` nor the dimension-uniform spectral benchmark is proved here.** The full deterministic spectral theorem in `CubeSpectralBenchmark.md` still has its `d²` loss. This file does not silently replace that theorem by a random-host assertion.

There is, however, a positive block argument with all three requested ingredients—**the actual block distribution, original-vertex collisions, and capacity**—proved below. Its hypothesis is an explicitly specified random exposure, not just a spectral norm bound. The useful new mechanism is:

> Make coordinate lists disjoint *within* each block; remove the few blocks whose prospective **host-edge queries** overlap; sample actual cube embeddings in the remaining, fresh random partite graphs; use product-permutation symmetry and a stopped greedy capacity estimate; complete the removed blocks in a second reservoir.

This is not matching-only gluing. Every matching uses the fixed `Q_k` coordinate labels, so all commuting-square relations are retained. Nor do we discard every block whose **vertices** overlap another block's lists: that would discard almost everything. It is overlap of *edge queries* that is rare.

### Theorem A: linear-size completion of an arbitrarily planted half of the blocks

Set
\[
 C_0=2^{14},\qquad d_0=2^{16}.
\]
For every integer `d >= d_0`, put
\[
 h=2^d,\quad k=\left\lceil\log_2(d\log_2d)\right\rceil,
 \quad b=2^k,\quad t=d-k,\quad m=2^{t-1}=h/(2b).
\]
Let `E_t,O_t` be the parity classes of `Q_t`. Suppose an **arbitrary fixed** injection
\[
 f:E_t\times V(Q_k)\longrightarrow A
\]
has already embedded the `m` internal copies of `Q_k`: `f(x,a)f(x,a')` is an edge whenever `aa'` is an edge of `Q_k`. No randomness or quasirandomness of this planted family is assumed.

Take two sets `B_0,B_1`, disjoint from `A` and each other, of size `C_0 h`. Independently put in each edge from `f(E_t×Q_k)` to `B_i`, and each edge inside `B_i`, with probability `1/2`. All these edges must be unexposed when `f` is selected. Other host edges are irrelevant.

Then, with probability at least
\[
 \boxed{1-2^{-d/8},}
\]
there is an **injective embedding of `Q_t × Q_k = Q_d` extending the given `f`**, with all remaining vertices in `B_0∪B_1`.

In particular, an elementary independent packing argument also gives, for
\[
 N=(2C_0+1)2^d,
\]
\[
 \Pr\bigl(Q_d\subseteq G(N,1/2)\bigr)\ge 1-2\cdot2^{-d/8}
 \qquad(d\ge d_0).                                      \tag{A1}
\]
Random-graph cube containment itself is **not claimed as a new literature result**. The substantive checkpoint here is the stronger, fully quantified **arbitrary planted-block completion theorem**, together with the capacity-preserving mechanism proving it.

Other results in this file are:

* exact block-lift, moment, and finite-population collision identities;
* a genuine local block lower tail `exp(-Ω(L²/(k2^k)))`, not an inference from a large first moment;
* a cube-specific column-load estimate, proved by a truncated connected-component expansion;
* an explicit large-domain block-embedding lemma under the **original** spectral hypothesis;
* a precise, still-unproved spectral transfer requirement.

All counts are labelled. `log` in estimates means the natural logarithm; `log_2` is written explicitly. `(n)_r` denotes a falling factorial, zero if `r>n`. No Lean file is changed.

---

## 1. Exact block objects: labels, compatibility, and global injectivity

Let `G` be a finite simple graph with adjacency matrix `A_G`, including zero diagonal. Write
\[
 \Omega_k(G)=\{g:Q_k\hookrightarrow G:\ g\text{ is an injective graph homomorphism}\}.
\]
These are **labelled** embeddings, not unlabelled copies. For `g,g'∈Ω_k`, define
\[
 T(g,g')=\prod_{a\in Q_k}A_G(g(a),g'(a)),\qquad
 D(g,g')=\mathbf1\{\operatorname{im}g\cap\operatorname{im}g'=\varnothing\}.
\]
The locally injective block adjacency is `W=T D`. It is a symmetric zero-one matrix.

For every `t,k>=0`, the exact identity is
\[
 \boxed{
 \operatorname{inj}(Q_{t+k},G)
 =\sum_{(g_x)\in\Omega_k^{V(Q_t)}}
    \prod_{xy\in E(Q_t)}T(g_x,g_y)
    \prod_{\{x,x'\}\subseteq V(Q_t)}D(g_x,g_{x'}).
 }                                                        \tag{1}
\]
Equivalently, use `W` on the edges of `Q_t` and retain `D` on every nonedge pair of distinct block positions.

**Proof.** The map corresponding to a summand is `(x,a)↦g_x(a)`. The internal edges are supplied by membership in `Ω_k`; the other edges are precisely the coordinatewise factors in `T`. The last product is exactly injectivity between different blocks. This correspondence is a bijection. ∎

In particular, `hom(Q_t,W)` alone is not the desired count: it has not enforced disjointness of nonadjacent blocks. Formula (1) also proves associativity of blocking: a globally disjoint, coordinate-compatible `Q_ℓ` of `Q_k` embeddings is exactly a labelled `Q_{k+ℓ}` embedding.

No independently chosen matching permutation occurs. Around an outer square, a label `a` returns to the same label `a`; around a square using one internal and one outer coordinate, both routes use the same internal edge `aa'`. This is the commuting-square condition, not an additional conjecture.

### 1.1 Exact block-star moments and the Gram identity

Let `M=|Ω_k|>0`, choose independent uniform `F_1,…,F_t∈Ω_k`, and put
\[
 Z=\sum_{g\in\Omega_k}\prod_{j=1}^t W(F_j,g).
\]
For every integer `r>=1`,
\[
 \boxed{
 \mathbb E Z^r
 =\sum_{g_1,\ldots,g_r\in\Omega_k}
   \left(\frac1M\sum_{f\in\Omega_k}\prod_{i=1}^rW(f,g_i)\right)^t.
 }                                                        \tag{2}
\]
The `g_i` in a moment are allowed to repeat or overlap. The independently sampled `F_j` need not be globally disjoint either. Adding those restrictions changes the sampling law; (2) must not be applied to that changed law without a new calculation.

Set
\[
 q_g=M^{-1}\sum_fW(f,g),\quad
 c_{gg'}=M^{-1}\sum_fW(f,g)W(f,g'),\quad R_{gg'}=c_{gg'}-q_gq_{g'}.
\]
Then `R=M^{-1}(W-1q^T)^T(W-1q^T)` is positive semidefinite. For `t>=2`, with `a_g=q_g^{t-1}`,
\[
 \boxed{\begin{aligned}
 \operatorname{Var}Z={}&t\,a^TRa\\
 &+\sum_{g,g'}R_{gg'}^2
   \sum_{i=0}^{t-2}(i+1)(q_gq_{g'})^i c_{gg'}^{t-2-i}.
 \end{aligned}}                                           \tag{3}
\]
The whole Gram term and every term of the remainder are nonnegative. This follows from (2) and
\[
 x^t-u^t-tu^{t-1}(x-u)
 =(x-u)^2\sum_{i=0}^{t-2}(i+1)u^i x^{t-2-i}.
\]
Thus the reflection/Gram positivity survives blocking **exactly**. This is an identity, not a dimension-free lower-tail estimate for the block lift.

### 1.2 First moment in the actual unexposed-edge experiment

Fix `t` pairwise vertex-disjoint labelled boundary blocks outside an `n`-vertex reservoir `B`. For each coordinate `a`, its new image must be adjacent to the `t` boundary images with label `a`. Let all relevant boundary–reservoir and reservoir-internal edges be independent fair bits, and let `Z_B` count injective block completions. With
\[
 e_k=k2^{k-1}=kb/2,\qquad q=2^{-t},
\]
\[
 \boxed{\mathbb E Z_B=(n)_b\,2^{-tb-e_k}=(n)_bq^b2^{-e_k}.} \tag{4}
\]
For `n=C2^d`, `t=d-k`, this is exactly
\[
 (Cb)^b2^{-kb/2}\prod_{i=0}^{b-1}(1-i/n)
 =C^b b^{b/2}\prod_{i=0}^{b-1}(1-i/n).                     \tag{5}
\]
This verifies the proposed amplification scale, including the finite-population correction. The conditioning that made the boundary blocks valid does not alter (4), provided it used only edges outside the reservoir experiment.

### 1.3 Exact second moment with cross-coordinate collisions retained

A partial bijection `π:S→T` between two subsets of `V(Q_k)` specifies exactly the coincidences between two injective completions: `g(a)=g'(π(a))`. Define
\[
 s=|S|,\quad f(\pi)=|\{a\in S:\pi(a)=a\}|,
\]
\[
 e(\pi)=|\{aa'\in E(Q_k[S]):\pi(a)\pi(a')\in E(Q_k)\}|.
\]
Then
\[
 \boxed{
 \mathbb E Z_B^2
 =\sum_{\pi:S\simeq T}(n)_{2b-s}
       2^{-2(tb+e_k)+t f(\pi)+e(\pi)}.
 }                                                        \tag{6}
\]
Indeed, there are `(n)_{2b-s}` assignments with precisely those coincidences. External requirements are shared only at fixed points of `π`, giving `t f(π)` shared edges. The common internal edges are exactly those counted by `e(π)`. A collision between different labels does **not** save `t` boundary edges.

Formula (6) is useful bookkeeping for a spectral continuation: replacing every partial bijection by an identity overlap, or dropping all cross-coordinate collisions before justifying exclusive pools, is incorrect.

---

## 2. A real lower-tail amplification theorem for one block

### Lemma 2.1: a random partite cube has exponentially small failure probability

Let `k>=1`, `b=2^k`, and let `(U_a:a∈Q_k)` be pairwise disjoint sets, each of integer size `ℓ>=64b`. Between `U_a,U_{a'}` for every cube edge `aa'`, take independent `Bernoulli(1/2)` host edges. Let `X` count embeddings taking each label `a` into `U_a`. Then
\[
 \mu=\mathbb EX=\ell^b2^{-kb/2},
\]
\[
 \boxed{\Pr(X<\mu/2)\le
          \exp\left(-\frac{\ell^2}{512kb}\right).}         \tag{7}
\]

**Proof.** For two independent uniform maps into the parts, their equality set `S` has independent membership probability `1/ℓ`. Their required edge sets overlap in exactly `e(Q_k[S])` edges. If `Δ` is the ordered sum of joint probabilities over distinct embeddings sharing at least one required edge, then
\[
 \frac{\mu+\Delta}{\mu^2}
 =\mathbb E\left[2^{e(Q_k[S])}\mathbf1_{e(Q_k[S])>0}\right]
 \le\sum_{S:e(Q_k[S])>0}\ell^{-|S|}2^{e(Q_k[S])}.           \tag{8}
\]
The term `μ` accounts for identical embeddings.

Two elementary source bounds suffice:

1. `e(Q_k[S]) <= |S| log_2|S|/2` (the cube edge-isoperimetric inequality).
2. The number of connected `s`-sets in a graph on `b` vertices of maximum degree `k` is at most `b(4k)^{s-1}`. To see this, root a spanning tree and encode it by a rooted plane tree, at most `4^{s-1}` choices, and a neighbor choice at each tree edge.

The first bound follows by splitting a set across one cube coordinate and using
`u log_2u+v log_2v+2 min(u,v) <= (u+v) log_2(u+v)`, then inducting.

Let `A_*` be the sum of `ℓ^{-|S|}2^{e(S)}` over connected sets of size at least two. It is at most the sum, for `2<=s<=b`, of
\[
 A_s=\frac{b(4k)^{s-1}s^{s/2}}{\ell^s}.
\]
For consecutive terms,
\[
 \frac{A_{s+1}}{A_s}
 \le\frac{4\sqrt e\,k\sqrt b}{\ell}<\frac14,
\]
using `ℓ>=64b` and `k²<=2b`. Consequently
\[
 A_*\le\frac43 A_2<16kb/\ell^2.
\]
Decompose `S` into its connected components. Forgetting disjointness between components only increases the positive sum in (8). Singleton components have total weight `b/ℓ`; at least one nonsingleton is required. Hence (8) is at most
\[
 e^{b/\ell}(e^{A_*}-1)\le2A_*\le32kb/\ell^2.
\]
Here `b/ℓ<=1/64` and `A_*<=1/256`. The usual Janson lower-tail inequality
\[
 \Pr(X<\mu/2)\le\exp[-\mu^2/(8(\mu+\Delta))]
\]
now gives a bound even stronger than (7). ∎

This proof counts overlaps of *required edges*, not every pair of embeddings sharing a vertex. That distinction produces the `kb/ℓ²` scale.

### Lemma 2.2: exact law of the successful block sampler

In Lemma 2.1, inspect the partite graph. Declare failure if `X<μ/2`; otherwise choose uniformly among its `X` actual cube embeddings. **After averaging over the fresh random graph**, conditional on success the output is exactly uniform on
\[
 \prod_{a\in Q_k}U_a.                                    \tag{9}
\]
In particular its coordinate images are independent uniform vertices of their respective parts.

**Proof.** The distribution of the graph, the success event, and the uniform-among-embeddings rule are invariant under the product of the permutation groups of the parts. That group acts transitively on the displayed product. Every output tuple must therefore have the same conditional probability. ∎

This statement is about the actual embedding-selection experiment, not about an independently drawn tuple being an embedding. It is an **averaged** statement. For one fixed realized graph the uniform embedding law generally is not a product law.

### Corollary 2.3: amplification for a fixed boundary star

In the experiment of (4), assume `(b-1)q<=1/2` and let
\[
 \ell=\lfloor nq/4\rfloor\ge64b.
\]
Define the raw lists `L_a` by the boundary adjacencies, and the exclusive lists
\[
 P_a=L_a\setminus\bigcup_{a'\ne a}L_{a'}.
\]
For a fixed reservoir vertex, the `b` raw-list indicators are independent, so
\[
 |P_a|\sim\operatorname{Bin}\bigl(n,q(1-q)^{b-1}\bigr),
 \qquad\mathbb E|P_a|\ge nq/2.
\]
Chernoff and (7), selecting `ℓ` elements of each `P_a`, give
\[
 \boxed{
 \Pr\left(Z_B<\tfrac12\ell^b2^{-kb/2}\right)
 \le b e^{-nq/16}+e^{-\ell^2/(512kb)}.
 }                                                        \tag{10}
\]
All completions counted on the good event are injective.

This also applies after deleting any fixed forbidden vertex set **before the relevant random edges are exposed**, replacing `n` by the remaining reservoir size. It is not an assertion about adversarial deletions chosen after inspecting those edges.

For `n=C_0 2^d`, under the preceding hypotheses, a block with `b/k >= log d` already makes (10) at most `2d^{-512}`. One can choose such a block with
\[
 k=\log_2\log d+\log_2\log\log d+O(1).
\]
Thus slowly growing blocks really can beat a `d²` local-dependency budget **in this exposure model**. The global completion proof below instead takes `b/k>=d/2`, allowing a direct union bound over exponentially many block positions.

---

## 3. Cube-specific column control without paying the maximum dependency degree

A reservoir vertex can occur in many lists. We need to bound this number, not merely count how large individual lists are.

### Lemma 3.1: a truncated star-count generating function

Let `t>=2^15`, independently mark each vertex of `E_t` with probability `1/2`, and let
\[
 T=|\{y\in O_t:N_{Q_t}(y)\text{ is entirely marked}\}|.
\]
Put
\[
 r=\left\lceil\frac{3t}{\log_2t}\right\rceil\le t/4.
\]
Then
\[
 \boxed{\Pr(T\ge r)\le2^{-2t},\qquad
        \mathbb E e^{\min(T,r)}\le e^{3/2}.}               \tag{11}
\]

**Proof.** Join two odd vertices when their cube neighborhoods intersect. This is the distance-two graph, of maximum degree `binom(t,2)`. For a set `S` of `s` odd vertices,
\[
 |N(S)|\ge ts-s(s-1),                                     \tag{12}
\]
since two different neighborhoods intersect in at most two vertices. Distinct components in the distance-two graph have disjoint neighborhoods, so the probability `2^{-|N(S)|}` factors over components.

The sum of this probability over connected `s`-sets is, for `2<=s<=r`, at most
\[
 \frac12(2t^2)^{s-1}2^{-(s-1)(t-s)}
 \le\frac12\vartheta^{s-1},\qquad
 \vartheta=2t^2 2^{-3t/4}.
\]
For singleton sets the sum is exactly `1/2`. Thus the truncated factorial-moment polynomial satisfies, for `0<=z<=r`,
\[
 \begin{aligned}
 F_r(z)&:=\sum_{s=0}^r z^s\mathbb E\binom Ts\\
 &\le\exp\left(\frac z2+
            \frac{\vartheta z^2}{2(1-\vartheta z)}\right)
 \le e^{z/2+1/2}.                                        \tag{13}
 \end{aligned}
\]
The first inequality is the same positive connected-component relaxation as above. The last follows from `ϑ r²<=1/2` and `ϑ r<1/2`, valid for `t>=2^15`.

Taking `z=r` gives
\[
 \Pr(T\ge r)\le\mathbb E\binom Tr
 \le r^{-r}e^{r/2+1/2}\le2^{-2t}.
\]
For the numerical last step, put `u=log_2t>=15`. The inequality
`log(u/3)+1/2 <= u log(2)/4` holds at `u=15` and is preserved by differentiation. Substituting `r>=3t/u` gives exponent at most `-(9/4)t log 2+1/2 <= -2t log 2`.

Finally, put `z=e-1` in (13) and use
\[
 e^{\min(T,r)}=\sum_{s=0}^r(e-1)^s\binom{\min(T,r)}s,
 \qquad \binom{\min(T,r)}s\le\binom Ts.
\]
The result is at most `exp(e/2)<exp(3/2)`. ∎

### Corollary 3.2: actual list-column loads

In Theorem A, reveal only the edges from the planted vertices into `B_0`. For `y∈O_t,a∈Q_k`, write
\[
 L_{y,a}=\{v\in B_0:A_G(v,f(x,a))=1\text{ for every }x\sim y\}.
\]
For a fixed `v`, its raw-list load is `Σ_a T_a`, where the `T_a` are independent copies of `T` in Lemma 3.1. Therefore
\[
 \boxed{
 \Pr\left(\max_{v\in B_0}|\{(y,a):v\in L_{y,a}\}|>4b\right)
 \le C_0h\bigl(b2^{-2t}+e^{-2b}\bigr).
 }                                                        \tag{14}
\]
Indeed, truncate each `T_a` at `r`, apply (11) and exponential Markov to their independent sum, then add the probability that a truncation occurred. This is not a Chernoff bound applied to falsely independent cube neighborhoods.

---

## 4. Capacity-preserving selection: a stopped greedy lemma

### Lemma 4.1

Let a finite family of rows be partitioned into blocks. Each row `s` has a list `S_s` of the same even size `L`. Lists within one block are pairwise disjoint, and each resource belongs to at most `D` lists.

Process blocks in any fixed order. Before a block is processed, remove resources previously selected. If every list in that block still has at least `L/2` resources, choose any `L/2`-subset of each available list and then choose independent uniform representatives from these subsets. Otherwise fail.

If there are `M_rows` rows and `L>4eD`,
\[
 \boxed{
 \Pr(\text{failure})\le
 M_{\rm rows}\left(\frac{4eD}{L}\right)^{L/2}.
 }                                                        \tag{15}
\]
The choices of subsets may depend on all earlier choices.

**Proof.** Fix a row `s`. Until stopping, a selection for another row `u` hits its original list with conditional probability at most
\[
 p_{u,s}=2|S_u\cap S_s|/L.
\]
The sum of these deterministic bounds is at most
\[
 \frac2L\sum_u|S_u\cap S_s|\le2D.                          \tag{16}
\]
Expose the coordinate choices one at a time, and set subsequent indicators to zero after stopping or after row `s` is processed. Conditional exponential moments are bounded by those of Bernoulli variables with total mean bound `2D`: for `θ>=0`, the moment of their sum is at most `exp(2D(e^θ-1))`. This follows by iterated conditional expectation, so independent choices at different times are not being assumed.

Loss of availability requires at least `L/2` hits. Exponential Markov with `e^θ=L/(4D)` bounds this by `(4eD/L)^{L/2}`. A union bound over rows proves (15). The case `D=0` is trivial. ∎

This is a capacity argument at the **original vertex** level. It does not apply a generic endpoint-conflict degree to the space of blocks. In particular it does not incur a factor `b` in the required ratio `L/D`.

When a block is selected by Lemma 2.2 in a fresh random partite graph, its successful output has exactly the law required here. The failure probability of the block-count test can be added separately. This is the crucial use of a proved distributional statement rather than just the large number of block embeddings.

---

## 5. Proof of Theorem A

The following elementary parameter inequalities hold for `d>=2^16`:
\[
 d\log_2d\le b<2d\log_2d\le d^2,\quad
 k\le2\log_2d,\quad t\ge d/2\ge2^{15},\quad
 \frac bk\ge\frac d2,\quad b^2/h<1/2.                    \tag{17}
\]
Write `q=2^{-t}=b/h`, and set
\[
 L=C_0b/4=4096b,\qquad \ell=L/2=2048b,\qquad D=4b.         \tag{18}
\]

### 5.1 Expose the lists, but no internal reservoir edges

Reveal all relevant planted-vertex–`B_0` edges. For each block `y`, take its exclusive lists
\[
 P_{y,a}=L_{y,a}\setminus\bigcup_{a'\ne a}L_{y,a'}.
\]
Within a block these are disjoint. For every row their mean size is at least `C_0b/2`. Therefore, except with probability
\[
 (h/2)e^{-C_0b/16},                                       \tag{19}
\]
all have size at least `L`. For every outcome, define `S_{y,a}` to be the first `min(L,|P_{y,a}|)` elements in a fixed reservoir ordering. On the good event these are `L`-subsets. This convention makes the query-overlap variable below defined **unconditionally**, including on bad-size outcomes. By (14), except with additional probability
\[
 C_0h\bigl(b2^{-2t}+e^{-2b}\bigr),                         \tag{20}
\]
each reservoir vertex belongs to at most `D=4b` of these lists.

These statements concern the **actual** simultaneous list distribution. Lists at distance two in the outer cube were not treated as independent.

### 5.2 Remove overlapping edge-query blocks, not overlapping vertex lists

For each block `y`, define its possible internal query set
\[
 \mathcal E_y=
 \{\{v,w\}:v\in S_{y,a},\ w\in S_{y,a'},\ aa'\in E(Q_k)\}.
\]
Call `y` exceptional if `E_y` intersects `E_z` for some `z≠y`. All other query sets are pairwise disjoint. This designation uses only the already exposed cross edges, not the random edges inside `B_0`.

Put `J=Σ_{y<z}|E_y∩E_z|`. We claim
\[
 \boxed{\mathbb EJ\le C_0^2 k^2b^4.}                      \tag{21}
\]
For different outer vertices `y,z`, and any labels `a,c`,
\[
 \Pr(v\in L_{y,a}\cap L_{z,c})\le4q^2.                   \tag{22}
\]
If `a≠c`, the underlying planted vertices are disjoint. If `a=c`, the two outer neighborhoods have intersection at most two, so at least `2t-2` independent edges are required. Requirements at different reservoir vertices are independent.

For each pair of internal cube edges there are at most four orientations assigning their endpoints to an unordered host pair `{v,w}`. With `e_k=kb/2` and `n=C_0h`, a union bound gives
\[
 \mathbb EJ
 \le\binom m2\binom n2\,4e_k^2\,16q^4
 \le16m^2n^2e_k^2q^4=C_0^2k^2b^4.
\]
Passing from raw lists to exclusive or truncated lists only decreases this count. At most `2J` blocks are exceptional, so
\[
 \Pr(\#\text{exceptional blocks}>h^{1/4})
 \le2C_0^2k^2b^4h^{-1/4}.                                \tag{23}
\]

Notice the scale: many blocks share candidate **vertices**, but only a small number share potential **queried edges**. This distinction makes deferred decisions possible without throwing away the capacity of the main reservoir.

### 5.3 Process the nonexceptional blocks

Condition on the cross-edge data satisfying the previous good events. Process nonexceptional blocks in any fixed order. Maintain the set of used original vertices.

For a current block with at least `ℓ=L/2` unused choices per row, select arbitrary `ℓ`-subsets `U_a` of its unused lists. All edges needed inside these parts belong to `E_y`. They are independent fair bits **even conditional on the entire previous history**, since no earlier nonexceptional block queried an edge of `E_y`.

Apply Lemma 2.1. On passing its count test, choose uniformly among the actual internal cube embeddings. Lemma 2.2 says that, conditional on the current past and on passing this test, the coordinate outputs are independent uniform vertices of their chosen parts.

For clarity about conditioning: for fixed `k,ℓ` the success probability of this test is the same for every tuple of parts. Thus the joint law can be represented by a success coin with that fixed probability and, on success, a product-uniform output. Deferred decisions give this representation at every step. It is legitimate to couple the outputs to the ideal process in Lemma 4.1 and add the probabilities of failed count tests.

Here
\[
 4eD/L=e/256<1/4.
\]
Consequently capacity failure has probability at most
\[
 (h/2)2^{-L}.                                             \tag{24}
\]
The probability of any internal block-count failure is at most
\[
 h\exp\left(-\frac{\ell^2}{512kb}\right)
 \le h e^{-4096d},                                        \tag{25}
\]
by (17)–(18). All selected block images are globally disjoint in `B_0`.

### 5.4 Complete the exceptional blocks in the independent second reservoir

The exceptional set was determined without using any edges incident to or inside `B_1`. Suppose its size is at most `h^{1/4}`. Reveal its raw coordinate lists in `B_1`.

There are at most `b h^{1/4}` such rows. For any two distinct rows, the probability that a prescribed reservoir vertex belongs to both is at most `4q²`, by exactly the calculation in (22), also covering two labels within one block. Therefore
\[
 \Pr(\text{some two exceptional-row lists intersect})
 \le 2C_0b^4h^{-1/2}.                                    \tag{26}
\]
Each row list has mean `C_0b`. Except with probability at most
\[
 (h/2)e^{-C_0b/8},                                        \tag{27}
\]
all have at least `L` elements. On the good event these lists are **globally disjoint**, so select `ℓ` elements of each and apply Lemma 2.1 to each exceptional block. Their additional failure probabilities can be included in the bound (25), since the total number of blocks is at most `h`.

Their images are distinct from each other, from the main-reservoir images, and from the planted vertices. All required outer edges are supplied by the lists. All required internal edges are supplied by the sampled block embeddings. Formula (1) now gives an ordinary injective `Q_d`.

### 5.5 Explicit error bound

The sum of (19), (20), (23), (24), (25), (26), and (27) is at most
\[
 2^{32}d^{10}2^{-d/4}\le2^{-d/8}\qquad(d\ge2^{16}).         \tag{28}
\]
For example, the two polynomial terms in (20), (23) are respectively
`C_0b³/h` and `2C_0²k²b⁴h^{-1/4}`. Use `b<=d²,k<=d` for these and (26). Every remaining exponential term is at most `2^{-2d}` by (17)–(18). Finally,
`32+10 log_2d <= d/8` holds at `d=2^16` and remains true by differentiation. The generous coefficient in (28) covers their sum. This proves Theorem A. ∎

### 5.6 Proof of the random-host corollary (A1)

Partition a `G((2C_0+1)h,1/2)` host into a set `A` of size `h` and the two reservoirs. First pack `m` disjoint `Q_k` blocks in `A`, inspecting only edges with at least one endpoint in the currently selected block.

At the start of each block, the graph on the remaining `n>=h/2` vertices is still a fresh random graph. For every set `S` of at most `k` vertices its common neighborhood outside `S` is binomial with mean at least `n/(2b)`. Since `n>=4b²`, Chernoff and a union bound show that, with failure probability at most
\[
 (k+1)h^k e^{-h/(32b)},
\]
every such set has at least `b` common neighbors. On this event any ordinary greedy embedding of a `b`-vertex graph of maximum degree `k` succeeds.

The greedy search can query only edges incident to already chosen vertices of the current block. Thus, when the block is removed, no edge between remaining vertices has been inspected; deferred decisions apply at the next block. A union bound over at most `h` blocks gives failure probability at most
\[
 h(k+1)h^k e^{-h/(32b)}\le2^{-d/8}
 \qquad(d\ge2^{16}).
\]
The successful packing is independent of all reservoir edges. Apply Theorem A and add the two errors. ∎

---

## 6. A positive block lemma under the actual spectral hypothesis

The preceding argument's first-half block selection is not intrinsically a random-host issue. Here is an explicit deterministic preparation result.

### Theorem B: large-domain blocks, counts, and a genuine spread sampler

For every `K>=0`, integer `k>=1`, and real `0<σ<=1`, put
\[
 b=2^k,\qquad \gamma=\tfrac12(1-1/(2k)).
\]
Suppose `G` has `N` vertices, actual density `p>=1/2`,
\[
 \|A_G-p(J-I)\|_{\mathrm{op}}\le K\sqrt N,
\]
and
\[
 \boxed{N\ge
       4096(K^2+1)(k+1)^3b^2/\sigma^2.}                   \tag{29}
\]
For any sets `(V_a:a∈Q_k)` with `|V_a|>=σN`, the number of injective labelled block embeddings with `g(a)∈V_a` is at least
\[
 \boxed{(\sigma N/2)^b\gamma^{kb/2}
             \ \ge\ (\sigma N/4)^b2^{-kb/2}.}             \tag{30}
\]
There is also an explicitly defined sampler supported on these **actual** embeddings such that for every `J⊆Q_k` and every prescribed map `φ:J→V(G)`,
\[
 \boxed{\Pr(g|_J=\phi)\le
                 \left(\frac{4b}{\sigma N}\right)^{|J|}.} \tag{30a}
\]
The domains need not be disjoint. Thus (30a) includes genuine internal injectivity rather than sampling a tuple and ignoring its collisions.

**Proof.** Write `B=A_G-p(J-I)`. If `|T|>=8k`, at most
\[
 \frac{64K^2k^2N}{|T|}                                   \tag{31}
\]
vertices have fewer than `γ|T|` neighbors in `T`. At such a vertex,
\[
 (B1_T)_v\le -(p-\gamma)|T|+1
        \le-|T|/(4k)+1\le-|T|/(8k),
\]
whereas `||B1_T||² <= K²N|T|`.

Embed in any fixed order. Maintain each future domain intersected with the required neighborhoods of earlier images, excluding all used images. Only choose vertices retaining at least a `γ` fraction of every future neighboring domain. If a label has `r` earlier neighbors, its maintained domain has size at least
\[
 \sigma N\gamma^r-b.
\]
The subtractive errors from single-vertex deletions total at most `b`. Bernoulli's inequality gives
\[
 \gamma^k=2^{-k}(1-1/(2k))^k\ge1/(2b).
\]
Under (29), every maintained domain consequently has size at least
\[
 a_0=\sigma N/(4b)\ge8k.
\]
The union of the bad-vertex sets for at most `k` future neighboring domains has size at most `256K²k³b/σ`, by (31). The same hypothesis ensures
\[
 b+256K^2k^3b/\sigma\le\sigma N/(4b)
                         \le\tfrac12\sigma N\gamma^r.
\]
Thus the step for this label has at least `σNγ^r/2` permissible choices. The sum of the earlier-neighbor counts over all labels is `kb/2`, proving the first inequality in (30). The second follows from `(1-1/(2k))^k>=1/2`.

For the sampler, choose uniformly among the permissible vertices at each step. At every history its largest one-point probability is at most `4b/(σN)`. Exposing the prescribed labels in their order, and applying conditional expectation between them, proves (30a). All choices exclude earlier images. ∎

For example, if an initial reservoir remains of size at least `σN` after all requested deletions, Theorem B can be applied repeatedly to pack vertex-disjoint `Q_k` blocks there. For the block size of Theorem A, its requirement is only polynomial in `d` for fixed `K,σ`, whereas `N=C2^d` is exponential. Thus **constructing and labelling the initial disjoint small blocks is available under the original spectral hypothesis** in all sufficiently large dimensions, with the explicit condition (29).

The limitation is equally explicit: the theorem needs domains of size proportional to `N`. After `t=d-k` external constraints, the desired coordinate lists have size about `Cb`, not `σN`. Applying (29) with `σ≈Cb/N` does not work. No such substitution is made here.

---

## 7. The precise continuation target, and what has not been transferred

The random proof demonstrates that blocking can overcome both the small-list obstruction and the endpoint-capacity obstruction **without changing the source graph**. It also identifies where independence, rather than scalar spectral control, was used:

1. For a fixed boundary star, the raw coordinate-list indicators are independent Bernoulli variables, giving exclusive pools and (10).
2. The marked outer-cube vertices in Lemma 3.1 are independent; different block coordinates give independent copies of that process.
3. Once overlapping edge-query blocks are removed, each new internal partite graph is fresh. Lemma 2.2 then gives the exact output law needed for (16).
4. The second reservoir remains independent of the choice of exceptional blocks.

A fixed graph with `||A-p(J-I)||<=K sqrt N` does not acquire these properties merely because one chooses to inspect its edges later. Randomly choosing block embeddings in that fixed graph also does not, without proof, give the product law (9).

The existing scalar Gram estimate, applied at codimension `t`, controls a single coordinate's bad-list probability only at scale `O(K²/(Cb))`. A union bound over `b` coordinates supplies only `O(K²/C)`, not (10). This observation is a limitation of the **available estimate**, not a counterexample to the desired spectral embedding theorem.

### 7.1 A capacity target stated in terms of actual embedding distributions

There is a useful deterministic sufficient version of the distributional step. Suppose the lists in Lemma 4.1 are in a fixed host, and put `θ=log(L/(4D))>0`. At every history of previous, mutually disjoint valid choices for which the current block's lists each still have at least `L/2` resources, suppose a distribution on **actual** injective labelled block embeddings in the remaining lists exists. Require that distribution to satisfy, for every original row list `S_r`,
\[
 \boxed{
 \mathbb E\left[e^{\theta|\operatorname{im}g\cap S_r|}
                  \mid\text{previous history}\right]
 \le\exp\left[\frac{2(e^\theta-1)}L
                   \sum_{a\text{ in current block}}
                      |S_{y,a}\cap S_r|\right].
 }                                                        \tag{32}
\]
Then the proof of Lemma 4.1, now exposing one whole block at a time, gives the same failure bound (15). Consequently, if its right-hand side is below one, there is a capacity-respecting simultaneous choice of actual block embeddings. Fixed, correctly labelled outer adjacencies then give a cube via (1).

This is a proved implication, **not an assertion that (32) holds for every spectral host**. It asks only for hit-set exponential moments against the actual list family, not for an impossible claim that a fixed graph's whole embedding law is literally product-uniform. In the random-exposure theorem the corresponding conditional, averaged bound follows exactly from Lemma 2.2.

A spectral continuation could therefore aim for:

* a suitable distribution of disjoint initial blocks and reservoirs;
* enough large exclusive lists, or a replacement retaining equally good capacity;
* bounded aggregate list loads or a weaker direct expansion certificate;
* a signed/reflection estimate of the hit-set moments (32), after internal block edges and collisions have been summed **together**;
* a controlled repair for the exceptional blocks.

The exact Gram identity (3) and overlap identity (6) retain the required information, but **no bound achieving these items from the spectral hypothesis has been established here**. In particular, positivity of (3) does not by itself imply (32).

There is also a separate final gap to the Ramsey problem: even a proof of the uniform spectral benchmark would not automatically cover every two-coloring. A structural or two-color reduction supplying an appropriate host is still required. This file claims neither that reduction nor a formal settlement of `Spec.lean`.

---

## 8. Source audit and verification

The following corpus sources were inspected directly:

* `/corpus/src/1507.00547/1507.00547.tex`, Section 3: Conlon–Fox–Sudakov's `R(H)<=2^(Δ+6)|H|` and its sparse-hypergraph local-lemma proof. Its all-tuples/capacity budget is not imported as a linear cube theorem.
* `/corpus/src/1505.04773/1505.04773.tex`, the one-side bounded theorem and Section 2: Lee's defect method, and the explicit consequence `R(Q_d)<=4^d+d²2^d` for sufficiently large `d`. This is a corpus result, not a claim about the latest literature worldwide.
* `/corpus/src/0707.4159/0707.4159.tex`: Fox–Sudakov's density theorem, distinguishing its `ρ^{-Δ}|H|` scale from the desired linear scale.
* `/corpus/src/1306.0461/1306.0461.tex`, especially the introduction and matching-compression discussion: the fixed-clique-versus-cube theorem has extra forbidden-clique and internal-degree hypotheses; these do not follow from absence of a monochromatic large cube.
* `/corpus/src/2203.05485/2203.05485.tex`, the proof outline for grid products: its two-sided, codegree-controlled extension families are relevant to why a distributional/capacity statement, not just an auxiliary edge count, is needed. Its tree–path product theorem is not a theorem about `Q_d` at the scale considered here.

The comparison files `CubeSpectralBenchmark.md`, `CubeSpectralBenchmarkGaps.md`, `CubeSpectralStarControl.md`, and `CubeEndpointConflictInvestigation.md` were also read. The new positive proof avoids their generic endpoint-conflict loss by working with original-vertex hit probabilities and rare **edge-query** overlaps.

The companion script `check_cube_block_amplification.py` has been run successfully; its recorded output is `CubeBlockAmplificationVerification.txt`. It checks:

* 138 exact globally injective block-lift identities and 24 block-star/Gram cases;
* the partial-bijection formula on 29,592 pairs of embeddings, plus all 512 hosts in a small random experiment;
* the successful sampler's exact product law on all 66,064 hosts in three small partite experiments;
* 65,808 source subsets for the cube overlap bound, and 65,812 markings and supports for the outer-star component calculation;
* exact query-overlap and capacity budgets, 90 spectral matrix/set cases, and 640 rational checks of the large-domain count/spread constants;
* the explicit large-dimension inequalities at 489 dimensions from `2^16` through `2^128+1`, using logarithms rather than allocating the hosts.

Three additional finite implementation diagnostics construct actual `Q_6` and `Q_7` embeddings with `Q_2` or `Q_3` blocks. They exercise both the main reservoir and the exceptional-block reserve, and verify all 832 required edges and 1,152 commuting squares across the three certificates. These small diagnostics use parameters below the theorem's asymptotic thresholds and optionally prune multiply eligible reserve vertices. They are implementation checks, **not estimates of the theorem's failure probability**; the recorded output includes how many attempts they took.

To reproduce from `/workspace/leanproject`:

```sh
python3 -u Submission/check_cube_block_amplification.py
```

The finite checks supplement the all-dimensional proofs. They do not test an astronomically large random host or prove the missing spectral transfer.

`Submission/Spec.lean` is unchanged. Its SHA-256 is
`9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`.
