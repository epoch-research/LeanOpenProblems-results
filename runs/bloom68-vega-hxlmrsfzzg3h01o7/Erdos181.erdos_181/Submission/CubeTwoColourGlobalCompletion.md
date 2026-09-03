# Two-colour global completion attempt: Hall-circuit trees and conditional resampling entropy

## Status

**The missing global theorem is not proved. This is not a proof of `R(Q_d)=O(2^d)`, and no absolute Ramsey constant is claimed.** `Spec.lean` is unchanged.

This was a positive attempt to pass from **simultaneous Hall failure in both colours, for every full-parity injection and every host partition**, to an actual cube. It does not use a homomorphism relaxation, a presumed random-edge law, or a distribution averaged over incompatible embedding histories.

The new proved parts of this attempt are:

1. **A tree inside every minimal Hall certificate.** Its `s-1` distinct candidate vertices can be assigned to the edges of a tree on its `s` source rows. Each assigned candidate is genuinely adjacent, in the certificate colour, to both corresponding cube neighbourhoods, whose union has size at least `2d-2`.
2. **A star-block partition in every dimension.** Blocks have size `ell`, where `d/2 < ell <= d` is a power of two. Every source row other than the block's distinguished root meets that block in at most two variables. The partition can be chosen after the joint certificate, with an exact bound on the number of exceptional roots.
3. **Exact simultaneous, injective resampling constraints.** After the other blocks are pinned, the non-root constraints of both certificates are unary or binary. Cube intersections impose a further compatibility rule: at any remaining host candidate, opposite-colour active constraints cannot share a block variable.
4. **Positive certificate-to-cube lemmas.** Large forced unary rectangles give actual monochromatic cubes. A sufficiently large common pair-residual set gives an actual complementary-colour cube unless the *actual conditional injection fibre* loses a definite amount of entropy. The latter uses a clique-count argument, not independent candidate marginals.
5. **An exact global entropy ledger for the entire joint-certificate cover.** It keeps all injections and both colours. It also identifies the conditional-information term that the attempted completion has not controlled.

The attempted completion stops at a concrete point: the global certificate-entropy bound does **not** upper-bound the sum of the conditional resampling deficits, and the global hypotheses have not been shown to supply enough large forced/common residual sets. The missing information cannot be discarded by maximizing over boundaries. Section 7 gives the exact inequality reached, including its remaining terms. It is **not** offered as a new conjecture or an assumed bridge.

The required inputs were read directly: `CubeDirectRamseyProgress.md`, `CubeAdaptiveBridgeAttempt.md`, and `CubeGlobalHallReduction.md`. In particular, the robust-core extraction and the unrestricted rematching/global-exchange reductions are not being reproved or weakened here.

---

## 1. Global setting and the joint certificate ensemble

Put

\[
 h=2^d,\qquad m=2^{d-1},\qquad E\dot\cup O=V(Q_d).
\]

The substantive resampling discussion uses `d>=3`. Nothing about a dimension-uniform conclusion is inferred by omitting the smaller dimensions.

Suppose, for the attempted contradiction, that a red-blue complete graph on `U`, `|U|=N`, has **neither** colour of ordinary injective `Q_d`. We may additionally assume the both-colour robust-core condition from the supplied extraction, but the lemmas below do not need it.

For every ordered host partition

\[
 U=A\dot\cup B,\qquad |A|=a\ge m,\quad |B|=b\ge m,
\]

and every injection `f:E -> A`, define the exact lists

\[
 L_{f,c}(y)=B\cap\bigcap_{x\in N_Q(y)}N_c(f(x)).             \tag{1.1}
\]

A matching saturating `O` is exactly a colour-`c` cube extension of `f`. There are no within-parity edges to check, and `A,B` are disjoint. Thus the countercolouring assumption says that **both** list systems fail Hall, for **every** such `f` and **every** such partition.

For each `(A,B,f,c)`, choose an inclusion-minimal nonempty Hall-deficient set `S_c` by a fixed deterministic rule, and set

\[
 T_c=\bigcup_{y\in S_c} L_{f,c}(y).
\]

The key is the simultaneous four-tuple

\[
 K(f)=(S_R,T_R,S_B,T_B).                                   \tag{1.2}
\]

The same `f` is used for both colours. Different keys are not mixed when constructing a conditional resampling law.

### Minimality and the size of the catalogue

If `s=|S_c|`, then

\[
 |T_c|=s-1.                                                \tag{1.3}
\]

For `s=1`, this is immediate. Otherwise remove any row from `S_c`; minimality gives a union of at least `s-1` candidates, contained in `T_c`, while deficiency gives `|T_c|<=s-1`.

Consequently the number of possible single-colour keys is at most

\[
 M(b,m)=\sum_{s=1}^{m}\binom ms\binom b{s-1}
       =\binom{b+m}{m-1}.                                \tag{1.4}
\]

The identity is Vandermonde's identity. There are at most `M(b,m)^2` joint keys.

Let `F` be uniform on **all** `(a)_m` injections `E -> A`. Under the global countercolouring assumption the key is defined everywhere, and

\[
 H(F\mid K)=\log(a)_m-H(K),\qquad H(K)\le2\log M(b,m).     \tag{1.5}
\]

Here `(a)_m=a(a-1)...(a-m+1)` and all logarithms are natural. Every conditional law `F | K=k` is uniform on an actual injection fibre.

A useful fixed-size reservoir is `b=3m`, `a=N-3m`. This requires only `N>=4m`. Then

\[
 M(3m,m)\le\binom{4m}{m}
       \le(256/27)^m,
 \qquad H(K)\le2m\log(256/27)<4.50m.                      \tag{1.6}
\]

The last binomial bound follows by taking the `m`-th term in `(1+1/3)^{4m}`. In particular, this catalogue cost has **no hidden `log C` or `d` factor** at `N=C h`.

### Where global optimization enters

All the statements in (1.1)--(1.6) hold for every host partition of the stated sizes. One can select a largest joint fibre over **all** partitions, keys, and the two colour names, obtaining a fibre of size at least `(a)_m/M^2`. More strongly, Section 7 keeps the *entire* cover by fibres for every partition, rather than retaining just that largest fibre.

No assertion below is based on one arbitrarily unsuccessful injection. Nor do we condition on globally maximum-rank partial embeddings and silently assign them the entropy of all injections. The ordinary global matching optimum remains

\[
 \max_{A,B,c,f}\nu(L_{f,c})<m
\]

under the contradiction hypothesis; the entropy calculation uses all `f`, not an unjustifiably large subfamily attaining that maximum. Conversely, any actual cube can have its even and odd images placed in `A` and `B`, respectively, and the two pools padded to the prescribed sizes, since `a,b>=m`. Thus optimizing over all these partitions preserves the original existence problem; it does not impose a stronger fixed-cut Ramsey assertion.

---

## 2. A minimal Hall certificate has a rainbow tree of actual common neighbours

This lemma applies to any finite list system, so it may be used for both colours simultaneously.

### Lemma 2.1 — Hall-circuit tree

Let `S` be an inclusion-minimal deficient set, `|S|=s`, and `T=L(S)`, so `|T|=s-1`. There is a tree `tau` on vertex set `S` and a bijection

\[
 v\in T\longleftrightarrow e_v=\{y_v,z_v\}\in E(\tau)
\]

such that

\[
 v\in L(y_v)\cap L(z_v).                                  \tag{2.1}
\]

For `s=1`, this means the empty tree and empty candidate set.

**Proof.** For `v in T`, let `R_v={y in S:v in L(y)}`. For every nonempty `W subset T`,

\[
 \left|\bigcup_{v\in W}R_v\right|\ge |W|+1.               \tag{2.2}
\]

Indeed, put `X=S \ union R_v`. If `X` is nonempty, minimality gives

\[
 |X|\le |L(X)|\le |T\setminus W|=s-1-|W|.
\]

The same desired conclusion is immediate if `X` is empty. In particular, each candidate occurs in at least two certificate rows.

Here is an elementary tree-selection proof from (2.2). Induct on `s`.

* If a proper nonempty `W subset T` has `|union R_v|=|W|+1`, first build a tree for these hyperedges on their union. Contract that union to one vertex. The remaining hyperedges still satisfy (2.2): for a subfamily meeting the contracted set, apply (2.2) to its union with `W`; for a disjoint subfamily, use (2.2) directly. Induction in the contracted system, followed by expansion, gives the tree.
* If there is no such proper tight subfamily, choose any `v in T` and any distinct `y,z in R_v`. Delete `v` and contract `y,z`. Every remaining nonempty subfamily had union size at least its cardinality plus two, so contraction leaves (2.2). Apply induction and restore the edge `yz` assigned to `v`.

The bases `s=1,2` are immediate. No candidate is reused. This proves (2.1). QED.

### Cube consequence

For distinct odd cube vertices `y,z`,

\[
 |N_Q(y)\cap N_Q(z)|=
 \begin{cases}2,&d_H(y,z)=2,\\0,&d_H(y,z)\ne2.
 \end{cases}                                               \tag{2.3}
\]

Indeed, a common neighbour corresponds to the two possible intermediate vertices on a length-two cube path. Therefore each candidate `v` assigned to a tree edge in Lemma 2.1 satisfies at least `2d-2` actual colour requirements:

\[
 v\in\bigcap_{x\in N_Q(y_v)\cup N_Q(z_v)}N_c(f(x)),
 \qquad |N_Q(y_v)\cup N_Q(z_v)|\ge2d-2.                   \tag{2.4}
\]

This gives more information than merely naming `s-1` candidates. It does **not** justify multiplying `s-1` independent probabilities: different tree edges still constrain the same even images. Also, conditioning on a chosen tree is not free. A canonical tree is a function of the injection; any further tree conditioning must pay its actual entropy.

---

## 3. Star blocks with only binary non-root intersections, in every dimension

Let

\[
 \ell=2^{\lfloor\log_2 d\rfloor},\qquad d/2<\ell\le d.
\]

Use the first `ell` cube coordinates as inner coordinates and the remaining `d-ell` as outer coordinates. Index the inner coordinates by the elements of `F_2^r`, where `ell=2^r`, **including the zero index**. For an inner bit vector `x`, define its syndrome

\[
 \sigma(x)=\sum_{i=0}^{\ell-1}x_i\,i\quad\text{in }\mathbf F_2^r.
\]

Fix an outer fibre. Its even source vertices have one specified inner parity. For any syndrome `s`, take as roots the inner vertices of the opposite parity with syndrome `s`. For each such odd root `r`, make the block

\[
 I_r=\{r+e_i:0\le i<\ell\}\subset E.                     \tag{3.1}
\]

### Lemma 3.1 — partition and intersection formula

Choosing one syndrome in each outer fibre partitions `E` into `m/ell` blocks of size `ell`. For every block with root `r` and every odd source vertex `y`,

* `N_Q(r) intersect I_r=I_r`;
* if `y` is in the same outer fibre, `y!=r`, its intersection with `I_r` has size zero or two;
* if `y` is in an adjacent outer fibre, its intersection with `I_r` has size at most one;
* otherwise the intersection is empty.

For each pair `{i,j}` of distinct inner indices, the unique non-root row meeting `I_r` exactly in `{r+e_i,r+e_j}` is

\[
 y_{ij}=r+e_i+e_j.                                       \tag{3.2}
\]

The affected non-root rows consist of `binom(ell,2)` binary rows and `ell(d-ell)` unary rows.

**Proof.** For any even vertex `x` in the fibre, the unique root adjacent to it with the chosen syndrome is obtained by flipping the coordinate indexed by `sigma(x)+s`. This proves both coverage and disjointness. The intersection statements follow by separating inner and outer Hamming distances; (3.2) is the two-intermediate-vertices calculation. The incidence check is exact:

\[
 \ell+2\binom\ell2+\ell(d-\ell)=\ell d.
\]

QED.

### Lemma 3.2 — controlling the exceptional roots

For any fixed `S subset O`, the syndromes can be chosen so that at most `|S|/ell` block roots belong to `S`.

**Proof.** In each outer fibre the `ell` syndrome classes partition its odd vertices. Choose one whose intersection with `S` is no larger than the average. Sum over outer fibres. QED.

Apply this to `S_R union S_B` after a joint key has been selected. The resulting partition is a deterministic function of the key, fixed before resampling. At most

\[
 \frac{|S_R\cup S_B|}{\ell}
 \le\frac{|S_R|+|S_B|}{\ell}                              \tag{3.3}
\]

blocks have a root appearing in either certificate. The bound is allowed to be vacuous when the union is all of `O`; that case is not silently omitted.

---

## 4. Exact simultaneous conditional constraints

Fix one joint key, one of its blocks `I=I_r`, and an actual outside assignment

\[
 g:E\setminus I\hookrightarrow A
\]

occurring with positive probability in that key's fibre. Set

\[
 A_0=A\setminus\operatorname{im}(g),\qquad
 n=|A_0|=a-m+\ell.
\]

All resamplings are ordinary injections `z:I -> A_0`.

For colour `c` and row `y in S_c`, put

\[
 J_y=N_Q(y)\cap I,
 \qquad
 K_{y,c}=(B\setminus T_c)\cap
       \bigcap_{x\in N_Q(y)\setminus I}N_c(g(x)).          \tag{4.1}
\]

Then, exactly,

\[
 L_{g\cup z,c}(y)\setminus T_c
   =K_{y,c}\cap\bigcap_{x\in J_y}N_c(z(x)).               \tag{4.2}
\]

Thus the relaxed witness condition `L(S_c) subset T_c` is equivalent to all the following tests:

* `J_y=empty`: `K_{y,c}=empty`;
* `J_y={i}`: `z(i)` is opposite-colour complete to `K_{y,c}`;
* `J_y={i,j}`: every `v in K_{y,c}` is opposite-colour adjacent to at least one of `z(i),z(j)`;
* the root row, if present: the corresponding single `ell`-variable test in (4.2).

These tests are simultaneous over both colours. They concern the *same* resampling and the *same* pinned history.

The actual canonical-key fibre can be smaller than this constraint system: minimality, equality `T_c=L(S_c)`, and the canonical choice may impose further conditions. We use the system as an **upper bound** on that actual fibre, never as an unjustified equality with it. Equation (4.2) itself is an equality.

### Lemma 4.1 — compatibility of the two signed systems

Assume `d>=3`. Fix a host vertex

\[
 v\in B\setminus(T_R\cup T_B).
\]

Call a non-root unary or binary row active in colour `c` when `v in K_{y,c}`. The sets of block variables occurring in active red rows and active blue rows are disjoint.

**Proof.** Suppose opposite-colour active rows `y,z` both contain a block variable `x`. If `y=z`, the non-root row has at least one pinned neighbour: its intersection with `I` has size at most two and `d>=3`. The two colours would be required on the edge from `v` to that pinned image.

If `y!=z`, these odd rows share exactly two even neighbours. One is `x`. The other is outside `I`. Indeed, two distinct non-root rows cannot contain the same pair of block variables, by (3.2); a unary row cannot do so either. Opposite activity would again require opposite colours to the same pinned image. Contradiction. QED.

For example, binary rows `y_ij` and `y_ik` share the pinned source vertex `r+e_i+e_j+e_k`, in addition to their common block variable. This pinned vertex is essential to the compatibility rule.

### What both colours actually contribute locally

At a fixed `v`, let `X_i` be the assertion that `z(i)v` is red. A red active pair forbids `X_i=X_j=1`; a blue active pair forbids `X_i=X_j=0`. Unary clauses force the opposite colour. Lemma 4.1 says that the two kinds of non-root clauses have disjoint variable supports.

Consequently the anticipated alternating red/blue implication-chain amplification does not materialize in a single root-free block at a fixed candidate: its pair components are monochromatic. This is a proved structural calculation, not a bad-boundary example. It does not rule out a global multi-block exchange. It means that such an exchange cannot be replaced by a purported alternating implication already present in these local clauses.

The disjointness is **candidate-by-candidate**, not a product decomposition of the host-value law. As `v` varies, all bits `X_i(v)` must be realized by the **same actual host vertex** `z(i)`. Independently choosing satisfying Boolean patterns for the different candidates would discard the ordinary-injection problem.

---

## 5. Positive local completion: forced rectangles and conditional entropy

For `i in I` and a desired colour `c`, let

\[
 W_{i,c}=\bigcup_{\substack{y\in S_{\bar c}\\J_y=\{i\}}}
                    K_{y,\bar c}.                        \tag{5.1}
\]

Every actual resampling in the joint fibre maps `i` to a vertex colour-`c` complete to `W_{i,c}`. If `D_i` is the set of values of coordinate `i` over that conditional fibre, then

\[
 D_i\times W_{i,c}\text{ is entirely colour }c.           \tag{5.2}
\]

The sets lie in disjoint host pools `A_0,B`.

### Lemma 5.1 — a genuine rectangle completion

If `|D_i|>=m` and `|W_{i,c}|>=m`, there is an ordinary colour-`c` `Q_d`.

**Proof.** Inject the two source parity classes into the two sets. Every required cube edge crosses the monochromatic rectangle. QED.

This uses the complementary colour of the original Hall clause, and does not require rematching or a relaxed homomorphism law.

### Entropic version

Let `P` be the actual conditional fibre and let its distribution be uniform. Write

\[
 \mathcal D(P)=\log(n)_\ell-\log|P|,
 \qquad
 \beta(n,\ell)=\log\frac{n^\ell}{(n)_\ell}.
\]

Let `u(P)` be the number of block positions `i` for which at least one `W_{i,c}` has size at least `m`. In a countercolouring, Lemma 5.1 forces `|D_i|<=m-1` at every such position. Subadditivity of entropy gives the **proved** inequality

\[
 \boxed{\quad
 \mathcal D(P)\ge
 u(P)\log\frac{n}{m-1}-\beta(n,\ell).
 \quad}                                                  \tag{5.3}
\]

Indeed, `H(P)<=sum_i log|D_i|`, and the remaining supports have size at most `n`. A violation of (5.3) produces an actual cube by Lemma 5.1; it is not merely a fractional matching assertion.

This is conditional entropy at one positive-probability history. No unconditional marginal estimate has been substituted for it.

---

## 6. Positive local completion from pair constraints

Unary rectangles may be absent. The following argument uses a whole binary resampling fibre instead of treating its coordinates independently.

Suppose the block data in one colour `c` has a set `K subset B\T_c`, `k=|K|`, with this property:

\[
 \text{for every pair }\{i,j\}\subset I,\quad
 y_{ij}\in S_c\quad\text{and}\quad K\subseteq K_{y_{ij},c}.
                                                               \tag{6.1}
\]

This is an explicitly checkable property of the actual residual sets (4.1). It is **not** asserted to hold in an arbitrary core. Under (6.1), every allowed tuple `z` satisfies

\[
 (N_c(z(i))\cap K)\cap(N_c(z(j))\cap K)=\varnothing
 \quad(i\ne j).                                         \tag{6.2}
\]

Thus its images form a clique in the graph on `A_0` in which two vertices are joined when their colour-`c` neighbourhoods in `K` are disjoint.

### Lemma 6.1 — cube or an explicit small fibre

Assume `k>=m`. Define

\[
 D_* =\left\lfloor\frac{k-m}{d}\right\rfloor,
 \qquad q=\left\lfloor\frac{k}{D_*+1}\right\rfloor.
\]

Let

\[
 G=\{a\in A_0:\deg_c(a,K)\le D_*\},\qquad g=|G|.
\]

Either there is a colour-`bar(c)` cube, or `g<=m-1` and every actual conditional fibre obeying (6.1) has size at most

\[
 \boxed{\quad
 U(n,\ell,g,q)=
 \sum_{j=0}^{\ell}\binom\ell j
       (g)_{\ell-j}(n-g)^j\frac{(q)_j}{q^j}.
 \quad}                                                  \tag{6.3}
\]

As usual `(q)_j=0` for `j>q`.

**Proof of the cube branch.** If `g>=m`, map the even cube class injectively into `G`. Each odd source vertex loses at most `dD_*` candidates in `K`. Since

\[
 k-dD_*\ge m,
\]

the odd class can be assigned injectively, one vertex at a time. This is an ordinary complementary-colour cube.

**Proof of the counting branch.** In the disjoint-neighbourhood graph restricted to `A_0\G`, a clique has size at most `q`: its vertices have pairwise disjoint colour-`c` neighbour sets, each of size at least `D_*+1`, inside the `k`-set `K`.

For any graph on `v` vertices with clique number at most `q`, the number of ordered `j`-cliques is at most

\[
 v^j\frac{(q)_j}{q^j}.                                   \tag{6.4}
\]

For completeness, symmetrize nonadjacent twin classes in a graph maximizing the number of `j`-cliques, and among ties maximize the sum of squared twin-class sizes. Cloning the class with smaller per-vertex clique count into the larger cannot decrease the clique count or increase the clique number. At an extremum nonadjacent distinct twin classes cannot remain. The extremal graph is complete multipartite with at most `q` parts. Padding with zero part sizes and averaging pairs of part sizes shows that its `j`-th elementary symmetric sum is at most `binom(q,j)(v/q)^j`. Multiplication by `j!` proves (6.4).

Now prescribe the `j` block positions taking values outside `G`. There are at most `(g)_(ell-j)` injective choices for the other positions and, by (6.4), at most `(n-g)^j (q)_j/q^j` ordered choices for these `j` positions. Dropping cross-adjacency tests only enlarges the count. Sum over the positions. This proves (6.3). QED.

### A dimension-uniform entropy consequence

Suppose further that

\[
 k\ge2m,\qquad n\ge e^{16}m,\qquad \ell\ge8.
\]

In the no-cube branch,

\[
 q<\frac{kd}{k-m}\le2d<4\ell,
 \qquad p=\frac{m-1}{n}\le e^{-16}.
\]

Dividing (6.3) by `n^ell` and enlarging `g` in the numerator only gives

\[
 \frac{|P|}{n^\ell}
 \le\sum_{j=0}^{\ell}\binom\ell j p^{\ell-j}
                               \frac{(q)_j}{q^j}.        \tag{6.5}
\]

For `j>=3ell/4`,

\[
 \frac{(q)_j}{q^j}
 \le\exp\left(-\frac{j(j-1)}{2q}\right)
 \le e^{-\ell/32}.
\]

The sum of these terms is at most `(1+p)^ell e^(-ell/32)<=e^(-ell/64)`. The other terms sum to at most

\[
 2^\ell p^{\ell/4}\le e^{-\ell}.
\]

Therefore

\[
 |P|\le2n^\ell e^{-\ell/64},
 \qquad
 \boxed{\mathcal D(P)\ge\ell/64-\log2-\beta(n,\ell).}     \tag{6.6}
\]

The finite-population correction is explicit:

\[
 0\le\beta(n,\ell)
 \le\frac{\ell(\ell-1)}{2(n-\ell+1)}.                    \tag{6.7}
\]

This proves a genuine positive implication: under the *observed residual property* (6.1), sufficiently high conditional resampling entropy forces an actual opposite-colour cube. It is stronger than declaring a failed one-colour extension to be a cut. It also handles the critical fact that a binary clique constraint allows one wrong-colour neighbour per tuple: that integer allowance is dealt with by the clique count, rather than incorrectly rounded away.

No part of this argument claims that (6.1), or the high conditional entropy needed to violate (6.6), is furnished by robust cut resilience.

---

## 7. The full global entropy ledger and the exact stopping point

We now retain **all** injections, all joint keys, and the key-dependent star partitions. This is the attempted completing step, not an assertion about a favorable arbitrary boundary.

Fix any host partition of the chosen sizes. For a key `k`, let `P_k` be its nonempty actual fibre, with uniform law `F_k`, and put

\[
 E_k=\log(a)_m-\log|P_k|.
\]

With the true key probabilities `p_k=|P_k|/(a)_m`,

\[
 \sum_k p_k E_k=H(K)\le2\log M.                           \tag{7.1}
\]

For each key, choose the star partition from Lemma 3.2 and write its blocks as `I_1,...,I_t`, where `t=m/ell`. Define

\[
 \Gamma_k
   =H(F_k)-\sum_{j=1}^t H(F_{k,I_j}\mid F_{k,E\setminus I_j}).
                                                               \tag{7.2}
\]

This nonnegative quantity is the dual total correlation of the blocks. Nonnegativity follows by comparing each term with the corresponding conditional entropy in a chain-rule ordering of the blocks. It is not generally zero.

For a conditional state of block `j`, the unused pool always has size `n=a-m+ell`. Its conditional deficit is relative to the uniform law on `(n)_ell` **actual injections**. Averaging it over that state's true outside assignment gives

\[
 D_{k,j}=\log(n)_\ell
       -H(F_{k,I_j}\mid F_{k,E\setminus I_j}).
\]

Set

\[
 \Xi=\log(a)_m-t\log(a-m+\ell)_\ell.
\]

Then, by direct substitution,

\[
 \boxed{\quad \sum_jD_{k,j}=E_k+\Gamma_k-\Xi.\quad}       \tag{7.3}
\]

The finite-population term satisfies

\[
 0\le\Xi
 \le m\log\frac a{a-m+1}
 \le\frac{m(m-1)}{a-m+1}.                                \tag{7.4}
\]

For the lower bound, under the *uniform full injection law*, the quantity in (7.2) is exactly `Xi`, and is nonnegative by the same chain-rule argument. The displayed upper bounds follow by bounding each factor of the falling factorials.

Averaging (7.3) over all keys gives the exact identity

\[
 \boxed{\quad
 \sum_kp_k\sum_jD_{k,j}
   =H(K)+\sum_kp_k\Gamma_k-\Xi.
 \quad}                                                  \tag{7.5}
\]

### Applying the positive local lemmas correctly

At every positive-probability conditional state, (5.3) gives a lower bound for its deficit. When that state's actual residual data also meets (6.1) and the numerical qualifications, (6.6) supplies another lower bound. Let `L(state)` be the maximum of zero and whichever of these proved lower bounds apply. In a countercolouring,

\[
 \sum_kp_k\sum_j
       \mathbb E[L(\text{state}_{k,j})\mid K=k]
 \le H(K)+\sum_kp_k\Gamma_k-\Xi.                         \tag{7.6}
\]

This inequality holds for **every** partition `A,B` of the stated sizes. Consequently it also holds for a partition globally maximizing any proposed surplus in this calculation. The underlying kernels are always conditioned on their own actual key and outside assignment. There is no interchange of a boundary mixture with a conditional kernel.

### Where the proof attempt stops

The attractive comparison was that the entire joint-certificate catalogue costs only `O(m)` in (1.6), while many unary forced positions would cost `log(n/(m-1))`, which can be an arbitrarily large absolute constant, per position. The pair lemma also gives a positive cost proportional to block size.

Two deductions needed to complete this comparison were not proved:

1. **Conditional-information control.** Equation (7.1) controls the mean *global* deficit `E_k`, not the mean sum of the local deficits. The exact difference is `Gamma_k-Xi`. Dropping `Gamma_k`, reversing (7.3), or replacing the conditional entropies by unconditional marginals would be an error. Even a globally largest fibre or a globally optimized host partition does not by itself provide the missing upper bound on this term.
2. **A sufficient supply of actual residual penalties.** The Hall-circuit tree in Section 2 gives real repeated-candidate structure, and Section 4 gives the exact two-colour residual constraints. Neither calculation proves that enough positions have `|W_i,c|>=m`, or that enough blocks have a common pair-residual set as in (6.1) of size `2m`. The shared pinned neighbours also prevent an unproved alternating-colour 2-SAT propagation from manufacturing those sets. Coherent multi-block changes remain available globally, but no terminating augmentation or entropy inequality using them has been established here.

These are not hypotheses being added to the Ramsey problem. They are the precise operations which the attempted proof failed to justify. The new local completion theorems are valid without them; a global conclusion is not.

In particular, no vertex potentials satisfying the low-waste cut inequality from `CubeAdaptiveBridgeAttempt.md` have been constructed. A monochromatic rectangle into a small part of `B` is not automatically a low-waste cut of the entire robust core: the remaining host vertices still have to be accounted for. The robust-core condition has not been shown to control either term just identified.

**Final mathematical outcome:** the proof chain reaches (7.6), together with the actual-cube extraction lemmas in Sections 5--6. It does not force a strict violation of (7.6), a complementary cube by another mechanism, or a forbidden robust cut. Thus the global completion theorem, and Erdős 181, remain unresolved by this attempt.

---

## 8. Verification and integrity

Executable audit:

```sh
python3 -u Submission/check_cube_two_colour_global_completion.py
```

Recorded output: `Submission/CubeTwoColourGlobalCompletionVerification.txt`.

The completed audit checks:

* **74,954 abstract list systems**, with **39,243 minimal Hall-circuit trees**, found by exhaustive edge selection rather than the inductive proof;
* **133,137 source block/row intersections** and **174,251 source pair intersections**, including the star partitions through dimension 10;
* **152,660 actual injective resamplings** in **213 actual-host conditional states** in dimensions 3--5, checking (4.2) directly against the original colour lists;
* **729 opposite-colour active-support disjointness tests**, **1,412 literal forced rectangles**, and **213 unary conditional-entropy bounds**;
* **6,504 clique-count inequalities** on all graphs through five vertices;
* **24,275 actual complementary-cube completions** in the good-degree branch and **41,761 local clique-fibre bounds** in its alternative, using all red bipartite relations on `4+4` vertices and 500 larger sampled relations;
* **40 numerical pair-entropy profiles**, **1,326 global/conditional entropy identities**, and **100 exact joint-catalogue bounds**.

The combinatorial enumeration and cardinality checks are exact. The entropy identities and the numerical profile tests use floating-point logarithms with the tolerances recorded in the script; the all-dimensional proofs are in the text above. These are tests of the stated lemmas, **not** tests at a useful asymptotic countercolouring scale. The audit does not assume or test the unproved global implication.

`Submission/Spec.lean` retains SHA-256

```
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```

No Lean files were edited, and no claimed solution was installed or submitted.
