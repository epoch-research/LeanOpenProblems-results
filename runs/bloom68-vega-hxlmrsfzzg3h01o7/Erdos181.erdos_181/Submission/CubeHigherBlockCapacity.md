# Higher-block capacity: integral ensembles, sparse vertex penalties, and the remaining outer-cube step

## Status

**This submission does not prove or disprove `R(Q_d) <= C 2^d`.** It obtains no new bound for that Ramsey number. `Spec.lean` is unchanged.

The positive result is a **global, integral block-capacity theorem for an arbitrary dense host**, not a theorem about a fresh random host and not just a feasible fractional matching. At `N >= 4096 * 2^d`, `k=floor(d/4)`, it constructs distributions on placements of **all `2^d` original source labels into distinct host vertices**, respecting their prescribed internal `Q_k` edges. It proves the following additional properties.

* Original-vertex capacities can be balanced by product vertex weights different from one at at most `N/128` vertices. The actual configurations, not merely their expected loads, are injective.
* A renewal version proves `Pr(f_i(a)=v | previous blocks) <= 128/N` **after every deletion-only history**. It also proves all-order pin bounds across distinct blocks, and bounds against arbitrary nonnegative, history-dependent original-vertex costs.
* A joint Gibbs version permits freezing any collection of other blocks. It has a proved lower bound on its conditional number of choices and on the probability of gluing a free, coordinate-labelled cube patch. This gives simultaneous, genuinely disjoint realizations of any prescribed family of vertex-disjoint outer cube patches within the stated dimension range.
* The same parameters retain the proposed exponential surplus: the proved one-block min-entropy parameter `B` and auxiliary density parameter `q` satisfy
  \[
  Bq^{d-k}\ge 2^{d2^k/64}.
  \]

These conclusions do **not** impose every edge of the outer `Q_(d-k)`. The exact unproved step is in Section 8: the capacity/partition lower bounds have not been established after imposing overlapping outer-neighbour constraints. We do not multiply bounds valid only for disjoint patches, carry an unconditional occupancy bound through such conditioning, or round a fractional family into a matching.

The proof below is mathematical, with executable exact finite audits. It is not a Lean formalization. No priority claim is made for the auxiliary lemmas.

---

## 1. Definitions and the starting identities

All graphs are finite, simple, and loopless. All maps and copies are labelled. Unadorned logarithms are natural, and `H_infty` denotes minus the logarithm of the largest atom. Formulas with negative powers of an unweighted density are used only when `p>0`. Write

\[
 p=\frac{2e(G)}{N^2},\qquad b_j=2^j,\qquad e_j=j2^{j-1},\qquad
 t_j=t(Q_j,G)=N^{-b_j}\operatorname{hom}(Q_j,G).
\]

This `p` is the **homomorphism-normalized** density. A majority colour of `K_N` satisfies

\[
 p\ge\frac{N-1}{2N},                                      \tag{1.1}
\]

not literally `p>=1/2`. The finite correction is retained below.

Hypercubes are weakly norming. The precise consequence used is: for a subgraph `F` of `Q_j`, with the same host probability measure on all source vertices,

\[
 t(F,G)\le t_j^{e(F)/e_j}.                                \tag{1.2}
\]

Isolated source vertices can be included or omitted. In particular, for `k>=1`,

\[
 t_{k+1}\ge t_k^{2(k+1)/k},\quad
 t(Q_k-u,G)\le t_k^{1-2/b},\quad
 t_k\ge p^{kb/2},\qquad b=2^k.                            \tag{1.3}
\]

These follow by using respectively `F=Q_k` in `Q_(k+1)`, `F=Q_k-u` in `Q_k`, and `F=K_2` in `Q_k`. They are not assumptions of an injective Sidorenko inequality.

### Collision subtraction

Fix distinct source vertices `u,v`. Among homomorphisms with `f(u)=f(v)`, drop the edges incident to `u`. What remains is a homomorphism of `Q_k-u`; the value of `u` is then determined. Thus the number of such maps is at most

\[
 N^{b-1}t(Q_k-u,G)\le N^{b-1}t_k^{1-2/b}.
\]

For adjacent `u,v` the count is actually zero. A union bound proves

\[
 \operatorname{inj}(Q_k,G)\ge N^bt_k(1-\epsilon_k),\qquad
 \epsilon_k=\frac{\binom b2}{N t_k^{2/b}}
 \le\frac{\binom b2p^{-k}}N.                              \tag{1.4}
\]

When `p>=1/2`, the last bound is at most `b^3/(2N)`. If `epsilon_k>1`, the displayed lower bound is still true but does not prove existence.

For a specified original vertex `v`, fix its source position and drop the edges at that position. Summing over positions gives

\[
 \#\{f\in\operatorname{Emb}(Q_k,G):v\in\operatorname{im}f\}
 \le bN^{b-1}t_k^{1-2/b}.                                \tag{1.5}
\]

Consequently a uniform injective block, when `epsilon_k<1`, has occupancy at most

\[
 \frac{b}{N t_k^{2/b}(1-\epsilon_k)}
 \le\frac{bp^{-k}}{N(1-\epsilon_k)}.                      \tag{1.6}
\]

The candidate `b^2/[N(1-epsilon_k)]` is therefore correct under the stated normalized `p>=1/2` hypothesis.

### Exact auxiliary graph

Let `Omega_k(G)` consist of actual injective maps `f:Q_k -> G`. For two such maps put

\[
 T(f,g)=\prod_{a\in Q_k}1_{f(a)g(a)\in E(G)},\qquad
 D(f,g)=1_{\operatorname{im}f\cap\operatorname{im}g=\varnothing}.
\]

The full auxiliary graph has adjacency `W(f,g)=D(f,g)T(f,g)`. Its ordered edge count is exactly

\[
 \sum_{f,g\in\Omega_k}W(f,g)=\operatorname{inj}(Q_{k+1},G).
                                                               \tag{1.7}
\]

The bijection sends `(a,0)` to `f(a)` and `(a,1)` to `g(a)`. No coordinate permutation is chosen along an auxiliary edge.

Writing `M=|Omega_k|` and `q_A=2e(A_k)/M^2`, (1.3)--(1.4) give

\[
 q_A\ge(1-\epsilon_{k+1})t_k^{2/k}
       \ge(1-\epsilon_{k+1})p^b.                         \tag{1.8}
\]

The error here is that of **`Q_(k+1)`**, not merely that of `Q_k`. For `p>=1/2`, one can use `epsilon_(k+1)<=4b^3/N`.

For `r=d-k`, this gives the verified budget

\[
 Mq_A^r\ge(1-\epsilon_k)(1-\epsilon_{k+1})^r
              N^b p^{b(d-k/2)}.                         \tag{1.9}
\]

At `N=C2^d`, `p=1/2`, the last density/size factor is `C^b2^(kb/2)`. With `k=floor(d/4)`, the errors, including their multiplication by `r`, tend to zero. Using (1.1) instead changes the factor by `(1-1/N)^(b(d-k/2))`, which also tends to one on this scale.

### A quantitative DRC check, and its endpoint

Here is a short explicit sufficient condition for the **ordinary auxiliary** conclusion. If a graph has `M` vertices and normalized density `q`, then for `r>=6`,

\[
 (M-1)q^r\ge 2^{r+1}                                    \tag{1.10}
\]

implies that it contains an injective `Q_r`.

To check this version of DRC, put `m=2^(r-1)` and take a balanced cut with bipartite density at least `q`. It suffices that both parts have at least `2q^(-r)m` vertices. Sample two vertices, with replacement, from the first part and let `A` be their common neighbourhood in the second. For an ordered `r`-tuple `Q`, put `omega(Q)=0` if its common neighbourhood has size at least `m`, and `omega(Q)=m/|N(Q)|` otherwise. The two-root DRC calculation gives a choice with

\[
 |A|\ge 2^{-1/r}q^2|V_2|\ge m,
 \qquad |A|^{-r}\sum_{Q\in A^r}\omega(Q)\le\tfrac12.
\]

For completeness, this follows by averaging
`|A|^r - 2 sum_(Q in A^r) omega(Q)`: its expectation is at least
`q^(2r)|V_2|^r/2`, since `m<=q^r|V_1|/2`. Tuples in `A^r` have a nonempty common neighbourhood, so no infinite defect is used.

Now inject one cube parity class uniformly into `A`. For `r>=6`,

\[
 \frac{m^r}{(m)_r}\le2,
 \quad\text{because}\quad r(r-1)\le m
 \quad\text{and}\quad (m)_r/m^r\ge1-r(r-1)/(2m).
\]

The expected total defect of the other parity class is at most `m`. For a choice attaining this, order those vertices by decreasing defect; the `i`th has at least `i` available candidates before excluding earlier choices. This gives an ordinary injective cube. Rounding the balanced cut gives (1.10).

Thus the proposed block entropy really is enough for an ordinary auxiliary cube, with constants and small cases treated appropriately. **It does not make the original images of nonadjacent auxiliary blocks disjoint.** No later claim in this submission uses that invalid inference.

---

## 2. Weighted versions needed for capacity

For nonnegative host weights `w_v`, put `W_0=sum_v w_v>0` and `mu(v)=w_v/W_0`. Define

\[
 H_j(G,w)=\sum_{f:Q_j\to G}\prod_{a\in Q_j}w_{f(a)},
 \qquad
 I_j(G,w)=\sum_{f:Q_j\hookrightarrow G}\prod_{a\in Q_j}w_{f(a)}.
\]

In the first sum the edge requirements are imposed but repetitions are allowed. In the second sum the map is injective. Write `t_j(mu)=H_j/W_0^(2^j)` and `p_mu=t(K_2,G;mu)`.

The weakly norming inequalities (1.2)--(1.3) hold for this probability measure. Formulas with negative powers of `t_j` assume `t_j>0`, and probability-law bounds with `1-epsilon_j` in the denominator assume `epsilon_j<1`. These conditions will follow from (3.1) in every use below. If `alpha=max_v mu(v)`, the weighted collision calculation is

\[
 I_j\ge W_0^{2^j}t_j(\mu)
       \left(1-\binom{2^j}{2}\alpha t_j(\mu)^{-2/2^j}\right).
                                                               \tag{2.1}
\]

Indeed, identifying two source positions replaces the weight at one remaining vertex by its square; `mu(v)^2<=alpha mu(v)`. Dropping the incident edges and applying (1.2) proves (2.1).

For the probability law proportional to `prod_a w_(f(a))` on actual injective `Q_j` blocks, the corresponding one-coordinate bound is

\[
 \Pr(f(a)=v)
 \le \frac{\mu(v)t_j(\mu)^{-2/2^j}}{1-\epsilon_j(\mu)}.
                                                               \tag{2.2}
\]

There is also an all-source-subset version. For an injective pin `z:S -> V(G)`, deleting all edges incident to `S` gives

\[
 \Pr(f|_S=z)
 \le \frac{\prod_{a\in S}\mu(z(a))}{1-\epsilon_j(\mu)}
       t_j(\mu)^{-[j|S|-e(Q_j[S])]/e_j}.                 \tag{2.3}
\]

This is an **unconditioned pin-probability** bound for the specified weighted block law. It is not a bound for the remaining law after dividing by an arbitrarily small pin-event probability.

### A robust weighted residual-host estimate

The following elementary observation will be used repeatedly. Suppose

* `S` is deleted;
* on `V(G)\S`, all weights satisfy `0<w_v<=1`;
* the weights differ from one only on a set `A`;
* `|S|+|A| <= sigma N`.

Then

\[
 W_0\ge(1-\sigma)N,
 \qquad
 p_\mu\ge p-2\sigma.                                    \tag{2.4}
\]

The numerator of the weighted edge density is at least the ordered edge count on `V(G)\(S union A)`, which is at least `pN^2-2N(|S|+|A|)`. Its denominator is at most `N^2`. This proves (2.4), including when `S` and `A` overlap.

---

## 3. The global integral capacity theorem

### Parameters

Let `k>=1`, `s>=1`, and put

\[
 b=2^k,\quad h=sb,\quad \tau=h/N.
\]

Choose `0<delta<1/4` and an integer `J>=k+1`. Assume

\[
 \tau\le\delta/2,\qquad
 \sigma=\delta+\tau,\qquad
 \rho=p-2\sigma>0,\qquad L_0=(1-\sigma)N,
\]
\[
 \eta_j=\frac{\binom{2^j}{2}\rho^{-j}}{L_0},\qquad
 \eta_J\le\tfrac12.                                     \tag{3.1}
\]

Define

\[
 B=(1-\eta_k)L_0^b\rho^{kb/2},\qquad
 q=(1-\eta_{k+1})\rho^b.                                \tag{3.2}
\]

Both are positive.

Let `P_(k,s)(G)` be the set of maps

\[
 F:[s]\times Q_k\hookrightarrow V(G)
\]

that respect every internal `Q_k` edge. **The arrow here is a global injection on all `h` source labels.** Write `F_i(a)=F(i,a)`. Thus `P_(k,s)` is a family of genuine integral packings of labelled cube blocks. It imposes no unspecified external edge requirements.

### Theorem 3.1: renewal, integral entropy, and conditional patch gluing

Under (3.1), all the following hold.

**A. Rebalanced block laws after every deletion.** For every `S subset V(G)` with `|S|<=h`, there is a law `nu_S` on actual injective `Q_k` blocks in `G-S`, of the form

\[
 \nu_S(f)=Z_S^{-1}\prod_{a\in Q_k}w_{f(a)},\qquad
 0<w_v\le1,                                             \tag{3.3}
\]

such that the weights differ from one on at most `delta N` vertices, and

\[
 Z_S\ge B,\quad \max_f\nu_S(f)\le B^{-1},\quad
 \Pr_{\nu_S}(f(a)=v)\le\frac1{\delta N},\quad
 \Pr_{\nu_S}(v\in\operatorname{im}f)\le\frac b{\delta N}.
                                                               \tag{3.4}
\]

For two **independent test draws** from this same current law,

\[
 \mathbb E_{f,g\sim\nu_S}[D(f,g)T(f,g)]\ge q.             \tag{3.5}
\]

Equation (3.5) does not say that a later sequential draw, rebalanced after the first, has that adjacency probability to the first.

**B. A genuinely integral sequential sampler.** Repeatedly use (3.3) on the currently unused vertices. This constructs a law `R` supported on `P_(k,s)(G)` with

\[
 \max_F R(F)\le B^{-s},\qquad
 \Pr_R(F_i(a)=v\mid F_1,\ldots,F_{i-1})\le\frac1{\delta N}.
                                                               \tag{3.6}
\]

Every displayed conditional assertion is valid at every positive-probability history. In particular, for distinct block indices `i_1<...<i_t`, fixed coordinates `a_j`, and specified host vertices `v_j`,

\[
 \Pr_R(F_{i_j}(a_j)=v_j\ \forall j)\le(\delta N)^{-t}.    \tag{3.7}
\]

Repeated specified host vertices have probability zero. There is also a conditional all-orders bound within each block: for `U subset Q_k` and an injective pin `z:U ->` the unused host,

\[
 \Pr_R(F_i|_U=z\mid F_1,\ldots,F_{i-1})
 \le\frac{\rho^{-k|U|+e(Q_k[U])}}
             {(1-\eta_k)L_0^{|U|}}.                      \tag{3.7a}
\]

These bounds can be multiplied over distinct blocks; they do not assert independence of coordinates inside a block. For `|U|=1`, the balanced bound in (3.6) is available instead; for `U=Q_k`, (3.7a) is exactly the `1/B` atom bound. For arbitrary nonnegative costs `z_v` chosen as a function of the previous history,

\[
 \mathbb E_R\left[\sum_{v\in\operatorname{im}F_i}z_v
                   \mid F_1,\ldots,F_{i-1}\right]
 \le\frac b{\delta N}\sum_{v\text{ unused}}z_v.           \tag{3.8}
\]

All host vertices have capacity one in **every outcome**, not just on average. Also `H_infty(R)>=s log B`, and hence `|P_(k,s)(G)|>=B^s`.

**C. A joint Gibbs law on integral packings.** There is a second law `P` on the same integral family, with

\[
 P(F)=\mathcal Z_s^{-1}\prod_{v\in\operatorname{im}F}w_v,
                                                               \tag{3.9}
\]

where again `0<w_v<=1` and at most `delta N` weights differ from one. It satisfies

\[
 \mathcal Z_s\ge B^s,\quad \max_F P(F)\le B^{-s},\quad
 \Pr_P(v\in\operatorname{im}F)\le\frac h{\delta N},\quad
 \Pr_P(F_i(a)=v)\le\frac1{\delta N}.                      \tag{3.10}
\]

After freezing any `t` whole blocks, its conditional partition function for the remaining `s-t` blocks is at least `B^(s-t)`, so every individual conditional configuration has probability at most `B^(-(s-t))`.

There is no assertion that the last marginal bound in (3.10) persists under arbitrary conditioning. The actual one-free-block conditional bound is given in (5.3) below; to obtain (3.6) one uses the separate renewal sampler.

**D. Coordinate-preserving cube patches.** Choose `2^ell` of the block positions and identify them with `Q_ell`, where `1<=ell` and `k+ell<=J`. Under `P`, after fixing all the other block values, the conditional probability that every prescribed outer edge of this patch is present is at least

\[
 q_\ell=(1-\eta_{k+\ell})\rho^{\ell 2^{\ell-1}b}>0.     \tag{3.11}
\]

Every such success is an actual injective `Q_(k+ell)` in the original host, not just an injective auxiliary copy.

For any prescribed family of **vertex-disjoint** outer cube patches, these bounds multiply:

\[
 \Pr_P(\text{all patches succeed})\ge\prod_{U}q_{\ell(U)}>0.
                                                               \tag{3.12}
\]

In particular, arbitrarily many prescribed disjoint patches can be glued simultaneously while all `h` original labels remain distinct. Patches sharing block positions are not covered by this multiplication rule.

---

## 4. Proof of the capacity and entropy assertions

### 4.1 Robust unweighted block availability

For any `T` of size at most `sigma N`, the graph `G-T` has at least `L_0` vertices and normalized density at least `rho`, by the same deletion calculation as (2.4). From (1.4),

\[
 \operatorname{inj}(Q_j,G-T)
 \ge(1-\eta_j)L_0^{2^j}\rho^{j2^{j-1}}>0
 \qquad(k\le j\le J).                                   \tag{4.1}
\]

In particular every such residual graph has at least `B` actual `Q_k` blocks.

This also gives an **integral strict-feasibility witness**, which is important for the optimization below. Put

\[
 L=\left\lfloor\frac{\delta N}{b}\right\rfloor+1.
\]

After any fixed deletion `S` with `|S|<=h`, greedily choose `L` vertex-disjoint `Q_k` blocks. Before each choice the additional deletion has size at most `(L-1)b<=delta N`, so (4.1) applies. Thus the construction really exists. A uniformly chosen member of these `L` disjoint blocks has every vertex occupancy at most

\[
 1/L<b/(\delta N).                                      \tag{4.2}
\]

The theorem is not assuming feasibility of a fractional cube family; (4.2) was obtained from a literal packing.

### 4.2 Sparse vertex penalties for one block

For the current residual host `G-S`, minimize, over `lambda_v>=0`,

\[
 \Phi(\lambda)=\log\sum_{f\in\Omega_k(G-S)}
                 \exp\left(-\sum_{v\in\operatorname{im}f}\lambda_v\right)
                 +\frac b{\delta N}\sum_v\lambda_v.      \tag{4.3}
\]

This is a finite convex function. It attains its minimum at finite multipliers. Here is a direct justification, rather than a formal appeal to an unverified dual optimum. Let `nu_0` be the law in (4.2). The log-sum-exp inequality gives

\[
 \Phi(\lambda)\ge H(\nu_0)+
        \left(\frac b{\delta N}-\frac1L\right)\sum_v\lambda_v.
                                                               \tag{4.4}
\]

The coefficient is strictly positive, so the sublevel sets in the nonnegative orthant are bounded. Continuity gives a minimizer.

Set `w_v=exp(-lambda_v)` there. Differentiating the finite sum shows

\[
 \frac{\partial\Phi}{\partial\lambda_v}
      =\frac b{\delta N}-\Pr_{\nu_S}(v\in\operatorname{im}f).
\]

The optimality conditions give occupancy at most `b/(delta N)`, with equality whenever `lambda_v>0`. Since every block uses exactly `b` vertices,

\[
 |\{v:\lambda_v>0\}|\frac b{\delta N}\le b,
 \qquad |\{v:w_v<1\}|\le\delta N.                       \tag{4.5}
\]

This small exceptional set is the key point: the balancing weights do not destroy a constant portion of the host without a bound. The product-weight law is invariant under cube automorphisms. Since the cube is vertex-transitive and every map is injective, its occupancy at `v` is exactly `b` times any specified source-coordinate marginal. This proves the last two assertions of (3.4).

Let `A={v:w_v<1}`. On `G-(S union A)` all weights equal one. By (4.1) there are at least `B` blocks entirely there, so `Z_S>=B`. Because each individual block has weight at most one, `nu_S(f)<=1/B`.

Finally apply (2.4) to this weighted residual host. Its total vertex weight is at least `L_0`, its normalized edge density is at least `rho`, and its largest normalized vertex atom is at most `1/L_0`. Therefore (2.1) has error at most `eta_j`. The exact weighted version of (1.7) gives

\[
 \mathbb E_{\nu_S\otimes\nu_S}DT
 =\frac{I_{k+1}(G-S,w)}{I_k(G-S,w)^2}
 \ge(1-\eta_{k+1})t_k(\mu)^{2/k}
 \ge q.                                                 \tag{4.6}
\]

This proves A in full.

### 4.3 Actual capacity renewal

At step `i`, the previously used set has size `(i-1)b<=h`; hence A applies afresh to that **actual residual graph**. Sample a genuine block using its newly optimized weights. It avoids all preceding images by definition. Induction proves that the whole outcome is in `P_(k,s)`.

The conditional bounds (3.6) follow from (3.4) at the current history, not from an earlier law. Multiplying conditional atom bounds gives `R(F)<=B^(-s)`. Repeated conditional expectation proves (3.7). Applying (2.3) to the current weighted residual host, using `mu(v)<=1/L_0`, `t_k(mu)>=rho^(kb/2)`, and collision error at most `eta_k`, proves (3.7a). The exponent of `rho^(-1)` is the actual number of cube edges incident to `U`, with internal edges counted once. Summing the conditional occupancies against the currently specified costs proves (3.8), even for costs depending on the history. This proves B.

No external edge to an old block has been imposed in this induction. That qualification is essential, not an implicit freedom to forget required cube edges.

### 4.4 The joint integral law

Now optimize over the **already integral** set `P_(k,s)(G)`:

\[
 \Psi(\lambda)=\log\sum_{F\in P_{k,s}}
                  \exp\left(-\sum_{v\in\operatorname{im}F}\lambda_v\right)
                 +\frac h{\delta N}\sum_v\lambda_v.      \tag{4.7}
\]

Strict feasibility again has a literal integral witness. Take the `L` disjoint blocks from 4.1 with `S` empty and choose a uniformly random ordered `s`-tuple of distinct members. This is possible because `delta N/b>=2s`. Its total vertex occupancy is at most

\[
 s/L<h/(\delta N).
\]

Thus (4.4), with these new occupancies, proves coercivity of (4.7). Its finite minimizer satisfies

\[
 \Pr_P(v\in\operatorname{im}F)\le h/(\delta N),
 \quad\lambda_v>0\Longrightarrow
       \Pr_P(v\in\operatorname{im}F)=h/(\delta N).
\]

The total occupancy is exactly `h`; hence the active set has size at most `delta N`. Permuting the block positions and independently applying cube automorphisms acts transitively on the `h` source labels and preserves the law. Every source marginal is therefore the total occupancy divided by `h`, proving (3.10)'s marginal bound.

These conditions also certify maximum Shannon entropy among laws on `P_(k,s)` with the stated total occupancy ceilings. Indeed, for any such law `nu`,

\[
 H(\nu)\le\log\mathcal Z_s+\sum_v\lambda_v\Pr_\nu(v\text{ used})
 \le\Psi(\lambda),
\]

and equality holds for the optimized law by complementary slackness. This is an entropy optimization **on integral configurations**, not an integrality theorem deduced from fractional constraints.

To lower-bound its partition, choose all blocks outside the active set `A`. At every stage the total deleted set is contained in `A` together with at most `s-1` previously chosen blocks, of total size at most `sigma N`. There are at least `B` choices each time, and their weights are all one. Consequently

\[
 \mathcal Z_s\ge B^s.                                   \tag{4.8}
\]

The same argument after freezing `t` arbitrary valid blocks proves a lower bound `B^(s-t)` on the remaining partition. Each remaining configuration has weight at most one. This proves C, including its conditional atom bound.

### 4.5 Site-dependent capacity ceilings

The joint argument also permits different original-vertex ceilings `c_v`, provided

\[
 h/(\delta N)\le c_v\le1.
\]

Replace the last term of (4.7) by `sum_v c_v lambda_v`. Strict feasibility remains valid. Active vertices satisfy `occupancy(v)=c_v`, so their number is still at most `delta N`; all partition and patch bounds survive. The per-source bound becomes `c_v/h`.

Smaller arbitrary ceilings, especially zero ceilings, are not covered by this statement. Reserved vertices must be deleted and charged to the stated deletion budget. The theorem makes no unsupported assertion about arbitrary fractional demands.

---

## 5. Conditional gluing, with all labels and square relations retained

Freeze every block outside a chosen patch `U` of size `l=2^ell`. Under the joint law (3.9), cancel the weights of the frozen images. The remaining law is exactly the product vertex weighting on `l` globally disjoint injective `Q_k` blocks in the residual graph `H`.

Write `Z_l(H,w)` for its denominator. If `mu` is the normalized residual vertex-weight measure, then

\[
 Z_l(H,w)\le H_k(H,w)^l
             =W_0^{bl}t_k(\mu)^l.                       \tag{5.1}
\]

The numerator for all the outer `Q_ell` edges is **exactly** `I_(k+ell)(H,w)`. This follows from the fixed map `(x,a) -> F_x(a)`, using the prescribed identification of `U` with `Q_ell`. No independent matching permutation or edge-dependent coordinate relabelling appears.

The residual weighted graph has `W_0>=L_0` and `p_mu>=rho`: the frozen blocks use at most `h` vertices and the active set has at most `delta N` vertices. Thus

\[
 \begin{aligned}
 \frac{I_{k+\ell}(H,w)}{Z_l(H,w)}
 &\ge(1-\eta_{k+\ell})\frac{t_{k+\ell}(\mu)}{t_k(\mu)^l}\\
 &\ge(1-\eta_{k+\ell})t_k(\mu)^{l\ell/k}\\
 &\ge(1-\eta_{k+\ell})\rho^{\ell 2^{\ell-1}b}.
 \end{aligned}                                          \tag{5.2}
\]

The second line uses `e_(k+ell)/e_k=l(k+ell)/k`. This proves (3.11).

For disjoint patches, the success of every other patch is measurable from the block values outside the currently considered patch. Conditional expectation therefore lets us apply (5.2) and remove that patch from the event. Induction proves (3.12). This is an all-orders, globally integral assertion, not a pairwise heuristic.

### The correct conditional occupancy statement

If all but one block are fixed under the joint law, (2.2) gives the actually justified bound

\[
 \Pr_P(F_i(a)=v\mid\text{all other blocks})
 \le\frac{1}{L_0\rho^k(1-\eta_k)}.                       \tag{5.3}
\]

This is not the sharper `1/(delta N)` from (3.10). To get the sharper bound after a deletion history, Section 4.3 **reoptimizes the law** and proves its optimality conditions again. The two distributions `P` and `R` are not identified.

### Commuting squares

In a successful patch, internal edges come from each `F_x in Omega_k`; outer edges join `F_x(a)` to `F_y(a)` with the same label `a`. An outer square returns to that same label. For a mixed square, both routes use the same internal coordinate edge `aa'` in the two prescribed blocks. All four corner images are distinct because the whole configuration belongs to `P_(k,s)`.

Thus (5.2)--(5.3) retain every coordinate and all square-closing conditions asserted by the patch. They do not replace them by an arbitrary collection of matchings.

---

## 6. Explicit linear-host parameters and the surviving entropy surplus

Take a majority-colour graph on

\[
 N\ge4096\,2^d,\quad d\ge8,\quad
 k=\lfloor d/4\rfloor,\quad b=2^k,\quad
 r=d-k,\quad s=2^r,\quad h=sb=2^d,
\]

and set `delta=1/128`. Then

\[
 \tau\le1/4096,\quad\sigma\le33/4096,
 \quad L_0\ge(63/64)N,\quad\rho\ge15/32.                 \tag{6.1}
\]

The last assertion follows directly from (1.1):
`rho >= 1/2-1/(2N)-66/4096 >= 15/32`.

Let `C=N/2^d`. The exact inequality `(32/15)^8<2^9` gives

\[
 \eta_j\le\frac{32}{63C}\,2^{25j/8-d}.                  \tag{6.2}
\]

In particular, using `k+1<=d/4+1` and `2^(25/8)<9`,

\[
 \eta_{k+1}\le\frac1{512}2^{-7d/32}<\tfrac12.            \tag{6.3}
\]

Thus Theorem 3.1 applies with `J=k+1`. Its actual configurations use all `h` original source labels injectively, and

\[
 \Pr_R(F_i(a)=v\mid\text{previous blocks})\le128/N,
 \qquad \Pr_P(v\text{ used})\le128h/N\le1/32.            \tag{6.4}
\]

The latter is an average ceiling **in addition to** the pointwise capacity-one constraint in every configuration.

### Analytic surplus calculation

From (3.2),

\[
 Bq^r=(1-\eta_k)(1-\eta_{k+1})^r
              L_0^b\rho^{b(d-k/2)}.                    \tag{6.5}
\]

The product of error terms is at least `1/2`. One elementary uniform check is that `d*2^(-7d/32)<=8`: for `d<=8` this is immediate, and from `d=8` onward the ratio of consecutive terms is at most `(9/8)2^(-7/32)<1`. Hence `(d+1)eta_(k+1)<=9/512` and Bernoulli's inequality suffices.

Also `(63/64)^32>=1/2`, so `log_2(63/64)>=-1/32`. Therefore

\[
 \begin{aligned}
 \log_2(Bq^r)
 &\ge -1+b\left[\log_2 C+d-\frac1{32}
                         -\frac98(d-k/2)\right]\\
 &\ge -1+b\left[\log_2 C+\frac d{64}-\frac{19}{32}\right]\\
 &\ge \frac{db}{64}.                                    \tag{6.6}
 \end{aligned}
\]

The second line uses `k>=d/4-1`; the last uses `C>=4096`. In particular,

\[
 \log_2 B^s+sr\log_2 q\ge dh/64.                         \tag{6.7}
\]

This proves, rather than numerically tests, that global original-label injectivity for the **unlinked block packing** need not consume the proposed surplus.

It is important not to interpret `B` as a number of independent auxiliary choices after arbitrary graph constraints. Equations (6.6)--(6.7) are a retained entropy/density budget for the laws actually constructed. They are not an application of ordinary DRC to a dependent integral-packing law.

### Higher-dimensional patches, not just one-dimensional matchings

For `d>=40`, one may take

\[
 J=\lfloor3d/10\rfloor\ge k+1.
\]

Equation (6.2) then gives

\[
 \eta_J\le\frac{32}{63C}\,2^{-d/16}<\tfrac12.             \tag{6.8}
\]

Consequently (3.11)--(3.12) apply to arbitrary disjoint prescribed outer subcubes of dimensions up to `J-k`, which grows linearly with `d`. For example, partition the outer `Q_r` into its fibres in any fixed `J-k` coordinates. All these fibres can be realized simultaneously and disjointly, on all `h` original labels, as genuine `Q_J` patches.

This is not a claim that the edges between different fibres have been supplied. In particular the growing patch dimension is not silently promoted to dimension `d`.

---

## 7. What has been gained globally

There are three differences from the unconditioned single-block estimate (1.6).

1. **Spread with a dimension-independent overhead.** Instead of the factor `p^(-k)` in the general uniform-block image-occupancy bound, the rebalanced laws have occupancy `b/(delta N)`. This improves that worst-case bound once `p^(-k)>1/delta`; it is not asserted to improve every small-dimensional or host-specific bound. Only `delta N` original vertices receive nontrivial penalties, which is why the density and partition estimates remain available. This is proved for every deleted set within the budget.
2. **An actual integral family of full size.** The sampler and Gibbs law are supported on injections of all `h` source labels. The strict-feasibility and partition arguments explicitly construct integral packings. No hypergraph matching integrality gap is being ignored.
3. **Valid conditioning and gluing.** The renewal law proves its capacities after each previous-block history. The joint law proves conditional partition and patch probabilities after all outside blocks are fixed. These are different, precisely specified assertions, not an assumed product law or the use of old marginals after freezing a boundary.

The price is not a hidden original-label collision: there are no such collisions in these ensembles. The unsupplied requirements are the remaining **edges** of the outer cube.

---

## 8. The exact remaining gap in the attempted global implication

Let the `s` block positions now be the actual vertices of `Q_r`, `r=d-k`. Starting from a globally injective packing, fix some outside blocks and require a free block at `x` to be adjacent to already fixed neighbours `y` of `x`. Its coordinate domains become

\[
 L_a=(V(G)\setminus S)\cap
                \bigcap_{y\in N_{Q_r}(x)\text{ fixed}}N_G(F_y(a)),
 \qquad a\in Q_k.                                       \tag{8.1}
\]

The corresponding partition is

\[
 Z_{\rm boundary}
 =\sum_{f:Q_k\hookrightarrow G-S}
        \prod_a\left(w_{f(a)}1_{f(a)\in L_a}\right).      \tag{8.2}
\]

The domains depend on `a`. This is not `I_k(G-S,w)` for a common host vertex measure. A lower bound on the edge density of `G-S`, even after the small penalty set has been removed, supplies **no proved lower bound here on (8.2)**.

Specifically, the proof of the capacity renewal would now require a strict-feasibility witness like (4.2) consisting of actual completions satisfying (8.1), or an independently justified global rematching of the old blocks that supplies such a witness. We have proved neither. Running the convex minimization without that witness can lose coercivity, finite multipliers, and the small active-set conclusion. It cannot be used to assert that these conditional families satisfy the old capacities.

Likewise, (3.11) is conditional on **outside block values but no requirements from the patch to those outside values**. For two vertex-disjoint patches the other success event is measurable outside the first patch, which is why the tower argument works. After constraints involving a shared block have been imposed, it is not. Thus the patch probabilities cannot be multiplied over the overlapping faces, or over successive coordinate matchings, of the full outer cube. Regrouping a whole component into a larger cube is valid while the explicit `eta_j` criterion holds; that criterion has not been made useful at `j=d` and is grossly insufficient there on a fixed linear-host scale.

This identifies the remaining mathematical task more specifically than a count of auxiliary vertices:

> Establish capacity and a positive partition for a globally selected set of the actual coordinate-domain families (8.1), allowing the old blocks to be rebuilt, while retaining all already required outer edges; or prove that failure of this global rebuild forces a blue `Q_d` in the original complete host.

Neither assertion follows from the proved entropy surplus or from the scalar density of the full auxiliary graph. No cube-free-qualified comparison accomplishing this, and no red-failure-to-blue-cube augmentation theorem, is established here.

Accordingly, this investigation does **not** stop by declaring an injective auxiliary cube to be an original cube. It first resolves hard original capacity for a large, coordinate-labelled integral packing ensemble, follows its conditional gluing rule as far as proved, and records the unsolved edge-conditioning step. The original Ramsey theorem remains unproved by this work.

---

## 9. Verification, sources, and file integrity

### Mathematical inputs

The only non-elementary graph-counting input in the new proof is the established weakly norming property of cubes and its subgraph inequality. The exact source was inspected:

* Hatami, *Graph norms and Sidorenko's conjecture*, arXiv:0806.0047, local file `/corpus/src/0806.0047/normFinal.tex`: the weakly Hölder cube theorem and the probability-measure subgraph inequality, labelled `thm:Hypercubes` and `thm:strongSid`.

The short two-root DRC calculation in Section 1 was checked against:

* Lee, *Ramsey numbers of degenerate graphs*, arXiv:1505.04773, local file `/corpus/src/1505.04773/1505.04773.tex`, Section 2. Its ordinary auxiliary embedding conclusion is kept distinct from original-label injectivity.

`CubeEndpointConflictInvestigation.md`, `CubeIndependentAttackB.md`, and `CubeBlockAmplification.md` were consulted for scope. None of their examples is used as a counterexample to the Ramsey conjecture, and none of the fresh-random-host independence assumptions is transferred to this arbitrary-host proof. No new obstruction construction is a premise or conclusion of this report.

### Exact executable audits

Run from `/workspace/leanproject`:

```sh
python3 -u Submission/check_cube_higher_block_capacity.py
```

The output is saved in `Submission/CubeHigherBlockCapacityVerification.txt`. It checks:

* 384 weighted cube norm, Sidorenko, and deletion cases, using all simple four-vertex hosts, and 6,644 collision and pin checks, including arbitrary source subsets;
* 68 exact weighted auxiliary-edge/disjoint-pair identities, including actual `Q_3` lifts with all square relations checked;
* a nontrivial, exact 440-configuration integral Gibbs/KKT example with a strict feasible law and a genuinely nonunit vertex penalty;
* 44 exact conditional two-free-block product-weight laws after another actual block is fixed;
* 16 all-order cube-patch formulas in complete bipartite hosts;
* the integer inequalities used in (6.1)--(6.8), density normalization and floor bounds at 4,089 dimensions, and the finite-population DRC condition.

The dimension loop checks formulas with arbitrary-precision integers/rationals, not embeddings in exponentially large sampled hosts. The all-dimensional conclusions rest on the proofs above. The small Gibbs example audits the convex algebra; it is not asserted to satisfy the asymptotic theorem's parameter restrictions.

All checks pass. They do not verify the missing statement in Section 8, and no numerical result is substituted for it.

### Unchanged specification

Before and after this work, `Submission/Spec.lean` has SHA-256

```
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```

Neither its conjectural theorem declaration nor its purported disproof declaration is invoked. No Lean file was edited.
