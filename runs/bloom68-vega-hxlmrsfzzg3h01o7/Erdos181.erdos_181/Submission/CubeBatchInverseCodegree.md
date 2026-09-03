# Inverse-codegree sampling and global Hall batches

## Outcome

**The dimension-uniform Ramsey bound is not proved.** The inverse-codegree primitive does have a rigorous Hall-batch extension, but its one-face bound is sharp even for the cube, and it does not supply positivity of the global matching partition function.

The main conclusions are:

1. In a genuinely 3-uniform, role-labelled construction, the retained inverse-codegree kernel is doubly substochastic. This gives the sharp bound
   \[
   \Pr(U\subseteq A)\le {D\over |B||Z|}\nu(\Gamma_U),
   \]
   and a Hall-deficient batch with resource union `W` gives the upper bound `D |W|/(|B||Z|)`. There is also an exact falling-factorial capacity bound for multiple sampled faces.
2. There is a cube instance attaining the Hall bound, with `|A|=2m`, an exactly uniformly spread even injection, no bad singleton tuples, and **every proper odd batch matchable**, but no matching of all `m` odd labels. Thus the primitive alone cannot give a sublinear-in-batch-size replacement for the Hall-cover factor or an exponential batch probability bound.
3. A separate, global Hall comparison is proved in the random-host regime. After discarding columns containing two overlapping cube-neighborhood witnesses, the remaining random list graph is stochastically dominated by an independent bipartite graph. Only `O(d^2)` columns are exceptional in expectation. Consequently the probability that a fixed parity injection extends into the specified opposite part `B` is at most
   \[
   \exp\{m\log(1-e^{-\lambda})+o(m)\},\qquad |B|=\lambda2^d.
   \]
   This remains true, to leading exponential order, with a fixed number of universal anchor columns. It quantifies an extensive global reweighting cost, not merely a constant singleton bad density.

4. At the stated `delta<=1/(100d^3)` threshold, the standard pruned permutation-LLL output has full-injection density ratio at most `exp(O(m/d))`. Combining this with the third conclusion shows that no such low-density local tuple family can force global Hall in these fixed-cut examples. An extensive global tilt or another genuinely global step is necessary.

The third conclusion uses independent random host edges. It is **not** a bound for an arbitrary colouring or for an injection selected adaptively from the remaining host edges. The first conclusion is deterministic apart from the specified sampler.

No Lean files or specification files are changed. These are proved inequalities and sharpness tests, not a formalization of an unproved Ramsey step.

## 1. The precise 3-uniform primitive

Let `P,B,Z` be three disjoint vertex roles of a 3-partite 3-uniform hypergraph. Write

\[
 d(b,z)=|\{p:pbz\in E\}|,\quad
 d(p,b)=|\{z:pbz\in E\}|,\quad
 d(p,z)=|\{b:pbz\in E\}|.
\]

Choose `D>0` no larger than every positive sampled-face degree `d(b,z)`. Put `M=|B||Z|`. Give the ordered, role-specified pair `(b,z)` the **unconditional** probability

\[
 {D\over M d(b,z)}\quad(d(b,z)>0),                              \tag{1}
\]

and put the remaining probability on a null outcome. The total in (1) is at most one. Define

\[
 A_{b,z}=\{p:pbz\in E,\ d(b,z)\ge d(p,b),\ d(b,z)\ge d(p,z)\}.
                                                                    \tag{2}
\]

No application with `r=2` is being made. There are exactly three vertex roles, and no growing-uniformity factorial is hidden in (1).

This is the Claims 3–4 cancellation of arXiv:2203.05497, written for one specified face orientation. The original paper samples all ordered pairs with denominator `N^2`. The rectangular denominator here is valid because we sample only `B x Z`; we prove its normalization and estimates directly. Selecting a prescribed extension role does **not**, by itself, inherit the paper's moment lower bound: a separate mass estimate in that role would be needed.

### Kernel lemma

For a fixed nonempty `U subset P`, set

\[
 K_U(b,z)={\mathbf1\{U\subseteq A_{b,z}\}\over d(b,z)},
                                                                    \tag{3}
\]

with value zero on zero-degree pairs. Then

\[
 \sum_zK_U(b,z)\le1,\qquad \sum_bK_U(b,z)\le1,
 \qquad K_U(b,z)\le |U|^{-1}.                                  \tag{4}
\]

**Proof.** Fix `p_0 in U`. For a fixed `b`, the contributing `z` lie among the `d(p_0,b)` extensions of the face `(p_0,b)`. Every contributing denominator is at least `d(p_0,b)`, by (2). Thus the row sum is at most one; the zero-degree case contributes nothing. Interchanging `b,z` proves the column bound. Finally every contributing face extends to all of `U`, so its degree is at least `|U|`. ∎

Let `Gamma_U` be the bipartite support graph of `K_U` on `B,Z`. For any vertex cover `C_B union C_Z` of this graph, (4) gives

\[
 \sum_{b,z}K_U(b,z)\le |C_B|+|C_Z|.
\]

König's matching–cover theorem therefore proves the rank bound

\[
 \boxed{\Pr(U\subseteq A)
       ={D\over M}\sum_{b,z}K_U(b,z)
       \le {D\over M}\nu(\Gamma_U).}                           \tag{5}
\]

Equivalently, `K_U` is a fractional matching in a bipartite graph, whose fractional and integral matching numbers coincide. This is stronger than first selecting an arbitrary maximal matching and covering by both of its endpoint sets.

The retained support `Gamma_U` may be smaller than the full common link. Replacing its matching number by that of the full common link gives a weaker, still valid bound. It must not be replaced without justification by the matching number of a different batch list graph.

## 2. Hall batches and the exact capacity polynomial

Fix nonempty sets `S_i subset P`, indexed by a batch `I`. The resource list for label `i` is

\[
 L_i=\{b\in B:\text{some }z\in Z\text{ satisfies }S_i\subseteq N(b,z)\},
 \quad N(b,z)=\{p:pbz\in E\}.                                  \tag{6}
\]

Here **only `B` consumes target-vertex capacity**. If the intended application also needs distinct actual `Z` vertices, that second capacity must additionally be enforced; it is not part of Hall's theorem for (6).

For nonempty `J subset I`, put

\[
 U_J=\bigcup_{i\in J}S_i,\qquad W_J=\bigcup_{i\in J}L_i.
\]

Every edge of `Gamma_(U_J)` has its `B` endpoint in `W_J`. Hence a Hall-deficient batch satisfies

\[
 \boxed{\begin{aligned}
 |W_J|<|J|\quad\Longrightarrow\quad
 \Pr(U_J\subseteq A)
 &\le {D\over M}\nu(\Gamma_{U_J})\\
 &\le {D\over M}|W_J|
 \le {D\over M}(|J|-1).
 \end{aligned}}                                               \tag{7}
\]

This is a genuine batch extension of the anchor-cover argument. It is a bound on **inclusion of a fixed batch's images in the random set**, not on the probability of failure after an injection has been chosen adaptively inside that set.

### Several sampled faces: the factorial is capacity, not uniformity

For possibly different nonempty sets `U_1,...,U_q`, suppose the `B` support of every `K_(U_i)` lies in one set `W` of size `w`. Then

\[
 \boxed{
 \sum_{\substack{b_1,\ldots,b_q\ \mathrm{distinct}\\z_1,\ldots,z_q}}
       \prod_{i=1}^q K_{U_i}(b_i,z_i)\le (w)_q.}               \tag{8}
\]

Here `(w)_q=w(w-1)...(w-q+1)`, with value zero for `q>w`.

**Proof.** Sum first over the `z_i`. Each resulting row sum is at most one by (4). There are `(w)_q` ordered assignments of distinct resources. ∎

After multiplication by `(D/M)^q`, (8) bounds the unconditional mass of independent face samples with distinct resources. Requiring distinct fillers can only decrease it.

There is a two-role version. If the supports of all `K_(U_i)` have a common vertex cover of size `w` in `B union Z`, then the sum restricted to vertex-disjoint pairs `(b_i,z_i)` is also at most `(w)_q`. Assign every support edge to one of its endpoints in the cover. Disjoint edges get distinct assigned endpoints; the kernel mass charged to each endpoint is at most one by (4). Sum over injective assignments of indices to the cover.

Thus the primitive really does support a hard-capacity upper bound. But (8) needs **fresh face samples**. Applying it to `q` neighborhoods in the same `A_(b,z)` would replace one anchor by `q` nonexistent independent anchors. In particular, (7) cannot be raised to the power `|J|`.

For a Hall-deficient `J`, taking one fresh kernel for every label in `J` makes the corresponding distinct-resource partition function zero, exactly as it should. What is absent is a positive lower bound for that global, mutually consistent partition function.

## 3. A sharp cube obstruction to stronger one-face conclusions

Take `d>=3`, `m=2^(d-1)`, and the parity classes `X,Y` of `Q_d`. Let

\[
 |P|=|B|=|Z|=2m,\qquad W\subset B,\quad |W|=w=m-1,
\]

and use the hypergraph

\[
 E=P\times W\times Z.                                         \tag{9}
\]

Its positive codegrees are

\[
 d(b,z)=d(p,b)=2m\quad(b\in W),\qquad d(p,z)=m-1.
\]

All sampled positive faces are maximal, so `A_(b,z)=P` for every `b in W, z in Z`. Every positive codegree is at least `D=w`, so even the stronger all-face pruning condition is satisfied.

For any nonempty `U subset P`,

\[
 K_U(b,z)={1\over2m}\mathbf1_{b\in W},\qquad
 \nu(\Gamma_U)=w,\qquad
 \Pr(U\subseteq A)={Dw\over4m^2}.                              \tag{10}
\]

Thus (5) and (7) are attained exactly. With `D=w`, the probability in (10) tends to `1/4`, however large the batch and its union become. The multiple-face expression in (8) is exactly `(w)_q`; with distinct fillers it is

\[
 (w)_q{(2m)_q\over(2m)^q}.                                     \tag{11}
\]

### These are actual cube lists, not an unrelated set system

Take an actual disjoint host cut `P,B`, put all red cross edges between `P` and `W`, and put all remaining cross edges in blue. Let `Z` be an auxiliary role-copy of `P`; put `pbz` in the auxiliary hypergraph when both `pb` and the corresponding `zb` are red. This gives exactly (9). The filler is an auxiliary sampling variable, not another cube vertex needing an image.

Choose **any** injection `f:X -> P` and set

\[
 S_y=f(N_{Q_d}(y)).
\]

These sets have size `d`, every image vertex occurs in `d` sets, and distinct sets intersect in zero or two vertices. Nevertheless,

\[
 L_y=W\quad\text{for all }y\in Y.                              \tag{12}
\]

Consequently:

* every individual list has `m-1` vertices;
* every proper batch of odd labels has a matching;
* the full batch has matching number `m-1` and Hall deficiency exactly one;
* no change of the even injection inside `P` repairs it;
* the empty-list bad-tuple family has density zero;
* the uniform injection into `P`, of size `2m`, has the exact joint-spread identity
  `Pr(f(x_j)=a_j for all j)=1/(2m)_q` for distinct prescribed domain and range points.

So even granting the user's permutation-LLL/pruning conclusion, with its small bad-family density and joint spread, gives no missing capacity here. All `d`-sets in `P` are even locally `t`-rich in the auxiliary hypergraph for every `t<=m-1`. If instead the bad family on `P` is defined by failure of `m`-richness, every tuple is bad, and the LLL's small-density hypothesis is false; that hypothesis is not being asserted. The red cross-edge density in this example is `(m-1)/(2m)`, tending to `1/2`.

For the original unlabelled ordered-pair sampler on `N_aux=6m` vertices, the probability of selecting `A=P` is `2wD/N_aux^2`, still a positive constant when `D` is a fixed positive multiple of `m`. If one also wants `e(H)>=2D N_aux^2` in the usual pruning bookkeeping, take `D=w/18`; then this probability tends to `1/324`. The example is not an artefact of the rectangular normalization. This checks the sampler, maximal-face, and pruning-budget hypotheses; it is not an assertion that the much stronger edge threshold of the paper's `t`-rich-set theorem holds with `t=m`.

In particular, there is no valid universal replacement of the factor `|J|-1` in (7) by `o(|J|)` based only on the stated hypotheses and the cube's intersection pattern. Nor is there a multiplicative batch decay coming from one shared face.

**This is not a Ramsey countercolouring.** For example, colouring all edges inside `P` blue gives a blue clique of order `2m` and hence a blue cube. A proof using both colours and changing the cut is not ruled out. What is ruled out is the proposed stronger conclusion from the one-face hypotheses alone.

## 4. A global Hall comparison in a genuinely random host

Here is a separate inequality that uses the cube's small neighborhood intersections and keeps capacities exactly. It also explains why reweighting only the bounded number of DRC anchor choices cannot remove the random-host obstacle.

### Product-space witness lemma

Let independent Bernoulli variables `xi_x` be given, and let

\[
 E_i=\{\xi_x=1\text{ for every }x\in S_i\},\qquad p_i=\Pr(E_i).
\]

Call a realized set of occurring indices **good** if no two occurring events have overlapping variable sets. Assume goodness has positive probability. Conditional on goodness, the vector `(1_(E_i))` is stochastically dominated, coordinate by coordinate, by independent Bernoulli variables of parameters `p_i`.

**Proof.** Condition on all event indicators except `E_i`. If an occurring event overlaps `S_i`, goodness forces `E_i` to be false. Otherwise, the occurring events fix variables outside `S_i` to one and leave a product measure on the other variables. Requiring all remaining events to be false is a decreasing event. Harris's product-measure inequality bounds the conditional probability of the increasing event `E_i` by its original probability `p_i`. Thus every full single-site conditional probability is at most `p_i`. Averaging gives the same bound for sequential conditional probabilities, and a sequential uniform-variable coupling proves the domination. ∎

The product-measure hypothesis is essential to this proof.

### Application to cube lists

Fix an injection `f:X -> P`. Give the edges between `f(X)` and `B`, `|B|=b`, independent red/blue colours of probability `1/2`. Let `L` be the red list graph from `Y` to `B`, and put

\[
 p=2^{-d}={1\over2m}.
\]

For one column `b_0 in B`, its adjacent row labels are the events that all `d` edges to `f(N(y))` are red. Declare the column bad if two of these occurring events have overlapping neighborhoods.

There are `m binom(d,2)/2` overlapping pairs of cube neighborhoods; each pair has union size `2d-2`. Therefore the bad-column probability `beta_d` satisfies

\[
 \boxed{\beta_d\le {m\over2}\binom d2\,2^{-(2d-2)}
                ={d(d-1)\over4m}.}                            \tag{13}
\]

Different host columns are independent. By the witness lemma, each good column is stochastically dominated by `m` independent Bernoulli-`p` entries.

It follows that there is a coupling with

\[
 H\sim G_{\mathrm{bip}}(m,b,p),\qquad
 K\sim\operatorname{Bin}(b,\beta_d),\qquad H\text{ independent of }K,
\]

such that all good-column edges of `L` are in `H`, and `L` has `K` bad columns. To see independence in this assertion, first generate the column flags; independently generate the Bernoulli columns for `H`; couple each good column using the sequential coupling above, and generate each bad column from its conditional law.

In this coupling, **simultaneously for every batch** `J subset Y`,

\[
 |N_L(J)|\le |N_H(J)|+K.
\]

Hence, writing `def` for maximum Hall deficiency,

\[
 \boxed{\operatorname{def}(L)\ge\operatorname{def}(H)-K,
 \qquad \nu(L)\le\nu(H)+K.}                                   \tag{14}
\]

This is a global matching/capacity statement, not just a count of local common-link matchings. A bad column can have many neighbors, but can repair at most **one** unit of matching deficiency. Without that capacity fact the argument would not work.

If `b=lambda 2^d` with fixed `lambda`, then `E K=O_lambda(d^2)=o(m)`. The sign in (14) is important: it gives an obstruction/upper comparison for extendibility, not a lower bound proving extendibility.

### An extensive, rather than merely constant, reweighting cost

The isolated-row count of `H` is

\[
 Z_0\sim\operatorname{Bin}(m,q),\qquad q=(1-p)^b,
\]

and is independent of `K`. Even if `t` additional arbitrary columns are allowed, a full matching in `L` with those columns requires `Z_0<=K+t`. Thus for every `theta>0`,

\[
 \boxed{\Pr(\text{full matching with }t\text{ extra columns})
 \le e^{\theta t}(1-q+qe^{-\theta})^m
                     (1-\beta_d+\beta_d e^{\theta})^b.}       \tag{15}
\]

One may replace `beta_d` on the right by the upper bound in (13), capped at one.

For fixed `lambda>0`, `b=lambda2^d+O(1)` and fixed `t`, take `e^theta=sqrt(m)/d`. Then `q=e^(-lambda)+O_lambda(1/m)`, and (15) gives

\[
 \boxed{\log\Pr(\text{full matching})
 \le m\log(1-e^{-\lambda})
       +O_\lambda(d\sqrt m+t\log m+1).}                       \tag{16}
\]

The error is `o(m)`. In particular, this is exponential suppression in `m`, not just the weaker suppression obtained by selecting a disjoint subfamily of cube neighborhoods. Equation (16) is only an upper bound; no matching asymptotic for the success probability is asserted.

### This applies to the actual one-center cherry sampler

For a concrete constant-ratio example, take a fixed cut with `|P|=5m`, `|B|=2m`, and independently colour its cross edges. Use `Z` as a role-copy of `P` and the cherry hypergraph from Section 3, separately in each colour.

With probability tending to one, every centre has degree at least `2m` into `P`, in both colours. Since `d(p,z)<=|B|=2m` and `d(p,b)=d(b,z)`, the max-face rule then retains exactly

\[
 A_{b,z}=N_c(b)\cap P
\]

for every positive sampled face. All these sets have size at least `2m`. Standard binomial concentration also gives all positive face degrees at least `m/4`, in both colours. For example, choose `D=m/100`. There are `N_aux=12m` auxiliary vertices and at least `2m(2m)^2=8m^3` hyperedges, so even `e(H)>=2D N_aux^2` holds. The unconditional non-null mass of the role-specified sampler is exactly `D/|P|=1/500`; its choice of centre is uniform after conditioning on being non-null.

Fix a centre `b_0` and expose its incident colours. A uniform injection into `A=N_c(b_0) cap P` is independent of all remaining centre columns. The already exposed centre is one universal extra column, so (16) applies with `t=1` and `b=2m-1=2^d+O(1)`, hence with `lambda=1`. Averaging over the uniform injection and then applying Markov's inequality shows, with high probability over the colouring, that its fraction successful for extending `Y` into this fixed `B` is at most

\[
 \exp\{-(c_1/2-o(1))m\},\qquad c_1=-\log(1-e^{-1})>0.
                                                                    \tag{17}
\]

A union bound over both colours and all `2m` centres preserves this conclusion. Thus (17) holds for **every** non-null set selected by this role-labelled max-face sampler, not only for an average anchor. The underlying complete host has `7m=(7/2)2^d` vertices; colours of internal edges can be filled in arbitrarily.

Multiplying both cut sizes by any fixed `L>=1` (rounding if necessary) gives the same construction on `N=(7L/2)2^d+O(1)` vertices, with `c_L=-log(1-e^(-L))>0` replacing `c_1`. Thus the phenomenon persists at arbitrarily large fixed host multipliers; it is not restricted to the numerical choice `7/2`.

Consequently, a law supported on successful injections into one of these sets, if such injections exist, has relative entropy at least `(c_1/2-o(1))m` from the uniform injection law. A subexponential density tilt cannot be supported on successes or place substantial mass on them.

This does **not** rule out an exponentially tilted global law, an adaptive reconfiguration argument, or even a successful law with good local joint-spread bounds. Local spread does not bound the full density ratio subexponentially. Nor does (17) say there are no successful injections: an exponentially small fraction can still contain very many injections.

## 5. Quantitative consequence for the cited permutation LLL

This section connects the random Hall comparison to the actual small-density local-avoidance method, rather than assuming that all spread laws are almost uniform.

Let `A` have size `a`, let `F subset binom(A,d)` have density `delta`, and let the source hypergraph be the cube parity hypergraph. Delete every vertex whose `F`-degree exceeds

\[
 2d\delta\binom{a-1}{d-1}.
\]

The degree sum shows that at most `a/(2d)` vertices are deleted. Let `A'` be the remainder, `a'=|A'|`, and assume `a'>=2m`. (In the random example above, with high probability all the sets `A` even have size at least `9m/4`, so this assumption holds for all sufficiently large `d`.) Since `a>=2d`, comparison of the binomial products gives

\[
 \boxed{\delta':={|F\cap\binom{A'}d|\over\binom{a'}d}\le3\delta,
 \qquad
 \Delta(F|_{A'})\le6d\delta\binom{a'-1}{d-1}.}                 \tag{18}
\]

For completeness, writing `r=a-a'<=a/(2d)`, we have `a'-d+1>=a/2`. The logarithm of either needed binomial ratio is at most `dr/(a'-d+1)<=1`, and `e<3` proves (18). This deletion and these inequalities can be performed after seeing the host graph.

Use the exact permutation space on `a'` points, with dummy domain entries for the unused points. A canonical bad event specifies a bijection from one cube neighborhood onto one member of `F|_(A')`; its probability is `p_0=1/(a')_d`. Assign `mu=2p_0` to every such event.

The total original event probability incident to a prescribed source point is at most `3d delta`: that point lies in `d` cube neighborhoods. At a prescribed range point it is at most

\[
 {md\over a'}\,6d\delta\le3d^2\delta.
\]

These counts use `d! binom(a',d)=(a')_d` exactly; there is no additional factorial loss. Hence a canonical event fixing `k` images has total adjacent `mu` weight at most `12k d^2 delta`. For a bad event, `k=d`, and

\[
 12d^3\delta\le {3\over25}<\log2
 \quad\text{when}\quad\delta\le{1\over100d^3}.
\]

This verifies the permutation-LLL criterion with `mu=2p_0`. For every `U subset X` and fixed injection `h:U -> A'`, the output-distribution proposition in arXiv:1612.02663 then gives the explicit joint-spread bound

\[
 \boxed{\Pr_{\rm MT}(f|_U=h)
 \le {\exp(12|U|d^2\delta)\over(a')_{|U|}}
 \le {\exp(3|U|/(25d))\over(a')_{|U|}}.                        \tag{19}
\]

In particular, using `|U|=m` is legitimate: the full-injection density ratio from the uniform injection law is at most `exp(3m/(25d))`, not just an unspecified `K^m`.

Let `r_A` be the fraction of uniform injections into the original `A` that have a full matching into the fixed opposite part `B`. Irrespective of how `F` and the deleted vertices depended on the graph,

\[
 r_{A'}\le r_A{(a)_m\over(a')_m},\qquad
 \log{(a)_m\over(a')_m}
 \le {m(a-a')\over a'-m+1}\le {2m\over d}.
\]

Combining this deterministic counting comparison with (19),

\[
 \boxed{\Pr_{\rm MT}(\text{full Hall into }B)
       \le e^{3m/d}r_A.}                                      \tag{20}
\]

Thus in the actual max-face cherry sets of Section 4, the right side is `exp(-(c_1/2-o(1))m)`, simultaneously for every choice of a family `F` satisfying the stated density bound. No union bound over the families is required: (20) is a pointwise deterministic comparison once `r_A` is bounded.

**A concrete no-go consequence.** For these fixed-cut examples, no family of `d`-tuples of density at most `1/(100d^3)` can make the implication

> every cube neighborhood avoids the family => the full list graph satisfies Hall

valid for all injections into `A`. Otherwise the pruned Swapping Algorithm would avoid the family with probability one and therefore satisfy Hall with probability one, contradicting (20). In fact its Hall-failure probability tends to one.

This is not a claim about all distributions described qualitatively as jointly spread. A different distribution could allow an `exp(Theta(m))` full-injection tilt while keeping bounded local spread. Nor does (20) rule out testing global Hall after local resampling, changing the host cut, or using a new batch reconfiguration mechanism. The absent ingredient would still be a proof that such a mechanism has positive successful mass.

## 6. Exactly what is still missing

The results above separate several hypotheses that cannot be conflated.

* **One face versus many.** The fixed-face cancellation supplies marginal anchor capacities. The tensorized bound (8) requires separate samples, not repeated use of one common anchor.
* **Unconditional versus conditional.** Equations (5)–(7) concern fixed sets under the unconditional subprobability sampler. Conditioning on non-null outcomes, on a large `A`, on previous successful constraints, or on an adaptively selected injection needs its normalization and a fresh argument.
* **Witness projection versus actual resources.** The cherry construction projects exactly to real common-neighbor lists; fillers are auxiliary. A different face/pair construction must prove its own projection and account for any second consumed vertex.
* **Role mass.** The cancellation is valid in a chosen role. A large-set/moment lower bound in that same role is not automatic from the unlabelled paper's orientation count.
* **Spread versus Hall.** The sharp cube example has exact joint spread and zero empty-list density. Neither supplies simultaneous capacity for the full batch.
* **Random versus arbitrary host.** Equations (13)–(17) use independent host edges and a fixed parity injection (or an independent uniform one). They cannot be applied directly to an adaptively chosen injection or an arbitrary colouring. The adaptivity allowed in (20) is justified instead by the deterministic density-ratio comparison.
* **Fixed cut versus Ramsey.** All success fractions and (20) concern extension into one specified opposite part `B`. No uniform comparison over all host cuts is asserted.
* **Positive mass versus upper bounds.** The hard-capacity expressions are well defined and can be zero. A positive lower bound for some globally consistent batch, or a justified reconfiguration/colour-switching argument, is still required. The sharp example does not rule out either of these additional inputs.

Thus the direct Hall-cover generalization exists and is optimal at its level of information. It does **not** close the gap in `CubeGlobalHallReduction.md` or provide the positive capacitated baseline missing in `CubeOccupancyPruning.md`. No absolute Ramsey constant has been established.

## Verification

The companion script `check_cube_batch_inverse_codegree.py` checks the substochastic kernel, matching-rank bound, Hall bounds, capacity polynomial, sharp cube construction, random-column domination, and the pruning/LLL load calculations on finite examples using exact integer/rational arithmetic. Its recorded output is in `CubeBatchInverseCodegreeVerification.txt`. These checks supplement the proofs; they are not evidence for the unresolved uniform Ramsey assertion.

The recorded checks include:

* all 256 hypergraphs on three roles of size two, and 250 sampled hypergraphs on roles of size three;
* 2,518 substochastic kernels, 62,384 mixed-batch capacity polynomials, and 9,304 two-role capacity polynomials;
* the sharp cube construction in dimensions 3 through 8;
* all 127 nonempty set families on three product-space bits, with unequal Bernoulli parameters;
* all 65,808 column masks for cube dimensions 3, 4, and 5, and 896 full conditional-probability checks;
* exact global matching-tail comparisons for the dimension-three list graph with one through four random columns;
* 720 pruning binomial-ratio cases, 14 actual bad-family pruning/load cases, and 84 full-injection tilt comparisons.

All checks passed. `Submission/Spec.lean` retains SHA-256 `9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`.

Source audit: Claims 3–5 of `/corpus/src/2203.05497/2203.05497.tex`, together with their preceding pruning and sampling definitions, were read directly. The injection implementation and output-distribution proposition of `/corpus/src/1612.02663/lllperm-journal3-arxiv.tex` were also checked directly; Section 5 supplies the load and normalization calculations needed for the stronger quantitative consequence.
