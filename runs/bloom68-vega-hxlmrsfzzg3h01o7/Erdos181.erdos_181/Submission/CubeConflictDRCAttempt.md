# Conflict-free block DRC: a fixed-linear-scale rounding and penalty-selection bottleneck

## Status

**No proof of `R(Q_d)=O(2^d)` is obtained. No new Ramsey bound is claimed.** This report attempts the specific route of ordinary DRC on injective `Q_k` blocks, followed by original-capacity rounding, with simultaneous vertex/edge penalties used to select an outer parity. It proves an exact failure of two proposed transitions in that route, rather than proposing another unproved sufficient hypothesis.

The main new diagnostic is at **fixed `N=C2^d`**, with arbitrarily large fixed `C`. In an actual majority host satisfying the audited small-cube inputs:

* an entire outer parity is placed in pairwise original-disjoint, internally valid `Q_k` blocks;
* it lies in the common neighborhood of two actual DRC root blocks, and that full neighborhood has size at least `Mq_A^2/32`;
* every opposite vertex has the **same** family of at least `2^((s-2)2^k)` valid, unused common-neighbor blocks, far more than the number of opposite vertices;
* these lists give an actual injective auxiliary `Q_(d-k)`, but they cannot be rounded to original-disjoint blocks: every completion is confined to `O_C(2^k)` original vertices;
* averaging actual auxiliary embeddings over host automorphisms gives **strictly feasible expected original multiplicities and all host-edge budgets simultaneously**. The joint nonnegative vertex/edge price objective has its unique finite minimum at zero, although every configuration in this family has original collisions;
* for an optimistic stable product of the actual original row lists, **every sector cap is zero but the common-price cap of their sum is strictly positive and is minimized at zero**. This proves an infinite min–sum gap, not just a loss of a factor `b`.

Thus this is more specific than a bad arbitrary pinned full parity: all internal block edges, the integral first outer parity, very large opposite **block** lists, and an ordinary auxiliary cube are already present. It also tests all fixed vertex/edge penalty directions, not just one-coordinate marginals. It does **not** show that a high-entropy DRC law on the full auxiliary graph must select these bad sectors. In fact the host has an explicit original `Q_d`. A genuinely global selection with capacity taken **inside each sector before summation** is not refuted and remains unproved.

Files added by this work:

* `Submission/CubeConflictDRCAttempt.md`;
* `Submission/check_cube_conflict_drc.py`;
* `Submission/CubeConflictDRCVerification.txt`.

`Spec.lean` and the three input reports were not edited. No corpus or literature search was used.

---

## 1. The DRC calculation being attempted

Write

\[
 b=2^k,\qquad r=d-k,\qquad m=2^{r-1},\qquad h=2bm=2^d.
\]

The auxiliary vertices are actual labelled injections `f:Q_k -> G`. Adjacency requires both matching-coordinate original edges and disjoint original images. Thus an auxiliary edge is exactly an injective `Q_(k+1)`, with no coordinate permutation along it. Let `M` be the number of these vertices and `q_A` the normalized auxiliary density.

The audited collision subtraction and weak-norm inequalities give

\[
 Mq_A^r\ge(1-\epsilon_k)(1-\epsilon_{k+1})^r
                 N^b p^{b(d-k/2)},                    \tag{1.1}
\]

where `p=2e(G)/N^2`. This really is enough for the ordinary auxiliary DRC conclusion. Original conflicts at nonadjacent outer positions are the additional requirements.

Here is the exact two-root identity, including where a capacity-aware modification would have to enter. Let `X,Y` be a bipartite graph with probability measures `mu,nu` on its parts and density `q`. Choose two roots independently from `mu`, and let `U` be their common neighborhood in `Y`. For an ordered `r`-tuple `Q` from `Y`, write

\[
 c(Q)=\mu(N(Q)).
\]

For every nonnegative defect `D(Q)` for which the expression is finite,

\[
 \mathbb E\int_{U^r}D(Q)\,d\nu^r(Q)
       =\int_{Y^r}c(Q)^2D(Q)\,d\nu^r(Q),               \tag{1.2}
\]

and

\[
                       \mathbb E\nu(U)^r\ge q^{2r}.   \tag{1.3}
\]

The first identity is simply that the two roots both lie in `N(Q)` with probability `c(Q)^2`. For the second, Jensen gives `E nu(U)>=q^2` and then `E nu(U)^r >= (E nu(U))^r`.

With uniform `mu` on `X`, put `tau=m/|X|`. The ordinary inverse-size defect is

\[
 D_{\rm size}(Q)=\frac{\tau}{c(Q)}1_{0<c(Q)<\tau}.
\]

Tuples with `c=0` never occur in `U^r`, and are assigned defect zero here. The useful estimate is

\[
                     c(Q)^2D_{\rm size}(Q)\le\tau^2.   \tag{1.4}
\]

This supports selecting a whole outer parity with sufficiently small total inverse-size defect, and then choosing distinct **auxiliary vertices** for the opposite parity. It is not an original-capacity estimate.

The attempted refinement was to select this parity while controlling sparse vertex penalties and edge budgets, and subsequently round with original linear-form capacities. Sections 2–6 prove that neither a size-defect-good parity nor simultaneous expected budgets provide the needed sector capacity. In particular, (1.4) cannot be used for the missing capacity defect: it can be zero when the relevant original Hall deficit is nearly all `h/2` slots.

---

## 2. A precise fixed-linear-scale construction

Fix an integer `s>=3`. Let `k>=4` be even and, for the capacity obstruction, assume `3k>=2s`. Set

\[
 \begin{gathered}
 d=4k+1,\quad r=3k+1,\quad b=2^k,\quad m=b^3,\quad h=2b^4,\\
 n=4k+2s,\quad D=2^{2s},\quad N=2^n=Db^4,
       \quad C=N/h=2^{2s-1}.                          \tag{2.1}
 \end{gathered}
\]

`C` is fixed as `k` tends to infinity. Taking any fixed `s>=7` gives `C>=8192`, within the audited deletion-only capacity regime. There is no growing `C` hidden in the construction.

Let `V=F_2^n`, with a nondegenerate alternating bilinear form `B`, and let

\[
                        A(x,v)=1_{B(x,v)=1}.            \tag{2.2}
\]

This is a simple graph: `B(x,x)=0`. Its zero vertex is isolated; every nonzero vertex has degree `N/2`. Consequently

\[
 e(G)=N(N-1)/4,\qquad p(A)=(N-1)/(2N).                 \tag{2.3}
\]

In particular, it has exactly half of the edges of `K_N` and is a legitimate majority colour.

### 2.1 All the small-cube inputs hold

The symplectic group acts transitively on nonzero vertices and on oriented host edges. One proof is to extend a nonzero vector, or an ordered pair with pairing one, to a symplectic basis. Uniform weighted laws at the unweighted kernel inherit this symmetry, both for homomorphisms and, when nonempty, for injections. Thus a fixed source vertex is uniform on `V\{0}`, and a fixed oriented source edge has probability

\[
                  \frac{2}{N(N-1)}\le \frac K{N^2}     \tag{2.4}
\]

on each possible oriented host edge, for `K>=64`.

Moreover `A` is an **actual unique finite edge-fugacity minimizer**, not just a kernel satisfying flux bounds. For any cube dimension `j>=1`, let `e_j=j2^(j-1)` and `alpha=2K/N^2`. At zero penalties the unordered host-edge multiplicities satisfy

\[
                      \mathbb E M_e/e_j=1/e(G).
\]

For any `lambda>=0`, Jensen yields

\[
 \Phi_j(\lambda)-\Phi_j(0)
 \ge (\alpha-1/e(G))\sum_e\lambda_e.                   \tag{2.5}
\]

The coefficient is strictly positive. This proves finite optimality, uniqueness, and the full slack KKT certificate in every dimension. All optimized kernels in the monotone profile are the same `A` here.

Use the symplectic rank estimate proved in Section 3 of `CubeEdgePressureResolutionAttempt.md`:

\[
 \log p(A)\le\log a_j(A)
 \le-\log2+\frac1{j^2}\log(1+4\,2^{2j-n}),\qquad n\ge2j.
                                                               \tag{2.6}
\]

This is an unconditioned hom-count estimate; no boundary law is deduced from it. At the scale in (2.1),

\[
 \begin{split}
 0\le(k+1)\Delta_k(A)
 &\le \frac{\log(1+2^{4-2k-2s})}{k+1}
                   -(k+1)\log(1-1/N)\\
 &\le \frac{2^{4-2k-2s}}{k+1}+\frac{2(k+1)}N
       \longrightarrow0.                              \tag{2.7}
 \end{split}
\]

Thus **any positive universal small-increment threshold** eventually holds, with fixed `C` and the actual minimizer.

The injective auxiliary surplus also holds. Since `N>=2(k+1)`,

\[
 \epsilon_k\le b^3/N=1/(Db),\qquad
 \epsilon_{k+1}\le8b^3/N=8/(Db).                        \tag{2.8}
\]

For example, `p^(-k)<=2b` follows from
`(1-1/N)^k>=1-k/N>=1/2`; applying the same argument to `k+1` gives the second bound. Combining (1.1) with Bernoulli's inequality gives, for all even `k>=4,s>=3`,

\[
 \begin{split}
 Mq_A^r
 &\ge C^b2^{kb/2}
       (1-\epsilon_k)(1-\epsilon_{k+1})^r
       (1-1/N)^{b(7k/2+1)}\\
 &\ge \tfrac12 C^b2^{kb/2}.                            \tag{2.9}
 \end{split}
\]

Indeed the sum of the three error bounds is at most

\[
              \frac{24k+9}{D2^k}
                    +\frac{b(7k/2+1)}N<\tfrac12.       \tag{2.10}
\]

Both summands decrease with even `k>=4` and with `s>=3`; the inequality holds already at `k=4,s=3`.

This implies the stronger proposed budget

\[
                         Mq_A^r\ge h^2\exp(kb/10).     \tag{2.11}
\]

For a purely elementary check, use `1/2<=log 2<=1`; after multiplying by 20, a sufficient inequality is

\[
                  b(3k+20s-10)>20(8k+3),               \tag{2.12}
\]

which holds at `k=4,s=3` and increases thereafter. Also
`b(k/2+2s-1)-1>=r+2`, so (2.9) implies the audited ordinary-DRC threshold `(M-1)q_A^r>=2^(r+1)`.

The hom version `N^b t_k q_k^r` is at least
`N^b p^{b(d-k/2)}`, so it has the same required surplus as well. Here `q_k=t_(k+1)/t_k^2` and `q_A` is the actual injective auxiliary density; they are not identified.

Finally, uniform injective blocks have the exact unconditional capacities

\[
 \Pr(f(a)=v)=1/(N-1),\qquad
 \Pr(v\in\operatorname{im}f)=b/(N-1)\quad(v\ne0).       \tag{2.13}
\]

For `s>=7`, the deletion-only, sparse-product-penalty capacity theorem of `CubeHigherBlockCapacity.md`, Theorem 3.1 and Section 6, applies with `k=floor(d/4)`. Its actual renewal law, conditional capacities after deletions, integral packing partitions, and retained `Bq^r` bound are all available in this very same host. The failure below is after **overlapping outer-neighbor constraints**, not a failure of that theorem.

### 2.2 An explicit inner cube

Decompose the symplectic space as an orthogonal direct sum

\[
 V=U\perp T,\quad \dim U=3k,\quad\dim T=k+2s,
 \qquad T=T_0\perp W,                                  \tag{2.14}
\]

where `dim T_0=k+2` and `dim W=2s-2`. These are all even dimensions.

For `a in F_2^k`, define

\[
 Q(a)=\sum_{i=1}^{k/2}a_{2i-1}a_{2i},\qquad
 L(a)=\sum_{i=1}^k a_i,\qquad F(a)=Q(a)+L(a).            \tag{2.15}
\]

All operations in these formulas are over `F_2`. Let `p_0,q_0` be a symplectic pair orthogonal to the first `k` coordinates of `T_0`, and put

\[
                       \zeta_a=a+p_0+F(a)q_0.           \tag{2.16}
\]

Polarization gives the useful exact identity

\[
                   B(\zeta_a,\zeta_c)=F(a+c).           \tag{2.17}
\]

In particular, it equals one whenever `a,c` differ in one coordinate.

Choose a symplectic basis `e_1,f_1,...,e_(s-1),f_(s-1)` of `W`, and define

\[
 z_a=\zeta_a+e_1,\qquad Z=\{z_a:a\in Q_k\},\qquad
 H=\langle e_2,\ldots,e_{s-1}\rangle,
 \quad\mathcal T=f_1+H.                                \tag{2.18}
\]

The `z_a` form an injective `Q_k`. Also

\[
 |\mathcal T|=2^{s-2},\qquad
 B(t,t')=0\ (t,t'\in\mathcal T),\qquad B(e_1,t)=1.
                                                               \tag{2.19}
\]

### 2.3 Pin an entire, genuinely disjoint outer parity

Let `E_r` be the even parity of `Q_r`. The map `u:E_r -> U` taking the first `r-1=3k` coordinates is a bijection. Define

\[
                        F_x(a)=u(x)+z_a,\qquad x\in E_r. \tag{2.20}
\]

All `m` blocks are internally valid: `U` is orthogonal to `T`, and `B(u,u)=0`. They are pairwise original-disjoint because the decomposition `U direct-sum T` is unique and the `z_a` are distinct. Thus their used set is

\[
 S=U+Z,\qquad |S|=mb=h/2,\qquad S\cap T=Z.             \tag{2.21}
\]

No fractional packing or noninjective first-parity placement occurs here.

### 2.4 Every opposite block list is huge but has the same tiny support

Fix an odd outer vertex `y`. The first `r-1` coordinates of its `r` neighbors are

\[
              v,\ v+e_1',\ldots,v+e_{3k}',             \tag{2.22}
\]

an affine basis of `U`. Here primes distinguish the basis of `U` from the basis in (2.18).

If a candidate block `g` is adjacent to all these pinned neighbor blocks, then for each inner coordinate `a`,

\[
                 B(g(a),u(x)+z_a)=1\quad(x\sim y).
\]

Subtracting the equations for (2.22) forces `g(a)` orthogonal to **all** of `U`. Since `U` is nondegenerate, this says `g(a) in T`. The remaining equation is `B(g(a),z_a)=1`.

After deleting **all** previously used original vertices `S`, the exact residual block family is therefore independent of `y`:

\[
 \mathcal H=\left\{g:Q_k\hookrightarrow G[T\setminus Z]:
                     B(g(a),z_a)=1\ \forall a\right\}. \tag{2.23}
\]

It is not small as a family of auxiliary vertices. For every function
`tau:Q_k -> mathcal T`, put

\[
                        g_\tau(a)=\zeta_a+\tau(a).      \tag{2.24}
\]

These maps are injective since their first `k` coordinates are `a`. They avoid `Z`, hence avoid the whole pinned set `S`. Equations (2.17) and (2.19) prove all internal cube edges and all required matching-coordinate edges. Different functions give different labelled blocks **and different image `b`-sets**; the count is not produced merely by relabelling one image. Hence

\[
                     |\mathcal H|\ge 2^{(s-2)b}\ge m.  \tag{2.25}
\]

In fact the final ratio tends to infinity doubly exponentially in `k` relative to the outer scale `m=2^(3k)`.

Nevertheless every member of `mathcal H` is supported on

\[
                   S_0=T\setminus Z,\qquad
                   |S_0|=(D-1)b.                     \tag{2.26}
\]

There are `mb` opposite original source labels. Since `m=b^3>D-1`, no original-disjoint completion exists. The maximum number of disjoint blocks from this family is at most `D-1`, **independent of `k`**. The support shortage, not a `b`-factor loss in a matching theorem, proves impossibility.

Notice that (2.23) is after all first-parity vertices were deleted. The obstruction is not an unremoved conflict with a nonneighbor on the first parity.

### 2.5 Genuine DRC roots and a genuine auxiliary cube

Take the two constant-tag maps (2.24) with values `f_1` and `f_1+e_2`. They are distinct, original-disjoint auxiliary vertices, each adjacent to **every** block (2.20). Thus the pinned parity lies inside an actual two-root common neighborhood.

Choose any `m` distinct functions `tau` in (2.24), and assign their blocks to the odd outer vertices. Together with (2.20) this is an injective auxiliary `Q_r`. Every one of its edges lifts to an actual injective `Q_(k+1)`. Every opposite common-neighborhood size is at least `m`, so its ordinary size defects are all zero, even after removing all first-parity original vertices.

Only original conflicts between **nonadjacent odd blocks** prevent an original `Q_d`. No such conflicts can be removed while retaining the pinned parity, regardless of how one chooses from the full lists (2.23).

This proves the first bottleneck:

> Even with the fixed-linear-scale surplus, actual finite minimizer, arbitrarily small common-kernel norm increment, exact unconditioned flux, deletion-only capacities, an integral first parity inside a two-root DRC neighborhood, and zero ordinary inverse-size defects, that parity need not admit conflict-free rounding.

This is a statement about rounding a selected parity, not a counterexample to a theorem asserting that **some other** good parity exists.

### 2.6 The two roots have a DRC-scale common neighborhood, not just this small parity

There is also a direct positive count for the full common neighborhood of these two roots. Write it as `mathcal A`, to distinguish it from the subspace `U`. Then

\[
 |\mathcal A|\ge\tfrac14 N^b2^{-kb/2-2b}
                    \ge\tfrac1{32}Mq_A^2.             \tag{2.27}
\]

Here is a proof that retains actual original injectivity. For each inner source coordinate `a`, independently choose `v_a in T` with pairing one to both roots at that coordinate. The two root vectors are linearly independent, so there are exactly `|T|/4` choices. We seek a block of the form `f(a)=u_a+v_a`.

Choose the `u_a` on one **inner** cube parity uniformly in `U`, whose order is `m=b^3`. Require (i) distinct values on this parity, and (ii) linearly independent `k`-tuples on every opposite vertex's neighborhood. For `k` independent uniform vectors in a space of order `m`, dependence probability is at most `(2^k-1)/m=(b-1)/m`. A union bound over the `b/2` opposite neighborhoods and over equal pairs in the first parity shows that the fraction of good choices is at least

\[
                  1-\frac{b(b-1)}{2m}
                       -\frac{\binom{b/2}{2}}m
                     \ge1-\frac5{8b}.                 \tag{2.28}
\]

Every selected value is nonzero, since it lies in one of the independent neighborhood tuples. Now take the opposite inner parity sequentially. At each vertex the `k` internal edge equations are independent affine linear equations for `u_a`, regardless of the already chosen `v` values. They have exactly `m/2^k=b^2` solutions. Avoid zero and all previous `u` values, removing at most `b` choices. Thus the entire block has distinct nonzero `U` components, proving both its original injectivity and disjointness from the two root images in `T`.

The number of blocks obtained is at least

\[
 (|T|/4)^b m^{b/2}(1-5/(8b))(m/b)^{b/2}(1-1/b)^{b/2}
      \ge\tfrac14 N^b2^{-kb/2-2b}.                    \tag{2.29}
\]

For the last inequality use Bernoulli's inequality to get
`(1-1/b)^(b/2)>=1/2`, and `1-5/(8b)>=1/2`.

For completeness, (2.6) and (2.8) bound the full auxiliary parameters above by

\[
 \begin{split}
 M&\le N^b2^{-kb/2}\exp(2/(kDb))\le2N^b2^{-kb/2},\\
 q_A&\le2^{-b}\exp\left(\frac{4+16/(k+1)+2k/b^2}{Db}\right)
                  \le2\,2^{-b}.                       \tag{2.30}
 \end{split}
\]

The exponent in the second line bounds the three losses from injective collision subtraction, the `Q_(k+1)` norm upper bound, and the finite `p` correction, respectively. Both displayed exponent bounds are less than `1/2<=log 2` at `k=4,s=3` and decrease thereafter. Equations (2.29)–(2.30) prove (2.27).

Thus the chosen roots really have a common neighborhood within an absolute constant of the usual `Mq_A^2` DRC size scale. This does **not** assert that all of that neighborhood has a small averaged inverse-size defect, or that the bad pinned parity is typical there. Its own defects are zero by the explicit construction. Those distinctions remain essential.

---

## 3. The exact original-capacity invariant already fails in a stable relaxation

For the pinned parity (2.20), drop only the internal edges of the opposite blocks. The remaining original row lists, one for each odd outer `y` and inner `a`, are

\[
              L_{y,a}=L_a=\{v\in T\setminus Z:B(v,z_a)=1\}. \tag{3.1}
\]

Every row has at least `(D/2-1)b` entries, because a nonzero `z_a` has `|T|/2` neighbors in `T` and at most `b` vertices were removed. Nonetheless all `mb` rows are supported on only `(D-1)b` columns.

Use the product of the actual row linear forms

\[
            P_F(\boldsymbol x)
            =\prod_{y\ {
m odd}}\prod_{a\in Q_k}
                       \left(\sum_{v\in L_a}x_v\right). \tag{3.2}
\]

This polynomial is real stable. Its square-free part is identically zero, because its degree `mb` exceeds the number of variables in its support. The row-sum-one, column-sum-at-most-one polytope is empty for the same reason. Thus the capped entropy is `-infinity` even in this **optimistic relaxation**; restoring the opposite internal edges cannot fix it.

More explicitly, define the nonnegative-price cap of a row product by

\[
 \mathcal C(P)=\inf_{\lambda_v\ge0}
       \exp\left(\sum_v\lambda_v\right)P(e^{-\lambda}). \tag{3.3}
\]

For a product of row linear forms, this is the exponential of the usual column-capped entropy dual. The sparse direction `lambda=t 1_(S_0)` gives

\[
 \exp\left(\sum_v\lambda_v\right)P_F(e^{-\lambda})
       =P_F(1)\exp\big(-t[mb-(D-1)b]\big)
           \longrightarrow0.                         \tag{3.4}
\]

Hence `C(P_F)=0`. The detecting set is extremely sparse:

\[
                         |S_0|/N=(D-1)/(Db^3)\to0.     \tag{3.5}
\]

The issue is that **which** sparse set detects failure depends on the pinned sector.

The one-block renewal optimization also demonstrably loses its finite minimizer after these neighbor constraints. If it is run over (2.23) with the deletion-only ceiling `b/(delta N)`, its value on the same direction is

\[
 \log|\mathcal H|-bt+\frac b{\delta N}|S_0|t
       \longrightarrow-\infty                         \tag{3.6}
\]

as soon as `|S_0|<delta N`. Thus coercivity and the strict-feasibility witness have not merely gone unproved: for this valid overlapping boundary they are **false**. This does not contradict renewal after deletions alone.

---

## 4. Simultaneous original-vertex and edge budgets do not select a good sector

One might try to avoid a bad individual boundary by choosing a whole distribution of DRC parities, checking every fixed vertex penalty and host-edge budget simultaneously, and then rounding. The same construction gives an exact obstruction to that interchange.

Fix one of the actual auxiliary `Q_r` embeddings from Section 2.5 and regard its lift as a map `phi:Q_d -> G`. It respects **every cube edge**. Its individual `Q_k` blocks and all adjacent block pairs are injective; it has original repetitions only across nonadjacent odd blocks.

Let `mathcal O` be its orbit under the finite symplectic group, with the uniform orbit law. Every element still has an uncompletable pinned outer parity. But transitivity gives, for each source label `z` and source oriented edge `zz'`,

\[
 \Pr(\phi(z)=v)=\frac1{N-1}\quad(v\ne0),\qquad
 \Pr(\phi(z)=x,\phi(z')=v)=\frac2{N(N-1)}\quad(B(x,v)=1).
                                                               \tag{4.1}
\]

Let `M_v` now mean the **multiplicity** of an original vertex in the full map, not its used/not-used indicator. Let `M_e` count source edges with multiplicity, and let `e_d=dh/2`. Then

\[
 \mathbb E M_v=h/(N-1)<1\quad(v\ne0),\qquad
 \mathbb E M_0=0,\qquad
 \mathbb E M_e=e_d/e(G)<\alpha e_d.                    \tag{4.2}
\]

Thus the expected original capacity-one constraints and all edge budgets hold **strictly at once**. In particular they hold against every nonnegative original-vertex cost, not only against indicators of predetermined sets.

This yields a finite-perturbation conclusion stronger than a list of marginal checks. Define a simultaneous vertex/edge price objective on this actual auxiliary-embedding orbit:

\[
 \begin{split}
 \Psi(\lambda,\mu)
 ={}&\log\sum_{\phi\in\mathcal O}
       \exp\left(-\sum_v\lambda_vM_v(\phi)
                  -\sum_e\mu_eM_e(\phi)\right)\\
 &+\sum_v\lambda_v+\alpha e_d\sum_e\mu_e,
       \qquad \lambda,\mu\ge0.                       \tag{4.3}
 \end{split}
\]

Jensen and (4.2) give

\[
 \begin{split}
 \Psi(\lambda,\mu)-\Psi(0,0)
 \ge{}&\left(1-\frac h{N-1}\right)\sum_{v\ne0}\lambda_v
                  +\lambda_0\\
 &+e_d\left(\alpha-\frac1{e(G)}\right)\sum_e\mu_e.
                                                               \tag{4.4}
 \end{split}
\]

All coefficients are positive. Therefore this objective is coercive on the nonnegative orthant and has its **unique finite minimizer at zero**. Every nonzero feasible nonnegative price perturbation increases it. Restricting to sparse vertex penalties or sparse edge budgets plainly does not help.

Yet there is no original injection anywhere in its support. This is not a fractional matching rounded incorrectly in the proof: it is an explicit proof that such rounding is impossible within this family.

The conclusion is limited but exact:

> Optimizing original expected multiplicities and host-edge budgets on an ensemble of ordinary auxiliary embeddings does not force an original injection, even when the optimum is finite, strictly feasible in every budget, and tested against all finite nonnegative penalty vectors.

The successful integral optimization in `CubeHigherBlockCapacity.md` optimizes over **already integral original packings**. It does not make the false assertion above. Nor does this construction identify the orbit law with the small-cube Gibbs law: the host's actual small-cube minimizer was verified separately in (2.5).

---

## 5. Exact min–sum gap for sectorwise stable capacities

The loss in Section 4 has a particularly transparent stable-linear-form version.

For each symplectic automorphism `sigma`, rotate the pinned parity and its row lists, and let `P_sigma` be the product (3.2) on those rotated lists. Each product is stable, all have the same value at one, and by (3.4)

\[
                         \mathcal C(P_\sigma)=0.        \tag{5.1}
\]

Define the positive sum, with group multiplicities allowed,

\[
                         P=\sum_\sigma P_\sigma.       \tag{5.2}
\]

Sample `sigma` uniformly, then choose one entry independently in each of its `mb` row lists. Under this normalized polynomial law every source row is uniform on the nonzero host vertices, by transitivity. The expected exponent of each such variable is `mb/(N-1)<1`.

For every `lambda>=0`, Jensen therefore gives

\[
 \begin{split}
 e^{\sum_v\lambda_v}\frac{P(e^{-\lambda})}{P(1)}
 &\ge\exp\left[
       \left(1-\frac{mb}{N-1}\right)\sum_{v\ne0}\lambda_v
                                  +\lambda_0\right]\\
 &\ge1.                                                \tag{5.3}
 \end{split}
\]

Equality at zero proves the exact formula

\[
 \boxed{\quad
 \sum_\sigma\inf_{\lambda\ge0}e^{\sum\lambda}P_\sigma(e^{-\lambda})=0,
 \qquad
 \inf_{\lambda\ge0}e^{\sum\lambda}\sum_\sigma P_\sigma(e^{-\lambda})
       =P(1)>0.\quad}                                  \tag{5.4}
\]

Thus all fixed common prices see a strictly feasible mixture, while **every** sector has a sparse Hall certificate. The sector-adaptive prices `t 1_(sigma S_0)` cannot be replaced by a common price before the sector sum. The gap is infinite on the logarithmic scale.

There is no stability-of-mixtures assertion: `SF(P_sigma)=0` for every sector, so `SF(P)=0` by linearity. The positive common cap in (5.4) is precisely why the stable row-product rounding theorem cannot be applied after this sum. Stability is valid inside each summand only.

This refutes the following attempted global selection step, including versions that test all fixed prices simultaneously:

\[
 \text{a price-balanced mixture of size-defect-good DRC sectors}
 \quad\Longrightarrow\quad
 \text{some sector with feasible original row capacities}.      \tag{5.5}
\]

It does not refute selecting sectors by their **already capped** weights. On this restricted family those weights are all zero, as they should be.

---

## 6. Where the focused proof attempt stops

### 6.1 The ordinary moment does not estimate the needed adaptive defect

For the pinned parity in Section 2, every neighborhood tuple has at least `m` residual auxiliary choices and therefore size defect zero. Its common family is nevertheless destroyed by deleting the same set `S_0` of size much less than `h`; and all the original relaxed row capacities together vanish.

The exact two-root formula (1.2) remains valid for a specified finite cost, but its useful estimate (1.4) exploits **small common-neighborhood mass**. It does not control a sector-adaptive capacity cost which can be fatal at a tuple with many common-neighbor blocks. Neither edge-flux symmetry nor the small norm increment changes that calculation.

No estimate of the root-weighted probability or entropy cost of such adaptive capacity failures has been proved here. The example does not assert that their probability is large under the full DRC law. Nor is the explicit lower bound `2^((s-2)b)` for the residual lists being advertised as the full `exp(Omega(kb))` surplus: their exact count is not determined here. A refinement that spends surplus on a larger tuple threshold or on an adaptive capacity defect still needs its own estimate; this report does not refute every such refinement.

### 6.2 Taking all fixed penalties at once is still the wrong quantifier order

Sections 4–5 go beyond pointing out that marginals change on conditioning. They give the exact finite inequalities for all common penalties and an exact zero-versus-positive capacity gap. A minimax or convex-optimization argument that first mixes sectors and then imposes the original budgets may certify this bad family as strictly feasible.

To use the stable pinned linear-form capacities correctly, one must keep the sector-dependent infimum **inside** the sector sum. Ordinary scalar DRC does not supply a lower bound for that quantity. Averaging the sector prices into a host-edge direction is also unavailable here: every common nonnegative edge direction increases the actual small-cube objective (2.5), and every common vertex/edge direction increases the orbit objective (4.4).

This is the precise proved bottleneck in the attempted simultaneous-price route. It is not a claim that a new sector-adaptive DRC estimate is impossible.

### 6.3 Why this is not a counterexample to full summed EL or to Ramsey

There are two important qualifications.

First, the constructed orbit is a specially selected, low-entropy collection of outer parities, not the full capacity-weighted sector ensemble. For example its number of different pinned parities is at most the size of the symplectic group, which is at most `2^(n^2)`. By contrast, the audited residual-block count gives at least `B^m` integral unlinked parity packings, with `log B=Omega(kb)` at fixed large `C`. Thus this orbit alone does not supply a significant lower bound on the weight of bad sectors in the full ensemble. The large `Mq_A^r` of the full graph is not being attributed to this small orbit. In particular no promised post-DRC min-entropy bound is falsely asserted for the orbit law.

Second, the same symplectic host explicitly contains an original `Q_d`. Since `d` is odd, take an even base space of dimension `d+1`, put a zero in its last coordinate, and use the quadratic lift (2.15)–(2.17) with one further symplectic pair. This embeds `Q_d` in a symplectic subspace of dimension `d+3<=n` for `s>=3`. Distinct source strings have distinct first `d` coordinates, and every cube edge has pairing one. This is an original injection, not an auxiliary one.

Therefore a successful global selection can escape the bad sectors. This work does not prove the estimate ensuring that it does. In particular, it supplies neither EL nor a counterexample to the correctly sector-capped **full** sum in the pressure program.

### Full-chain conclusion

The chain actually justified by the audited inputs ends at ordinary auxiliary embedding and deletion-only original capacity. This report proves that its next two tempting steps are false:

1. round any integral outer parity with huge opposite block lists and zero ordinary DRC defect;
2. replace sector-adaptive original capacities by simultaneous common vertex/edge prices on a mixture of those parities.

The specific remaining task is to obtain a lower bound for the full DRC-selected sum with **sector capacities already imposed**, retaining the overlapping source constraints. Neither (1.2), the surplus, nor the exact finite budget optima proved here provide such a lower bound. No uniform-`C` Ramsey argument follows from this attempt.

---

## 7. Exact verification and integrity

Run from `/workspace/leanproject`:

```sh
python3 -u Submission/check_cube_conflict_drc.py
```

The recorded output is `Submission/CubeConflictDRCVerification.txt`. All checks pass.

The checker performs the following exact audits, without constructing an exponentially large host adjacency matrix.

* On the 16-vertex symplectic host, all 15 transvections preserve all pairings; their generated nonzero-vertex and oriented-edge orbits have sizes 15 and 120. This audits the symmetry and flux arithmetic used in the proofs.
* The full-root-neighborhood counting lemma is audited on all 4,096 small first-parity assignments (`k=2`): 3,906 are good, and all 15,624 affine right-hand sides have the claimed 16 solutions and valid sequential avoidance counts. This checks the linear algebra of (2.27)–(2.29), not the size of a materialized large common neighborhood.
* At `k=4,s=3`, hence `d=17,r=13,N=4,194,304,C=32`, it constructs all **4,096 pairwise original-disjoint** even `Q_4` blocks and all **65,536** tag-defined common-neighbor blocks.
* It constructs a genuine injective auxiliary `Q_13`, checks all **851,968** outer matching-coordinate edges and adjacent-block disjointness, and checks two distinct disjoint DRC roots. Every affine-basis constraint system is checked.
* The complete residual original pool has **1,008 vertices for 65,536 required slots**, a Hall deficit of **64,528**. The particular chosen odd blocks use only 28 original vertices. Their maximum original multiplicity is 4,096. Every relaxed row list has 506 entries.
* It also verifies an explicit original injective `Q_17` in the same host, so the diagnostic is demonstrably not a cube-free graph or a Ramsey counterexample.
* A small exact row-product audit tests the min–sum/Jensen algebra against 81 rational simultaneous penalty vectors and checks the sector-adaptive vanishing-cap identity exactly. This finite toy checks the algebra; the all-dimensional symplectic min–sum result is proved in Section 5, not inferred from a numerical optimization.
* There are **765 exact parameter audits** at three fixed constants and even dimensions `4<=k<=512`; 762 also meet `3k>=2s` and thus have the capacity obstruction. These check density, strict flux slopes, collision errors, the actual injective auxiliary surplus, the upper bounds in (2.30), and the ordinary DRC threshold using integers and rationals, not materialized exponential-size counts.
* For `C=8192`, even `k>=6` in that audit, the rational bound in (2.7) is at most `3.41107287178e-08`; the proof shows it tends to zero. The finite loop is not used as a proof for all dimensions.

`python3 -m py_compile Submission/check_cube_conflict_drc.py` also succeeds. No Lean formalization was attempted and no theorem with `sorry` was used as a premise.

The unchanged `Submission/Spec.lean` SHA-256 is

```
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```

The three read-only input report hashes were unchanged during this work:

```
CubeHigherBlockCapacity.md:
7ecd42fb32cd8df7603d290d15fe7b20c17aca4f0cf8bcb56b3102edf60232c3
CubeEdgePressureProgram.md:
aa5c8b275afff40cbf99a0124bd3fec1a7b6d7be19b68de8fb84e685c0848edb
CubeEdgePressureResolutionAttempt.md:
94c4fe5148ea5d5f51db57dd106de61c6604d2b653385416d2e8f0e51482c540
```
