# EL with actual edge-fugacity minimizers: focused resolution attempt

## Status and scope

**Summed EL remains unproved and unrefuted. No Ramsey claim is made.** I use the correction in the request: `A=A_lambda*` may be assumed to be an **actual finite minimizer of `Phi_(k+1)` for a majority host G**, not merely a kernel satisfying the oriented flux bound. `Spec.lean` is unchanged.

The proved results below are:

1. An exact finite-perturbation/maximum-entropy characterization of this additional hypothesis.
2. An integral/full-pattern and an entropy-chain-rule reformulation of the remaining global pressure problem, without stability of mixtures.
3. An explicit family satisfying **all the corrected EL hypotheses**, with unique minimizer `lambda*=0` and `(k+1)Delta_k -> 0` exponentially fast, but possessing initially feasible pinned sectors whose **capacity correction alone diverges**. An exact minimum-cost matching formula quantifies the divergence.
4. Those affine pinned sectors have total initial normalized pressure weight at most `exp(-Omega(kh))`. Thus their failure does **not** constitute a counterexample to summed EL. It rigorously rules out a sectorwise price-to-edge-direction/norm-gap implication, including under actual optimality.

The unresolved point is still a **global, pressure-weighted** lifting statement. None of the calculations below supplies it.

## 1. What actual minimization supplies, exactly

Fix `j=k+1`, `e=e_j`, and the finite set `Omega=Hom(Q_j,G)`. Let `M=(M_a)_(a in E(G))` be the host-edge multiplicity vector, `nu=nu_j^(lambda*)`, and `mu=E_nu M`. All multiplicities here count repeated source images.

For every finite feasible displacement `xi`, meaning `lambda*+xi>=0`,

\[
\begin{split}
\Phi_j(\lambda^*+\xi)-\Phi_j(\lambda^*)
&=\frac1e\log\mathbb E_\nu e^{-\xi\cdot M}
       +\alpha\sum_a\xi_a\\
&=\frac1e\log\mathbb E_\nu e^{-\xi\cdot(M-\mu)}
       +\sum_a\xi_a(\alpha-\mu_a/e).                 \tag{1}
\end{split}
\]

The first term on the second line is nonnegative by Jensen. Under the full KKT certificate, the second is nonnegative too: on active coordinates its coefficient is zero; on inactive coordinates `xi_a>=0` and its coefficient is nonnegative. Conversely, optimality implies this certificate by differentiation.

**Consequently finite optimality is equivalent to the full flux plus complementary-slackness certificate.** It is stronger than EL's oriented-flux bullet alone, but all its finite-perturbation optimality inequalities follow from (1) and KKT. In particular, replacing a derivative argument by a finite edge perturbation does not evade the need to construct a valid lift of the sector information.

There is also an exact entropy dual:

\[
 b_j\log N+e_jc_j
 =\max\{H(\rho):\rho\in\mathcal P(\Omega),\quad
           \mathbb E_\rho M_a/e_j\le\alpha\ \forall a\}.       \tag{2}
\]

Indeed Gibbs' inequality gives
`H(rho)<=log hom(Q_j,A_lambda)+lambda dot E_rho M`;
feasibility bounds this by `b_j log N+e_j Phi_j(lambda)`.
At `lambda*`, the law `nu` attains equality by complementary slackness.
An optimality contradiction through this dual must produce an **actual small-cube law with the edge budgets**, and with entropy exceeding (2). Sector-dependent row marginals are not such a law.

## 2. The global pressure problem after removing the rounding issue

Put `m=h/2` and `gamma=rh/(2e_(k+1))`. The sandwich (S) in the program gives

\[
 \left|\big(\log\widehat Z_0-\log\widehat Z_T\big)
             -\big(\log Z_0-\log Z_T\big)\right|\le m.       \tag{3}
\]

So proving integral EL and proving capped EL are equivalent up to adding `1/2` to `L`. The `exp(m)` rounding loss is not the outstanding obstacle.

### Full-pattern formulation

Sample an actual global injection with probability proportional to its internal `A` weights (`Z_0` law). Independently on each outer edge, mark a defect with probability `1-A` at its host pair. If `S` is the total number of defects, then exactly

\[
                 Z_T/Z_0=\mathbb E e^{-TS}.                 \tag{4}
\]

Similarly, sample a proper homomorphism `Q_(k+1)->K_N` uniformly, mark all its edges with those probabilities, and let `S'` count the marks. Then

\[
 t_{k+1}(K_T)/t_{k+1}(K_0)=\mathbb E e^{-TS'}.               \tag{5}
\]

For `0/1` kernels these are ordinary counts of bad edges. For weighted kernels they are the positive full-pattern expansions of `A+exp(-T)(1-A)`. The global sample space in (4) consists of **injections**, not independent blocks with their collisions ignored. No stability assertion is made about either summed polynomial.

The missing estimate is consequently the log-Laplace comparison

\[
 -\log\mathbb E e^{-TS}
       \le-\gamma\log\mathbb E e^{-TS'}+O_K(h),\qquad T\ge0.  \tag{6}
\]

### What an entropy chain rule does, and does not, remove

For a pinned sector with nonzero uncapped row product define

\[
 u_{f,T}=\prod_y\sum_{v\in X_f}c_{f,T}(y,v),\qquad
 \delta_{f,T}=\log u_{f,T}-F_{f,T}\in[0,\infty].
\]

Set `U_T=sum_f u_(f,T)` and `pi_T(f)=u_(f,T)/U_T`, omitting zero terms. Then

\[
 \log U_T-\log\widehat Z_T
 =-\log\mathbb E_{\pi_T}e^{-\delta_{f,T}}
 =\inf_\omega\{D(\omega\Vert\pi_T)+\mathbb E_\omega\delta_{f,T}\}. \tag{7}
\]

This is the finite Gibbs variational identity, allowing infinite costs. It already permits abandoning bad sectors. In particular, the global capacity cost is **not** the average of the sector costs under an arbitrarily retained sector distribution.

For the integral partition, Gibbs' identity likewise gives

\[
 \log Z_0-\log Z_T
 =\inf_\rho\{D(\rho\Vert\rho_0)+\mathbb E_\rho C_T\},\qquad
 C_T(\phi)=-\sum_{a\ {\rm outer}}\log K_T(\phi(a)).          \tag{8}
\]

Disintegrating relative entropy over the pinned parity gives both a sector-selection term and a conditional-extension term. Neither (1), (2), nor the known small-cube KL comparison bounds their sum by the right side of (6). A construction accomplishing that bound, rather than simply averaging column prices, is the required entropy lift.

## 3. A diagnostic with an actual, unique minimizer

Take **even** `k>=2` and set

\[
 d=4k,\quad n=5k+2,\quad b=2^k,\quad h=2^d,\quad
 N=2^n=4bh,\quad r=3k.
\]

Let `V=F_2^n` with its nondegenerate alternating form `B`, and use the simple graph

\[
                         A(x,v)=1_{\{B(x,v)=1\}}.           \tag{9}
\]

The zero vector is isolated; the diagonal is zero. Every nonzero vertex has degree `N/2`, so

\[
 |E(G)|=N(N-1)/4,\qquad p(A)=(N-1)/(2N)\ge15/32.
\]

This is exactly a majority colour: it has half the edges of `K_N`.

The symplectic group is transitive on ordered pairs with `B(x,v)=1`. Hence at `lambda=0`, for **every** cube dimension,

\[
 \Pr(\phi(u)=x,\phi(v)=z)=\frac2{N(N-1)}
 \quad\text{on each oriented host edge},\qquad
 \mathbb E M_a/e_j=1/|E(G)|.
\]

For `K>=64`, `alpha>1/|E(G)|`. Applying Jensen to the first line of (1), now at zero, proves for every `lambda>=0`

\[
 \Phi_j(\lambda)-\Phi_j(0)
       \ge(\alpha-1/|E(G)|)\sum_a\lambda_a.                 \tag{10}
\]

Thus **zero is the unique finite minimizer**, not merely a stationary point. Every nonzero feasible host-edge penalty increases the objective.

### A quantitative small-norm-gap bound

Here is a useful direct bound, avoiding any assumption about conditional flux. For `n>=2j`,

\[
 \log p(A)\le\log a_j(A)
       \le-\log2+\frac1{j^2}\log(1+4\,2^{2j-n}).           \tag{11}
\]

For the upper bound, independently sample the images of one cube parity. An opposite vertex has allowed proportion `q<=2^(-R)`, where `R` is the rank of its `j` sampled neighbours. Each sampled variable appears in exactly `j` such factors. The read-`j` form of Hölder (Finner's inequality) gives

\[
 t_j(A)\le(\mathbb E q^j)^{2^{j-1}/j}.
\]

For the rank defect `ell=j-R`, a union bound over `ell`-dimensional subspaces of the kernel of a random `n` by `j` matrix gives

\[
 \Pr(\ell\ge l)\le4\,2^{-l(n-j+l)}.
\]

(The Gaussian binomial coefficient is at most `4*2^(l(j-l))`.) Summing tails,

\[
 \mathbb E2^{j\ell}
 \le1+4\sum_{l\ge1}2^{-l(n-2j+l)}
 \le1+4\,2^{2j-n}.
\]

This proves the upper bound in (11); the lower bound is cube Sidorenko. Therefore in this family

\[
 0\le(k+1)\Delta_k(A)
 \le\frac{\log(1+4\,2^{-3k})}{k+1}
       -(k+1)\log(1-2^{-(5k+2)})\longrightarrow0.          \tag{12}
\]

The surplus hypothesis also holds. Weak norming gives `q_k>=a_k^b`, whence

\[
 \log(N^b t_kq_k^r)
 \ge b\big[(3k/2+2)\log2+(7k/2)\log(1-1/N)\big]
 \ge 2\log h+kb/10.                                      \tag{13}
\]

For the last inequality: `log(1-1/N)>=-2/N`; for `k>=4`, `8k/2^k<=2`, leaving a margin at least `k(1.5 log 2-0.1-7/N)>0` after division by `b`. The case `k=2` has positive margin by the same elementary bound.

For any proposed positive universal `epsilon_0` and any fixed `C_0(K)`, sufficiently large even `k` satisfies (12) and `N/h=4b>=C_0(K)`. Thus this family genuinely meets **every corrected EL hypothesis**.

## 4. Initially feasible sectors with unbounded capacity excess

Choose coordinates in which `B` pairs consecutive coordinates. Let `W` be the span of the first `d` coordinates and

\[
 H=\{w\in W:w_0=1\},\qquad |H|=m=h/2.
\]

For the even source parity `E`, define the affine bijection

\[
 f(x)=e_0+\sum_{i=0}^{d-2}x_i e_{i+1},\qquad x\in E.       \tag{14}
\]

For every odd source vertex `y`, its `d` neighbours form an affine basis of `E`; their images form an affine basis of `H`. Thus the **full** endpoint list is the same at every row:

\[
 L=\{v:B(w,v)=1\ \forall w\in H\}=e_1+W^\perp,
       \qquad s:=|L|=2^{n-d}=4b.                          \tag{15}
\]

Also `L` is disjoint from `H`. Since `s<m`, these identical lists fail Hall.

This sector is nevertheless strictly feasible at `T=0`. Its `k` internal neighbours give `k` independent linear constraints, so each untrimmed internal list has size `2^(n-k)=4h`. After removing `H`, each list has at least `4h-m>m` entries. Uniform row distributions therefore give every column load less than one. In the specified coordinates their common list size is exactly

\[
                      L_0=4h-2^{r-1},\qquad F_{f,0}=m\log L_0. \tag{16}
\]

For finite `T` the support is unchanged, so the capped problem remains feasible. On an allowed internal-list entry write `c_(f,T)(y,v)=exp(-T j_y(v))`, where `j_y(v)` counts the failed outer constraints. We have `j_y(v)=0` exactly for `v in L`. Every feasible capped array must send at least `m-s` total mass outside `L`, so

\[
 F_{f,T}\le m\log(N-m)-(m-s)T.                             \tag{17}
\]

By contrast, the **uncapped** row product has the finite nonzero limit

\[
                 \log u_{f,T}\longrightarrow m\log s.
\]

In particular,

\[
 \delta_{f,T}\ge(m-s)T-m\log((N-m)/s)\longrightarrow\infty. \tag{18}
\]

This is not just a row becoming empty. All limiting rows have `s` allowed entries; the divergence is specifically a **column-capacity cost**. Meanwhile the small-cube pressure on EL's right side has a finite limit, because `t_(k+1)(A)>0`.

Equations (10), (12), and (18) rigorously refute a **sectorwise** version of “large integrated capacity excess yields a decreasing host-edge penalty or a norm gap.” They do not refute its proposed **summed, pressure-weighted** version.

## 5. Exact cost of this sector, retaining the whole pattern

The example has a closed finite matching calculation. For a host column permitted in any row, its number `j` of failed outer constraints is independent of the permitted row. There are

\[
 n_0=s,\qquad
 n_j=2\left[s\binom{r-1}{j}+(s-1)\binom{r-1}{j-1}\right],
                       \quad1\le j\le r,                 \tag{19}
\]

columns of cost `j`. Each zero-cost column is accessible to all `m` rows; every other column is accessible to exactly `m/2` rows. Each row accesses `n_j/2` columns of each positive cost.

To check (19), write the restriction of `B(-,v)` to `W` as `(t_0,a_0,...,a_(d-2))`. The internal constraints require the first `k` entries of `a` to have a common value `t`. The cost is

\[
                 j=t+|\{i\ge k:a_i\ne t\}|.
\]

For nonzero `a`, each of the two `t_0` values is allowed in half the rows. A restriction has `s` lifts to `V`. Exactly one lift lies in `H` when `t=1`, and none does when `t=0`. The exceptional `a=0` gives the `s` zero-cost columns (the other `t_0` is never permitted). This proves all the stated incidences.

Let `J` be the first index with `sum_(j=0)^J n_j>=m`. The exact minimum number of bad outer edges in an injective extension is

\[
 C_{\min}=\sum_{j<J}j n_j
           +J\left(m-\sum_{j<J}n_j\right).                \tag{20}
\]

The lower bound is the cost of the `m` cheapest columns. For equality, fill those cost levels to column load one, using a common partial load at the last level. Distribute a zero-cost column's load uniformly over all rows, and every other column's load uniformly over its `m/2` permitted rows. The incidences above make every row sum one. Matching-polytope integrality gives an actual minimum-cost injection. No product-mixture stability is used.

Entropy is bounded on this finite polytope, hence

\[
                \lim_{T\to\infty}-F_{f,T}/T=C_{\min}.
\]

Moreover,

\[
              r/2-4\sqrt r\le C_{\min}/m\le r/2.           \tag{21}
\]

For the lower bound, use `n_j<=2s binom(r,j)` and
`E[(r/2-X)_+]<=sqrt(r)/4` for `X~Bin(r,1/2)`, noting `2s*2^r=16m`. The uniform feasible array at `T=0` gives the upper bound (its mean cost is actually `r/2-1/(4s-2)`). Thus the sector's asymptotic capacity-pressure rate is `(1/4+o(1))*rh`, although (12) is exponentially small.

One can also compute its whole capped entropy without a numerical LP. Put `R_0=m`, `R_j=m/2` for `j>0`, and choose `u` so that

\[
 \gamma_j=\min\{1,R_j e^{u-jT}\},\qquad\sum_j n_j\gamma_j=m.
\]

The KKT solution is uniform on each column's permitted rows, and

\[
 F_{f,T}=-m u+\sum_jn_j\max\{0,u+\log R_j-jT\}.             \tag{22}
\]

For `k=2,d=8,n=12`, the exact data are

```
N=4096, h=256, m=128, s=16, L0=992
(n_0,...,n_6) = (16,190,470,620,460,182,30)
C_min = 112.
```

## 6. Why this is not a counterexample to summed EL

There are at most `N^d` affine injections from the `(d-1)`-dimensional source parity into `V`. If their image contains zero they have no internal extension. Otherwise their image is an affine hyperplane in its `d`-dimensional span, so the endpoint lists again coincide in a set of size `s`. Each such sector has initial weight at most `(4h)^m`.

Here is a quantitative bound on their **summed** initial weight. Let `H_k=hom(Q_k,A)`. The small-cube law is uniform at each source vertex on `V\{0}`. For any used set of size at most `h`, the probability a block hits it is at most

\[
                         bh/(N-1)<1/3.
\]

The block collision probability is at most

\[
 \binom b2/(N a_k(A)^k)\le b^3/N=1/(4b^2).
\]

For completeness, the first bound on collisions follows by dropping the `k` edges at one identified vertex and applying weak norming to the remaining subgraph: the relative count for a specified identification is at most `1/(N a_k^k)`. Adjacent identifications contribute zero. Since `p(A)^k>=1/(2b)`, the displayed estimate follows.

Therefore at least `H_k/2` ordered block maps remain injective and unused after every prefix of a packing. Consequently

\[
 Z_0\ge(H_k/2)^{h/b}
       \ge2^{-h/b}N^h p(A)^{kh/2}.
\]

Writing `mathcal A` for all those affine sectors, (S) gives

\[
 \frac{\sum_{f\in\mathcal A}e^{F_{f,0}}}{\widehat Z_0}
 \le\frac{N^d(4h)^m2^{h/b}}{N^h p(A)^{kh/2}}
 \le\exp\left(-[(5/2)k+1]h\log2+O(k^2+h/b)\right).         \tag{23}
\]

The same upper bound holds for their probability under the uncapped initial sector law. Discarding this entire family at time zero costs only `-log(1-P(mathcal A))`, not its enormous conditional capacity loss. No control of the later sector distributions is asserted here.

Thus this diagnostic establishes a genuine limitation on **local lifting**, while deliberately not pretending that a rare bad boundary proves a global obstruction. In particular, I have not proved that these hosts violate (6) or EL.

## 7. Exact remaining gap

The attempted routes stop at the following specific points.

* **Host-edge perturbations:** (1) is complete. One must extract an actual small-cube entropy/edge-budget violation from the **global excess**, not from a conditional capacity optimizer. The example shows that such an implication cannot hold sector by sector, even with actual optimality and arbitrarily small norm gap.
* **Entropy chain rules:** (7) and (8) account correctly for changing sectors. An `O_K(h)` upper bound for the optimal combined sector-selection and conditional-extension cost has not been obtained. Small-cube KL does not give it after pinning.
* **Quantitative Hölder/reflection:** (11)--(12) make a norm-gap-only response to conditional capacity excess impossible in this family. A useful inverse-Hölder theorem must also control which sectors carry the summed pressure. No such theorem is established here.
* **Global interpolation/full patterns:** (4)--(6) keep the actual integral partition throughout. Positivity of the pattern coefficients supplies neither the necessary log-Laplace ordering nor an `O_K(h)` bound on its failure.

Accordingly, there is **no complete proof of EL and no structural counterexample to EL for actual minimizers in this report**. The exact new diagnostic is a counterexample only to the sectorwise lifting alternative. The original Ramsey task remains unresolved.

## Verification

Run:

```
python3 Submission/check_cube_edge_pressure_resolution.py
```

The recorded output is `Submission/CubeEdgePressureResolutionVerification.txt`. It checks:

* Exact `Q_3` counts on the 16-vertex symplectic host: `hom=1,983,360`, and all 120 oriented host edges have identical rooted count `16,528`.
* The independent `C_4` trace formula, an integer small-norm monotonicity comparison, and 56 exact random-matrix rank distributions checking the tail/moment inputs to (11).
* All row/column incidences of (14)--(19) for `k=2`, and a genuine integer minimum-cost assignment attaining (20), cost `112`.
* The explicit entropy formula (22), the small-gap upper bound and the surplus lower bound at several scales. These numerical evaluations audit formulas; they do not prove the asymptotic claims or summed EL.

`Spec.lean` SHA-256 remains
`9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`.
