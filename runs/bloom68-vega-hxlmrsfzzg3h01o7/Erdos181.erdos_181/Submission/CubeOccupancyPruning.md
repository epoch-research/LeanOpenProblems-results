# Cube occupancy counting: a rigorous entropy replacement and a pruning obstruction

## Status

**No proof or disproof of a uniform bound `R(Q_d) <= C 2^d` is obtained.** In particular, the positive absolute injective baseline in the question is neither proved nor refuted.

Two conclusions below are proved:

1. A capacitated, conditional Shannon-entropy functional approximates the actual injective count within a factor `exp(h/2)`. This is an application of the permanent entropy bound, not a new proof of Sidorenko with hard occupancy constraints. The remaining lower bound on this functional is explicitly unproved.
2. There are two-colour, regular, quasirandom symplectic blow-ups whose mesoscopic monochromatic bicliques cover almost all edges uniformly. An exact inequality shows that deleting `o(N^2)` edges, or removing that much edge weight, cannot reduce their collapsed homomorphism contribution to within `exp(O(h))` of the random baseline. In fact the same obstruction holds relative to the retained principal-edge density for every nonzero retention. This is a statement about pruning host edges, not about cancellation or directly pruning configurations.

No assertion is made here that the injective count in these algebraic examples is near the random baseline. Without an upper bound on that count, the examples do not themselves disprove a hom-to-injective ratio for the pruned graph. No Lean files, including `Spec.lean`, were modified.

Throughout, `d>=1`, `h=2^d`, `m=h/2`, and `e=dh/2`; the injective-counting statements assume `N>=h`. Counts are labelled; copies are ordinary, not induced. Logarithms are natural unless labelled `log_2`.

## 1. An exact-to-exp(m) microcanonical entropy functional

### 1.1 Rectangular permanent entropy

For a zero-one matrix `A` with `m` rows and `n>=m` columns, let `per_m(A)` count assignments of its rows to distinct columns using only entries equal to one. Define

\[
\mathcal E(A)=\max_q\sum_{i=1}^m H(q_i),
\]

where

\[
q_{ij}\ge0,\qquad \sum_jq_{ij}=1,\qquad
\sum_iq_{ij}\le1,\qquad q_{ij}=0\text{ if }A_{ij}=0.
\]

If the feasible set is empty, set `E(A)=-infinity` and `exp(E(A))=0`. Then

\[
\boxed{e^{-m}\exp\mathcal E(A)\le\operatorname{per}_m(A)
       \le\exp\mathcal E(A).}                                      \tag{1}
\]

The upper bound is entropy subadditivity applied to a uniformly random valid assignment: its row marginals are feasible and its joint entropy is `log per_m(A)`.

Here is a proof of the lower bound, including the rectangular correction. The standard square permanent entropy bound is

\[
\operatorname{per}(D)\ge {n!\over n^n}
 \exp\left(\sum_{ij}B_{ij}\log{D_{ij}\over B_{ij}}\right)             \tag{2}
\]

for any nonnegative square matrix `D` and any doubly stochastic `B` supported on `D`. For positive `D`, matrix scaling and the van der Waerden permanent theorem prove (2): the entropy maximizer is a doubly stochastic scaling of `D`. General `D` follows by replacing it with `D+epsilon J` and taking a limit.

Append `n-m` all-one rows to `A`, obtaining `D`; then `per(D)=(n-m)! per_m(A)`. Given feasible `q`, write `u_j=1-sum_i q_ij`, so `0<=u_j<=1` and `sum_j u_j=n-m`. Extend `q` to a doubly stochastic matrix by putting `u_j/(n-m)` in each new row. If `n>m`, (2) gives

\[
\operatorname{per}_m(A)\ge
 {n!(n-m)^{n-m}\over n^n(n-m)!}
 \exp\left(\sum_iH(q_i)-\sum_j u_j\log u_j\right).
\]

The slack term is nonnegative. The prefactor is at least `exp(-m)`: the sequence

\[
a_t=\log(t!)-t\log t+t,\qquad a_0=0,
\]

is increasing, since `a_(t+1)-a_t=1-t log(1+1/t)>0` for `t>=1`, and `a_1>a_0`. The case `n=m` follows directly from (2). Maximizing over `q` proves (1). This also proves positivity whenever the displayed fractional constraints are feasible.

### 1.2 Application to the cube

Fix its two parity classes `X,Y`, each of size `m`. For a colour `c` and an injection `f:X -> V(K_N)`, form an `m` by `N-m` zero-one matrix `A_(c,f)`, with rows `y in Y`, columns `v notin f(X)`, and

\[
 A_{c,f}(y,v)=1
 \quad\Longleftrightarrow\quad
 vf(x)\text{ has colour }c\text{ for every }x\in N_{Q_d}(y).
\]

Let

\[
 S_c=\sum_{f:X\hookrightarrow V(K_N)}\exp\mathcal E(A_{c,f}).
\]

There is the exact identity `I_c=sum_f per_m(A_(c,f))`. Consequently,

\[
\boxed{e^{-h/2}(S_R+S_B)\le I_R+I_B\le S_R+S_B.}                  \tag{3}
\]

There is no comparison with the unrestricted homomorphism partition function in (3), and no injective reflection Cauchy--Schwarz assertion. All collisions are excluded in its definition: first on `X`, then between the two parity classes, and then within `Y` through the column capacities.

Equivalently, `log(S_R+S_B)` is the maximum of

\[
 H(c,f)+\mathbb E_{c,f}\sum_{y\in Y}H(q_{c,f,y})                   \tag{4}
\]

over laws on colour-injection pairs and feasible row distributions **conditional on each `(c,f)`**. This is the usual log-sum-exp entropy variational identity.

**Unproved remaining assertion.** To obtain the requested baseline, it would suffice to prove, for absolute `C,K` and `N=ceil(C h)`,

\[
 \log(S_R+S_B)\ge\log (N)_h+(1-e)\log2-Kh.                      \tag{5}
\]

It would give the desired injective lower bound with loss `exp(-(K+1/2)h)`. But (5) is not established. Indeed, even proving `S_R+S_B>0` at a fixed absolute multiplier `C` is equivalent, by (3), to the Ramsey existence assertion. Thus (3) is a quantitatively controlled reduction, not a decisive existence theorem. Feasibility here is conditional, not merely a bound on unconditional expected occupancies; replacing it with the latter changes the problem.

## 2. A deletion-robust family of collapsed phases

### 2.1 Construction

Take `d=5k`, `h=2^(5k)`, and a symplectic vector space

\[
 V=\mathbb F_2^{4k},\qquad M=|V|=2^{4k},
\]

with nondegenerate alternating form `B`. Put `r=2k`, and choose a symplectic basis `e_1,...,e_r,f_1,...,f_r`. Replace each nonzero vector by `L` clones, where

\[
 L=\left\lceil {C h\over M-1}\right\rceil,\qquad N=L(M-1)=(C+o(1))h.
\]

Between distinct host vertices with base labels `x,y`, colour the edge red if `B(x,y)=0` and blue if `B(x,y)=1`. In particular, edges within a clone class are red.

Both colours are regular. Their degrees are

\[
 d_B=LM/2,\qquad d_R=L(M/2-1)-1.
\]

They are quasirandom with densities tending to `1/2`. Indeed the full `M` by `M` matrix `H_xy=(-1)^{B(x,y)}` satisfies `HH^T=MI`. Let `H_0` be its restriction to nonzero labels. The signed off-diagonal colour matrix of the clone graph is

\[
 H_0\otimes J_L-I_N,
\]

whose operator norm is at most `L sqrt(M)+1=o(N)`. This gives the uniform cut-discrepancy bound `o(N^2)`.

### 2.2 Uniform biclique covers of the principal edge orbits

Call edges between different nonzero base labels principal. For each colour the symplectic group, together with clone permutations, is transitive on its principal edges. For red this follows by extending an ordered independent orthogonal pair to a symplectic basis; for blue, extend a pair with pairing one. Over `F_2`, distinct nonzero vectors are linearly independent.

The numbers of principal edges are

\[
 E_R^0={L^2(M-1)(M-4)\over4},\qquad
 E_B^0={L^2M(M-1)\over4}.                                      \tag{6}
\]

Each is `(1/4+o(1))N^2`. Only the within-clone red edges are nonprincipal, and there are `o(N^2)` of them.

There are principal monochromatic bicliques with side sizes

\[
 s_R=L2^{r-2},\qquad s_B=L2^{r-1}=2s_R.                          \tag{7}
\]

Explicitly, before cloning, use the following pairs of affine sets:

* Red: `e_1+U` and `e_2+U`, where `U=span(e_3,...,e_r)`.
* Blue: `e_1+W` and `f_1+W`, where `W=span(e_2,...,e_r)`.

The first pairing is always zero and the second always one. The two sets in each pair are disjoint and avoid zero. For fixed `C`, both have `2s_c<h` for all sufficiently large `k`, since `s_c=Theta_C(h^(3/5))`.

### 2.3 The exact pruning inequality

Let `w` be any retained nonnegative edge weighting in colour `c`, with `0<=w_e<=1`. Let

\[
 q_c={1\over E_c^0}\sum_{e\in E_c^0}w_e.
\]

A uniformly random group image of the biclique in (7) has average retained cross-edge weight with expectation exactly `q_c`, by edge transitivity. Some image therefore has cross-edge density at least `q_c`.

Apply the rectangular, part-respecting cube Sidorenko inequality to that weighted bipartite graph. All maps counted there have image in its `2s_c<h` vertices. Thus, if `Z_<h(Q_d,w)` denotes the total weight of homomorphisms with image size less than `h`,

\[
\boxed{Z_{<h}(Q_d,w)\ge s_c^h q_c^{e}.}                         \tag{8}
\]

This holds for every retention, not just for a typical deletion.

In particular, deleting `o(N^2)` edges or that much edge weight gives `q_c=1-o(1)` in **each** colour. Since

\[
 {s_R\over N}={2^{2k-2}\over 2^{4k}-1},\qquad e/h=5k/2,
\]

(8) implies

\[
\boxed{
 Z_{<h}(Q_d,w)\ge N^h2^{-e}
       \exp\big((1/10-o(1))h\log h\big).
}                                                              \tag{9}
\]

It also holds with `N^h` replaced by the smaller `(N)_h`. This is much larger than the absolute random baseline times `exp(O(h))`.

More quantitatively, to make the right side of (8) at most `N^h 2^(-e) exp(Kh)` for fixed `K`, it is necessary that

\[
 1-q_c\ge 1-2^{-1/5}-o(1).                                    \tag{10}
\]

So a positive fraction of the principal edges must lose their weight. Equivalently, the removed weight must be at least

\[
 \left({1-2^{-1/5}\over4}-o(1)\right)N^2.
\]

There is an even stronger density-adjusted version. Put

\[
 p_c^0=2E_c^0/N^2,\qquad p_w^0=2\sum_{e\in E_c^0}w_e/N^2=q_cp_c^0.
\]

For any `q_c>0`, (8) says

\[
 {Z_{<h}(Q_d,w)\over N^h(p_w^0)^e}
 \ge (s_c/N)^h(p_c^0)^{-e}
 =\exp\big((1/10)h\log h-O(h)\big).                            \tag{11}
\]

The factor is independent of the retained density. For red, (11) uses the retained **principal-edge** density; for blue all edges are principal.

To obtain exactly `ceil(C h)` host vertices, rather than `(C+o(1))h`, delete fewer than `M-1=o(N)` vertices from the displayed construction. Regard incident edges as an additional `o(N^2)` deletion when applying (8). Cube homomorphisms cannot use these isolated deleted vertices, because the cube has no isolated source vertices. Hence (9) survives, as does quasirandomness of the restricted two-colouring. The exact transitivity statements and (11) refer to the untrimmed construction.

### 2.4 These are not Ramsey counterexamples: both colours contain cubes when C>=4

For completeness, the unpruned examples have an explicit ordinary `Q_d` in **both** colours for `C>=4`. This verifies directly that the large collapsed mass is not, by itself, an obstruction to containment.

Put `D=4k-2` and

\[
 q_0(x)=\sum_{j=1}^{D/2}x_{2j-1}x_{2j},\qquad
 q_c(x)=q_0(x)+c\sum_i x_i\quad(c\in\mathbb F_2).
\]

Let `B_0` be the polar form of `q_0`. On `F_2^D direct-sum F_2^2`, take the nondegenerate alternating form

\[
 \widetilde B((x,a,b),(y,a',b'))=B_0(x,y)+ab'+ba'.
\]

This space is symplectically isomorphic to `V`. The injective map

\[
 \Phi_c(x)=(x,q_c(x),1)
\]

uses only nonzero vectors and satisfies

\[
 \widetilde B(\Phi_c(x),\Phi_c(y))=q_c(x+y).
\]

If `x,y` are adjacent in `Q_D`, this is `c`. Thus the base graph contains a red and a blue `Q_D`.

A blow-up of `Q_D` with at least `2^(d-D)` clones per vertex contains `Q_d`: map

\[
 (a,z)\longmapsto a+\Big(\sum_i z_i\Big)e_1,
 \quad a\in\mathbb F_2^D,\ z\in\mathbb F_2^{d-D},
\]

and assign the `2^(d-D)` points of every fibre to distinct clones. Every cube edge projects to a cube edge. Here `2^(d-D)=2^(k+2)`, while `L>=C 2^k>=2^(k+2)` for `C>=4`.

The exact-size trimming described above can also preserve these embeddings: delete at most one clone from each affected base fibre. For `C>=4`, the chosen ceiling gives `L-1>=2^(k+2)`. No assertion is made that arbitrary subsequent edge pruning preserves these particular embeddings, or that their count attains the random baseline.

## 3. Uniform marginals and large Shannon entropy still do not enforce occupancy

The untrimmed regular construction also gives a precise warning concerning a weaker entropy relaxation of (4).

Choose a uniformly random group image of a principal biclique in (7), then map the two cube parity classes independently and uniformly into its two sides. The resulting law `mu_c` has:

* no injective maps, since its image has size at most `2s_c<h`;
* every source-vertex marginal uniform on the `N` host vertices;
* every source-edge marginal uniform on the oriented principal colour edges;
* `H(mu_c)>=h log s_c`, by conditioning on the randomly selected biclique.

For blue these are all the colour edges. For red, mix this law with the law that chooses a uniformly random oriented within-clone red edge and collapses the entire two parity classes onto its endpoints. Use mixture weight equal to the within-clone fraction of all red edges, which is `O(1/M)`. This makes **every source-edge marginal exactly uniform on all red edges**, keeps all source-vertex marginals exactly uniform, and loses only `O(h log h/M)=o(h)` in the entropy lower bound.

Thus in both colours there is a law supported entirely on noninjective homomorphisms satisfying

\[
 H(\mu_c)\ge (3/5)h\log h-O_C(h),\qquad
 \mathbb E_{\mu_c}\big|\phi^{-1}(v)\big|=h/N.
\]

For `C>1` the last quantity is less than one for large `k`, while the usual Sidorenko entropy target is only

\[
 h\log N+e\log p_c=(1/2)h\log h+O_C(h).
\]

Consequently, high entropy, exact uniform edge marginals, and expected per-site loads below one do not together imply any positive injective mass. This does not rule out constructing a different, genuinely hard-capacity witness. In particular, it does not establish or refute (5).

## Verification and inputs

The proofs above use the standard van der Waerden permanent theorem and the established rectangular hypercube Sidorenko inequality. The latter follows from the weakly Holder property in Hatami, *Graph norms and Sidorenko's conjecture*, arXiv:0806.0047, available at `/corpus/src/0806.0047/normFinal.tex`.

As checks of the explicit formulas, exact finite-field computations verified the Hadamard identity, degrees, principal-edge counts, and both displayed bicliques for symplectic half-dimensions `r=2,3,4`. The quadratic embedding identity and its balanced cube-to-cube quotient were checked exactly for `D=2,4,6,8`. These were deterministic checks of already-proved identities, not searches for Ramsey evidence. The asymptotic exponents in (9)--(11) and the rectangular permanent prefactor were verified algebraically in the proofs.

`Submission/Spec.lean` still has SHA-256 `9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`.

## Conclusion

Equation (3) is a valid positive microcanonical counting replacement with exactly the right uniform `O(h)` loss. The unproved part is its baseline estimate (5), not the transfer from that functional to ordinary copies.

Equations (8)--(11) rule out making collapsed mass harmless merely by deleting a negligible density of host edges, even in both regular quasirandom colours. They do not rule out signed cancellation, direct configuration pruning with a separately proved baseline, or an adaptive conditional-capacity argument.

**The original uniform Ramsey conjecture and the proposed absolute injective lower bound remain unresolved by this investigation.**
