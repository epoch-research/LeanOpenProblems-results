# Actual cube-fugacity minimizers: norm-supported survival and an exponential penalty budget

## Status

**No proof of EL or of `R(Q_d)=O(2^d)` is obtained.** This note records two consequences of the actual minimizer not recorded in the input pressure program, and their precise reach in a globally collision-free packing calculation. They concern the actual small-cube law, not a law obtained by transferring its flux certificate through pinning.

The central new calculation is a supporting-functional inequality for the weakly norming cube norm. It gives a multiplicative survival bound after *simultaneously deleting an arbitrary set of original host edges*, even when the usual union bound is vacuous. Complementary slackness also upgrades the linear penalty budget to an **exponential** penalty budget. Neither calculation performs the missing all-sector outer-edge extension.

`Spec.lean` is unchanged; its admitted statements are not used.

## 1. The supporting functional and simultaneous deletion survival

Put `j=k+1`, `e=e_j`, and `A=A_lambda*` as in the program. Write

\[
 \sigma_a=\frac{\mathbb E_{\nu_j} M_a}{e},\qquad
 \sum_{a\in E(G)}\sigma_a=1,\qquad
 \sigma_a\le\alpha=\frac{2K}{N^2}.
\]

All coordinates here are **unordered original host edges**. For `A_a>0`, differentiation gives

\[
 \frac{\partial a_j}{\partial A_a}(A)
       =a_j(A)\frac{\sigma_a}{A_a}.                 \tag{1.1}
\]

Weak norming means that `a_j` on nonnegative symmetric kernels is the restriction of a convex norm. Therefore its tangent on the face supported by `G` is a supporting functional. For every nonnegative kernel `B` supported by `G`,

\[
 \boxed{\quad
 a_j(B)\ \ge\ a_j(A)\sum_{a\in E(G)}
                    \sigma_a\frac{B_a}{A_a}.
 \quad}                                                \tag{1.2}
\]

Indeed, the tangent inequality is
`a_j(B)>=a_j(A)+sum_a partial_a a_j(A)(B_a-A_a)`;
(1.1) and `sum sigma=1` give (1.2). Differentiation is valid because the minimizer is finite, so `A` is strictly positive on the indicated face. No differentiability across a nonedge is needed.

For arbitrary `0<=u_a<=1`, put `B_a=A_a(1-u_a)`. The ratio of hom partitions is an exact generating function for edge multiplicities, including every repeated image:

\[
 \boxed{
 \mathbb E_{\nu_j}\prod_a(1-u_a)^{M_a}
 =\frac{t_j(B)}{t_j(A)}
 \ge\left(1-\sum_a\sigma_a u_a\right)^e.
 }                                                       \tag{1.3}
\]

At zero factors use the polynomial interpretation, including `0^0=1`.
In particular, for *any* original host-edge set `F`,

\[
 \boxed{
 \Pr_{\nu_j}(M_F=0)\ge(1-\sigma(F))^e
                         \ge(1-\alpha|F|)^e
 }                                                       \tag{1.4}
\]

where the last expression is asserted when `alpha|F|<=1`. The first bound always holds. This is not an independence assertion. For comparison, a direct union bound only gives `1-e sigma(F)`, which can be negative while (1.4) remains useful.

If `S` is any original vertex set, let `F_S` be all edges meeting `S`. Since the cube has no isolated vertices, avoiding `F_S` is exactly avoiding `S`. Thus, with `s=|S|` and `2Ks/N<1`,

\[
 \Pr_{\nu_j}(\operatorname{im}\phi\cap S=\varnothing)
       \ge\left(1-\frac{2Ks}{N}\right)^e.              \tag{1.5}
\]

The set `S` can be chosen adversarially: (1.5) holds for every set separately. It is still an **unconditioned** small-cube statement.

## 2. Actual complementary slackness gives an exponential penalty budget

Apply (1.2) to `B=1_G`. On inactive edges `A_a=1`, while on active edges `sigma_a=alpha`. Hence

\[
 \sum_a\frac{\sigma_a}{A_a}
     =1+\alpha\sum_a(e^{\lambda_a^*}-1).
\]

Consequently

\[
 \boxed{
 \alpha\sum_a(e^{\lambda_a^*}-1)
       \le\frac{a_j(1_G)}{a_j(A)}-1
       \le\frac1{a_j(A)}-1
       \le\frac1{p(A)}-1.
 }                                                       \tag{2.1}
\]

This uses the full complementary-slackness certificate; flux alone does not make the displayed exponential sum appear. Under `p(A)>=15/32`, it implies

\[
 \alpha\sum_a(e^{\lambda_a^*}-1)\le\frac{17}{15},
 \qquad
 \lambda_a^*\le\log\left(1+\frac{17}{15\alpha}\right),
 \qquad
 A_a\ge\frac{15\alpha}{17+15\alpha}
       \quad(a\in E(G)).                              \tag{2.2}
\]

In particular, the minimizer cannot assign a super-polynomially small positive weight to a host edge: for fixed `K`, its positive entries are bounded below by a constant times `N^{-2}`. This removes a possible quantitative fugacity problem, **not** the support/injectivity problem. The zeros of `A` remain exactly the nonedges of `G`.

## 3. A full collision-accounted packing bound retaining the optimized norm

Here all normalized hom densities use the original denominator `N`, even after rows and columns are zeroed. Put

\[
 b=2^k,\quad h=2^d,\quad \ell=h/b,\quad
 H_k=\operatorname{hom}(Q_k,A),\quad
 q=t_j(A)/t_k(A)^2.
\]

For `S` let `A^S` be `A` with rows and columns in `S` zeroed, and set

\[
 \theta_S=\sigma(E(G)\setminus F_S),\qquad
 \eta=2Kh/N<1,\qquad u=a_j(A)(1-\eta),
 \qquad \varepsilon=\frac{\binom b2}{N u^j}.
\]

The definitions and (1.2) give

\[
 a_j(A^S)\ge a_j(A)\theta_S
                 \ge a_j(A)(1-2K|S|/N)\ge u
                 \qquad(|S|\le h).                   \tag{3.1}
\]

Dropping the matching between the two `Q_k` faces, using `A^S<=1`, gives the elementary *upper* bound

\[
 t_j(A^S)\le t_k(A^S)^2.
\]

In particular,

\[
 a_k(A^S)^k\ge a_j(A^S)^j\ge u^j,
\]

and

\[
 \operatorname{hom}(Q_k,A^S)
       \ge H_k q^{1/2}\theta_S^{e_j/2}.               \tag{3.2}
\]

### All internal collisions

Let `n=N-|S|` and normalize the residual kernel by `n` temporarily. For any distinct source labels `v,w`, restrict to maps with `phi(v)=phi(w)`, then drop all `k` edges incident with `v`. Their weights are at most one. Weak-norming subgraph Hölder bounds the remaining `Q_k-v` count. Dividing by the original `Q_k` hom count bounds this collision probability by

\[
 \frac1{n\,a_k(A|_{[N]\setminus S})^k}
   =\frac{n}{N^2 a_k(A^S)^k}
   \le\frac1{N u^j}.
\]

Taking a union bound over **all** `binom(b,2)` pairs therefore proves

\[
 \operatorname{inj}(Q_k,A|_{[N]\setminus S})
       \ge(1-\varepsilon)H_k q^{1/2}\theta_S^{e_j/2}.
                                                               \tag{3.3}
\]

No pair type is omitted. Adjacent-label collisions already have weight zero; including them in the union bound is harmless.

### All interblock collisions

Order the `ell` labelled blocks. At stage `i`, exactly `ib` original vertices are already used. Apply (3.3) to that actual set and sum over all preceding packing choices. Provided `epsilon<1`, this gives the genuine integral partition bound

\[
 \boxed{
 Z_0\ge[H_kq^{1/2}(1-\varepsilon)]^\ell
       \prod_{i=0}^{\ell-1}
           (1-2Kib/N)^{e_j/2}.
 }                                                       \tag{3.4}
\]

Every counted configuration is a global injection of all `h` labels. Conversely `Z_0` is precisely the weighted partition of these internally valid, globally disjoint blocks, so the greedy summation addresses the correct partition, not independent blocks with conflicts ignored.

For `epsilon<=1/2`, taking logarithms and using
`-log(1-x)<=x/(1-eta)` gives

\[
 \boxed{
 \log Z_0\ge h\log N+\frac{jh}{2}\log a_j(A)
       -\frac{jK h(h-b)}{2N(1-\eta)}
       -2\ell\varepsilon.
 }                                                       \tag{3.5}
\]

For example `N>=16Kh` ensures `eta<=1/8`. With `p(A)>=15/32`, this gives `u>=105/256>2/5`; for `k<=d/4`,

\[
 \varepsilon\le\frac54\frac{10^k}{2^d}
       \le\frac54\left(\frac{10^{1/4}}2\right)^d\longrightarrow0.
\]

Thus (3.4)–(3.5) apply at the large dimensions in the program. They retain `a_j(A)`, rather than replacing the optimized norm by a bare density lower bound.

## 4. Where the attempted completion stops

Write `delta=j(log a_j(A)-log a_k(A))`. The small-norm increment enters the exact identity

\[
 \log q=b(\log a_k(A)+\delta),\qquad 0\le\delta\le\epsilon_0.
                                                               \tag{4.1}
\]

For example the face-deletion cost `q^{ell/2}` in (3.4) contributes exactly
`(h/2)(log a_k(A)+delta)`. This is an `O(h)` cost, not a missing `O(kh)` face comparison. The accumulated adversarial-deletion cost in (3.5), however, is of order `jKh^2/N`; at fixed `N/h` this is not an `O_K(h)` estimate.

More importantly, (3.4) only treats `Z_0`. No outer compatibility has been imposed. For a pinned full parity `f`, different opposite labels `y` require the different lists

\[
 L_f(y)=\bigcap_{x\sim y}N_G(f(x))\setminus\operatorname{im}f.
\]

A single kernel `A^S` models deleting a *common original forbidden set*. It does not model all these overlapping, row-specific restrictions. Applying (1.2) to each list independently would not produce a small-cube partition with one common edge direction. Applying it to a sector-weighted average would take the sector-specific capacity optimization outside the sum, which is invalid.

Even after only a common deletion, the argument does **not** preserve the flux certificate. The directly justified conditional bound for a retained edge is merely

\[
 \frac{\mathbb E[M_a\mid\operatorname{im}\phi\cap S=\varnothing]}{e_j}
 \le\frac{\alpha}{\Pr(\operatorname{im}\phi\cap S=\varnothing)}
 \le\alpha(1-2K|S|/N)^{-e_j}.
                                                               \tag{4.2}
\]

This can be exponentially worse than the original cap. Arbitrary boundary pinning is more restrictive still.

The attempted mathematical implication therefore stops precisely here: **no estimate has converted the norm-supported common-deletion survival, the exponential fugacity budget, and (4.1) into positive full-column capacity for at least one globally selected parity sector.** In particular there is no uniform-in-`T` lower bound for `Z_T` or `Zhat_T`, and no proof that `inj(Q_d,G)>0`. This note asserts the unconditional derivations above, not a conditional Ramsey completion.

## 5. Verification

The reproducible checker is `Submission/check_cube_norm_support.py`; its output is in `Submission/CubeNormSupportSurvivalVerification.txt`. It also passes `python3 -m py_compile`.

An exact-integer audit of (1.2), its normalization, and the face-deletion inequality checked all 728 nonzero Boolean pairs `0<=B<=A` on four vertices, and 240 rational-weight cases on three through eight vertices. Of the Boolean pairs, 656 have a majority support whose `Q_2` objective has strict KKT inequalities at zero penalties for `K=64`; hence zero is its actual unique minimizer. A further 130 complete-host cases checked the packing-product algebra against exact full-injection counts for `k=1`. These small cases check the identities, not the large-dimensional conclusion. The proofs above are all-dimensional.

The unchanged `Submission/Spec.lean` SHA-256 is

```
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```
