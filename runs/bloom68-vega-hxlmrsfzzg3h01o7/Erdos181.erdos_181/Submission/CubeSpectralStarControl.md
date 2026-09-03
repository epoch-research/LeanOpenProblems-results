# A linear-scale positive checkpoint: all induced-star activities

## Statement and scope

The exact whole-star resummation gives a nontrivial all-orders portion of the desired signed-activity estimate. After a degree-exception deletion, **every induced-star support in the cube, of every size, can be controlled at `N=C_K2^d`**.

This is a theorem about a subfamily of the full activities. It does not bound non-star supports, including larger supports which contain stars along with other source edges or isolated source vertices. It therefore does not establish positivity of the complete cube partition function.

The separate full embedding theorem currently proved remains
`N >= 10^6(K+4)^2 d^2 2^d => Q_d subset G`.

## 1. All-orders star-load lemma

Let `G` have `n` vertices, actual density `p>=1/3`, and

\[
 B=A_G-p(J-I),\qquad \|B\|_{op}\le L\sqrt n.
\]

For `d>=1`, assume

\[
 n\ge500d^2,\qquad
 \max_x|\deg(x)-p(n-1)|\le\frac{pn}{8ed}.                    \tag{1}
\]

Let `w(U)=w_1(U)` be the exact connected activities from the question, with source `Q_d` and this host. Let `S_d` consist of supports `U` for which `Q_d[U]` is an induced star `K_{1,r}`, `1<=r<=d`. Then

\[
 \boxed{
 \sup_{v\in Q_d}\sum_{\substack{U\in S_d\\v\in U}}
           |w(U)|e^{|U|-1}
 \le8000(L^2+1)\frac{d^2}{n}.
 }                                                           \tag{2}
\]

This bounds the absolute values of the **already fully resummed activities** on star supports, not the absolute values of their individual collision/spectral diagrams.

### Proof

Write `r_x=deg(x)-p(n-1)`. The actual-density convention gives

\[
 E_x r_x=0,\qquad E_x r_x^2=\|B\mathbf1\|^2/n\le L^2n.       \tag{3}
\]

The exact star generating function proved in `CubeSignedActivityLemmas.md` is

\[
 W(t):=\sum_{r\ge0}w(K_{1,r})\frac{t^r}{r!}
 =\frac{E_x(1+t/(pn))^{\deg(x)}}{(1+t/n)^n},                 \tag{4}
\]

where `w(K_{1,0})=1` is the singleton convention. Put `R=2ed`. On the complex disc `|t|<=R`, set

\[
 \lambda(t)=\log(1+t/(pn)),\qquad
 W_0(t)=(1+t/(pn))^{p(n-1)}(1+t/n)^{-n}.
\]

Use the analytic logarithm on this disc. It is well defined since `|t/(pn)|<1/4`. Equation (4) becomes the exact factorization

\[
 W(t)=W_0(t)E_x e^{r_x\lambda(t)}.                           \tag{5}
\]

Because `|lambda(t)|<=2R/(pn)`, the degree-flatness condition in (1) gives `|r_x lambda(t)|<=1/2`. For complex `u` with `|u|<=1/2`,

\[
 |e^u-1-u|\le |u|^2.
\]

Using the zero mean in (3), not the absolute first moment, therefore gives

\[
 |E_xe^{r_x\lambda(t)}-1|
 \le |\lambda(t)|^2 E_xr_x^2
 \le36L^2R^2/n.                                             \tag{6}
\]

The linear terms in `log W_0` cancel except for `-t/n`. The bound
`|log(1+u)-u|<=|u|^2/(2(1-|u|))` yields

\[
 |\log W_0(t)|\le R/n+\tfrac23(1/p+1)R^2/n\le4R^2/n\le1/4.
\]

Here `n>=500d^2>16R^2` is used. Consequently

\[
 |W_0(t)|\le2,\qquad |W_0(t)-1|\le8R^2/n.
\]

Combining with (5)--(6),

\[
 \sup_{|t|\le R}|W(t)-1|
 \le80(L^2+1)R^2/n=:M_*.                                    \tag{7}
\]

Cauchy's coefficient estimate, applied to `W-1`, gives for every `r>=1`

\[
 |w(K_{1,r})|\le r! M_* R^{-r}.                             \tag{8}
\]

For a fixed source vertex `v`, the number of `r`-leaf stars containing it is at most

\[
 \binom dr+d\binom{d-1}{r-1}=(r+1)\binom dr.
\]

The first term counts stars centred at `v`, the second those in which it is a leaf. For `r=1` this overcounts each edge, which is harmless. Cube neighbours are independent, so these are induced-star supports.

Since `binom(d,r)r! <= d^r` and `R=2ed`, (8) gives

\[
 \sum_{U\in S_d,\,v\in U}|w(U)|e^{|U|-1}
 \le M_*\sum_{r\ge1}(r+1)2^{-r}
 =3M_*
 =960e^2(L^2+1)d^2/n
 <8000(L^2+1)d^2/n.
\]

This proves (2). □

The use of `E r_x=0` in (6) is essential: replacing it by an absolute degree-error bound would lose the variance-scale gain.

## 2. Degree-flatness can be arranged under the original spectral hypothesis

Let `h=2^d`, `p=e(G)/binom(N,2)>=1/2`, and `||A-p(J-I)||<=K sqrt(N)`. Assume

\[
 \boxed{N\ge4\cdot10^9(K^2+1)h.}                            \tag{9}
\]

There is an induced subgraph `G'` on `n>=N/2` vertices such that, for its **actual** density `p'`,

\[
 p'\ge1/3,\qquad
 \|A_{G'}-p'(J-I)\|\le3K\sqrt n,
\]

and `G'` satisfies (1). At most `10^6K^2d^2` vertices are deleted.

**Proof.** Set `delta=N/(1000d)` and delete vertices with

\[
 |\deg_G(x)-p(N-1)|>\delta.
\]

The squared degree errors sum to at most `K^2N^2`, so the number `t` deleted is at most `10^6K^2d^2`. The elementary inequality `d^3<=4\,2^d`, together with (9), gives `t<=delta`. Thus `n=N-t>=.999N`, in particular `n>=N/2`.

For any remaining vertex,

\[
 |\deg_{G'}(x)-p(n-1)|\le\delta+t\le2\delta.
\]

Averaging this inequality and then subtracting the new mean gives

\[
 |p'-p|\le2\delta/(n-1),\qquad
 |\deg_{G'}(x)-p'(n-1)|\le4\delta=N/(250d).                  \tag{10}
\]

Since `n-1>=N/3`, the first inequality gives `p'>=1/2-6/(1000d)>1/3`. The second is at most `p'n/(8ed)`, using `p'>=1/3`, `n>=N/2`, and `e<3`.

For completeness, re-centring does not spoil the spectral bound. Let `B_S` be the principal restriction of the original centred matrix to the remaining vertices. Then

\[
 |p'-p|(n-1)=|\mathbf1^TB_S\mathbf1|/n\le K\sqrt N.
\]

It follows that

\[
 \|A_{G'}-p'(J-I)\|
 \le\|B_S\|+|p'-p|(n-1)
 \le2K\sqrt N<3K\sqrt n.
\]

Finally `d^2<=9\,2^d/8` and (9) ensure `n>=500d^2`. Both elementary inequalities used here follow by checking the increasing initial terms of `d^j/2^d` and then comparing consecutive terms: their maxima for `j=2,3` occur at `d=3,4`, respectively. □

The induced subgraph may have `p'<1/2`. This is not a change to the benchmark's hypothesis: the original graph still has `p>=1/2`, and embeddings in the induced subgraph are embeddings in it. The exact activity identity is valid for every positive actual density; the star-load lemma only needs `p'>=1/3`.

## 3. Linear-scale consequence for the full star subfamily

Applying (2) to `G'`, with `L=3K`, yields

\[
 \boxed{
 \sup_v\sum_{U\in S_d,\,v\in U}|w_{G'}(U)|e^{|U|-1}
 \le162000(K^2+1)\frac hN<10^{-3}
 }                                                           \tag{11}
\]

under (9). In fact the sharper bound
`8000(9K^2+1)d^2/n` is available.

Thus no truncation of the star size at two, three, or four is being made. All star activities are summed before estimating, and their entire contribution to the proposed per-vertex load is small at a dimension-independent multiplier of `h`.

This is **not** an estimate for all supports of the cube. Supports with a non-star induced source graph still contribute to the original partition function and may have either sign. A star-shaped selected spectral edge set inside a larger support is also not covered merely by (11); its collision attachments must be regrouped compatibly. Deleting those activities from the polymer gas has not been shown to lower-bound the original injective count.

The remaining required positive result is a compatible treatment of these non-star and overlapping cores. The all-dimensional full embedding theorem in `CubeSpectralBenchmark.md` avoids that issue at the cost of a factor `d^2` in the host size.

## 4. A precise remaining load budget, not an asserted estimate

For the pruned host, supports with no induced source edge have exactly their pure-collision activity. Their load is at most

\[
 \frac{eh}{n-eh}<10^{-6}
\]

under (9). This family is disjoint from the induced-star family. Together, the two **fully evaluated** families have negative load less than `0.002`.

Let `R_d` consist of supports `U` with `|U|>=2` such that `Q_d[U]` has an edge but is not a star. If one could prove

\[
 \sup_v\sum_{\substack{U\in R_d\\v\in U}}
       (-w_{G'}(U))_+ e^{|U|-1}\le1-e^{-1}-0.002,             \tag{12}
\]

then the proved positivity criterion would give an ordinary injective cube in `G'`, hence in `G`, at a constant multiplier of `2^d`.

**Equation (12) is unproved, and is not asserted to hold for the raw activities.** Whole non-star cores may need an additional exact regrouping. The concrete progress is that all induced-star sizes and all edgeless supports have already been accounted for with a small constant budget. The exact identity between the complete partition function and the injective count is never replaced by a truncated gas.

