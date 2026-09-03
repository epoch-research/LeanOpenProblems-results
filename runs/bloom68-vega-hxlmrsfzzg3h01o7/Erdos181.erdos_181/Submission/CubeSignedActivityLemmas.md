# Exact signed activity lemmas and whole-star resummation

## Scope

These are proved identities and positivity statements for the proposed signed expansion. They do **not** establish a dimension-uniform negative-activity load for the cube. The all-dimensional positive embedding result obtained in this investigation is instead proved in `CubeSpectralBenchmark.md`:

\[
 N\ge10^6(K+4)^2d^2 2^d\quad\Longrightarrow\quad Q_d\subseteq G.
\]

The `d^2` cannot be omitted from that full embedding result currently proved. A further positive conclusion from the whole-star formula is proved in `CubeSpectralStarControl.md`: after degree pruning, **all induced-star activities, at every size**, have total load `O((K^2+1)d^2/N)` even when `N/2^d` is a dimension-independent constant. The non-star/overlapping-core estimate is still absent.

Throughout this file, `H` is a simple source graph, `h=|V(H)|`, `G` is a simple `N`-vertex graph, and

\[
 p=e(G)/\binom N2>0,\qquad B=A_G-p(J-I),\qquad M=B/p.
\]

Thus `M` is symmetric, has zero diagonal, and its entries sum to zero. When `p>=1/2`, its entries are in `[-1,1]`.

## 1. Exact partition identities, including the diagonal convention

For independent uniform host labels `X_u`, put

\[
 f_{uv}=-\mathbf1[X_u=X_v]+\mathbf1[uv\in E(H)]zM(X_u,X_v),
\]

and

\[
 \Xi(z)=E\prod_{\{u,v\}\subset V(H)}(1+f_{uv}).
\]

For `|U|>=2`, define

\[
 w_z(U)=\sum_{\substack{F\subseteq\binom U2\;:\\(U,F)\text{ connected}}}
                 E\prod_{uv\in F} f_{uv}.
\]

The exact hard-core polymer expansion is

\[
 \boxed{\Xi(z)=\sum_{\mathcal P\text{ pairwise vertex-disjoint}}
                         \prod_{U\in\mathcal P}w_z(U).}       \tag{1}
\]

Uncovered vertices have weight one. To prove (1), expand the product over all source pairs and group its selected edges by connected components. Expectations factor over disjoint vertex sets.

Since the kernel has zero diagonal, every noninjective assignment has a vanishing pair factor. On an injective assignment, at `z=1` an `H`-edge has factor `1+M(x,y)=A_G(x,y)/p`. Hence

\[
 \Xi(0)=\frac{(N)_h}{N^h},\qquad
 \boxed{\Xi(1)=\frac{\operatorname{inj}(H,G)}{N^h p^{e(H)}}.} \tag{2}
\]

For `0<=z<1` and `N>=h`, one also has the elementary bound

\[
 \Xi(z)\ge\frac{(N)_h}{N^h}(1-z)^{e(H)}>0.
\]

This does not give strict positivity at `z=1`.

## 2. Contract collision components first: the exact multigraph formula

For a partition `pi` of `U`, let `r=|pi|`, `s=|U|`, and define

\[
 \mu(\pi)=\prod_{D\in\pi}(-1)^{|D|-1}(|D|-1)!.
\]

Choose `S subset E(H[U])`. Contract the blocks of `pi` in the selected edge set `S`, obtaining a multigraph `Q_pi(S)` on the blocks. Retain **every parallel edge**. Discard this term if a selected edge becomes a loop.

For a loopless multigraph `Q`, define

\[
 t_Q(M)=N^{-|V(Q)|}\sum_{x:V(Q)\to[N]}
                    \prod_{ab\in E(Q)}M(x_a,x_b),
\]

where the product uses edge multiplicities. The labels of different quotient vertices are independent; they are **not required to be distinct**.

Then

\[
\boxed{
 w_z(U)=\sum_{\pi\in\Pi(U)}\mu(\pi)N^{-(s-r)}
 \sum_{\substack{S\subseteq E(H[U])\;:\\
       Q_\pi(S)\text{ loopless and connected}}}
       z^{|S|}t_{Q_\pi(S)}(M).
}                                                               \tag{3}
\]

A quotient consisting of one vertex and no edges is connected and contributes one.

**Proof.** Expand each selected pair factor as a choice of a collision edge `-delta` or a spectral edge `zM`; these choices cannot occupy the same selected source pair. Let `T` be the collision-edge graph and `pi` its connected-component partition, including singleton components. A spectral edge within a block contributes zero because `M(x,x)=0`. In the surviving terms, no spectral edge lies inside a collision block, so the exclusion of the same pair imposes no further restriction on collision graphs inside the blocks.

The sum of `(-1)^{|E(T[D])|}` over connected graphs on a fixed block `D` is

\[
 (-1)^{|D|-1}(|D|-1)!.
\]

For example, this identity follows by taking the logarithm of the exponential generating function `1+t` for graphs weighted by `(-1)^{number of edges}`. Imposing equality within a block of size `b` has probability `N^{1-b}`; after this imposition its common label is uniform and independent of other blocks. Finally, `T union S` is connected exactly when its quotient on the collision blocks is connected. This proves (3). □

Two pitfalls avoided in (3):

* `pi` specifies the connected components of the **selected collision edges**, not the exact fibres of the labelling. Quotient labels can coincide accidentally.
* Parallel edges contribute pointwise powers `M(x,y)^j`; they are not a single edge or a matrix power. Further identifications can create genuine algebraic cycles.

At `z=0`, only the one-block partition survives, so

\[
 \boxed{w_0(U)=(-1)^{s-1}(s-1)!/N^{s-1}.}                   \tag{4}
\]

For a two-vertex support, the mean-zero property of `M` gives `w_z(U)=-1/N`. For an induced source path on three vertices, (3) gives

\[
 \boxed{w_z(P_3)=\frac2{N^2}
       +\frac{z^2}{p^2N^3}
           \bigl(\|B\mathbf1\|^2-\|B\|_F^2\bigr).}         \tag{5}
\]

The first spectral term comes from the uncontracted path; the second comes from identifying its two leaves. The positive degree-variance contribution must not be thrown away before the regrouping is evaluated.

## 3. A proof of the elementary signed positivity criterion

For arbitrary real polymer activities `w(U)`, set `a(U)=max(-w(U),0)` and `w_+(U)=max(w(U),0)`. Suppose

\[
 \sup_v\sum_{U\ni v}a(U)e^{|U|-1}\le1-e^{-1}.              \tag{6}
\]

Then

\[
 \boxed{Z(w)\ge e^{-h}Z(w_+)\ge e^{-h}>0.}                 \tag{7}
\]

**Proof.** First consider activities `-a`. For every subset `S` of source vertices, prove inductively that its partition function is positive and

\[
 Z_{-a}(S)/Z_{-a}(S\setminus\{v\})\ge e^{-1}\quad(v\in S).
\]

The vertex recurrence is

\[
 Z_{-a}(S)=Z_{-a}(S-v)-\sum_{U\subseteq S,\,v\in U}
                       a(U)Z_{-a}(S\setminus U).
\]

Repeated use of the already established ratios on proper subsets bounds
`Z_{-a}(S\setminus U)/Z_{-a}(S-v)` by `e^{|U|-1}`. Condition (6) therefore proves the next ratio and positivity. Iterating gives `Z_{-a}(S)>=e^{-|S|}`.

Now expand first over the selected positive polymers. Because `a(U)w_+(U)=0`, this gives the exact decomposition

\[
 Z(w)=\sum_{\mathcal P_+\text{ disjoint}}
       \Bigl(\prod_{U\in\mathcal P_+}w_+(U)\Bigr)
       Z_{-a}\left(V(H)\setminus\bigcup\mathcal P_+\right).
\]

Use the lower bound `e^{-h}` on every last factor. This proves (7). □

For pure collisions, even charging absolute values gives

\[
 \sum_{U\ni v}|w_0(U)|e^{|U|-1}
 =\sum_{r=1}^{h-1}(h-1)_r(e/N)^r
 \le\frac{eh}{N-eh}.
\]

At `N>=8h`, this is less than `1-e^{-1}`. This controls the collision-only gas, not the spectral terms in (3).

## 4. All-orders whole-star resummation

This is an explicit example of resumming a full core rather than bounding its alternating subpieces. It retains degree fluctuations exactly and is valid to every order.

For `r>=0`, let `w^star_{r+1}(z)` be the connected activity on a source star with one distinguished centre and `r` labelled leaves; put `w^star_1=1`. Work with formal power series, so no convergence assumption is needed. Define

\[
 W_\star(t;z)=\sum_{r\ge0}w^\star_{r+1}(z)\frac{t^r}{r!}.
\]

Then

\[
\boxed{
 W_\star(t;z)=
 \frac{\displaystyle\frac1N\sum_{x=1}^N
       \prod_{y\ne x}\left(1+\frac tN(1+zM_{xy})\right)}
      {(1+t/N)^N}.
}                                                               \tag{8}
\]

In particular, if `D_x=deg_G(x)`,

\[
\boxed{
 W_\star(t;1)=
 \frac{N^{-1}\sum_x(1+t/(pN))^{D_x}}{(1+t/N)^N}.
}                                                               \tag{9}
\]

**Proof.** Let `Z_r^star` denote the full partition function on a star with `r` leaves. Condition on the centre image `x`. Injectivity requires selecting distinct leaf images outside `x`, so

\[
 \sum_{r\ge0} Z_r^\star\frac{t^r}{r!}
 =\frac1N\sum_x\prod_{y\ne x}
                    \left(1+\frac tN(1+zM_{xy})\right).       \tag{10}
\]

In the polymer expansion, select the component containing the centre. If it contains `j` leaves, the other leaves support only pure collision polymers. Their exponential generating function is `(1+t/N)^N`, since the collision-only partition function on `r` leaves is `(N)_r/N^r`. This gives

\[
 \sum_{r\ge0} Z_r^\star\frac{t^r}{r!}
          =W_\star(t;z)(1+t/N)^N,
\]

proving (8). At `z=1`, `1+M_xy=A_G(x,y)/p` off the diagonal, which proves (9). □

The full star, including all of its collision pieces, has the manifestly nonnegative expression

\[
 \boxed{Z_r^\star(1)=\frac1N\sum_x\frac{(D_x)_r}{(pN)^r}.}  \tag{11}
\]

For every `r<=max_x D_x`, it is strictly positive. Equations (8)--(11) are not a claim that individual star activities are nonnegative. They show exactly why taking absolute values of their alternating coefficients loses useful structure. Expanding (9) through degree two recovers (5), including its positive degree-variance term.

For a regular host, (9) simplifies further to

\[
 W_\star(t;1)=
 (1+t/(pN))^{p(N-1)}(1+t/N)^{-N}.
\]

None of these formulas extends automatically to overlapping star cores. In particular, a cube parity class has many different, intersecting neighbourhoods, rather than repeated copies of a single star's leaf pool.

## 5. Positive even-cycle terms at every length, and their correct scale

For `ell>=2`, an uncontracted even spectral cycle has

\[
 t_{C_{2\ell}}(M)=\frac{\operatorname{tr}(M^{2\ell})}{N^{2\ell}}\ge0.
\]

If `||B||_op<=K sqrt(N)`, then the exact identity
`||B||_F^2=p(1-p)N(N-1)` gives

\[
 0\le t_{C_{2\ell}}(M)
 \le (K/p)^{2\ell-2}\frac{1-p}{p}\,N^{1-\ell}.              \tag{12}
\]

In particular, the general spectral scale for `C_4` is `O_K(1/N)`, **not** `O_K(1/N^2)`. Even for cycles, the estimate `N^{-|U|/2}` proposed for all graph products would be incorrect. Quotient multigraphs can be more complicated still. Formula (12) does not bound every activity on a cyclic support: there are also other spectral edge subsets and collision contractions in (3).

## 6. Cube support sparsity and what it does not yet prove

For every source support `U subset Q_d`,

\[
 e_{Q_d}(U)\le\tfrac12|U|\log_2|U|.
\]

For completeness, split by a coordinate, apply induction to the two halves, bound crossing matching edges by the smaller half, and use
`t H_2(t_0/t)>=2 min(t_0,t_1)`. This proves the inequality with its exact leading constant.

The stronger-for-this-purpose distance-two estimate and the counting of disjoint-star overload witnesses are proved and used in `CubeSpectralBenchmark.md`. They give an actual all-dimensional embedding theorem. However, these support inequalities alone do not bound the sum in (3): one must still control the signed quotient multigraph products, count the relevant dense core configurations, and justify a compatible whole-core regrouping.

No assertion of a convergent full signed cluster expansion, or of a constant negative load for `N=C_K2^d`, is made here.
