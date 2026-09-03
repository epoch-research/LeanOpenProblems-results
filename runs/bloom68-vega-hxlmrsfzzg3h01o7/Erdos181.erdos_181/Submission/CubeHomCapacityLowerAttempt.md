# Cube homomorphism capacities: a lower-bound attempt and its obstructions

## Outcome

**No genuine disproof of `R(Q_d) <= C 2^d` was found.** In particular, this investigation does **not** give complete two-colourings with unbounded `N_d/2^d` and no ordinary injective monochromatic cube.

The substantive results are:

1. An exact, **loop-aware** capacity criterion for homogeneous blow-ups, including the integer correction needed to turn a capacity into an actual lower-bound colouring.
2. An exact fixed-template limiting capacity, expressed by the largest fractional matching **in one monochromatic connected component**. The necessary direction applies to **every** cube homomorphism. A quantitative Hamming-weight construction proves the converse in the limit.
3. Matching-order capacity estimates for growing Cartesian tori, **including all nonlinear and lazy homomorphisms**. These give a real one-colour obstruction. However, an explicit complete bipartite graph in the other colour gives a cube whenever `N >= (5/2)2^d`, so they do not give a Ramsey disproof.
4. A universal barrier for **every polynomial-size uniform template**, not just templates already known to contain a torus: the established bounded-degree Ramsey theorem supplies the required monochromatic torus. The resulting constant depends on the polynomial exponent.
5. An attempted general all-map obstruction using lifts to triangle-and-square covers and balanced separators. A local-density theorem shows that one colour necessarily has cover treewidth of order the template size. Thus this particular obstruction cannot yield an unbounded Ramsey ratio, even for super-polynomial templates.

The remaining unproved inequality is stated exactly in Section 7. Neither an explicit template family satisfying it nor a proof that no such family exists is supplied.

### Relation to earlier investigations

`CubeSaturationStructure.md`, Section 4, already uses connected fractional matchings, loops, and capacity-controlled closed walks for a bounded-template embedding theorem. That mechanism is **not claimed as a new discovery here**. The additions here are the necessary occupation-flow inequality and exact optimal limiting capacity, the all-map finite-dimensional torus estimates, the universal polynomial-template barrier, and the cover/treewidth obstruction with its density no-go theorem.

No binary Cayley colouring or switched-symplectic example is offered as a counterexample. No affine-only exclusion, typical-map assertion, or independently chosen collection of smaller cube maps is substituted for exclusion of ordinary cubes.

Throughout, `d >= 1`, `h = 2^d`, and a cube copy is an injective, noninduced graph copy. Additional edges on the image are harmless. Divergence requirements may be taken along a subsequence of dimensions: an unbounded-ratio avoiding family has such a subsequence, since finite Ramsey existence bounds the ratio in each fixed dimension.

---

## 1. The exact blow-up problem, including internal edges

### 1.1 Homogeneous clusters require coloured loops

Let `T` be a complete red-blue template on `m` labels. Assign exactly one colour to each unordered pair of **distinct** labels, and exactly one colour to a loop at each label. Let `H_c` be the relation consisting of colour-`c` edges and loops.

The uniform blow-up `T[s]` has `s` vertices in each cluster:

* edges between distinct clusters have their template pair's colour;
* all edges inside a cluster have its loop's colour.

This is an ordinary complete two-colouring. A template loop describes edges between **distinct host vertices** in that cluster; the host graph itself has no loops.

Define

\[
 b_d(H)=\min_{f:Q_d\to H}\max_v |f^{-1}(v)|,
 \qquad
 \beta_d(H)=b_d(H)/h.                                      \tag{1.1}
\]

A homomorphism here may map adjacent cube vertices to the same label **only if that label has a loop in `H`**. Set `b_d(H)=infinity` if there is no homomorphism. Put

\[
 \kappa_d(T)=\min_{c\in\{R,B\}}b_d(H_c).
\]

At least one colour has a loop, so `kappa_d(T)` is finite.

**Exact criterion.**

\[
 T[s]\text{ contains a monochromatic ordinary }Q_d
 \quad\Longleftrightarrow\quad s\ge\kappa_d(T).              \tag{1.2}
\]

**Proof.** Project an injective cube embedding to its cluster labels. Required edges give a homomorphism, and injectivity bounds each fibre by `s`. Conversely, given a legal homomorphism with fibres at most `s`, inject each fibre into its assigned cluster. Different fibres use disjoint clusters. Every required edge either crosses a correctly coloured template pair or lies inside a cluster with the correct loop colour. This produces an ordinary injection. No conditions on cube nonedges are required.

Consequently the largest avoiding cluster size is exactly `kappa_d(T)-1`, and the exact available amplification is

\[
 \boxed{\quad
 \Gamma_d(T)=\frac{m(\kappa_d(T)-1)}{2^d}.
 \quad}                                                     \tag{1.3}
\]

The subtraction of one is essential. If `kappa_d(T)=1`, there is already an injective cube in the template. A large value of `m*kappa_d(T)/h` when `m >> h` is then **not** a lower bound.

### 1.2 Arbitrarily coloured or recursive interiors

If a cluster's internal edges are not monochromatic, a single loop does not describe it exactly. A safe necessary projection condition is obtained by allowing **both** colours to stay at every label, i.e. using the reflexive closure `H_c^circ` of each off-diagonal colour graph.

Thus

\[
 \text{an actual colour-}c\text{ cube}
 \quad\Longrightarrow\quad
 f:Q_d\to H_c^\circ\text{ with every fibre at most }s.       \tag{1.4}
\]

Nonexistence of these more permissive maps suffices for a lower bound. Existence of such a map alone does **not** justify lifting through arbitrary interiors.

There is one important safe converse: a **strict** homomorphism, mapping every cube edge between distinct clusters, lifts regardless of the internal two-colouring. Section 5 uses only such maps.

Giving both colours *no* loop would incorrectly make internal edges a third forbidden colour. None of the results below does that.

### 1.3 Fixed branching does not amplify recursively

If an equal-cluster top-level template has `m >= 2` labels, any template edge supplies a monochromatic `K_(s,s)` between two whole clusters. Hence

\[
 s\ge h/2\quad\Longrightarrow\quad Q_d\text{ in that colour}.
                                                               \tag{1.5}
\]

The parity classes of the cube can be injected arbitrarily into the two clusters. In particular, increasing the depth of a balanced fixed-arity recursive blow-up does not multiply its Ramsey ratio: `N/h >= m/2` already gives a cube at the top level. This observation is about equal-size, or uniformly large, top-level clusters; it is not an assertion about every unbalanced recursive representation.

---

## 2. A necessary occupation inequality for every homomorphism

### 2.1 Fractional matching convention

For a finite looped graph `H`, a fractional matching consists of weights `x_e >= 0` satisfying

\[
 \sum_{e\ni v,\ e\text{ nonloop}}x_e+2x_{vv}\le1
 \quad\text{at every }v.
\]

Its size is `sum_e x_e`, denoted at the maximum by `nu_f(H)`. A loop consumes capacity twice, so a single loop has fractional matching number `1/2`.

Components are taken in the underlying off-diagonal graph. Write

\[
 \nu_f^*(H)=\max_{C\text{ a component of }H}\nu_f(H[C]).       \tag{2.1}
\]

A component with no edge and no loop has matching number zero and cannot receive a homomorphism from `Q_d`, for `d >= 1`.

### 2.2 The regular-edge marginal identity

Let `f:Q_d -> H` be **any** homomorphism, and let

\[
 p_v=|f^{-1}(v)|/h.
\]

Choose a uniformly random unoriented cube edge. Let `a_e` be the probability that its pair of labels is the template edge or loop `e`. Since `Q_d` is regular,

\[
 p_v=\frac12\sum_{e\ni v,\ e\text{ nonloop}}a_e+a_{vv},
 \qquad \sum_e a_e=1.                                      \tag{2.2}
\]

Equivalently, `p` is in the convex hull of the endpoint laws

\[
 u_{ab}=(\delta_a+\delta_b)/2,
 \qquad u_{aa}=\delta_a.                                    \tag{2.3}
\]

Moreover, all used edges and vertices lie in **one component**, because the cube is connected.

If `b=max_v p_v`, the weights `x_e=a_e/(2b)` form a fractional matching of size `1/(2b)` in that component. Therefore

\[
 \boxed{\qquad
 \beta_d(H)\ge\frac{1}{2\nu_f^*(H)}.
 \qquad}                                                    \tag{2.4}
\]

This is a necessary inequality for all maps, not an entropy assertion about typical homomorphisms. Conversely, a maximum fractional matching `x` in a component, normalized by `a_e=x_e/nu_f`, gives an endpoint law of maximum coordinate `1/(2 nu_f)`. Thus (2.4) is the exact optimum of this occupation-flow relaxation.

**Why the component restriction matters.** For a disjoint union of `r` edges, the global fractional matching number is `r`, but every cube map lies on one edge and has maximum fibre `h/2`. Using the global matching number would incorrectly predict `h/(2r)`.

### 2.3 A balanced dimension extension

The map

\[
 (x_1,\ldots,x_d,x_{d+1})
 \longmapsto(x_1\mathbin\oplus x_{d+1},x_2,\ldots,x_d)
                                                               \tag{2.5}
\]

is a strict, exactly two-to-one homomorphism `Q_(d+1) -> Q_d`. Composing gives

\[
 b_{d+1}(H)\le2b_d(H),\qquad
 \beta_{d+1}(H)\le\beta_d(H).                                \tag{2.6}
\]

The optimal normalized capacity is monotone even though a particular Hamming-weight construction need not improve monotonically at every dimension.

---

## 3. Exact fixed-template limiting capacity

### Theorem 3.1

For every fixed finite looped graph with an edge or loop,

\[
 \boxed{\quad
 \lim_{d\to\infty}\beta_d(H)
   =\frac{1}{2\nu_f^*(H)}.
 \quad}                                                     \tag{3.1}
\]

The lower bound was proved in Section 2. Here is a direct converse which also tracks the transition cost between different edge phases.

### 3.1 Joining phases by actual target walks

Fix a connected component on `q` vertices and an endpoint-law mixture

\[
 p=\sum_{i=1}^r\lambda_i u_{a_i b_i},\qquad
 \lambda_i>0,\quad\sum_i\lambda_i=1.                         \tag{3.2}
\]

The atoms are actual edges or allowed loops of this component. Let

\[
 W\sim\operatorname{Bin}(d,1/2),\qquad
 \eta_d=\max_j\Pr(W=j)
       =2^{-d}\binom d{\lfloor d/2\rfloor}=O(d^{-1/2}).       \tag{3.3}
\]

Partition the integer weights `0,...,d` into consecutive quantile intervals `J_i`, with

\[
 |\Pr(W\in J_i)-\lambda_i|\le2\eta_d.
\]

For a fixed mixture, all these intervals eventually have length at least `q`: their masses stay bounded away from zero while each individual layer has mass at most `eta_d`.

Within `J_i`, alternate on the edge `a_i b_i`, or stay at the loop if `a_i=b_i`. At a change of phase, use a path of length at most `q-1` from the previous phase's last vertex to `a_i`, consuming the first at most `q-1` positions of the new interval. Then alternate on its edge. Choose the alternating phase to agree with the arrival point.

This constructs a **single legal walk**

\[
 w_0,w_1,\ldots,w_d
\]

in `H`, not independently selected edge phases. Consequently

\[
 f(x)=w_{|x|}                                                \tag{3.4}
\]

is a homomorphism of the entire cube, including every coordinate square.

For any consecutive interval, the difference between its even and odd binomial masses is at most `2 eta_d`. One proof splits the unimodal binomial sequence at its maximum and uses the alternating-sum bound for each monotone piece. Thus the ideal alternating phase differs from `lambda_i u_(a_i b_i)` in each coordinate by at most `3 eta_d`. The connector positions add at most `(r-1)(q-1) eta_d` total mass. Hence

\[
 \boxed{\quad
 \|p_f-p\|_\infty
 \le\bigl(3r+(r-1)(q-1)\bigr)\eta_d
 \quad}                                                     \tag{3.5}
\]

once the quantile intervals have the stated lengths.

Apply this to the normalized maximum fractional matching in a component attaining `nu_f^*(H)`. It proves the upper bound in (3.1), and indeed `beta_d(H) <= 1/(2 nu_f^*(H)) + O_H(d^(-1/2))`.

The dependence on `H`, and the threshold for sufficiently long quantile intervals, are important. Equation (3.1) does **not** allow exchanging `d -> infinity` with an arbitrary growing-template limit.

### 3.2 The two-colour fractional bound, with loops retained

For completeness, the connected fractional matching lemma from `CubeSaturationStructure.md` has the following particularly useful consequence:

\[
 M(T):=2\max_{c,C}\nu_f(H_c[C])\ge 2m/3.                    \tag{3.6}
\]

Here is its proof for unit capacities. One off-diagonal colour graph is connected on all labels: the complement of a disconnected graph is connected. Call a connected colour red. The one-label case is immediate using its loop colour.

If `nu_f(H_R) >= m/3`, stop. Otherwise fractional matching/vertex-cover duality gives a red fractional vertex cover of cost less than `m/3`. It may be chosen with values in `{0,1/2,1}`. To see the half-integral rounding directly, truncate a cover to `[0,1]`, choose `t` uniformly in `(0,1/2)`, and round a value `y` to `0`, `1/2`, or `1` according as `y<t`, `t<=y<=1-t`, or `y>1-t`. Each edge constraint, including `2y>=1` for a loop, is retained; expected cost is unchanged.

Let the zero, half, and one sets have sizes `A,B,F`. Then

\[
 F+B/2<m/3,\qquad A>m/3,\qquad A+B>2m/3.
\]

Every loop on the zero set, every pair within it, and every pair from it to the half set is blue. This **one blue component** has a fractional matching covering

\[
 \min(2A,A+B)>2m/3:
\]

match between the zero and half sets, and, if the zero set has leftover capacity, use its blue loops. This proves (3.6).

Combining (1.3), (3.1), and (3.6) gives the exact asymptotic amplification for a fixed homogeneous template:

\[
 \boxed{\quad
 \lim_{d\to\infty}\Gamma_d(T)
   =\frac{m}{M(T)}\le\frac32.
 \quad}                                                     \tag{3.7}
\]

Also `M(T)<=m`, so this limit is between `1` and `3/2`.

### 3.3 A sharp constant example, not a disproof

Take three labels `0,1,2`, all with red loops. Colour `01` red and `02,12` blue. The red components have two and one labels; blue is the loopless two-leaf star. Exactly

\[
 b_d(H_R)=b_d(H_B)=h/2,\qquad \kappa_d(T)=h/2.
\]

For red, a cube lies in one red component, giving the lower bound, and a balanced assignment into labels `0,1` attains it. For blue, one source parity class must map to the star centre, and the ordinary parity map attains the bound.

For `d>=2`, with `s=h/2-1`, red has components of orders `2s<h` and `s<h`, while blue is `K_(2s,s)` with smaller side below `h/2`. Thus this is an actual avoiding colouring on

\[
 N=3(h/2-1),\qquad N/h\longrightarrow3/2.                   \tag{3.8}
\]

It has a **bounded** ratio. The usual unequal two-block construction, of sizes `h-1` and `h/2-1`, improves the finite count to `N=3h/2-2`, again with bounded ratio.

### 3.4 Weighted extension

For fixed positive capacities `a_v`, replace the bottleneck by `max_v p_v/a_v` and the matching constraints by incident load at most `a_v`. The same edge-flow argument and phase construction give limiting bottleneck `1/(2 max_C nu_f(H[C];a))`. This is an exact fractional characterization for fixed unequal cluster proportions too. It does not provide uniform convergence for arbitrarily growing templates or vanishing proportions.

---

## 4. Growing tori: a genuine all-map obstruction in one colour

Let

\[
 T_{\ell,k}=C_\ell\square\cdots\square C_\ell
 \quad(k\text{ factors}),\qquad m=\ell^k,\qquad\ell\ge5.
\]

Any subset of vertex loops may be allowed. In particular the lower bound below remains valid for the **fully reflexive** torus and hence for projections through arbitrarily coloured cluster interiors.

### Theorem 4.1 — bounds valid for all homomorphisms

For `d>=k`, partition the coordinates into `k` nonempty blocks of sizes `d_i` differing by at most one. Then

\[
 \boxed{
 \max\left\{\ell^{-k},
 \frac{1}{2[3(1+\sqrt{d/k})]^k}\right\}
 \ \le\ \beta_d(T_{\ell,k})
 \ \le\ \prod_{i=1}^k
       \left(\frac1\ell+\sqrt{\frac{2}{\pi d_i}}\right).
 }                                                          \tag{4.1}
\]

The lower bound applies even with all loops, and the upper bound uses a strict map, so the assertion is valid for every intermediate choice of loops.

In particular, for each fixed `k`, these bounds give the correct order, uniformly in growing `ell`:

\[
 \beta_d(T_{\ell,k})
   \asymp_k\bigl(\min\{\ell,\sqrt{d/k}\}\bigr)^{-k}.
                                                               \tag{4.2}
\]

This is an order estimate, not a claim of an exact finite integer value.

### 4.1 Why nonlinear maps cannot beat the lower bound

Let `f:Q_d -> T_(ell,k)` be any lazy homomorphism. Assign an oriented source edge its unique increment in

\[
 \{0,\pm e_1,\ldots,\pm e_k\}\subset\mathbb Z^k.
\]

The sum of increments around a cube square is zero modulo `ell` in every coordinate, and has `l1` norm at most four. Since `ell>=5`, this sum is **zero in the integers**. Backtracks also have zero sum.

Coordinate squares and backtracks generate all relations between paths in a cube. Therefore these increments integrate to a globally defined map

\[
 F:Q_d\longrightarrow\mathbb Z^k
\]

whose reduction modulo `ell` is `f`, up to a fixed translation. Every source edge changes `F` by zero or one signed coordinate vector. This is a lift of an arbitrary map, not an assumption that `f` is a linear or Hamming-weight map.

For uniform `X` in the cube, the cube Poincare inequality gives

\[
 \mathbb E\|F(X)-\mathbb EF(X)\|_2^2
 \le\frac14\sum_{i=1}^d
       \mathbb E\|F(X)-F(X\oplus e_i)\|_2^2
 \le d/4.                                                   \tag{4.3}
\]

For a scalar function this follows immediately from its Walsh expansion: the two sides before the final inequality are `sum_(S nonempty) a_S^2` and `sum_S |S| a_S^2`. Sum over target coordinates.

At least half the mass of `F(X)` lies in a lattice ball of radius `sqrt(d/2)`. Uniformly over its real centre `a`, the number `L` of lattice points in such a ball satisfies

\[
 L\le [3(1+\sqrt{d/k})]^k.                                  \tag{4.4}
\]

For an elementary proof, use

\[
 \sum_{n\in\mathbb Z}e^{-t(n-a)^2}\le1+\sqrt{\pi/t}
\]

(the sum of a nonnegative unimodal function at unit-spaced points is at most its maximum plus its integral), then set `t=k/d`:

\[
 L\le e^{td/2}(1+\sqrt{\pi/t})^k
   =\left[\sqrt e(1+\sqrt{\pi d/k})\right]^k
   \le[3(1+\sqrt{d/k})]^k.
\]

Some lifted point consequently has probability at least `1/(2L)`. Its probability is no greater than that of its template label. This proves the nontrivial lower bound in (4.1). The other lower bound is pigeonhole.

### 4.2 Strict maps and a uniform binomial residue estimate

For the upper bound use

\[
 f(x)=\bigl(|x^{(1)}|\bmod\ell,\ldots,
            |x^{(k)}|\bmod\ell\bigr).                       \tag{4.5}
\]

Every cube edge changes exactly one residue by `+1` or `-1`, so this is strict. Independence of the blocks multiplies their residue probabilities.

If `W~Bin(t,1/2)`, Fourier inversion gives

\[
 \Pr(W\equiv a\pmod\ell)
 =\frac1\ell\sum_{j=0}^{\ell-1}
   e^{-2\pi ija/\ell}
   \left(\frac{1+e^{2\pi ij/\ell}}2\right)^t.                \tag{4.6}
\]

Writing `r=min(j,ell-j)`, the modulus of the nonzero factor is

\[
 |\cos(\pi j/\ell)|^t
 \le e^{-\pi^2 t r^2/(2\ell^2)}.
\]

Summing the Gaussian tail and bounding it by its integral yields the **uniform** estimate

\[
 \boxed{\quad
 \max_a\Pr(W\equiv a\pmod\ell)
 \le\frac1\ell+\sqrt{\frac{2}{\pi t}}.
 \quad}                                                     \tag{4.7}
\]

It holds for both odd and even `ell`. There is no missing parity obstruction: the binomial increments are `0/1`, not a periodic non-lazy random walk. In particular, `t>=ell^2` implies a maximum residue probability strictly less than `2/ell`.

This proves the upper bound in (4.1). It also shows why an exclusion based on a particular phase decomposition cannot exclude all balanced maps.

### 4.3 Why the one-colour obstruction cannot be a counterexample

Colour torus edges red and all other pairs of template labels blue. Blow up the labels equally, with **any** internal two-colouring.

Let

\[
 a=\lfloor(\ell-2)/2\rfloor,
 \quad I=\{0,\ldots,a-1\},
 \quad J=\{a+1,\ldots,2a\}.
\]

No element of `I` equals or is cyclically adjacent to an element of `J`. Thus the template vertices whose first coordinates lie in `I`, and those whose first coordinates lie in `J`, have **all cross-edges blue**, irrespective of their other coordinates. Each set has

\[
 a\ell^{k-1}\ge m/5
\]

labels, for every `ell>=5` and every `k>=1`.

The actual blow-up therefore has two complete blue pools of size at least `N/5`. If `N >= (5/2)h`, inject the two cube parity classes into those pools. This is an ordinary blue cube, using no internal-cluster edges.

Hence even when the rigorous red capacity obstruction in (4.1) has an arbitrarily large normalized value, the complementary colour defeats the construction at an **absolute constant**. This remains true if `k` grows. The obstruction is real but one-sided; it is not a Ramsey disproof.

---

## 5. Every polynomial-size uniform template has a constant amplification bound

The next statement quantifies the product-torus issue for **arbitrary** two-colour templates, not only explicitly toroidal ones.

### Established external input

The bounded-degree Ramsey theorem of Chvatal, Rodl, Szemeredi, and Trotter states:

> For every fixed integer `Delta` there is a finite constant `B_Delta >= 1` such that every graph `F` of maximum degree at most `Delta` satisfies `R(F) <= B_Delta |V(F)|`.

Only fixed-degree instances of this established theorem are used. It is not the cube Ramsey conjecture: in that conjecture the maximum degree tends to infinity with `d`.

### Theorem 5.1 — universal polynomial-template barrier

For every fixed `A>0`, there are constants `K_A,D_A` such that, for

\[
 d\ge D_A,\qquad 2\le m\le d^A,
\]

every red-blue complete template on `m` labels admits, in one colour, a **strict** homomorphism from `Q_d` with maximum fibre at most

\[
 K_A h/m.                                                   \tag{5.1}
\]

Consequently every uniform blow-up with `N=ms >= K_A h` contains an ordinary monochromatic `Q_d`, **whatever the internal two-colourings of the clusters are**.

For homogeneous clusters, `m=1` is trivial separately. For arbitrary interiors, that case is deliberately excluded: treating one arbitrary cluster as solved would assume the original conjecture.

**Proof with constants.** Choose an integer `k>2A`, and let `B=B_(2k)`. One may take

\[
 K_A=5^k B.                                                 \tag{5.2}
\]

Choose `D_A` so that, for all `d>=D_A`,

\[
 d\ge2k,\qquad d^{1-2A/k}\ge2k.                             \tag{5.3}
\]

If `m<5^k B`, use any template edge and the parity map, which has maximum fibre `h/2`; this is at most `K_A h/m`.

Otherwise put

\[
 \ell=\left\lfloor(m/B)^{1/k}\right\rfloor\ge5.
\]

Then

\[
 \frac{m}{2^kB}\le\ell^k\le\frac mB.                       \tag{5.4}
\]

The torus `T_(ell,k)` has maximum degree `2k`, so the bounded-degree Ramsey theorem places an ordinary monochromatic copy of it in the template.

Divide the `d` source coordinates into `k` nearly equal blocks. Each block size is at least

\[
 \lfloor d/k\rfloor\ge d/(2k)
 \ge d^{2A/k}\ge\ell^2.                                    \tag{5.5}
\]

By (4.7), the strict map (4.5) has maximum fibre at most

\[
 h(2/\ell)^k\le4^kB\,h/m\le K_A h/m.                       \tag{5.6}
\]

Compose with the injective monochromatic torus embedding into the template. Finally lift the fibres injectively into their clusters. No source edge stays inside a cluster, so their internal colours are irrelevant. This proves the theorem.

### Necessary template growth for a lower-bound family

Suppose equal-cluster blow-ups with `m_d>=2` have no ordinary monochromatic `Q_d` and satisfy `N_d/h -> infinity`. Theorem 5.1 implies that, eventually, for **every fixed** `A`,

\[
 m_d>d^A,
 \qquad\text{equivalently}\qquad
 \frac{\log m_d}{\log d}\longrightarrow\infty.              \tag{5.7}
\]

This applies even with recursive, nonhomogeneous cluster interiors. Merely taking polynomially many clusters cannot produce the requested disproof.

The constants depend on `A`. Allowing `k` to grow while silently keeping `B_(2k)` bounded would be invalid. The theorem does not cover arbitrary super-polynomial template sizes and does not establish the global cube Ramsey conjecture.

---

## 6. A new all-map candidate: cubical lifts and balanced separators

The torus argument suggests using a cover in which every cube map has restricted geometry. The following route handles all maps but is blocked by a general density inequality.

### 6.1 The triangle-and-square cover

For an off-diagonal graph `G`, form a two-dimensional complex `X(G)` by attaching a disc to every simple triangle and every simple four-cycle. Let `U(G)` be the one-skeleton of its universal cover, component by component. Define `w(G)` as the supremum of the treewidths of its finite subgraphs; it may be infinite.

Every lazy map `f:Q_d -> G^circ` lifts to `U(G)`. Indeed, a source square maps to a closed walk of length at most four. After stationary steps and backtracks are removed, it is a triangle, a four-cycle, or trivial, hence null-homotopic in `X(G)`. All path relations of the cube are generated by these squares and backtracks. This proves lifting for arbitrary maps, including nonlinear maps and within-cluster steps.

Every lifted fibre is contained in a template fibre, so its size is at most the latter's size.

### 6.2 The separator certificate

Let `sigma_d` be the smallest size of a set whose deletion leaves every component of `Q_d` with at most `h/2` vertices. Deleting the middle Hamming layer proves the elementary bound

\[
 \sigma_d\le\binom d{\lfloor d/2\rfloor}=\eta_d h.           \tag{6.1}
\]

If `w(G)<infinity`, every homomorphism into `G^circ` satisfies

\[
 \boxed{\qquad
 \max_v|f^{-1}(v)|\ge\frac{\sigma_d}{w(G)+1}.
 \qquad}                                                    \tag{6.2}
\]

**Proof.** Give each vertex of the finite lifted image weight equal to its number of cube preimages. A graph of treewidth at most `w` has a weighted balanced separator of at most `w+1` vertices: take a centroid bag in a tree decomposition after assigning the vertex weights to bags. Its removal leaves components of weight at most `h/2`.

The separator's preimage is a balanced source separator. If the maximum original fibre is `s`, this preimage has size at most `(w+1)s`. Hence `sigma_d <= (w+1)s`.

For the two colour graphs, let `W=max(w(G_R),w(G_B))`. The sufficient certificate

\[
 s<\frac{\sigma_d}{W+1}                                    \tag{6.3}
\]

would rule out both colours through **any** internal cluster colouring. An unbounded ratio obtained from this certificate would require, by (6.1), `W=o(m/sqrt(d))`.

This requirement is only for this proposed certificate, not a claimed necessary condition on every possible Ramsey counterexample.

### 6.3 Density forces large cover treewidth

**Theorem 6.1.** If `G` has `m` vertices and `e` edges, then

\[
 \boxed{\qquad w(G)\ge\frac{2e^2}{m^3}.\qquad}              \tag{6.4}
\]

Thus for any complete two-colouring,

\[
 \boxed{\quad
 \max\{w(G_R),w(G_B)\}
 \ge\frac{(m-1)^2}{8m}.
 \quad}                                                     \tag{6.5}
\]

**Proof.** Fix `v` and a lift of it. Its neighbours have uniquely determined lifts. For each vertex reached by a two-edge path from `v`, all such paths end at the same lifted vertex, because the paths differ by a filled square. If that vertex is already a neighbour of `v`, the filled triangle makes the two-step lift agree with the direct lift. Backtracks handle `v` itself.

This defines an injective section on the vertices at distance at most two from `v`. In particular, the cover contains a copy of the graph `J_v` consisting of all edges with at least one endpoint in `N(v)`. There are at most `m` vertices, and

\[
 e(J_v)\ge\frac12\sum_{u\in N(v)}\deg_G(u).                  \tag{6.6}
\]

A graph of treewidth `w` has at most `w` times its number of vertices edges; for example, a tree decomposition shows it is `w`-degenerate. Therefore

\[
 w(G)\ge\frac{1}{2m}\max_v\sum_{u\in N(v)}\deg_G(u).
\]

But

\[
 \frac1m\sum_v\sum_{u\in N(v)}\deg_G(u)
 =\frac1m\sum_u\deg_G(u)^2
 \ge\frac{4e^2}{m^2}
\]

by Cauchy-Schwarz. This proves (6.4). One colour has at least `m(m-1)/4` edges, which gives (6.5).

### 6.4 Consequence for the attempted lower bound

Combining (6.1), (6.3), and (6.5), any ratio certified by this method would satisfy, for `m>=2`,

\[
 \frac{ms}{h}
 <\frac{m\eta_d}{W+1}
 \le\frac{8m^2}{(m-1)^2}\eta_d
 \le32\eta_d\longrightarrow0.                              \tag{6.7}
\]

So this cover/treewidth certificate cannot even certify a nontrivial asymptotic ratio above one, much less an unbounded one.

Nor is this merely an artefact of filling all triangles. If one fills all squares but only the triangle relations forced by the actual allowed loops, the two-step construction still supplies a graph on at most `2m` lifted vertices. Each edge counted in the neighbour-degree sum can coincide with at most its reverse copy, so it has at least half that sum in distinct edges. The same argument gives cover treewidth at least `e^2/m^3`, and hence `(m-1)^2/(16m)` in one colour. With only square relations and no allowed stationary steps, parity separates the two layers and restores the stronger constant in (6.4).

**Logical limitation.** Large cover treewidth is not an upper bound on `b_d(G)` and does not construct a balanced cube map. This section rules out a proposed sufficient *lower-bound certificate*. It does not prove the Ramsey conjecture or eliminate every possible obstruction in such covers. A finer invariant depending on the actual lifted image and its occupation weights could behave differently; no useful two-colour inequality for such an invariant is proved here.

---

## 7. The exact unproved inequality needed for a disproof

For homogeneous uniform blow-ups, the unresolved task is to give actual loop-coloured complete templates `T_d` and positive integers `s_d` such that

\[
 \boxed{\begin{aligned}
 &\min_{c\in\{R,B\}}
   \min_{f:Q_d\to H_{c,d}}\max_v|f^{-1}(v)|
      \ \ge s_d+1,\\
 &\frac{m_d s_d}{2^d}\longrightarrow\infty.
 \end{aligned}}                                             \tag{7.1}
\]

The inner minimum ranges over **all** homomorphisms, with the actual coloured loops. By Section 1 this is necessary and sufficient for this proposed family of blow-ups. Equivalently, one must prove

\[
 \boxed{\qquad
 \Gamma_d(T_d)
 =\frac{m_d(\kappa_d(T_d)-1)}{2^d}
 \longrightarrow\infty.
 \qquad}                                                    \tag{7.2}
\]

For arbitrary internal colourings, replacing each target by its fully reflexive closure in the first line of (7.1) is a **stronger sufficient** condition, not an equivalent one.

### 7.1 The missing estimate is a finite-dimensional excess, not fractional feasibility

The fixed-template calculation makes the nature of the missing inequality more explicit. Define

\[
 E_d(T)=m\min_c\beta_d(H_c)-\frac{m}{M(T)},
 \qquad M(T)=2\max_{c,C}\nu_f(H_c[C]).                        \tag{7.3}
\]

Then, unconditionally,

\[
 E_d(T)\ge0,\qquad 1\le\frac m{M(T)}\le\frac32,
\]

and exactly

\[
 \boxed{\qquad
 \Gamma_d(T)=\frac m{M(T)}+E_d(T)-\frac m{2^d}.
 \qquad}                                                    \tag{7.4}
\]

Thus the needed new inequality is an unbounded **simultaneous two-colour finite-dimensional excess**

\[
 E_d(T_d)-m_d/2^d\longrightarrow\infty.                      \tag{7.5}
\]

If `m_d=o(2^d)`, this is simply `E_d(T_d)->infinity`. For each fixed template `E_d(T)->0`. For every fixed polynomial template-size range, Section 5 bounds it by a constant depending on that range. Hence a nontrivial uniform-cluster disproof must leave **every** polynomial template-size range and prove a genuinely new, finite-`d`, all-map obstruction in both colours.

No estimate proving (7.1), (7.2), or (7.5) for such a family has been obtained. In particular:

* Fractional matching scarcity cannot by itself supply it: some monochromatic component always covers at least two thirds of the template mass fractionally.
* Nonexistence of affine maps or typical balanced phases does not bound the minimum over all maps in (7.1).
* The torus lower bound does control all maps in its colour, but its complementary complete bipartite pools destroy (7.1).
* A small-treewidth cubical-cover certificate is defeated by the majority-colour local-density inequality.
* Independent smaller-cube choices or a hypothetical multiplicative recurrence for capacities do not establish compatibility on the coordinate faces of one larger cube.

For unrestricted `m` and `s=1`, (7.1) contains the original Ramsey problem itself. The capacity formulation is an exact checkpoint, **not a solution by reformulation**. No concrete super-polynomial template family is asserted to satisfy it.

---

## 8. Verification and preserved specification

The deterministic script

```
Submission/check_cube_hom_capacity_lower_attempt.py
```

was run successfully. Its output is saved in

```
Submission/CubeHomCapacityLowerVerification.txt
```

It does not search for countercolourings. It audits the displayed constructions and inequalities:

* exact rational primal/dual fractional-matching certificates for `P4`, `C5`, a star, a path with an allowed loop, and `K_(2,5)`;
* ten quantile-walk constructions at dimensions `4096` and `8192`, with exact binomial fibre counts, connector legality, the bound (3.5), and the regular-edge marginal identity including loops;
* rejection of an attempted connection between atoms in different components;
* 198 specified binomial residue tests, with both even and odd cycle lengths;
* an actual ordinary injection of `Q_16` into a torus blow-up: **65,536 distinct images and all 524,288 required red edges checked**, with the internal edges explicitly assigned both colours;
* a nonlinear lazy map built from distances to a three-point set, verifying path-independent lattice lifting, the Poincare energy inequality, and the exact two-to-one dimension extension;
* explicit complementary torus pools of size at least one fifth of the template for the tested parameters;
* the exact three-cluster threshold and its ordinary injection at the threshold;
* exact local-neighbourhood edge counts and the majority-colour density certificate on 243 prescribed colour graphs.

These tests check finite constructions, signs, factors, loop incidence, and injectivity. The all-dimensional conclusions rest on the proofs above. The polynomial-template theorem explicitly invokes the established fixed-maximum-degree Ramsey theorem; no uniform bound for growing maximum degree is assumed.

All 90 pre-existing top-level files in `Submission/` were hash-checked against a baseline taken before these additions. `Submission/Spec.lean` remains unchanged, with SHA-256

```
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```

Neither opposed placeholder in that file was used. No Lean proof of the conjecture or its negation is claimed.

**Final status: no genuine disproof was found.**
