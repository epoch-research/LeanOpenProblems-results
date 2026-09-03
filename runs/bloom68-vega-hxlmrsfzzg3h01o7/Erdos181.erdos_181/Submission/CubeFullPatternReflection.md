# Full-injective colour-pattern reflection: audited operator and remaining global gap

## Status

**The dimension-uniform embedding theorem is not proved here.** In particular, this work does not establish an absolute `C` with `R(Q_d) <= C 2^d`, and does not change `Submission/Spec.lean`.

The investigation stays with full-injection pattern counts. It obtains:

* a complete, independently derived reflection operator, including its implementation by unbiased elementary folds;
* the exact nonmonochromatic survival probability `2(d-2)/(d(d-1))` for a specified additional symmetrization — **not** for the plain random two-face retraction, whose probability is `2/d`;
* a universally valid joint-colour, full-injection matrix inequality controlling the negative reflection spectrum by **half-pattern row marginals**;
* a literal injective completion map for collision configurations.

The missing step is to replace the row-marginal control by a sufficiently strong control relative to the maximum **full-pattern** count, or to prove strict count ascent in the zero-monochromatic-count case. Neither step is proved below. The operator calculation is not presented as an embedding theorem. No catalogue of host constructions or previously known collision obstructions is used.

---

## 1. Full counts, and what a fold does and does not do

Let `d >= 2`, `h = 2^d`, and `N >= h`. Write the cube vertex set as `F_2^d`, and let

\[
 c:\binom{[N]}2\longrightarrow\{0,1\}
\]

be an arbitrary colouring. For every pattern `sigma : E(Q_d) -> {0,1}`, set

\[
 T_\sigma
 =\#\{\phi:V(Q_d)\hookrightarrow[N]:
       c(\phi(x)\phi(y))=\sigma(xy)\ \text{for all }xy\in E(Q_d)\}.
\]

Every injection realizes exactly one pattern. Consequently

\[
 \sum_\sigma T_\sigma=(N)_h,
 \qquad M:=\max_\sigma T_\sigma>0.                         \tag{1.1}
\]

Let `m_0,m_1` denote the two constant patterns. The desired conclusion is

\[
 T_{m_0}+T_{m_1}>0.                                        \tag{1.2}
\]

If `g` is a cube automorphism, precomposition by `g` is a bijection on full injections. Therefore `T_{sigma o g}=T_sigma`.

For a graph homomorphism `R:Q_d -> Q_d` that sends every edge to an edge, define the pulled-back pattern

\[
 \sigma^R(xy)=\sigma(R(x)R(y)).
\]

Here `T_{sigma^R}` **still counts injections of all `h` cube vertices**. This notation does not assert that `phi o R` is injective. Indeed, the retractions below are not injective, and composing a host embedding with one of them is not an allowed embedding argument.

### 1.1 The four edge retractions of a square

Order a coordinate pair as `(i,j)`, writing its bits `(a,b)`. Let

* `F_0` send `10 -> 01`, and `F_1` send `01 -> 10`, fixing `00,11`;
* `G_0` send `11 -> 00`, and `G_1` send `00 -> 11`, fixing `01,10`.

Each is an elementary reflection fold. Direct evaluation gives

| Vertex-map composition | Result |
| --- | --- |
| `G_0 o F_0` | `(a,b) -> (0,a+b)` |
| `G_1 o F_0` | `(a,b) -> (a+b+1,1)` |
| `G_0 o F_1` | `(a,b) -> (a+b,0)` |
| `G_1 o F_1` | `(a,b) -> (1,a+b+1)` |

All additions of bits are in `F_2`. Thus the four compositions are exactly

\[
 E_{i\gets c}(a,b)=(c,a+b+c),\qquad
 E_{j\gets c}(a,b)=(a+b+c,c),\quad c\in\{0,1\}.             \tag{1.3}
\]

They fix their image edges pointwise, preserve the sum of the two bits, and take an edge to an edge: changing either input bit changes the surviving output bit. Edges in other coordinates are unchanged in that coordinate. These facts verify parity preservation and edge preservation on the whole cube.

Choosing `F` and `G` independently and uniformly gives a uniform choice among the four edge retractions. There is an order convention to retain: the pattern pullback by `G o F` is `(sigma^G)^F`. Thus, on patterns, the complementary fold is applied first and the ordinary fold second. Both choices are unbiased.

---

## 2. Two-block parity patterns and two-face retractions

For a coordinate set `S`, write

\[
 p_S(x)=\sum_{i\in S}x_i\pmod 2.
\]

Suppose `S` and `S^c` are nonempty. Given four bits

\[
 w=(A_0,A_1,B_0,B_1),
\]

define a pattern `sigma_{S,w}` by

\[
 \sigma_{S,w}(x,x+e_i)=
 \begin{cases}
 A_{p_{S^c}(x)},&i\in S,\\
 B_{p_S(x)},&i\notin S.
 \end{cases}                                               \tag{2.1}
\]

The indexing parity is unchanged along the edge in question, so this is well-defined on unoriented edges. These are pullbacks of a four-edge square pattern under `x -> (p_S(x),p_{S^c}(x))`.

The reduced patterns are those with `S={a}`. Denote their represented state space by `mathcal R_d`. There are at most `16d` actual patterns; keeping a representation causes no difficulty when a pattern has more than one representation.

For ordered distinct coordinates `a,b` and fixed bits `t_j`, `j notin {a,b}`, define

\[
 \begin{aligned}
 R_{a,b,t}(x)_a&=x_a,\\
 R_{a,b,t}(x)_b&=p_{[d]\setminus\{a\}}(x)
                         +p_{[d]\setminus\{a,b\}}(t),\\
 R_{a,b,t}(x)_j&=t_j\quad(j\notin\{a,b\}).
 \end{aligned}                                             \tag{2.2}
\]

This is a retraction onto the specified two-face. On that face the two parity contributions from the fixed coordinates cancel, so it is the identity there. Its total output parity is the input parity. An input edge in coordinate `a` changes output coordinate `a`; every other input edge changes output coordinate `b`. In particular no edge is collapsed.

It can also be built by successively using (1.3) to freeze every `j notin {a,b}` to `t_j` while merging its parity into `b`. Its pullback of an arbitrary pattern belongs to `mathcal R_d`: the `a`-edge colour depends only on the parity of all other input coordinates, and all non-`a` edge colours depend only on `x_a`.

Define the plain operator `P` by choosing `a,b` uniformly among ordered distinct coordinates and all fixed bits `t` independently uniformly, then pulling back by (2.2).

### 2.1 The exact action before taking symmetry classes

For `sigma_{S,w}`, fix a face with ordered free coordinates `p,q` and frozen vector `t`.

* If `p,q in S`, the pullback is constant with colour `A_{p_{S^c}(t)}`.
* If `p,q in S^c`, it is constant with colour `B_{p_S(t)}`.
* If `p in S, q in S^c`, put `c=p_{S\setminus{p}}(t)`. The resulting reduced pattern has distinguished coordinate `p` and square data
  \[
  (A_c,A_{1+c},B_c,B_{1+c}).                                \tag{2.3}
  \]
* If `p in S^c, q in S`, put `c=p_{S^c\setminus{p}}(t)`. Its square data are
  \[
  (B_c,B_{1+c},A_c,A_{1+c}).                                \tag{2.4}
  \]

For example, in the third case,

\[
 p_S(Rx)=x_p+c,\qquad
 p_{S^c}(Rx)=p_{[d]\setminus\{p\}}(x)+c,
\]

which proves (2.3). The fourth case is the same calculation with the blocks interchanged. These rules, together with the specified uniform face law, define the full transition law, not only its survival probability.

### 2.2 The quotient action relevant to counts

Translations of the cube can independently interchange `A_0,A_1` and `B_0,B_1`. Coordinate permutations move the distinguished coordinate. Thus any cube-automorphism-invariant function `u` on patterns, including `u=T`, has a well-defined reduced value `u_1(w)` independent of the chosen distinguished coordinate and invariant under those two interchanges.

Put

\[
 \begin{aligned}
 w^\top&=(B_0,B_1,A_0,A_1),\\
 A_u(w)&=\tfrac12\bigl(u(m_{A_0})+u(m_{A_1})\bigr),\\
 B_u(w)&=\tfrac12\bigl(u(m_{B_0})+u(m_{B_1})\bigr).
 \end{aligned}
\]

Let `s=|S|`, `t=d-s`. Counting the four cases above proves

\[
 \boxed{
 (Pu)(\sigma_{S,w})=
 \frac{s(s-1)}{d(d-1)}A_u(w)
 +\frac{t(t-1)}{d(d-1)}B_u(w)
 +\frac{st}{d(d-1)}\bigl(u_1(w)+u_1(w^\top)\bigr).}         \tag{2.5}
\]

When the face uses two coordinates from one block, the other block is nonempty and wholly frozen; its frozen parity is uniform. This justifies the monochromatic averages in (2.5), including the cases where one block has size one.

In particular, for `s=1`,

\[
 (Pu)(\sigma_{\{a\},w})
 =\frac{u_1(w)+u_1(w^\top)}d+\frac{d-2}{d}B_u(w).            \tag{2.6}
\]

If `w` is nonconstant, a face using both blocks sees all four entries of `w`, and hence remains nonconstant. A face contained in one block is monochromatic. Therefore the **plain** operator has exact nonmonochromatic survival probability

\[
 \boxed{\beta_d^{\rm plain}=2/d.}                           \tag{2.7}
\]

It is not `2(d-2)/(d(d-1))`.

---

## 3. Unbiased-fold implementation of the entire operator `P`

A deterministic composition producing (2.2) specifies which coordinate is frozen at every merge. Such conditioning is not automatically an unbiased reflection average. The following implementation removes that issue.

Fix the distinguished coordinate `a`; let `m=d-1` be the number of other coordinates. Maintain a vertex map `R`, initially the identity, and update it by right composition

\[
 R\longleftarrow R\circ E,
\]

where `E` is a uniform edge retraction (1.3) on two coordinates other than `a`.

On these `m` coordinates, write the affine map as

\[
 R(x)=Ax+c.
\]

Every column of `A` is a coordinate unit vector. Label input position `i` by `ell_i` when its column is `e_{ell_i}`. The labels are initially all distinct. Choose uniformly a pair of positions with different labels; apply a uniform one of the four edge retractions on that pair.

If coordinate `i` is frozen and `j` survives, both columns become the old column at `j`; conversely both become the old column at `i`. These alternatives have probability one half each. The frozen bit is an independent fair bit. Thus the label update copies one of the two labels to the other position, with equal probabilities. Stop when all labels agree.

### 3.1 Almost-sure termination and exact expected length

Let `n_b` be the number of positions carrying label `b`, and set

\[
 Z=\sum_b n_b^2.
\]

For a selected pair with distinct labels having populations `u,v`, the two changes in `Z` are

\[
 2(u-v)+2\quad\text{and}\quad2(v-u)+2.
\]

Their mean is exactly `2`. Before absorption, `m <= Z <= m^2`. If `tau` is the number of compound steps, stopped telescoping gives

\[
 \mathbb E Z_{k\wedge\tau}=m+2\mathbb E(k\wedge\tau)\le m^2.
\]

Monotone convergence yields `E tau <= m(m-1)/2`, so termination is almost sure. At termination `Z=m^2`; bounded convergence then gives the exact value

\[
 \boxed{\mathbb E\tau=\binom m2.}                           \tag{3.1}
\]

For `m=1` the process has length zero.

Each `n_b` is a bounded martingale: a step involving label `b` changes its population by `+1` or `-1` equiprobably. Initially `n_b=1`, and finally it is `m` or zero. Hence each surviving label has probability `1/m`.

### 3.2 The frozen face is uniform, not just the surviving coordinate

Every step preserves total parity. At termination all columns are `e_b`, so on these coordinates

\[
 R(x)=p_{[m]}(x)e_b+c,
 \qquad \sum_j c_j=0.
\]

Consequently the frozen coordinates are `t_j=c_j`, `j != b`, and
`c_b=sum_{j != b} t_j`, exactly as in (2.2).

To identify their distribution, conjugate the entire process by a translation `x -> x+v` on the `m` coordinates. A conjugated edge retraction freezing coordinate `i` to `c` freezes it to `c+v_i`; hence the uniform four-retraction law is unchanged. The chosen-pair rule depends only on the linear columns and is also unchanged. The initial identity map is unchanged by conjugation.

For a terminal map with surviving label `b`, conjugation changes its constant term to

\[
 c+v+Av.
\]

On coordinates `j != b` this changes `t_j` to `t_j+v_j`. These translations act transitively on all `2^(m-1)` frozen vectors, while leaving `b` fixed. Thus, conditionally on `b`, the frozen vector is uniform.

After also choosing `a` uniformly, the terminal map has **exactly** the law of `R_{a,b,t}` defining `P`.

This is an unbiased elementary-fold implementation of `P`: every compound step is two independent fair elementary folds, in the pattern order specified in Section 1.1. Its random length has finite expectation. Intermediate vertex maps need not be retractions, but they are edge-preserving, parity-preserving homomorphisms; only patterns, not host embeddings, are composed with them.

---

## 4. The additional symmetrization and the claimed coefficient

Start with a represented reduced pattern `sigma_{{a},w}`. Define `Q_a` as follows:

1. choose `j != a` uniformly;
2. apply a uniform one of the four edge retractions on `(a,j)`.

Then apply an independent `P`. Call this reduced-state operator `K`.

Half of the four retractions freeze the old distinguished coordinate `a`. Freezing it to `c` makes the entire pulled-back pattern monochromatic of colour `B_c`.

The other half freeze `j` to `c`. The resulting pattern has blocks

\[
 S=\{a,j\},\qquad S^c=[d]\setminus\{a,j\},
\]

with both index pairs of `w` shifted by `c`. When `d>=3`, these shifts do not change the value of an automorphism-invariant `u`. Applying (2.5) with `s=2` gives

\[
 \boxed{
 \begin{aligned}
 (Ku)(\sigma_{\{a\},w})={}&
 \frac{1}{d(d-1)}A_u(w)
 +\frac{d^2-3d+3}{d(d-1)}B_u(w)\\
 &+\frac{d-2}{d(d-1)}
       \bigl(u_1(w)+u_1(w^\top)\bigr).
 \end{aligned}}                                            \tag{4.1}
\]

For `d=2`, the first compound fold already maps the entire square onto an edge. It gives each of the four edge colours with probability `1/4`. Formula (4.1) still holds: its last coefficient is zero and the other two coefficients are `1/2`.

For a nonconstant `w` and `d>=3`, the only nonmonochromatic branch is:

* the initial fold freezes `j`, of probability `1/2`;
* the subsequent two-face uses one coordinate from each of the blocks of sizes `2,d-2`, of probability `4(d-2)/(d(d-1))`.

Thus

\[
 \boxed{\beta_d=\frac{2(d-2)}{d(d-1)}}                       \tag{4.2}
\]

is independently verified for this explicit `K`. For `d=2` it is zero, as required.

### 4.1 Full reduced quotient matrix

Index a square datum by

\[
 (u,v)=(A_0+A_1,B_0+B_1)\in\{0,1,2\}^2.
\]

Translations justify identifying the two orderings within each pair. There are nine represented quotient states. The monochromatic ones are `(0,0)` and `(2,2)`; the other seven are nonmonochromatic. Formula (4.1) gives every entry of the quotient transition matrix: `A_u` and `B_u` choose the corresponding monochromatic colours in their indicated proportions, and the two remaining terms go to `(u,v)` and `(v,u)`.

On the seven nonmonochromatic states the transition submatrix is exactly

\[
 K_{\rm tr}=q_d(I+S),\qquad
 q_d=\frac{d-2}{d(d-1)},                                    \tag{4.3}
\]

where `S(u,v)=(v,u)`. It has row sum `beta_d`, eigenvalue `beta_d` on the swap-symmetric subspace, and eigenvalue zero on the swap-antisymmetric subspace. The spectral radius is `beta_d` (zero at `d=2`). Starting at any represented nonmonochromatic reduced pattern, survival after `k` applications is exactly `beta_d^k`.

This is a pattern-space assertion, not a count comparison.

---

## 5. Exact full-injection reflection defects

Let `rho` be either kind of elementary reflection on a coordinate pair. Its fixed vertex set `F` has size `2r`, and its two exchanged interiors `U,V` have size `r`, where

\[
 r=h/4.
\]

There are no cube edges between `U` and `V`. Reflection identifies the two half templates and fixes `F` pointwise.

Fix a pattern `sigma`. For each injection `f:F -> [N]` realizing the boundary pattern, let

\[
 X_f=[N]\setminus f(F),\qquad n=|X_f|=N-2r.
\]

For an `r`-subset `S` of `X_f`, let `a_f(S)` count injective `U`-extensions with image `S` satisfying all left-half constraints. Let `b_f(S)` count the reflected right-half extensions, using the same left-half labels to index their domain.

Let `Dmat` be the disjointness matrix on the `r`-subsets of `X_f`:

\[
 Dmat(S,T)=\mathbf1_{S\cap T=\varnothing}.
\]

All vertex capacities are now explicit. If `sigma_L,sigma_R` are the two folded patterns, then

\[
 \begin{aligned}
 T_\sigma&=\sum_f a_f^{\mathsf T}Dmat\,b_f,\\
 T_{\sigma_L}&=\sum_f a_f^{\mathsf T}Dmat\,a_f,\\
 T_{\sigma_R}&=\sum_f b_f^{\mathsf T}Dmat\,b_f.
 \end{aligned}                                             \tag{5.1}
\]

Indeed the boundary is injective; each half is injective into its unused host set; disjointness of the two half images is exactly the remaining full-injectivity requirement. These constructions and restrictions are inverse bijections.

Define the arithmetic reflection defect

\[
 \Delta_\rho(\sigma)
 :=T_\sigma-\tfrac12(T_{\sigma_L}+T_{\sigma_R}).
\]

For `v_f=a_f-b_f`, expansion of the quadratic form gives

\[
 \boxed{\Delta_\rho(\sigma)
       =-\tfrac12\sum_f v_f^{\mathsf T}Dmat\,v_f.}           \tag{5.2}
\]

There is no positivity assertion in (5.2).

### 5.1 Spectrum, with normalization audited

Put

\[
 L=\binom nr,\qquad D=\binom{n-r}r,
 \qquad q=\frac{r}{n-r}=\frac{h}{4N-3h}.
\]

The matrix `Dmat` has row sum `D`. Its eigenvalues are

\[
 \kappa_j=(-1)^j\binom{n-r-j}{r-j}
          =D(-1)^j\frac{(r)_j}{(n-r)_j},\quad 0\le j\le r.  \tag{5.3}
\]

For completeness, put `V_{-1}=0`, and for each `j>=0` let `V_j` be spanned by the functions
`1_{A subset S}`, `|A|=j`, on the `r`-subsets. These spaces are nested and `V_r` is the full space. Disjointness sends such a function to

\[
 \binom{n-r-j}{r-j}\mathbf1_{A\cap S=\varnothing}
 =\binom{n-r-j}{r-j}
      \sum_{B\subseteq A}(-1)^{|B|}\mathbf1_{B\subseteq S}.
\]

Modulo `V_{j-1}` this is `kappa_j` times the original function. Self-adjointness therefore gives that eigenvalue on `V_j intersect V_{j-1}^perp`, proving (5.3).

With Euclidean norms and orthogonal projections `Pi_j`, (5.2) is exactly

\[
 \Delta_\rho(\sigma)=
 \frac D2\sum_f\sum_{j\ \mathrm{odd}}
       \frac{(r)_j}{(n-r)_j}\|\Pi_jv_f\|^2
 -\frac D2\sum_f\sum_{j\ \mathrm{even}}
       \frac{(r)_j}{(n-r)_j}\|\Pi_jv_f\|^2.                 \tag{5.4}
\]

The even sum includes `j=0`. No factor of `L` is missing: these are Euclidean, not uniform-probability, norms.

Since `n>=2r`, every nonconstant eigenvalue is at least `-qD`. More precisely,

\[
 Dmat\succeq D\left((1+q)\frac{\mathbf1\mathbf1^{\mathsf T}}L
                         -qI\right).                     \tag{5.5}
\]

For `N>=Ch`, `q<=1/(4C-3)`. This small spectral factor by itself does not bound the squared extension-family norms relative to `M`.

---

## 6. What joint complementary-colour normalization actually proves

This section sums **all** colour patterns, rather than treating a selected monochromatic extension family in isolation.

Fix a boundary pattern `gamma`. For each compatible boundary injection `f`, index all left-half patterns by `alpha`, and let `w_{f,alpha}(S)` count their injective extensions with image `S`. The half includes its internal edges and its edges to the boundary. There are

\[
 B_d=2^{(d-2)r/2+2r}=2^{(d+2)r/2}                          \tag{6.1}
\]

possible half patterns. Every bijection from the labelled half to `S` realizes one and only one such pattern, so

\[
 \boxed{\sum_\alpha w_{f,\alpha}(S)=r!.}                   \tag{6.2}
\]

Define the full-pattern sector matrix

\[
 C_{\alpha\beta}
   =\sum_f w_{f,\alpha}^{\mathsf T}Dmat\,w_{f,\beta}.
                                                                  \tag{6.3}
\]

It is symmetric, and its entries are exactly the full-injection counts
`T_{gamma,alpha,beta}`. In particular

\[
 0\le C_{\alpha\beta}\le M.                                \tag{6.4}
\]

Write

\[
 R=C\mathbf1,\qquad S_*=\mathbf1^{\mathsf T}C\mathbf1.
\]

These are **row marginals**, not maximum full-pattern counts. If `g` is the number of compatible boundary injections, then

\[
 \begin{aligned}
 R_\alpha&=Dr!\sum_f Z_{f,\alpha},
       &Z_{f,\alpha}&=\sum_S w_{f,\alpha}(S),\\
 S_*&=gD(r!)^2L.
 \end{aligned}                                             \tag{6.5}
\]

If `g=0`, the whole matrix is zero. Otherwise `S_*>0`, since `N>=h` permits unrestricted injective extensions of each boundary map.

### Theorem 6.1 — joint full-injection PSD correction

For every host colouring, every elementary cube reflection, and every boundary pattern with `S_*>0`,

\[
 \boxed{
 C+q\operatorname{diag}(R)
       -\frac{1+q}{S_*}RR^{\mathsf T}\succeq0.}             \tag{6.6}
\]

All entries defining `C`, `R`, and `S_*` count full injections. No monochromatic-count or quasirandomness hypothesis is imposed.

**Proof.** For a real coefficient vector `x`, put

\[
 z_f(S)=\sum_\alpha x_\alpha w_{f,\alpha}(S).
\]

By (6.2) and weighted Cauchy–Schwarz,

\[
 z_f(S)^2\le r!\sum_\alpha x_\alpha^2w_{f,\alpha}(S).       \tag{6.7}
\]

Apply (5.5), sum over `f`, and use (6.7):

\[
 x^{\mathsf T}Cx
 \ge\frac{D(1+q)}L\sum_f
       \left(\sum_\alpha x_\alpha Z_{f,\alpha}\right)^2
       -q\sum_\alpha R_\alpha x_\alpha^2.
\]

Cauchy–Schwarz over the `g` boundary maps bounds the first term below by

\[
 \frac{D(1+q)}{Lg}
       \left(\sum_{f,\alpha}x_\alpha Z_{f,\alpha}\right)^2
 =\frac{1+q}{S_*}(x^{\mathsf T}R)^2,
\]

using (6.5). This proves (6.6). `□`

For distinct `alpha,beta`, applying (6.6) to `e_alpha-e_beta` gives the genuine finite-population reflection comparison

\[
 \boxed{
 \begin{aligned}
 C_{\alpha\beta}
 -\tfrac12(C_{\alpha\alpha}+C_{\beta\beta})
 \le{}&\frac q2(R_\alpha+R_\beta)\\
 &-\frac{1+q}{2S_*}(R_\alpha-R_\beta)^2.
 \end{aligned}}                                            \tag{6.8}
\]

For equal indices the reflection defect is zero.

### 6.1 Where the maximum normalization stops helping

The last square in (6.8) is a useful negative correction, but when the two row marginals agree it contributes nothing. From maximality alone, (6.4) gives only

\[
 R_\alpha\le B_d M,
 \qquad \Delta_\rho(\sigma)\le qB_dM.                       \tag{6.9}
\]

The factor `B_d` is not dimension-uniform. It is not a collision volume silently discarded from the proof; it is the number of unconstrained half-colour sectors in the actual full-injection row marginal.

There is also an exact way to see what complementarity cancels spectrally. Let `W` map a vector of half-sector coefficients to the direct sum of the extension-family vectors over `f`. If `Dmat=Dmat_+-Dmat_-` is its positive/negative spectral decomposition, then

\[
 C=C^+-C^-,\qquad
 C^\pm=W^{\mathsf T}(I\otimes Dmat_\pm)W,
 \qquad C^-\mathbf1=0.                                    \tag{6.10}
\]

The last identity follows from (6.2), since the negative spectral part annihilates a constant vector. Thus all complementary colour terms are included jointly. However, the bounds `C_{alpha beta}<=M` bound their **difference** `C^+-C^-`, not the individual negative quadratic form on `e_alpha-e_beta`. The proof of (6.6) controls that issue by row marginals; it does not remove them.

No estimate converting (6.8) into the required dimension-uniform, maximum-relative bound was obtained. In particular (6.6) is not being interpreted as positivity of connected cumulants.

---

## 7. The exact global defect that would have to be controlled

To avoid assuming that a positive maximum has already transferred into the reduced space, define one operator `H` on arbitrary patterns by the following three stages:

1. apply `P`, retaining its represented distinguished coordinate;
2. apply the targeted compound fold `Q_a` from Section 4;
3. apply a new independent `P`.

All outputs are reduced. Conditional on a nonmonochromatic output of the first stage, the last two stages have survival probability exactly `beta_d`; conditional on a monochromatic output, they stay monochromatic.

Thus, **under the assumption** `T_{m_0}=T_{m_1}=0`,

\[
 (HT)(\sigma)\le\beta_d M\quad\text{for every }\sigma.      \tag{7.1}
\]

This conclusion uses only the transition law and the definition of `M`; it does not compare the input count with the output count.

Implement the two copies of `P` by Section 3. The expected number of compound folds is

\[
 L_d=2\binom{d-1}2+1=(d-1)(d-2)+1.                         \tag{7.2}
\]

There are two elementary folds per compound fold. Let `sigma_k` be the random current pattern immediately before an elementary fold, `rho_k` its reflection, and `nu` the total number of elementary folds. The choices within each compound step are fair, and stopping occurs only at compound boundaries. Consequently conditional expectation and telescoping give the exact identity

\[
 \boxed{
 T_\sigma-(HT)(\sigma)
  =\mathbb E_\sigma\sum_{k<\nu}\Delta_{\rho_k}(\sigma_k).}   \tag{7.3}
\]

This also holds for the random stopping times used here: every count is between `0` and `M`, every defect has absolute value at most `M`, and `E nu=2L_d<infinity`. These bounds justify passing from finite stopped sums to (7.3).

Now let `sigma_*` attain the full maximum `M`. If both monochromatic counts vanish, (7.1) and (7.3) imply

\[
 \mathbb E_{\sigma_*}\sum_{k<\nu}\Delta_{\rho_k}(\sigma_k)
       \ge(1-\beta_d)M.                                   \tag{7.4}
\]

The proved estimate (6.9) gives only

\[
 \mathbb E_{\sigma_*}\sum_{k<\nu}\Delta_{\rho_k}(\sigma_k)
       \le 2L_d qB_dM,                                    \tag{7.5}
\]

which is quantitatively insufficient at every fixed multiplier `N/h=C` as `d` grows.

### The unresolved zero-level estimate

To complete this particular route, one would need a joint-colour argument, valid for `N>=C 2^d` with an absolute `C`, that contradicts (7.4), for example by proving in the zero-monochromatic-count case that

\[
 \mathbb E_{\sigma_*}\sum_{k<\nu}\Delta_{\rho_k}(\sigma_k)
       <(1-\beta_d)M.                                    \tag{7.6}
\]

The signed defects in (5.4), rather than separately discarded collision terms, occur in this target. **I have not proved (7.6).** Its appearance as a sufficient estimate is not a settlement of the Ramsey problem.

There are two normalization points worth making explicit:

* The fact that `P` maps patterns into `mathcal R_d` does **not** prove that any positive full-injection count transfers there. The first stage of `H` includes this unresolved transfer in (7.3), rather than presuming it.
* If one instead proved `M_R:=max_{tau in mathcal R_d}T_tau >= a_d M` and used a reduced comparison with multiplicative constant `lambda_d` and additive error `epsilon_d M`, the zero-level contradiction would require
  \[
    \lambda_d\beta_d+\epsilon_d/a_d<1.
  \]
  Mere positivity of `M_R` is not enough to absorb an additive error normalized by the larger global `M`.

---

## 8. A literal collision-to-injection replacement, and the unproved ascent

The following map audits the proposed replacement step without calling a partially injective object an injection.

Let `S subset V(Q_d)` have size `s`, put `W=V(Q_d)\setminus S`, and fix a pattern `eta` on the edges induced by `W`. Let `U_eta` count injections `W -> [N]` realizing `eta`. Every such injection has exactly `(N-h+s)_s` injective extensions to all vertices, before imposing any colours on edges incident to `S`. Each extension realizes a unique full pattern. Therefore

\[
 \boxed{
 (N-h+s)_s U_\eta
  =\sum_{\tau:\,\tau|_{E(Q_d[W])}=\eta}T_\tau.}             \tag{8.1}
\]

There are exactly

\[
 2^{b(S)},\qquad b(S)=ds-e(Q_d[S]),                          \tag{8.2}
\]

terms on the right, since this is the number of edges incident to `S`. Maximality consequently gives the all-subsets, capacity-sensitive bound

\[
 U_\eta\le\frac{2^{b(S)}}{(N-h+s)_s}M.                       \tag{8.3}
\]

Now fix an equality partition `pi` of the source vertices and one representative from each block. Let the representatives be `W` and the nonrepresentatives be `S`; thus `pi` has `h-s` blocks. Let `J_{pi,sigma}` count maps realizing `sigma` with **exactly** equality partition `pi`. Such a map is injective on `W` but is not a full injection unless `s=0`. If an adjacent pair is identified, this count is zero because the host has no loops.

For each counted map `phi`, choose an injection

\[
 z:S\hookrightarrow[N]\setminus\phi(W).
\]

Define a new map by

\[
 \psi(w)=\phi(w)\ (w\in W),\qquad \psi(s)=z(s)\ (s\in S).
                                                                  \tag{8.4}
\]

This is a full injection: both restrictions are injective and their images are disjoint. Its pattern agrees with `sigma` on `E(Q_d[W])`. Given `pi`, the representatives, and `psi`, the old map is recovered as

\[
 \phi(v)=\psi(\operatorname{rep}_\pi(v)),
\]

and `z=psi|S`. Thus `(phi,z) -> psi` is an injection on this completion family. No division by an unverified multiplicity is used. It follows that

\[
 \boxed{
 J_{\pi,\sigma}(N-h+s)_s
 \le\sum_{\tau:\,\tau|_{E(Q_d[W])}=\sigma|_{E(Q_d[W])}}T_\tau
 \le 2^{b(S)}M.}                                         \tag{8.5}
\]

If `J_{pi,sigma}>0`, there is a pattern arising among these actual completions with count at least

\[
 \frac{J_{\pi,\sigma}(N-h+s)_s}{2^{b(S)}}.                  \tag{8.6}
\]

This makes the replacement literal, but it does **not** prove strict ascent. To force a count greater than `M` by this argument, the first numerator would have to exceed `2^{b(S)}M`. No such lower bound was obtained for an identified-pair family arising from reflection. Nor was a signed, bounded-multiplicity aggregation over all collision partitions obtained. Different partitions can lead to the same completed injection, so simply summing their completion families is not an injective charging argument.

Equations (8.1)–(8.6) retain all capacity constraints. They identify the exact missing counting inequality in the proposed zero-level replacement, rather than asserting that spare host vertices automatically give a more numerous full-pattern sector.

---

## 9. What the determinant representation contributes to this attempt

Let `E,O` be the cube parity classes, each of size `m=h/2`. For an injection `f:E -> [N]`, use the unused host set `X_f`, and define the zero-one list matrix

\[
 L_{\sigma,f}(y,v)
   =\prod_{x\in N_{Q_d}(y)}
       \mathbf1_{c(f(x)v)=\sigma(xy)},
 \qquad y\in O,\ v\in X_f.
\]

With independent signs `epsilon_{yv}`, set `A=epsilon*L`. Cauchy–Binet and expansion of each squared determinant give

\[
 \mathbb E\det(AA^{\mathsf T})
 =\sum_{S\in\binom{X_f}m}\operatorname{per}(L_{\sigma,f}[O,S]).
                                                                  \tag{9.1}
\]

In detail, different bijections in a determinant expansion give different sign monomials, so their cross terms have expectation zero; the identical-bijection terms have square one and count permitted bijections. The column set is a subset, not a multiset. Summing (9.1) over `f` therefore counts precisely the full injections:

\[
 T_\sigma=\sum_f\mathbb E\det(AA^{\mathsf T}).               \tag{9.2}
\]

In the direct-sum Hilbert space with coordinates `(f,S)` and the sign functions `det(A[O,S])`, call the corresponding vector `V_sigma`. If `sigma != tau`, expansion of the inner product again leaves only identical bijections. At an edge where the two patterns differ their indicator products vanish. Hence

\[
 \langle V_\sigma,V_\tau\rangle=0\quad(\sigma\ne\tau),
 \qquad \|V_\sigma\|^2=T_\sigma,
 \qquad \sum_\sigma\|V_\sigma\|^2=(N)_h.                  \tag{9.3}
\]

Thus maximal full-pattern normalization supplies

\[
 \left\|\sum_\sigma a_\sigma V_\sigma\right\|^2
     \le M\sum_\sigma|a_\sigma|^2.                          \tag{9.4}
\]

What is absent is a bounded operator or charging map converting the negative reflection vectors in (5.4) into a combination in (9.4) with the necessary coefficient bound. The naive operation on an injection would be composition with a noninjective retraction, which leaves this Hilbert basis of full injections. Section 8 gives an actual repair, but not the needed norm or strict-ascent bound. Applying Cauchy–Schwarz to the already orthogonal sector vectors alone does not prove positivity of either monochromatic sector.

---

## 10. Verification and final audit

The executable audit is

```
python3 Submission/check_cube_full_pattern_reflection.py
```

Its saved output is `Submission/CubeFullPatternReflectionVerification.txt`. It checks:

* all four compound-fold tables, edge preservation, parity preservation, idempotence, and the deterministic formula for two-face retractions through dimension 6;
* the exact action of `P` on all 16 square patterns, every nonempty proper block size, and dimensions 2 through 7;
* the exact action of `K`, including all monochromatic branches and the coefficient (4.2), on all 16 patterns in those dimensions;
* every label update used in the stopped-fold implementation for up to five active coordinates, including the affine constants and the exact `+2` potential drift;
* direct enumeration of full injections for the Kneser identities (5.1)–(5.2) and completion identity (8.1) in finite test cases;
* exact rational Schur-complement certificates for (6.6) on all boundary-sector matrices in those matrix test cases.

The finite checks passed. They supplement the proofs above; they are not tests of the missing all-dimensional assertion (7.6).

The specification hash before and after this work is

```
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```

No declaration from `Spec.lean`, including either existing `sorry`, is used as an assumption in this report. No Lean theorem or specification was edited.

**Exact remaining gap:** prove a maximum-relative, jointly complementary-colour control of the signed full-injection defects strong enough to contradict (7.4), including the initial transfer into the reduced space; or prove that the literal completion construction forces a strictly larger normalized full-pattern count whenever the required zero-level reflection fails. The row-marginal estimate (6.6), the positive determinant identity, and the verified absorbing operator do not supply that step. There is therefore no audited proof of `R(Q_d) <= C 2^d` here.
