# Joint-colour signed counting: an iterable positive-core bound, but not a completion

## Outcome

**The full assertion `R(Q_d) <= C 2^d` is not proved.** No dimension-independent
constant `C` for arbitrary colourings is claimed. `Submission/Spec.lean` is
unchanged, and neither of its admitted conclusions is used.

There is substantive all-orders progress, rather than another bounded-size
activity calculation:

* Sections 2--4 prove a **finite-population collision bound for arbitrary
  real-stable positive core image polynomials**. It permits arbitrarily large
  cores and unrestricted positive core weights. At flat occupation it loses
  only the birthday-scale factor `exp(-O(h^2/N))`, not an additive error against
  a largest pattern. The single-coordinate capacity bound is sharp, and it
  really iterates through every host site using one fixed capacity exponent.
* It specializes to an explicit **sum-of-squares inequality for disjoint
  determinant cores**, including all isolated-vertex additions. Positivity is
  proved for these genuinely disjoint cores, not inferred from a Gram kernel's
  connected cumulants.
* Section 5 gives the **exact equality with full injective cube counts**, and
  a quantitative lower bound, after conditioning on an injective parity-class
  map. All remaining cube neighbourhoods, of arbitrary arity and with arbitrary
  overlaps, are included simultaneously.
* Two tempting ways to finish the argument fail. Averaging the two colours
  **before** taking connected cumulants creates large negative activities even
  in an all-red host (section 6). Averaging the positive pinned core laws does
  **not** preserve real stability, even in a symmetric two-part colouring with
  perfectly flat marginals (section 7).

**Exact remaining gap:** no argument here forces a positive red or blue pinned
sector with the required occupation/capacity control when `N >= C 2^d`.
Alternatively, an overlap-compatible stable positive-core decomposition with
that control would suffice, but none is constructed for the whole cube. The
unrestricted scalar negative-activity criterion is not applied to all cube
supports.

These are mathematical proofs and executable audits, not new Lean
formalizations. No literature novelty is claimed for the capacity machinery.

---

## 1. Keep the global injection and the global colour sign

Let `H=Q_d`, `h=2^d`, `e=dh/2`, and let `A` be the red adjacency matrix of a
complete two-colouring on `[N]`. Put

\[
 M=2B=2A-(J-I).
\]

Thus `M_xy` is `+1` or `-1` for distinct host vertices, and `M_xx=0`.
For independent uniform `X_u`, use exactly

\[
 f_{uv}(z)=-\mathbf1[X_u=X_v]
       +\mathbf1[uv\in E(H)]zM(X_u,X_v),\qquad
 \Xi(z)=\mathbb E\prod_{\{u,v\}\subset V(H)}(1+f_{uv}(z)).
\]

Every noninjective assignment has a zero pair factor, including collisions
between nonadjacent source vertices. On an injection the edge factors at
`z=+1,-1` are twice the red and blue indicators, respectively. Hence

\[
 \boxed{\Xi(+1)+\Xi(-1)=\frac{2^e}{N^h}(T_R+T_B),}       \tag{1.1}
\]

where `T_R,T_B` count labelled **full injections**. Equivalently,

\[
 \Xi(+1)+\Xi(-1)
 =\frac{2}{N^h}\sum_{\phi:V(H)\hookrightarrow[N]}
       \sum_{\substack{S\subseteq E(H)\\ |S|\text{ even}}}
            \prod_{uv\in S}M_{\phi(u),\phi(v)}.           \tag{1.2}
\]

In particular, disjoint odd spectral components are not individually deleted:
their product survives when the **total** parity is even. Parity-projecting each
connected activity separately would not give (1.2).

The positive-core expansion below evaluates (1.1), not a homomorphism surrogate
for it. Intermediate polynomials that allow repeated labels are explicitly
marked as such; square-free extraction is always performed before identifying
them with an injective count.

---

## 2. A sharp one-site capacity bound

For a polynomial with nonnegative coefficients and a vector
`alpha in [0,1]^n`, define

\[
 \operatorname{Cap}_{\alpha}(P)
    =\inf_{x_1,\ldots,x_n>0}\frac{P(\mathbf x)}{\prod_v x_v^{\alpha_v}}.
                                                               \tag{2.1}
\]

Let

\[
 \mathcal T_vP=P|_{x_v=0}+x_v\,\partial_vP|_{x_v=0},\qquad
 \operatorname{SF}P=\left(\prod_v\mathcal T_v\right)P.      \tag{2.2}
\]

`SF` discards every monomial that uses a host site more than once. It does
not identify or subsequently repair repeated labels. The operators commute.

A real polynomial is **real stable** if it is nonzero whenever every variable
has strictly positive imaginary part. Here the zero polynomial is allowed as
a degenerate output of a stability-preserving operation, not as a positive
core. Real stability is a substantially stronger hypothesis than nonnegative
coefficients or positivity of a scalar partition function.

For an integer `D>=1` and `0<=a<=1`, put

\[
 g_D(a)=\frac{(1-a/D)^{D-a}}{(1-a)^{1-a}},\qquad
 g_\infty(a)=\frac{e^{-a}}{(1-a)^{1-a}},                  \tag{2.3}
\]

with `0^0=1`. Thus `g_D(0)=1`, `g_1(a)=1`, and
`g_D(1)=(1-1/D)^{D-1}`.

### Lemma 2.1: first-degree truncation preserves real stability

If `P` is real stable, then `T_v P` is real stable or zero. Nonnegative
coefficients remain nonnegative.

**Proof.** The elementary real-boundary specialization property says that
`P|_{x_v=0}` is stable or zero. It follows by taking `x_v=i epsilon` and
applying Hurwitz's nonvanishing-limit theorem; the multivariate version follows
by restriction to complex lines in the product upper half-plane.

Suppose first that `P_0=P|_{x_v=0}` is not identically zero. Fix all the other
variables in the upper half-plane. The resulting polynomial `p(t)` has no root
in that half-plane and `p(0)=P_0 != 0`. If its roots are `lambda_j`, then

\[
 \frac{p'(0)}{p(0)}=\sum_j\frac1{-\lambda_j}
\]

has nonpositive imaginary part. If this ratio is nonzero, the only root of
`p(0)+t p'(0)` is its negative reciprocal, again with nonpositive imaginary
part. If the ratio is zero, the truncation is a nonzero constant. Therefore
`T_v P` never vanishes with all variables in the upper half-plane.

If `P_0` is identically zero, write `P=x_v^k Q` with `k>=1` maximal. The
polynomial `Q` is stable. If `k>=2`, the truncation is zero. If `k=1`, it is
`x_v Q|_{x_v=0}`, which is stable by the same specialization property. This
proves the lemma. `□`

This lemma concerns **host occupation polynomials**, not PSD graph products
or connected cumulants.

### Lemma 2.2: the single-variable estimate

Let `p(t)=a_0+a_1t+...` have nonnegative coefficients, all roots real and
nonpositive, and degree at most `D`. For `0<=a<=1`,

\[
 \boxed{\operatorname{Cap}_a(a_0+a_1t)
       \ge g_D(a)\operatorname{Cap}_a(p).}                \tag{2.4}
\]

The constant `g_D(a)` is sharp for this assertion.

**Proof.** For `a_0,a_1>0`, write

\[
 p(t)=a_0\prod_{j=1}^D(1+r_jt),\qquad
 r_j\ge0,\qquad \sum_jr_j=a_1/a_0=:s,
\]

padding with zero `r_j` if necessary. The arithmetic-geometric mean inequality
gives, for every `t>0`,

\[
 p(t)\le a_0(1+st/D)^D.
\]

For `0<a<1`, direct minimization therefore gives

\[
 \begin{aligned}
 \operatorname{Cap}_a(p)
  &\le a_0^{1-a}a_1^a a^{-a}(1-a/D)^{-(D-a)},\\
 \operatorname{Cap}_a(a_0+a_1t)
  &=a_0^{1-a}a_1^a a^{-a}(1-a)^{-(1-a)}.
 \end{aligned}                                             \tag{2.5}
\]

Their ratio proves (2.4). For example, the first minimum is evaluated at
`t=aD/(s(D-a))`, not at the minimizer of the truncated polynomial.

The endpoints are included by limits, or directly: `Cap_0(p)=a_0`, and the
linear polynomial has `Cap_1=a_1`. If `a_0=0`, then for `a<1` the original
capacity is zero; for `a=1` both capacities equal `a_1`. If `a_0>0,a_1=0`,
real-rootedness forces `p` to be constant, and the assertion is immediate.
The identically zero case is also immediate.

For `p(t)=(1+rt)^D`, the AM--GM step is an equality, and both displayed
capacities can be evaluated exactly. Their ratio is `g_D(a)`, including the
endpoints. Thus the constant is sharp. `□`

### Lemma 2.3: a capacity invariant which really iterates

Let `P` be real stable with nonnegative coefficients and degree at most `D_v`
in `x_v`, where `D_v>=1`. For any fixed `alpha in [0,1]^n`,

\[
 \operatorname{Cap}_{\alpha}(\mathcal T_vP)
       \ge g_{D_v}(\alpha_v)\operatorname{Cap}_{\alpha}(P).
                                                               \tag{2.6}
\]

**Proof.** Fix positive real values of all other variables. By real stability,
real-boundary specialization, and real coefficients, the remaining univariate
polynomial is real-rooted. Its coefficients are nonnegative, so its roots are
nonpositive. Apply (2.4), divide by the other `x_u^{alpha_u}`, and take their
infimum. Infima over separate positive variables commute. `□`

By Lemma 2.1 the next truncated polynomial again has the needed stability and
coefficient signs. Its remaining degrees have not increased. Consequently,
with the **same exponent vector at every stage**, (2.6) gives

\[
 \boxed{\operatorname{SF}P(\mathbf1)
 \ge \operatorname{Cap}_{\alpha}(P)
                  \prod_v g_{D_v}(\alpha_v).}             \tag{2.7}
\]

A variable absent from `P` has `alpha_v=0` in the applications and is omitted.
There is no assertion that the conditioned marginals stay bounded. Requiring
such an assertion would lose the iteration; capacity is what is propagated.

---

## 3. Positive cores: a multiplicative, all-orders collision inequality

For each labelled source core `i`, let `Omega_i` be a finite set of **internally
injective** configurations. A configuration `omega` has nonnegative weight
`w_i(omega)` and a host image set `S_i(omega)`. All configurations of core `i`
use exactly `r_i` distinct host sites. Define

\[
 p_i(\mathbf x)=\sum_{\omega\in\Omega_i}
                      w_i(\omega)x_{S_i(\omega)},\qquad
 Z_i=p_i(\mathbf1)>0.                                    \tag{3.1}
\]

Multiple configurations with the same image contribute additively. Each `p_i`
is homogeneous and multiaffine. **Assume that each `p_i` is real stable.** Put

\[
 P=\prod_i p_i,\quad H=\sum_i r_i,\quad
 \ell_v=\sum_i\frac{\partial_vp_i(\mathbf1)}{p_i(\mathbf1)}.
                                                               \tag{3.2}
\]

Thus `ell_v` is the sum of the actual occupation probabilities of `v` in the
independent positive core laws, and `sum_v ell_v=H`. Let `D_v` be the number
of core polynomials in which `x_v` occurs; it bounds its degree in `P`.

### Theorem 3.1: disjoint positive cores

If `ell_v<=1` for every host vertex, then

\[
 \boxed{
 \begin{aligned}
 Z_{\rm disj}
 &:={\sum}_{\substack{(\omega_i)_i\\
                 S_i(\omega_i)\text{ pairwise disjoint}}}
                          \prod_iw_i(\omega_i)\\
 &=\operatorname{SF}P(\mathbf1)\\
 &\ge\Bigl(\prod_i Z_i\Bigr)\prod_{v:D_v>0}g_{D_v}(\ell_v)\\
 &\ge\Bigl(\prod_i Z_i\Bigr)
            \exp\!\left[-\sum_v I(\ell_v)\right]>0,
 \end{aligned}}                                           \tag{3.3}
\]

where

\[
 I(a)=a+(1-a)\log(1-a),\qquad I(0)=0,\quad I(1)=1.        \tag{3.4}
\]

**Proof.** In the expansion of `P`, the exponent of a host variable records
how many cores used that site. Since individual cores are already injective,
`SF` retains exactly and only pairwise disjoint core configurations. This
proves the equality, including all cross-core capacity constraints.

Normalize the coefficients of `P` by `P(1)`. For its random exponent vector
`K` one has `E K_v=ell_v`. Jensen's inequality yields

\[
 \frac{P(e^{\mathbf t})}{P(\mathbf1)}
       =\mathbb E e^{\langle K,\mathbf t\rangle}
       \ge e^{\langle\ell,\mathbf t\rangle}.
\]

Equality holds at `t=0`, so

\[
 \operatorname{Cap}_{\ell}(P)=P(\mathbf1)=\prod_i Z_i.
                                                               \tag{3.5}
\]

Products preserve real stability. Apply (2.7) with `alpha=ell`. Finally,
`(1-a/D)^{D-a}>=e^{-a}`, using
`log(1-u)>=-u/(1-u)` and the endpoint convention. Thus
`g_D(a)>=g_infinity(a)=exp(-I(a))`. Every factor is strictly positive,
even when `ell_v=1`. `□`

### Quantitative scale and why this is not just a local identity

For `ell_v<=lambda<1`, integration of
`I'(a)=-log(1-a)` gives

\[
 \sum_v I(\ell_v)
 \le\frac{\sum_v\ell_v^2}{2(1-\lambda)}
 \le\frac{\lambda H}{2(1-\lambda)}.                       \tag{3.6}
\]

In particular, if `ell_v<=kappa H/N<1`,

\[
 Z_{\rm disj}\ge
  \exp\!\left[-\frac{\kappa H^2}{2(N-\kappa H)}\right]
  \prod_iZ_i.                                            \tag{3.7}
\]

For perfectly flat occupation `ell_v=H/N`, the stronger entropy expression is

\[
 \boxed{Z_{\rm disj}\ge
        e^{-H}(1-H/N)^{-(N-H)}\prod_iZ_i,}                \tag{3.8}
\]

with value `e^{-H}` for the displayed factor at `N=H`. For `N=CH`, `C>1`
fixed, its logarithm is `-O(H/C)` for large `C`. In the elementary uniform
single-vertex case, this is exactly the integral lower bound

\[
 \log\frac{(N)_H}{N^H}
   =\sum_{j=0}^{H-1}\log(1-j/N)
   \ge\int_0^H\log(1-x/N)\,dx
   =-H-(N-H)\log(1-H/N).                                  \tag{3.9}
\]

Thus the collision scale is the random finite-population scale, rather than a
loss from charging each pair separately until a union bound becomes negative.
The degree-sensitive bound in (3.3) is stronger; if only one core can use a
site, its factor is `g_1=1`.

This theorem is genuinely iterable and has no cutoff on core size, source
degree, number of cores, or number of added isolates. Multiplying any core's
weights by an arbitrarily large positive constant changes both sides equally.
No absolute positive-activity load is charged.

Positive product tilts are also allowed: replace every `p_i(x)` by
`p_i(t_1x_1,...,t_Nx_N)` for `t_v>0`. Stability is preserved, and the same proof
uses the tilted occupations. If `t_v<=1`, the resulting weighted disjoint count
is itself a lower bound on the unweighted disjoint count. This does not assert
that a suitable tilt always exists with the desired quantitative normalization.

### Corollary 3.2: an entire positive source-polymer background

This makes the compatibility issue explicit. Let `V` be a source set of size
`h`, with a finite catalogue `C` of allowed source cores `U subset V`,
`|U|>=2`. For each `U`, let `p_U` be the image polynomial of a positive,
internally injective core law as in (3.1), of degree `|U|`, with `a_U=p_U(1)>0`.
Assume that `p_U` is real stable and that its normalized occupation satisfies

\[
 q_U(v)\le\kappa |U|/N\quad\text{for every }U,v,
 \qquad \kappa\ge1.                                     \tag{3.10}
\]

For a pairwise source-disjoint family `F subset C`, put
`r_F=h-sum_{U in F}|U|` and `p_0(x)=N^{-1}sum_v x_v`. Define a positive
source-only reference partition and its globally injective version

\[
 \begin{aligned}
 Z_{\rm cores}&=\sum_{F\text{ source-disjoint}}\prod_{U\in F}a_U,\\
 Z_{\rm global}&=\sum_{F\text{ source-disjoint}}
       \operatorname{SF}\!\left(p_0^{r_F}\prod_{U\in F}p_U\right)(\mathbf1).
 \end{aligned}                                           \tag{3.11}
\]

In the second sum, every uncovered labelled source vertex has its own uniform
singleton core. Therefore it counts precisely the selected core configurations
and all remaining source images with **global** injectivity, with uniform
singleton weights `1/N`. Host collisions between different selected cores and
all collisions involving uncovered vertices are excluded, not approximated.

If `N>kappa h`, then

\[
 \boxed{Z_{\rm global}\ge
   \exp\!\left[-\frac{\kappa h^2}{2(N-\kappa h)}\right]
       Z_{\rm cores}>0.}                                \tag{3.12}
\]

**Proof.** For every compatible `F`, the total occupation of a site in its
product is at most
`kappa(h-r_F)/N+r_F/N <= kappa h/N`, and the total degree is exactly `h`.
Apply (3.7) to that family and its `r_F` labelled singleton cores. Sum the
result over the same source-disjoint families. The empty family gives
`Z_cores>=1`. This proves the exact positive-background comparison. `□`

If every `q_U(v)=|U|/N`, the total occupation is exactly `h/N` for **every**
family. Then the factor in (3.12) improves to
`e^{-h}(1-h/N)^{-(N-h)}`, for `N>=h`, by (3.8).

Thus arbitrary positive core amplitudes, arbitrary compatible collections of
cores, and all their isolated-vertex dressings are handled together in this
class. This is an overlap-compatible positive baseline with two explicit
resources: disjoint source supports and disjoint host images. It is **not**
asserted to equal the cube partition merely by replacing old activities by
these positive cores. Such a replacement would still require an exact
regrouping. The exact link actually obtained for the cube is (5.3)--(5.7).

---

## 4. A literal finite-population sum-of-squares corollary

Let `V_i` be a real full-row-rank `r_i`-by-`N` matrix, with columns `v_{i,v}`.
Cauchy--Binet gives

\[
 p_i(\mathbf x)
 =\det\!\left(\sum_v x_vv_{i,v}v_{i,v}^{\mathsf T}\right)
 =\sum_{|S|=r_i}\det(V_i[:,S])^2x_S.                     \tag{4.1}
\]

This is real stable: if all `Im x_v>0`, the matrix in the determinant has
positive definite imaginary part. Indeed, for a nonzero complex vector `u`,
its imaginary quadratic form is
`sum_v (Im x_v)|v_{i,v}^T u|^2>0`, by full row rank. It is therefore nonsingular.
Its coefficients in (4.1) are nonnegative, and every column set is a **set**,
not a multiset.

The occupation of `v` in this core is its leverage score

\[
 q_i(v)=v_{i,v}^{\mathsf T}(V_iV_i^{\mathsf T})^{-1}v_{i,v},
 \qquad\sum_vq_i(v)=r_i.                                 \tag{4.2}
\]

If `ell_v=sum_i q_i(v)<=1`, Theorem 3.1 proves the explicit inequality

\[
 \boxed{
 \sum_{\substack{S_i\text{ pairwise disjoint}\\|S_i|=r_i}}
                    \prod_i\det(V_i[:,S_i])^2
 \ge\prod_i\det(V_iV_i^{\mathsf T})
                   \exp\!\left[-\sum_vI(\ell_v)\right]>0.
 }                                                        \tag{4.3}
\]

The finite-degree factors from (3.3) can replace the entropy factor. This is
an all-rank, all-number-of-cores sum-of-squares inequality with exact host
capacity. It does not say that a graph product of entries of a PSD kernel has
nonnegative connected cumulants.

An isolated labelled source vertex is represented by the rank-one factor
`N^{-1} sum_v x_v`. Adding `j` such vertices adds exactly `j/N` to each
`ell_v`, and (3.3) resums **all** their collisions with one another and with
every core. For this class of cores, no negative isolated-vertex dressing is
left to be charged as a raw connected activity. This is a relative replacement
for that dressing problem, not a proof that arbitrary cube activity cores have
the form (4.1).

---

## 5. Exact pinned-core expansion for the cube, and the remaining application

For `d>=1`, let `E,O` be the cube parity classes, each of size `m=h/2`,
and assume `N>=h`. (The case `d=0` is a single vertex.) Fix an injection
`f:E -> [N]`. Put `X_f=[N] \ f(E)`, so all later images automatically avoid
**every** centre image. Write `chi` for the host edge-colouring. For `c=R,B`
and `y in O`, define the actual list

\[
 L_{f,c}(y)=\{v\in X_f:\ \chi(f(x),v)=c
                       \ \text{for all }x\in N_H(y)\}.     \tag{5.1}
\]

Set

\[
 P_{f,c}(\mathbf x)=\prod_{y\in O}\left(\sum_{v\in L_{f,c}(y)}x_v\right),
 \qquad J_{f,c}=\operatorname{SF}P_{f,c}(\mathbf1).         \tag{5.2}
\]

`P_{f,c}(1)` allows repetitions among the odd images and is **not** an
injective count. In contrast, `J_{f,c}` counts exactly the injective extensions
of this fixed `f` in colour `c`. There are no edges inside either parity class,
every cube edge is in a list constraint, and square-free extraction makes all
odd images distinct. Therefore

\[
 \boxed{T_c=\sum_{f:E\hookrightarrow[N]}J_{f,c},\qquad
 \Xi(+1)+\Xi(-1)=\frac{2^e}{N^h}
          \sum_{f:E\hookrightarrow[N]}\sum_{c=R,B}J_{f,c}.}
                                                               \tag{5.3}
\]

This is the requested exact link to the original joint-colour partition.
It neither omits cross-collisions nor substitutes a count of only one half.

If all lists are nonempty, put

\[
 D_{f,c}(y)=|L_{f,c}(y)|,\qquad
 \ell_{f,c}(v)=\sum_{y:v\in L_{f,c}(y)}\frac1{D_{f,c}(y)},\qquad
 b_{f,c}(v)=|\{y:v\in L_{f,c}(y)\}|.                     \tag{5.4}
\]

Each factor of `P_{f,c}` is a nonnegative linear form and is real stable.
All overlap patterns of the neighbourhoods are permitted. Consequently,
whenever `ell_{f,c}(v)<=1` for every `v in X_f`,

\[
 \boxed{J_{f,c}\ge\prod_{y\in O}D_{f,c}(y)
              \prod_{v:b_{f,c}(v)>0}
                 g_{b_{f,c}(v)}(\ell_{f,c}(v))
       \ge\prod_yD_{f,c}(y)e^{-\sum_{v\in X_f}I(\ell_{f,c}(v))}>0.}
                                                               \tag{5.5}
\]

For example, if `ell_{f,c}(v)<=kappa m/(N-m)<1`, (5.5) gives

\[
 J_{f,c}\ge
 \exp\!\left[-\frac{\kappa m^2}{2(N-m-\kappa m)}\right]
                  \prod_yD_{f,c}(y).                    \tag{5.6}
\]

Let `G` denote the set of pinned pairs `(f,c)` for which the nonempty-list and
`ell<=1` hypotheses hold. Dropping only **nonnegative actual injective counts**
from (5.3) proves the unconditional lower bound

\[
 \boxed{\Xi(+1)+\Xi(-1)\ge\frac{2^e}{N^h}
    \sum_{(f,c)\in\mathcal G}
       \prod_yD_{f,c}(y)
       \prod_{v:b_{f,c}(v)>0}g_{b_{f,c}(v)}(\ell_{f,c}(v)).}
                                                               \tag{5.7}
\]

This is an actual proved bound, not an asserted bound for an unknown corrected
cumulant. It applies at every dimension, and handles all outside-vertex
collision blocks at once. If no such pair is known, its right-hand side is
zero, and it provides no strict positivity.

### What (5.5) does and does not add

* The bound uses the unconditioned occupations of a positive pinned core law.
  The proof does not repeatedly assume that these same occupations survive
  the exclusion of previously occupied host vertices.
* This is also valid for an arbitrary source vertex cover: its internal edge
  constraints must first be satisfied by the pinned injection, and the
  complement is independent. No bound on outside-neighbourhood arity is used.
* Positivity in the list special case also follows from fractional matching
  integrality. The useful extra estimate here is the quantitative relative
  collision bound and its arbitrary stable-core/SOS extension, not merely
  another assertion that a fractional matching can be rounded.
* The occupation condition is sufficient, **not necessary**, for an injection.
  For example, lists `{a}` and `{a,b}` have an injective transversal, although
  their uniform-choice occupation at `a` is `3/2`. Hence failure of this
  criterion is not a Ramsey obstruction.
* No lower bound here is proved for the mass of `G`, or even its nonemptiness,
  for every colouring with `N>=C h`. The mean occupation over the unused host
  sites is merely `m/(N-m)`; this does not bound its maximum.
* Keeping both colours in (5.7) is legitimate, but their complementary edge
  indicators do not by themselves control either list-load maximum. No
  all-dimensional joint-colour argument supplying that control was found.

Thus the new result is the iterable positive-core collision estimate, not a
renaming of the universal existence question as the assertion `G != empty`.
The latter assertion is explicitly **not proved**.

---

## 6. Why a scalar joint-colour cumulant gas cannot be used naively

This obstruction is separate from Theorem 3.1. It explains why the already
proved signed-polymer positivity lemma cannot simply be applied after averaging
the two colour moments.

For a source subset `U`, define

\[
 \bar Z(U)=\frac{\Xi_{H[U]}(+1)+\Xi_{H[U]}(-1)}2,
 \qquad
 \widetilde w(U)=\sum_{\pi\in\Pi(U)}
       (-1)^{|\pi|-1}(|\pi|-1)!\prod_{D\in\pi}\bar Z(D).
                                                               \tag{6.1}
\]

These are the exact scalar connected activities for the **averaged moments**.
They are not `(w_+(U)+w_-(U))/2`. The common colour sign couples otherwise
disjoint source components.

Take the all-red complete host with `N>=max(h,32)`, so that the full red cube
count is positive. On any subset of a source matching, with `k` vertices and
`r` complete source edges,

\[
 \bar Z(U)=\frac{(N)_k}{N^k}
 \begin{cases}1,&r=0,\\2^{r-1},&r>0.\end{cases}           \tag{6.2}
\]

This formula is a count of full injections, including all isolated vertices.
For the union of four induced matching edges, exact evaluation of (6.1) gives

\[
 \boxed{\widetilde w(4K_2)=
 -2+\frac8N+\frac{148}{N^2}-\frac{1528}{N^3}
 +\frac{11230}{N^4}-\frac{42976}{N^5}
 +\frac{68400}{N^6}-\frac{40320}{N^7}.}                  \tag{6.3}
\]

A reproducible symbolic derivation uses the connected-component recurrence

\[
 \widetilde w(U)=\bar Z(U)
       -\sum_{\substack{v\in S\subsetneq U}}
                      \widetilde w(S)\bar Z(U\setminus S)
                                                               \tag{6.4}
\]

for one fixed `v in U`, starting from (6.2). The audit also evaluates all
`Bell(8)=4140` partitions in (6.1) independently at three host sizes. For
`N>=32`, discarding just the negative lower-order terms gives

\[
 \widetilde w(4K_2)
 \le-2+\frac8{32}+\frac{148}{32^2}
         +\frac{11230}{32^4}+\frac{68400}{32^6}<-1.       \tag{6.5}
\]

There is an induced matching of size `h/4` in `Q_d`: take the edges in one
coordinate whose remaining `d-1` bits have even parity. Distinct such edges
have no source edges between them. Fix a vertex `v` on this matching. For
`d>=4`, the `binom(h/4-1,3)` unions of its matching edge with three others all
contribute activities bounded above by `-1`. Hence for every `0<tau<=1`,

\[
 \sum_{U\ni v}(-\widetilde w(U))_+\tau^{-(|U|-1)}
 \ge\binom{h/4-1}{3}\tau^{-7}\ge1>1-\tau.               \tag{6.6}
\]

This violates the hypothesis of `SignedPartitionPositivity.Z_pos` for **every**
`tau`, even though the red cube count is positive. In particular the problem
persists at arbitrarily large fixed `N/h`; it is not caused by insufficient
host capacity.

The effect occurs at all orders. In the collision-free `N -> infinity` limit,
write `t_i=x_{a_i}x_{b_i}` for the matching edges in the square-free source
algebra. Its averaged moment polynomial is

\[
 \exp\!\left(\sum_vx_v\right)\cosh\!\left(\sum_it_i\right),
\]

so its connected logarithm contains
`log cosh(sum_i t_i)`. The coefficient on `r` complete matching edges is the
`r`th derivative of `log cosh` at zero; for `r=2,4,6,8` these are
`1,-2,16,-272`. The even orders alternate in sign: formally
`log cosh(i t)=log cos t`, while the odd Taylor coefficients of `tan t` are
positive by the recurrence `y'=1+y^2`, `y(0)=0`; integrate
`(log cos t)'=-tan t`. This proves the stated sign pattern at every order.
It is why the global colour variable should be kept outside a scalar
source-cumulant expansion, not a failure of the proved finite signed-partition
lemma itself.

---

## 7. The stable-core assumption cannot be supplied by averaging colours

There is an all-dimensional counterexample to the convenient but false
assertion that a joint full-injection cube image polynomial is automatically
real stable.

Let `H` be a connected balanced bipartite graph on `h=2m` vertices, `m>=2`
(in particular any `Q_d`, `d>=2`). Partition the host into two sets `A,B`, each
of size `a>=h`, colour within parts red, and between parts blue. Let

\[
 \mathcal J_H(\mathbf x)=\sum_{c=R,B}
       \sum_{\phi:H\hookrightarrow[N]\text{ monochromatic in }c}
                      \prod_{u\in V(H)}x_{\phi(u)}.
\]

This is already a full-injection, nonnegative, multiaffine polynomial. A red
copy lies wholly in one part; a blue copy has exactly the two orientations of
the fixed source bipartition. Consequently, writing `e_k` for an elementary
symmetric polynomial,

\[
 \mathcal J_H(\mathbf x)
  =h!\bigl(e_h(\mathbf x_A)+e_h(\mathbf x_B)\bigr)
       +2(m!)^2 e_m(\mathbf x_A)e_m(\mathbf x_B).           \tag{7.1}
\]

Set every variable in `A` equal to `s`, and every variable in `B` equal to `t`.
The result is

\[
 R(s^{2m}+t^{2m})+2D s^mt^m,
 \qquad R=(a)_{2m}>0,\quad D=(a)_m^2>0.                  \tag{7.2}
\]

If `J_H` were real stable, diagonalization and specialization `t=1` would make

\[
 R s^{2m}+2D s^m+R                                      \tag{7.3}
\]

a real-rooted polynomial with nonpositive roots. But it has a positive constant
term, positive degree, and zero coefficient of `s`. Every real-rooted polynomial
with nonnegative coefficients, positive degree, and positive constant has
strictly negative roots and a strictly positive linear coefficient, as is seen
by factoring it as `a_0 prod_j(1+r_j s)` with `r_j>0`. This is a contradiction.
Thus (7.1) is **not** real stable.

The host's part permutations and interchange act transitively on its vertices.
Therefore the normalized occupation of every host site in this actual joint
image law is exactly

\[
 \Pr(v\text{ is used})=h/N.
\]

One may take `N=C h` for any integer `C>=2`, and the marginals
are perfectly flat. Hence marginal flatness does not repair the missing
stability of the mixture. Both monochromatic cube counts in this example are
positive; no zero-monochromatic-qualified inequality is contradicted.

In the pinned formula (5.3), every list polynomial is stable. The obstruction is
that summing over pinned centres and colours, including their image monomials,
need not preserve stability. Likewise, being a positive sum of determinant
squares does not, without an appropriate common stable representation, preserve
this property. No application of Theorem 3.1 to that sum is justified.

---

## 8. Independent audit and final stopping point

The audit is reproducible with

```text
python3 Submission/check_cube_joint_signed_completion.py
lake env lean Submission/SignedPartitionPositivity.lean
```

The first output is saved in `CubeJointSignedCompletionVerification.txt`.
The script does not import an earlier checker or any conjecture. Its independent
checks include:

* **648 univariate capacity calculations**, using numerical minimization of
  the original polynomial, including both endpoints and the sharp equal-root
  cases, rather than evaluating only the AM--GM majorant;
* **3,795 positive-core products**, with square-free polynomial multiplication
  compared against independent enumeration of disjoint image sets; **1,062**
  final collision bounds are checked when their occupation hypotheses hold;
* **145 Gram/minor laws**, checking Cauchy--Binet totals and leverage marginals
  against separate exact rational matrix calculations;
* a complete source-polymer gas with **10 compatible families**, free isolates,
  and a core amplitude `10^12`, checked both by image polynomials and by a
  separate enumeration of weighted **full source injections**;
* **43 direct full cube counts**, compared with the pinned list formula,
  including `Q_3`; **2,483** eligible pinned colour sectors satisfy (5.5);
* direct independent-label pair products and the global even-edge expansion
  compared against full injections, including every non-edge collision factor;
* the polynomial (6.3), independently checked by all 4,140 set partitions,
  and the induced-matching construction through dimension eight;
* the actual full-injection image coefficients in (7.1)--(7.3), and their
  uniform one-point marginals, in three finite two-part hosts.

Exact integers and rationals are used for counting. Transcendental lower-bound
comparisons use 70-digit arithmetic. These finite checks support the written
proofs; they are not tests or certificates of the missing universal cube
statement. In particular, overloaded examples are explicitly excluded from the
bound tests, rather than treated as if the hypotheses held.

The separate Lean run succeeds. The existing partition identities, negative
ratio bounds, signed lower bound, and `Z_pos` report only
`[propext, Classical.choice, Quot.sound]`. This verifies the interface read in
this attempt, but the new real-stable polynomial arguments above are not
claimed to be kernel-checked by that run.

### Mathematical audit points

1. The new iteration uses capacity with a **fixed** exponent vector, not a
   repeated assertion about conditional marginals.
2. The square-free operation discards all repeated host labels and exactly
   equals a sum over disjoint, internally injective positive core configurations.
3. Products and single-site truncations preserve stability; arbitrary positive
   sums do not. The latter obstruction is exhibited by actual joint cube counts.
4. Equation (5.3) contains every cube edge and every injectivity constraint;
   equation (5.7) is a lower bound because only nonnegative full extension counts
   are discarded.
5. The negative cumulant in (6.3) is for the scalar cumulant of the **averaged
   moments**, not for the average of the one-colour activities.
6. No max-full-pattern to reduced-pattern transfer is assumed. No PSD-to-cumulant
   inference, source-size rank bound, or uncontrolled positive-core dressing is
   used.

**Final gap, concisely:** the stable positive-core collision inequality is
proved and iterable, but the existence of a suitable globally consistent
red/blue pinned core law at `N=C2^d` is not. Averaging the available laws cannot
be justified by stability, and raw joint cumulants cannot meet the stated
negative-load criterion even in the all-red example. Therefore this attempt
does not complete the Ramsey proof.

No Lean source was edited. The verified before/after SHA-256 of
`Submission/Spec.lean` is

```text
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```
