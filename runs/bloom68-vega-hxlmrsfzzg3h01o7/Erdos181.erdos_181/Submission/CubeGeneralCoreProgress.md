# General-core progress for the cube signed-activity programme

## Status and main results

This continues `CubeSignedActivityLemmas.md` and `CubeSpectralStarControl.md`.
It does **not** prove the full all-support negative-activity bound or the full
constant-multiplier cube embedding theorem. It does give the following positive
results, none of which truncates the number of leaves or isolated vertices.

1. **The proposed isolated-vertex identity is correct**, with a rising, not
   falling, factorial. A general load-transfer lemma accounts for every possible
   placement of the isolated vertices, including when the distinguished source
   vertex is one of them.
2. There is an **exact all-support vertex-cover resummation**, using a host
   occupation product followed by a cumulant over the retained centres. It
   handles arbitrary, intersecting neighbourhoods and disconnected induced
   supports. Taking a cube parity class as the retained set covers every support.
3. An **exact arbitrary-degree vertex-deletion identity** identifies the
   corrections to leaf stripping and to degree-two Gram reduction. Degree two
   produces a PSD Gram kernel, but also pair and three-vertex collision
   responses. The responses cannot be discarded or declared positive.
4. For the actual, fully resummed activities, **all stars and edge-centred
   double-stars, with arbitrary isolated-vertex dressing**, have load
   
   \[
   3\cdot10^6(L^2+1)d^3/n.
   \]
   After the existing pruning, this family together with all edgeless supports
   uses **less than `0.055`** of the negative-load budget when
   `N >= 4*10^9(K^2+1)2^d`. The sharper star-with-isolates bound is
   `34000(L^2+1)d^2/n`.
5. There is a **dimension-uniform cube skeleton summation lemma** for arbitrary
   connected once-subdivision cores. It uses both pair codegree two and the
   degree bound, not a rank bound in terms of total support size. The needed
   per-retained-centre estimate is proved for the nontrivial class of projection
   Gram kernels, by a nowhere-zero-flow interpretation. This last estimate is
   for bare spectral core products, **not** for all their activity corrections.
6. A complementary full-partition result handles **every 2-degenerate source**
   of maximum degree `d` on `h_0` vertices if
   `n >= 36(h_0 + ceil(576L^2)d^2 + 1)`, subject to the mild flatness conditions
   below. This includes the unbalanced cube levels-1-and-2 example. It proves
   positivity of those complete injective partitions, not a load bound for
   inserting their activities into a larger cube gas.

The identities below always refer back to the original partition function.
No positive core is silently deleted from `Xi`, and no replacement gas is
asserted to lower-bound it.

Verification is in `check_cube_general_core.py`, with saved output in
`CubeGeneralCoreVerification.txt`. `Spec.lean` is not edited. The new proofs in
this file are mathematical arguments, not new Lean formalizations.

---

## 1. Normalization and the useful logarithm

Use `n` for the host currently being used, possibly after pruning. Its actual
edge density is `p>0`, and

\[
 B=A-p(J-I),\qquad M=B/p,\qquad a=A/p.
\]

Thus `M` has zero diagonal, `a` has zero diagonal, and `a=1+M` **off the
diagonal**. For a simple source graph `H`,

\[
 f_{uv}=-\mathbf1[X_u=X_v]+\mathbf1[uv\in E(H)]M(X_u,X_v).
\]

Write `Z_H(S)=Xi(H[S])`, so

\[
 Z_H(S)=n^{-|S|}\sum_{\phi:S\hookrightarrow[n]}
                    \prod_{uv\in E(H[S])}a_{\phi(u)\phi(v)}.
\]

In particular `Z_H(empty)=1` and `Z_H({v})=1`. The original identity is

\[
 \Xi(H)=\frac{\operatorname{inj}(H,G)}{n^{|H|}p^{e(H)}}.
\]

Work in the commutative square-free algebra with `x_v^2=0`, and put

\[
 \mathcal Z_H(\mathbf x)=\sum_{S\subseteq V(H)}Z_H(S)x_S.
\]

The exponential formula for the original connected signed sums is exactly

\[
 \boxed{\log\mathcal Z_H(\mathbf x)
       =\sum_{\varnothing\ne S\subseteq V(H)}w_H(S)x_S.}       \tag{1.1}
\]

Here the singleton convention is `w({v})=1`. Singletons are still uncovered
vertices in the usual polymer formulation; this convention merely makes (1.1)
uniform. All logarithms in square-free variables are finite algebraic
identities. In particular, they do not presuppose positivity of `Xi`.

Equivalently,

\[
 w_H(U)=\sum_{\pi\in\Pi(U)}(-1)^{|\pi|-1}(|\pi|-1)!
                         \prod_{D\in\pi}Z_H(D).             \tag{1.2}
\]

These formulas also apply when one extra interaction on a specified nonempty
set of vertices is inserted. That observation will make the vertex-deletion
formula particularly clean.

---

## 2. Isolated vertices: exact identity and all-support load transfer

### 2.1 Verification of the proposed identity

Let `F` be any fixed source on `k>=1` labelled vertices. It need not be
connected, and it may itself have isolated vertices. Add `j` new isolated source
vertices, denoted `I_j`. On an injective assignment of a subset `S` of the old
vertices, the additional isolated labels have exactly `(n-|S|)_j` choices.
Consequently

\[
 \sum_{j\ge0}Z_{H[S]\sqcup I_j}\frac{t^j}{j!}
       =Z_H(S)(1+t/n)^{n-|S|}.
\]

Summing over `S` gives the stronger multivariate identity

\[
 \mathcal Z(\mathbf x,t)
   =(1+t/n)^n\mathcal Z_F\left(\frac{\mathbf x}{1+t/n}\right).
\]

Take the logarithm and extract the coefficient of `x_{V(F)}`. Since `k>0`,
`n log(1+t/n)` contributes nothing to this coefficient. Therefore

\[
 \boxed{C_F(t):=\sum_{j\ge0}w(F\sqcup I_j)\frac{t^j}{j!}
             =w(F)(1+t/n)^{-k},}                            \tag{2.1}
\]

and hence

\[
 \boxed{w(F\sqcup I_j)=(-1)^j\frac{k^{\overline j}}{n^j}w(F),
       \qquad k^{\overline j}=k(k+1)\cdots(k+j-1).}           \tag{2.2}
\]

This proves the fresh derivation in the question. The same argument works
coefficientwise for `w_z`, at every spectral parameter `z`, with the original
zero-diagonal convention. The case `k=0` is separate: the connected isolated-only
EGF is `n log(1+t/n)`. Taking `k=1` in (2.2) recovers the pure-collision formula.

A sign consequence that matters later is

\[
 (-w(F\sqcup I_j))_+=\frac{k^{\overline j}}{n^j}
 \begin{cases}(-w(F))_+,&j\text{ even},\\(w(F))_+,&j\text{ odd}.
 \end{cases}                                               \tag{2.3}
\]

Thus an uncontrolled positive core cannot simply be ignored: one isolated
source vertex changes its sign in the raw activity.

### 2.2 A general dressing-load lemma

Let the ambient source have `h` vertices, and let `C` be any family of supports
`F` whose induced source graphs have no isolated vertices. In particular
`k=|F|>=2`. Let `Dress(C)` consist of the supports whose **unique nonisolated
part** belongs to `C`. Define

\[
 x=eh/n<1,\qquad \beta=\frac e{1-x},\qquad
 A_\beta=\sup_v\sum_{\substack{F\in C\\v\in F}}
                            |w(F)|\beta^{|F|-1}.
\]

Then

\[
 \boxed{\sup_v\sum_{\substack{U\in\operatorname{Dress}(C)\\v\in U}}
                |w(U)|e^{|U|-1}\le\frac{A_\beta}{(1-x)^2}.} \tag{2.4}
\]

**Proof.** If `v in F`, use (2.2) and forget all restrictions on the placement
of the `j` extra isolated vertices. Their contribution is at most

\[
 \sum_{j\ge0}\frac{h^j}{j!}\frac{k^{\overline j}}{n^j}e^j
                    =(1-x)^{-k}.
\]

This gives at most `A_beta/(1-x)` for cores containing `v`.

If `v` is one of the isolated vertices, there are at most
`h^(j-1)/(j-1)!` choices of the others. The corresponding factor is at most

\[
 \frac{ek}{n}(1-x)^{-k-1}.
\]

Moreover

\[
 \sum_F k|w(F)|\beta^{k-1}
       =\sum_u\sum_{F\ni u}|w(F)|\beta^{k-1}\le hA_\beta.
\]

The second contribution is therefore at most
`x A_beta/(1-x)^2`. Adding the two bounds proves (2.4). Forgetting the
independence and nonadjacency requirements on the extra vertices only
increased the count. There is no assumption that an isolate cannot contain the
distinguished vertex. □

This is a general all-core transfer theorem, not a star-specific calculation.
It explains precisely which strengthened norm of the undressed cores suffices.
A bound on **negative** undressed activities alone does not suffice, because of
(2.3).

---

## 3. Exact vertex-cover resummation: every support is covered

Choose any vertex cover `C` of a source graph. Write `L=V(H)\C`, so that `L`
is independent. The graph on `C` is arbitrary. Group the vertices of `L` by
their exact neighbourhood `S subset C`; write `r_S` for the multiplicities and
introduce one EGF variable `t_S` for each type. Empty neighbourhoods are allowed.
Set `T=sum_S t_S`.

For `A subset C` and an injective map `phi:A -> [n]`, define

\[
 Q_{S\cap A}(\phi,y)=\prod_{i\in S\cap A}a_{\phi(i),y},
 \qquad Q_\varnothing=1,
\]

and the host-occupation polynomial

\[
 \boxed{
 \Phi_A(\mathbf t)=\frac1{n^{|A|}}
  \sum_{\phi:A\hookrightarrow[n]}
    \prod_{ij\in E(H[A])}a_{\phi(i),\phi(j)}
    \prod_{y\notin\phi(A)}
       \left(1+\frac1n\sum_{S\subseteq C}t_S
                                      Q_{S\cap A}(\phi,y)\right).
 }                                                         \tag{3.1}
\]

The intersection `S cap A` is essential. If some centres are absent, their
outside vertices remain present in the EGF, with the interactions to those
centres removed. They are not deleted along with the centres.

Each host site in the last product is either unused or occupied by exactly
one outside vertex. Thus (3.1) sums the full injective partition function on
`A` and any numbers of outside vertices. In particular

\[
 D(\mathbf t):=\Phi_\varnothing(\mathbf t)=(1+T/n)^n,
 \qquad \Psi_A=\Phi_A/D.
\]

The connected EGF on **all** the prescribed centres is

\[
 \boxed{
 W_C(\mathbf t)=
 \sum_{\pi\in\Pi(C)}(-1)^{|\pi|-1}(|\pi|-1)!
                           \prod_{A\in\pi}\Psi_A(\mathbf t).
 }                                                         \tag{3.2}
\]

Its coefficient is exactly

\[
 \left[\prod_S t_S^{r_S}\right]W_C
       =\frac{w(H)}{\prod_S r_S!}.                          \tag{3.3}
\]

**Proof.** Form `sum_{A subset C} x_A Phi_A(t)`, in square-free centre
variables. It is the full moment polynomial with the outside vertices treated
by EGF. Divide out its constant term `D`, and extract `x_C` from its logarithm.
The square-free logarithm gives the centre-partition cumulant in (3.2), with
exactly the factorial in (3.3). Division by `D` removes outside-only collision
components. The centre cumulant removes configurations in which the centres
belong to separate connected components. Both operations are identities for
the original connected activity. □

For a cube support, take either parity class of that support as `C`. Formula
(3.2) then covers **all supports, of all sizes**, including intersecting
neighbourhoods, disconnected nonisolated source components, and high-degree
outside vertices. It is not restricted to a core of bounded size. Cube pair
codegree two also implies `r_S<=2` for every type with `|S|>=2`, whereas a
singleton type has at most `d` vertices. Different higher-arity types can still
overlap extensively. More generally, one can retain non-pendant vertices and
treat pendant vertices by (3.1).

This supplies an algebraically compatible elimination procedure, **not a new
positive-core gas**: the output is exactly the original `w(U)`, so inserting all
the outputs back into the original polymer partition recovers `Xi`. It does
**not** by itself solve the load estimate or the compatibility of a further
positive-baseline regrouping.

### 3.1 The collision blocks left after outside-vertex elimination

For clarity give each individual outside vertex its own square-free variable
`t_l`. For fixed `phi`, the logarithm of the occupation product has coefficient
on a nonempty set `J` of outside vertices

\[
 \boxed{
 (-1)^{|J|-1}(|J|-1)!\,n^{-|J|}
 \sum_{y\notin\phi(A)}\prod_{l\in J}
                  Q_{N_H(l)\cap A}(\phi,y).
 }                                                         \tag{3.4}
\]

This is an exact resummation of all collisions within that outside block. At
`z=1` the summand is nonnegative, but the block sign alternates. A block can
join many different centres. The cube's pair-codegree bound constrains the
original neighbourhood types, not the arity of these merged interactions.
Replacing the occupation product by its singleton terms omits (3.4) for
`|J|>=2` and changes `Xi`.

The entire section remains valid for `z` if `a_xy` is replaced off the diagonal
by `1+zM_xy`, and is kept zero on the diagonal.

---

## 4. A local all-orders core identity: remove a vertex exactly

The vertex-cover formula has a useful local counterpart. It makes the proposed
leaf/degree-two strategy precise without pretending that only pair interactions
survive.

### 4.1 Connected responses to one marked interaction

Fix a source `F` and a nonempty subset `S` of its vertices. For a function
`g(X_S)`, multiply the full pair-factor product by the additional factor
`1+g(X_S)` whenever all vertices in `S` are present. Define

\[
 \Delta_S w_F[g]=w(F;\text{one extra interaction }1+g\text{ on }S)-w(F).
\]

This operation is **linear in `g`**, despite the nonlinear definition of
cumulants. Indeed, if `Z_g-Z` is the change in the moment polynomial, every
monomial of that change contains `x_S`. Consequently
`((Z_g-Z)/Z)^2=0` in the square-free algebra, and

\[
 \Delta_S w_F[g]
       =[x_{V(F)}]\frac{\mathcal Z_g-\mathcal Z_F}{\mathcal Z_F}.
                                                               \tag{4.1}
\]

For a singleton `S={u}`, this is the original connected signed sum weighted by
`g(X_u)`. For a pair or larger set it is **not** just the old connected sum
weighted by `g`.

More explicitly, write `C_F(D;X_D)` for the connected Mayer polynomial before
averaging, with value one on singletons. Then

\[
 \Delta_S w_F[g]
 =\sum_{\substack{\pi\in\Pi(V(F))\\D\cap S\ne\varnothing\ \forall D\in\pi}}
   E\left[g(X_S)\prod_{D\in\pi}C_F(D;X_D)\right].            \tag{4.2}
\]

All components must meet the one new interaction. In particular a pair
response includes both a single connected old component and two old components
joined by the inserted pair. This is one reason a PSD kernel is not a positive
activity by itself.

### 4.2 Arbitrary-degree vertex-deletion theorem

Let `H` be obtained from `F`, `|F|=k>=1`, by adding one vertex `l` with source
neighbourhood `R subset V(F)`. For nonempty `S subset R`, put

\[
 \Gamma_S(x_S)=\frac1n\sum_y\prod_{u\in S}M_{x_u y}.
\]

Then the following identity is exact:

\[
 \boxed{
 w(H)=-\frac{k}{n}w(F)
 +\sum_{\varnothing\ne S\subseteq R}
 \left\{\Delta_S w_F[\Gamma_S]
   -\frac1n\sum_{v\in V(F)\setminus S}
        \Delta_{S\cup\{v\}}w_F
                   \left[\prod_{u\in S}M_{X_u X_v}\right]\right\}.
 }                                                         \tag{4.3}
\]

**Proof.** Condition on an injective assignment of a subset `A` of the old
vertices. The factor for the new vertex, already summed over its unused host
label, is

\[
 \frac1n\sum_{y\notin\phi(A)}
                 \prod_{u\in R\cap A}(1+M_{\phi(u),y}).
\]

Expand over subsets `S subset R cap A`. The empty subset gives `1-|A|/n`.
For a nonempty subset the unrestricted sum is `Gamma_S`; subtract the occupied
labels `y=phi(v)`. Terms with `v in S` are zero because `M` has zero diagonal.
This gives all terms displayed in (4.3) at the moment level.

Divide the generating polynomial for moments containing `l` by `Z_F`, and
extract `x_{V(F)}`. The base term gives `-k w(F)/n`, since the Euler operator
on `log Z_F` multiplies this coefficient by `k`. Every other term is the marked
response (4.1). □

This is an arbitrary-degree identity, not a finite-order diagram expansion.
Together with (3.1)--(3.2) it gives an exact route for eliminating any independent
collection of vertices and a way to audit every correction in a leaf/core
recursion. Its natural outputs include marked and higher-arity interactions.

### 4.3 Leaves: a particularly short recurrence

Write

\[
 \rho_x=\frac1n\sum_yM_{xy}
       =\frac{\deg(x)-p(n-1)}{pn}.
\]

If `R={u}`, let `F oplus uv` mean that the Boltzmann factor on `uv` is multiplied
by one extra copy of `a=A/p`. If `uv` was already a source edge, this means
`a_xy^2`, not a single copy of `a_xy`. Formula (4.3) simplifies to

\[
 \boxed{w(F+\text{leaf at }u)
 =\Delta_{\{u\}}w_F[\rho]
  -\frac1n\left(w(F)+\sum_{v\ne u}w(F\mathbin\oplus uv)\right).} \tag{4.4}
\]

The simplification uses
`Delta_{uv} w_F[M] = w(F oplus uv)-w(F)` on injective old labels.
For a regular host the marked term vanishes. Thus regular-host leaf stripping
really is an exact sum of smaller, edge-filled cores, with a factor `-1/n` at
each simple pendant-edge removal. Parallel edges must remain: their multiplicity
can turn a two-vertex support into a degree-two multigraph core. In an irregular
host the marked degree-error terms must also remain; taking their absolute first
moments immediately would lose the variance cancellation used for stars.

For `R=empty`, (4.3) gives `w(F+I_1)=-k w(F)/n`, and iteration gives (2.2).

### 4.4 Degree two: the Gram kernel and the exact missing terms

For `R={a,b}`, put

\[
 \Gamma(x,y)=\frac1n\sum_zM_{xz}M_{yz}=\frac{(M^2)_{xy}}n.
\]

It is PSD. But (4.3) is

\[
\begin{aligned}
 w(H)={}&-\frac{k}{n}w(F)
       +\Delta_a w_F[\rho]+\Delta_b w_F[\rho]
       +\Delta_{ab}w_F[\Gamma]\\
 &-\frac1n\sum_{v\ne a}\Delta_{av}w_F[M_{av}]
  -\frac1n\sum_{v\ne b}\Delta_{bv}w_F[M_{bv}]\\
 &-\frac1n\sum_{v\notin\{a,b\}}
                \Delta_{abv}w_F[M_{av}M_{bv}].             \tag{4.5}
\end{aligned}
\]

So the finite-population correction includes **three-vertex interactions**.
Closing (4.5) within a class of PSD pair kernels is not valid.

Even the Gram response itself need not be positive. Let `F` consist of two
isolated old vertices, and let the host be regular and noncomplete. Then
`Gamma 1=0`, and

\[
 \Delta_{ab}w_F[\Gamma]
       =E_{x\ne y}\Gamma_{xy}
       =-\frac{\operatorname{tr}\Gamma}{n^2}<0.             \tag{4.6}
\]

Here `E_{x ne y}` means `n^{-2} sum_{x ne y}`, not conditioning and
renormalizing. In the `C_5` host, `p=1/2`, (4.6) is `-4/25`, and the full
three-vertex-star activity is `-2/25`. This is compatible with the existence of
many injective stars. It is also a small exact check that the correction and
cumulant conventions in (4.5) are essential.

### 4.5 What can safely be retained as a positive even cycle

For a bare spectral path with `q` edges, eliminating its `q-1` internal vertices
gives the kernel `M^q/n^(q-1)`. In particular an unweighted even cycle has

\[
 t_{C_{2r}}(M)=\frac{\operatorname{tr}M^{2r}}{n^{2r}}
             =\frac{\operatorname{tr}\Gamma^r}{n^r}\ge0.
\]

If `||B|| <= L sqrt(n)` and `kappa=L/p`, then

\[
 \|\Gamma\|_{op}\le\kappa^2,\qquad
 0\le t_{C_{2r}}(M)
       \le\kappa^{2r-2}\frac{1-p}{p}\,n^{1-r}.             \tag{4.7}
\]

This is the correct trace scale. Positive bare cycles are retained in the
exact formulas. Neither arbitrary vertex fields on those cycles nor the
connected responses in (4.5) inherit this trace-positivity statement.

---

## 5. A quantitative all-orders theorem: double-stars and all their isolates

The next estimate is for the **complete activities**, after all their signed
pieces have been summed, rather than for selected diagrams.

Assume

\[
 p\ge1/3,\quad \|B\|_{op}\le L\sqrt n,\quad n\ge4000d^2,
 \quad \max_x|r_x|\le\frac{pn}{8ed},
 \qquad r_x=\deg(x)-p(n-1).                                \tag{5.1}
\]

As before

\[
 E r_x=0,\qquad \sigma^2:=E r_x^2\le L^2n.                \tag{5.2}
\]

Let `D_{r,s}` be the source tree with adjacent centres, `r` private leaves at
the first, and `s` private leaves at the second, allowing either count to be
zero. Set

\[
 W_2(s,t)=\sum_{r,q\ge0}w(D_{r,q})\frac{s^r t^q}{r!q!}.
\]

### 5.1 The exact two-centre EGF

Specializing (3.1), define

\[
\begin{aligned}
 Z_{12}(s,t)&=\frac1{n^2}\sum_{x\ne y}a_{xy}
       \prod_{z\ne x,y}\left(1+\frac{s a_{xz}+t a_{yz}}n\right),\\
 Z_1(s,t)&=\frac1n\sum_x\prod_{z\ne x}
                         \left(1+\frac{s a_{xz}+t}n\right),\\
 Z_2(s,t)&=\frac1n\sum_y\prod_{z\ne y}
                         \left(1+\frac{s+t a_{yz}}n\right),\\
 D(s,t)&=(1+(s+t)/n)^n.
\end{aligned}
\]

Then

\[
 \boxed{W_2(s,t)=\frac{Z_{12}(s,t)}{D(s,t)}
                        -\frac{Z_1(s,t)Z_2(s,t)}{D(s,t)^2}.} \tag{5.3}
\]

The absent-centre leaf pools in `Z_1,Z_2` are isolated pools; omitting the
terms `t` or `s` in those formulas would give the wrong activity. At the origin
`W_2(0,0)=-1/n`, as required for a source edge.

The joint numerator can alternatively be written using degrees and codegrees:
for `x ne y`, let `c_xy=|N(x) cap N(y)|`. Its product is

\[
 (1+(s+t)/(pn))^{c_{xy}}
 (1+s/(pn))^{D_x-A_{xy}-c_{xy}}
 (1+t/(pn))^{D_y-A_{xy}-c_{xy}}.                            \tag{5.4}
\]

No independence assumption on the two leaf pools or their host neighbourhoods
has been made.

### 5.2 Uniform bidisc estimate

Put `R=2ed`. Then

\[
 \boxed{\sup_{|s|,|t|\le R}|W_2(s,t)|
              \le250(L^2+1)R^2/n=:M_2.}                  \tag{5.5}
\]

Here is a detailed estimate, retaining the degree means until they cancel.
Every logarithm below is the analytic logarithm near one; all its arguments
are within `1/4` of one by (5.1).

For the joint product divided by `D`, write

\[
 \log(P_{xy}/D)=u_{xy}+E_{xy},\qquad
 u_{xy}=\frac{s r_x+t r_y}{pn}.
\]

The linear remainder is
`-(s+t)/n-(s+t)A_xy/(pn)`. Using
`|log(1+z)-z| <= (2/3)|z|^2` for `|z|<=1/4`, `p>=1/3`, and `R>=1`, gives

\[
 |u_{xy}|\le1/2,\qquad |E_{xy}|\le35R^2/n.                \tag{5.6}
\]

Indeed the numerator logarithm remainder is at most `24R^2/n`, the denominator
remainder is at most `(8/3)R^2/n`, and the linear remainder is at most `8R^2/n`.
The analogous single-centre factors `Phi_i=Z_i/D` have pointwise logarithms

\[
 u_1=s r_x/(pn),\quad u_2=t r_y/(pn),\qquad
 |u_i|\le1/4,\quad |E_i|\le16R^2/n.                       \tag{5.7}
\]

For (5.7), the three bounds are `(32/3)R^2/n`, `(8/3)R^2/n`, and `2R^2/n`.
Since `R^2/n < 32/4000`, the pointwise joint exponential is bounded by `3`,
and the single-centre exponentials by `2`.

Use `|exp(u)-1-u|<=|u|^2` for `|u|<=1/2`. With uniform independent `x,y`,

\[
 E a_{xy}=1-1/n,\qquad
 E(a_{xy}r_x)=\frac{\sigma^2}{pn}.
\]

The second identity follows by summing the row `a_xy`, and using `E r_x=0`.
It is the weighted degree-mean cancellation in the two-centre problem. Thus

\[
 |E(a_{xy}u_{xy})|\le18L^2R/n,\qquad
 E(a_{xy}|u_{xy}|^2)\le108L^2R^2/n.
\]

The `E_xy` error costs at most `105R^2/n`. Including the mass defect `1/n`,

\[
 |Z_{12}/D-1|\le126(L^2+1)R^2/n.
\]

For a single centre, `E u_i=0`; the same argument gives

\[
 |\Phi_i-1|\le32(L^2+1)R^2/n,\qquad |\Phi_i|\le2.
\]

Finally

\[
 |W_2|\le|Z_{12}/D-1|+|\Phi_1\Phi_2-1|
       \le(126+3\cdot32)(L^2+1)R^2/n<M_2.
\]

This proves (5.5). The argument uses all leaf counts simultaneously. In
particular it does not replace degree fluctuations by their absolute first
moments, and it does not require a pointwise spectral codegree estimate.

Cauchy's estimate now gives, for every `r,s>=0`,

\[
 \boxed{|w(D_{r,s})|\le r!s!\,M_2R^{-r-s}.}                \tag{5.8}
\]

### 5.3 Counting cube supports and dressing them

An oriented central cube edge has at most
`binom(d-1,r)binom(d-1,s)` choices of the two leaf pools. Choices creating
extra source edges are discarded; counting them anyway is an upper bound.
By cube vertex transitivity, the number of such representations containing a
fixed vertex is at most

\[
 (r+s+2)d\binom{d-1}r\binom{d-1}s.
\]

This harmlessly overcounts symmetric representations and star representations.
For any `beta` with `q=beta d/R<1`, (5.8) gives

\[
 A_\beta\le\beta d M_2
          \sum_{r,s\ge0}(r+s+2)q^{r+s}
       =\frac{2\beta d M_2}{(1-q)^3}.                     \tag{5.9}
\]

Let `T_2` be the family of cube supports whose nonisolated part is a star or
an edge-centred double-star. This includes all sizes of independent isolated
attachments, and all stars are represented by allowing one leaf count in
`D_{r,s}` to be zero. If additionally `x=eh/n<=1/4`, take
`beta=e/(1-x)<=4e/3`. Then `q<=2/3`. Apply (2.4) to (5.9):

\[
\begin{aligned}
 \sup_v\sum_{\substack{U\in T_2\\v\in U}}|w(U)|e^{|U|-1}
 &\le\frac1{(1-x)^2}\,54\beta dM_2\\
 &\le128e dM_2
   =128000e^3(L^2+1)d^3/n\\
 &<\boxed{3\cdot10^6(L^2+1)d^3/n}.                       \tag{5.10}
\end{aligned}
\]

For stars alone, the previous star estimate has
`M_star=80(L^2+1)R^2/n`. Repeating the same argument with
`sum_{r>=1}(r+1)(2/3)^r=8` gives the sharper bound

\[
 \boxed{\sup_v\sum_{\substack{U:\ \text{nonisolated part a star}\\v\in U}}
        |w(U)|e^{|U|-1}\le34000(L^2+1)d^2/n.}              \tag{5.11}
\]

Both (5.10) and (5.11) bound complete activities, including every collision
contraction, before taking absolute values.

### 5.4 Explicit constant-linear consequence under the original hypothesis

Suppose the original host has `N` vertices,

\[
 p\ge1/2,\quad\|A-p(J-I)\|\le K\sqrt N,\quad
 N\ge4\cdot10^9(K^2+1)h,\qquad h=2^d.
\]

Use exactly the pruning proved in `CubeSpectralStarControl.md`. The induced
host has `n>=N/2`, actual density at least `1/3`, spectral constant `L=3K`,
and the flatness in (5.1). Its size also satisfies `n>=4000d^2`.
Using `d^3<=4h` in (5.10),

\[
 \sup_v\sum_{U\in T_2,\,v\in U}|w_{G'}(U)|e^{|U|-1}
 \le216\cdot10^6(K^2+1)h/N\le0.054.                       \tag{5.12}
\]

The disjoint family of edgeless supports has pure-collision load at most
`x/(1-x)<10^-6`. Thus these **complete support families** use less than
`0.055` of the negative load. A sufficient remaining statement is

\[
 \boxed{\sup_v\sum_{\substack{U\ni v:\ Q_d[U]\ \text{not edgeless},\\
                         U\notin T_2}}
       (-w_{G'}(U))_+e^{|U|-1}\le1-e^{-1}-0.055.}          \tag{5.13}
\]

Equation (5.13) is **not proved**. Unlike the previous star-only budget, its
excluded families already include arbitrary isolated dressing and all
edge-centred double-stars. It still includes supports with multiple nontrivial
source components, longer tree skeletons, and higher cores.

---

## 6. A cube-specific general skeleton summation lemma

The unbalanced example should guide the enumeration, not be excluded from it.
Let `C` lie in one parity class, `|C|=k>=2`. Let `D_2(C)` be the other-parity
vertices having exactly two neighbours in `C`, and let `m=|D_2(C)|`.

The cube gives **two simultaneous bounds**:

\[
 m\le dk/2,\qquad m\le2\binom k2=k(k-1).
\]

The first counts incident edges; the second uses pair codegree at most two.
Combining them, rather than choosing one uniformly, gives

\[
 \boxed{m\le\min\{dk/2,k(k-1)\}
             \le(d/2+1)(k-1).}                            \tag{6.1}
\]

For the last inequality, split at `k-1=d/2`. This small improvement is important:
it replaces a would-be free factor exponential in `d` by a factor per `k-1`.

If `C union T`, `T subset D_2(C)`, induces a connected source, then `C` is
connected in the distance-two graph of the cube. That graph has maximum degree
`Delta_2=binom(d,2)`. The standard labelled-tree bound gives at most
`(e Delta_2)^(k-1)` connected `k`-sets through a specified vertex. One proof
counts the `k^(k-2)` labelled spanning trees and at most `Delta_2^(k-1)` maps
rooted at the specified vertex, then divides by `(k-1)!`.

### 6.1 A precise sufficient weight hypothesis

Suppose weights `A(C,T)` for these connected supports satisfy

\[
 \boxed{|A(C,T)|\le A^k n^{1-k},\qquad A\ge1.}             \tag{6.2}
\]

This is a hypothesis on the **retained parity size**, not on total support
size. The constant `A` must be independent of `d`, `k`, and the number of outside
vertices; it may depend on the spectral constant. A cost exponential in the
number of outside vertices cannot simply be hidden in `A`. The hypothesis is
not asserted for general host activities or general Gram products. For the
weighted family in (6.2), however, the following implication is proved:

\[
 \boxed{n\ge C\,2^d,\ C\ge13000A
 \quad\Longrightarrow\quad
 \sup_v\sum_{C,T:\,v\in C\cup T}
       |A(C,T)|e^{|C|+|T|-1}\le610000A^2/C.}              \tag{6.3}
\]

Representations with either parity retained are allowed, so this is an upper
bound even when a support is counted twice.

**Proof.** The number of possible retained sets is at most
`h(e Delta_2)^(k-1)/k`. Summing the possible outside choices with the activity
fugacity costs

\[
 \sum_{T\subseteq D_2(C)}e^{|T|}
    =(1+e)^m\le(1+e)^{(d/2+1)(k-1)}.
\]

For rooted support counting, transitivity and
`|C union T|/k <= 1+d/2` give the load bound

\[
 A(1+d/2)\sum_{k\ge2}r_d^{k-1},\qquad
 r_d=\frac{A e^2\Delta_2(1+e)^{d/2+1}}n.                 \tag{6.4}
\]

Put

\[
 \tau=\log2-\tfrac12\log(1+e)>0.
\]

Since `n>=C2^d`,

\[
 r_d\le\frac{A e^2(1+e)}C\binom d2 e^{-\tau d}.
\]

The continuous bound `sup_{t>=0} t^j exp(-tau t)=(j/(e tau))^j` shows that
`r_d<=1/2` if `C>=4A(1+e)/tau^2`. In that range the load is at most

\[
 \frac{A^2}{C}
 \left(\frac{4(1+e)}{\tau^2}
              +\frac{27(1+e)}{2e\tau^3}\right).           \tag{6.5}
\]

For simple conservative integer constants, `tau>1/28`, `e<3`, and `e>2`
give (6.3). For example `tau>1/28` follows from `e<2.72` and the cubic lower
Taylor bound for `exp(-1/14)`, which gives `4 exp(-1/14)>3.72`.
Numerically, `tau=0.0365163368...`; the two constants before rounding in this
argument are about `11153.93` and `390399.03`. For `d=1` this family is empty. □

This is a genuinely dimension-uniform, all-size skeleton summation result.
There is no maximum core size cutoff. The core estimate (6.2), not the
combinatorial summation, is the unproved step for general resummed weights.

### 6.2 Why charging `2^{e(U)}` separately destroys this margin

For a once-subdivision support, every outside vertex supplies two source
edges. Charging the stability factor `2^{e(U)}` before the resummation changes
`(1+e)^m` to `(1+4e)^m`. The crucial ratio

\[
 \frac{\sqrt{1+e}}2<1
\]

then becomes `sqrt(1+4e)/2>1`. Thus this calculation gives a concrete reason
that the suggested stability/operator pairing must take place **inside a
whole-core estimate**. A raw stability factor followed by a separate spectral
bound loses precisely the small exponential margin that makes (6.3) work.

### 6.3 The unbalanced cube example is included

Take `C` to be the `d` vertices at level one, and `T` to be all `binom(d,2)`
vertices at level two. The induced graph is the once-subdivision of `K_d`.
It has minimum degree two for `d>=3`, but

\[
 |C|=d,\qquad |T|=\binom d2,\qquad |C\cup T|\asymp d^2.
\]

The retained-centre normalization in (6.2) is compatible with this example.
A claim of suppression `n^{-|C union T|/2}` is neither used nor established.

---

## 7. An all-core positive class: projection Gram kernels and flows

There is a useful nontrivial model in which the hypothesis (6.2) for **bare
spectral cores** can actually be proved for every connected skeleton, not just
cycles.

Suppose

\[
 M^2=nI-J,\qquad \Gamma=M^2/n=I-J/n.                       \tag{7.1}
\]

Paley graphs of prime order `n=1 mod 4`, with their actual density `p=1/2`,
satisfy this. Here is an elementary verification of that host class. With
`chi` the quadratic character, extended by `chi(0)=0`, their centred matrix is
`M_xy=chi(x-y)`. Its rows sum to zero. The diagonal entries of `M^2` are `n-1`;
for distinct `x,y`, the change of variable `z=y+(x-y)t` reduces the entry to
`sum_t chi(t(1-t))=-1`. To see the last character identity without an estimate,
count solutions to `u^2=t(t-1)`: the factorization
`(2t-1-2u)(2t-1+2u)=1` gives exactly `n-1` solutions, whereas summing over `t`
gives `n+sum_t chi(t(t-1))`. Since `chi(-1)=1`, this proves (7.1). In particular
`||B||=sqrt(n)/2`, so these are dense hosts satisfying the original spectral
hypothesis, not merely abstract PSD examples. More generally the following
statement only needs the displayed projection Gram kernel.

Let `S` be any connected loopless multigraph on `k` retained vertices and `m`
edges. Parallel edges are retained. Let `Sub(S)` replace each edge by its own
degree-two outside vertex. Then

\[
 \boxed{t_{\operatorname{Sub}(S)}(M)
    =t_S(\Gamma)
    =\frac{\operatorname{Flow}_S(n)}{n^m}
    \in[0,n^{1-k}].}                                     \tag{7.2}
\]

Here `Flow_S(n)` counts nowhere-zero flows in the finite abelian group
`Z/nZ`, after arbitrarily orienting the edges.

**Proof.** Eliminate the degree-two outside vertices to get `t_S(Gamma)`.
Expand each factor `Gamma_xy=delta_xy-1/n`. For a selected edge set `E'`, the
equality constraints have `c(E')` components, including isolated vertices, so

\[
 t_S(\Gamma)=n^{-m}
    \sum_{E'\subseteq E(S)}(-1)^{m-|E'|}
                       n^{|E'|-k+c(E')}.
\]

A flow supported on `E'` has exactly `n^{|E'|-k+c(E')}` choices: choose values
on non-tree edges and solve successively on a spanning forest. Inclusion-exclusion
for nonzero values on every edge gives (7.2). The full flow space of a connected
`S` has size `n^{m-k+1}`, so its nowhere-zero subset is no larger. This proves
both positivity and the bound. A bridge gives zero, as it should. □

Thus (6.3) applies with `A=1` to **all bare connected once-subdivision spectral
products** in a projection-Gram host. The load of this entire positive diagram
class is at most `610000/C` at `n>=C2^d`, `C>=13000`. This includes highly
unbalanced, dense skeletons and all their cycle lengths.

It is important to state exactly what this does **not** prove. Bare
homomorphism products are not the full connected activities. In fact, the
positivity in (7.2) is not even preserved by requiring only the retained
vertices to be injective. For distinct retained labels every Gram factor is
`-1/n`, so the corresponding partially injective product is

\[
 \boxed{\frac{(n)_k}{n^k}\left(-\frac1n\right)^m.}          \tag{7.3}
\]

For a triangle skeleton this is negative, although its once-subdivision is an
even six-cycle and its unrestricted product is positive. At `n=5`, the two
values are respectively `-12/3125` and `4/125`. Full outside injectivity has
further corrections. This exact example demonstrates why (3.4) and (4.5)
must accompany positive bare cores in any proof about `Xi`.

---

## 8. Complementary full-partition positivity for all 2-degenerate sources

The same Gram information gives a substantial general class for which one can
prove positivity of the **complete injective partition**, even though its raw
activities may have either sign.

Assume

\[
 p\ge1/3,\quad\|B\|\le L\sqrt n,\quad n\ge48,\qquad
 |\rho_x|\le1/16\quad\text{for every }x.                   \tag{8.1}
\]

The stronger flatness used in section 5 implies (8.1). Let

\[
 b=\lceil576L^2\rceil.
\]

### 8.1 A uniformly sparse bad-codegree graph

Since `|M_xy|<=2`,

\[
 \Gamma_{xx}\le4,\quad\|\Gamma\|\le(L/p)^2,\quad
 \sum_y\Gamma_{xy}^2\le\|\Gamma\|\Gamma_{xx}\le36L^2.
                                                               \tag{8.2}
\]

For `x ne y`, direct multiplication of `a=J-I+M` gives

\[
 \frac{\operatorname{codeg}(x,y)}{p^2n}
 =1-\frac2n+\rho_x+\rho_y-\frac{2M_{xy}}n+\Gamma_{xy}.
                                                               \tag{8.3}
\]

The part before `Gamma_xy` is at least `3/4` by (8.1). Therefore a pair with
codegree below `p^2 n/2` must have `Gamma_xy < -1/4`. By (8.2), every host
vertex has at most `576L^2 <= b` such bad partners.

This is a uniform statement for each row, not just an average over pairs.

### 8.2 Greedy theorem with a maintained pair condition

Let `H` be any 2-degenerate source with `h_0` vertices and maximum degree at
most `d`. If

\[
 \boxed{n\ge36(h_0+b d^2+1),}                             \tag{8.4}
\]

then `H` has an ordinary injective embedding in `G`, and hence `Xi(H)>0`.

**Proof.** Use an ordering with at most two earlier neighbours at each vertex.
Maintain the additional invariant that two already embedded source vertices
with a common **unembedded** neighbour have host codegree at least `p^2 n/2`.

At the next vertex, its zero, one, or two earlier neighbours give a candidate
set of size at least `n/18`: the two-neighbour case uses the invariant, and the
one-neighbour case uses the degree bound in (8.1). Remove the at most `h_0-1`
already used images. Also ensure the invariant for every earlier source vertex
sharing a future neighbour with the current one. There are at most `d(d-1)`
of these vertices, each forbidding at most `b` host labels. The number removed
is at most `h_0-1+b d^2<n/18` by (8.4), so a candidate remains. This preserves
both injectivity and the invariant. □

One may replace `b` in (8.4) by the actual maximum number of bad partners if it
is known more sharply. The verification script uses that sharper form for an
explicit embedding of cube levels one and two in `Paley(401)`.

For cube supports the inequality `d^2<=9*2^d/8` makes (8.4) a
constant-multiplier condition in the size of the ambient cube. Under the
original large-constant pruning assumptions of section 5 it holds for every
2-degenerate cube support. In particular the levels-1-and-2 incidence graph of
`K_d` is covered with no balanced-rank assumption.

This supplies a positive complete-partition baseline for a broad core class.
It does **not** authorize removing that class's activities from the complete
cube polymer gas: stars already show that `Xi(H)>0` and negative `w(H)` can
coexist. A further exact, overlap-compatible positive-baseline criterion would
be needed to use this positivity globally.

---

## 9. What is now reduced, and the precise remaining gap

### Established without a size cutoff

* All source-isolated vertices can be removed exactly, with the load transfer
  (2.4) and its unavoidable sign flip (2.3).
* Arbitrary independent outside sets, of every degree and with overlapping
  neighbourhoods, can be integrated by (3.1); (3.2) returns the original
  connected activity. This is a complete algebraic resummation for all cube
  supports, not merely a partition function for a selected subfamily.
* Leaf and degree-two deletion have the exact activity-level forms (4.4) and
  (4.5). Their filled edges, multiplicities, marked degree errors, and
  three-vertex corrections are explicit.
* Complete star/double-star activities with arbitrary isolates have the
  quantitative constant-linear-scale bound (5.12).
* A codegree-aware skeleton enumeration is sufficient at constant-linear
  scale if resummed core weights admit the retained-centre estimate (6.2).
  This condition is realized for all bare projection-Gram subdivision cores.
* Whole injective partitions of all 2-degenerate sources are positive under
  (8.4), including arbitrarily large unbalanced subdivision cores.

### Still required for the full cube load

1. **Control the marked responses, not just the kernels.** Even for degree two,
   `Delta_ab[Gamma]` is not a positive term in general. The triple responses in
   (4.5), or equivalently the higher occupation blocks (3.4), are not bounded
   here in a way that can be summed over all supports.
2. **Continue through branching cores and disconnected source components.**
   The centre cumulant (3.2) handles them exactly but has no uniform estimate
   here as the number of centres and neighbourhood arities grow. The two-centre
   estimate does not cover two separate stars with arbitrary placement, nor
   a double-star selected inside a larger non-double-star support.
3. **Obtain an adequate whole-core spectral estimate.** Formula (6.2) is not
   claimed for general Gram products, still less for all corrected activities.
   Its retained-centre exponent deliberately avoids the false total-support
   rank assumption. A proof may require a further decomposition by branching
   and bridge structure and a stability estimate applied before absolute values.
4. **Keep the partition identity at every change of baseline.** Positive bare
   even cycles, projection-flow cores, or the positive partitions in section 8
   cannot be substituted for activity blocks without an exact compatibility
   argument. Equations (4.6) and (7.3) are explicit finite-population warnings.

Consequently the full negative-activity criterion still needs (5.13), or a
proved alternative criterion for an exactly equivalent positive-core baseline.
No dimension-uniform full theorem for arbitrary dense spectral hosts is claimed.
The previously established full embedding bound with the additional factor
`d^2` is not improved by assertion.

---

## 10. Verification scope

Run

```text
python3 Submission/check_cube_general_core.py
```

The script checks:

* the original connected signed graph sum against moment-log cumulants;
* isolated dressing through four extra isolates, including disconnected old
  sources and `z=0,1/2,1`;
* the vertex-cover occupation formula and centre cumulant, including `Q_3`,
  shared degree-two neighbours, and disconnected star centres;
* the arbitrary-degree deletion identity through degree four, with exact
  pair/hyperedge responses and an already-present edge acquiring a second
  Boltzmann factor;
* both leaf counts `0..3` in the two-centre EGF against independently calculated
  rational activity coefficients;
* the analytic constant arithmetic and complex bidisc boundary samples in
  regular Paley examples satisfying the size assumptions;
* the isolated-dressing combinatorial majorants and cube degree-two pool
  inequalities for every core subset in dimensions two through five;
* projection-Gram/flow identities, including multigraphs and bridges, and the
  sign change caused by injecting only the retained centres;
* an actual 2-degenerate embedding certificate, and the unchanged hash of
  `Spec.lean`.

Finite checks do not prove the all-order estimates; the arguments in sections
2--8 do. The script expressly does not test or certify (5.13).
