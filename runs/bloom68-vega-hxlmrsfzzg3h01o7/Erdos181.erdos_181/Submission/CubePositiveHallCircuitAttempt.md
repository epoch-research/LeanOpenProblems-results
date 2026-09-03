# Positive Hall-circuit incidences: a global reservoir branch and its exact entropy price

## Outcome

**This does not prove or disprove `R(Q_d)=O(2^d)`. The diffuse branch of the attempted global proof is still open. No Ramsey constant or Lean theorem claim is made. `Submission/Spec.lean` is unchanged.**

This continues the exact **both-colour, all-partition** argument in `CubeHallEntropyClosureAttempt.md`, using the full positive incidence system behind `CubeTwoColourGlobalCompletion.md` §2. It does not replace the completion-weighted laws by uniform laws or multiply probabilities for Hall-tree edges.

The main new proved result is a genuine global, nearly complete reservoir branch:

> Put `m=2^(d-1)`. If `d>=2048`, `N>=5m`, and a colour `c` has disjoint host sets `T,Z` with
> 
> `|T|=m-u`, `|Z|=2m`, `u>=1`, and `u+e<=d^2`,
> 
> such that each vertex of `Z` has at most `e` non-`c` neighbours in `T`, then the **whole two-colouring contains an injective monochromatic `Q_d`**.

The proof does not call `K_(m,m-1)` a cube. It accounts for the original deficit `u`, the reservoir vertices removed to control errors, both parity classes of a smaller face, both sets of private neighbours of that face, and every remaining vertex. The smaller cube is constructed in an original host graph by an explicit dependent-random-choice argument; no Ramsey bound for a smaller cube is assumed.

Consequently, in a global countercolouring, for **every** `T` with `|T|<=m-1` and either colour,

\[
 \left|\{z\in U\setminus T:d_c(z,T)\ge m-d^2\}\right|\le2m-1.
 \tag{0.1}
\]

This supplies a new **full-positive-incidence entropy price without incidence-profile conditioning**. Sections 6–7 give the exact price, its insertion into the existing completion-density invariant, and the correctly charged full-profile count attempted for the remaining branch. The resulting argument has not shown that an arbitrary countercolouring supplies enough of this price, or a successful augmentation when the positive demands are more diffuse.

---

## 1. The global problem and the unchanged completion ledger

Throughout, the two parity classes of `Q_d` are `E,O`, each of size

\[
 m=2^{d-1}.
\]

The symbol `u` below denotes a **reservoir row deficit**, not the size of the cube.

Assume for the attempted contradiction that a red-blue complete host `U`, of size `N`, contains neither colour of ordinary injective `Q_d`. For every partition

\[
 U=A\dot\cup B,\qquad |A|=a\ge m,\quad |B|=b\ge m,
\]

and every injection `f:E -> A`, both exact list systems

\[
 L_{f,c}(y)=B\cap\bigcap_{x\in N_Q(y)}N_c(f(x))
 \tag{1.1}
\]

fail Hall. Let the canonical minimal joint key be

\[
 K(f)=(S_R,T_R,S_B,T_B),\qquad
 T_c=L_{f,c}(S_c),\qquad |T_c|=|S_c|-1.
 \tag{1.2}
\]

For a key `κ`, write

\[
 \mathcal F_\kappa=\{f:K(f)=\kappa\},\qquad
 P_\kappa=\operatorname{Unif}(\mathcal F_\kappa),\qquad
 E_\kappa=\log\frac{(a)_m}{|\mathcal F_\kappa|}.
\]

The reference `μ` is uniform on **all** injections `E -> A`. The input's catalogue calculation gives

\[
 \sum_\kappa\mu(\mathcal F_\kappa)E_\kappa
 =H(K)\le2\log\binom{b+m}{m-1}.
 \tag{1.3}
\]

We eventually take `b=3m`, `a=N-3m`, so

\[
 H(K)\le2m\log(256/27)<4.50m.
 \tag{1.4}
\]

The adaptive invariant from `CubeHallEntropyClosureAttempt.md` is retained exactly. At an actual prefix `g` exposing `q_0` even labels, put `n=a-q_0`, `r=m-q_0`, and

\[
 w_g=|\{f\in\mathcal F_\kappa:f\supset g\}|,\qquad
 \mathcal V_g=\log\frac{(n)_r}{w_g}.
\]

For a nonanticipating next batch `I`, of size `s`,

\[
 \pi_g(z)=\frac{w_{g,z}}{w_g},\qquad
 \delta_g=D\!\left(\pi_g\middle\Vert\operatorname{Unif}(\operatorname{Inj}(I,A\setminus\operatorname{im}g))\right),
\]

and

\[
 \mathcal V_g=\delta_g+\sum_z\pi_g(z)\mathcal V_{g,z},
 \qquad
 \mathbb E_{P_\kappa}\sum_g\delta_g=E_\kappa.
 \tag{1.5}
\]

There is no `Gamma` term. In particular, every positive-incidence restriction used below remains inside the actual `w_g`.

The reservoir extractions below may change the host cut, use vertices outside the old candidate pool, or produce the other colour. This is legitimate because the contradiction assumption concerns the **whole host**, not merely extensions respecting a frozen boundary.

---

## 2. Full positive incidences, not independent tree-edge events

Fix an actual key and an actual injection in its fibre. For `v in T_c`, define

\[
 R_{c,v}(f)=\{y\in S_c:v\in L_{f,c}(y)\},\qquad
 W_{c,v}(f)=N_Q(R_{c,v}(f))\subset E.
 \tag{2.1}
\]

Thus `W_(c,v)` is the **entire union** of cube neighbourhoods of the certificate rows containing `v`. Define the positive demand at an even label by

\[
 P_{x,c}(f)=\{v\in T_c:x\in W_{c,v}(f)\},\qquad
 \lambda_{x,c}(f)=|P_{x,c}(f)|.
 \tag{2.2}
\]

Every such demand is a literal host edge:

\[
 P_{x,c}(f)\subseteq N_c(f(x))\cap T_c.
 \tag{2.3}
\]

### The exact circuit condition in candidate-incidence form

For a list system on `S` with `T=L(S)` and `|T|=|S|-1`, inclusion-minimal deficiency is equivalent to

\[
 \left|\bigcup_{v\in V}R_v\right|\ge |V|+1
 \quad\text{for every nonempty }V\subseteq T.
 \tag{2.4}
\]

The forward direction is the input's Hall-circuit proof. For the converse, take a proper nonempty `X subset S` and put `V=T\L(X)`. If `V` is empty, `|L(X)|=|S|-1>=|X|`. Otherwise `X` is disjoint from `union_(v in V) R_v`, whence

\[
 |X|\le |S|-|V|-1=|L(X)|.
\]

So every proper subset satisfies Hall while `S` is deficient. This proves the equivalence, including the singleton case with `T` empty.

In particular, every candidate in a nonempty `T_c` occurs in at least two rows. Therefore

\[
 |W_{c,v}(f)|\ge2d-2,
 \qquad
 \sum_{x\in E}\lambda_{x,c}(f)
 =\sum_{v\in T_c}|W_{c,v}(f)|
 \ge(2d-2)|T_c|.
 \tag{2.5}
\]

The labelled tree of the input is a valid subcertificate of these incidences. We do **not** replace `W_(c,v)` by the two endpoint neighbourhoods when forming (2.2).

Both colours also remain simultaneous:

\[
 P_{x,R}(f)\cap P_{x,B}(f)=\varnothing.
 \tag{2.6}
\]

Equivalently, if the same host candidate belongs to both `T_R,T_B`, then its red and blue sets `W_(c,v)` are disjoint. Otherwise a single actual host edge would have both colours. These are restrictions on one common injection; they are not independence assertions about candidates or source variables.

---

## 3. A robust reservoir extension with every missing vertex filled

This strengthens the complete-reservoir extension in `CubeSquareFreeCriticalEstimate.md` §3. It is a statement about an original bipartite graph `G=(A,B_0)`.

### Theorem 3.1 — nearly complete row-reservoir extension

Let `d>=2`, `1<=k<d`, and put

\[
 j=d-k,\quad q=2^{k-1},\quad m=2^{d-1},\quad
 r=m-q,\quad D=(j+1)q.
\]

Let `Δ>=0` be an integer. Suppose `R subset A`, `|R|=r`, and

\[
 |B_0|\ge m+d\Delta,\qquad
 |B_0\setminus N_G(v)|\le\Delta\quad(v\in R).
 \tag{3.1}
\]

Define

\[
 A_+=\{a\in A\setminus R:d_G(a,B_0)\ge D+(d-1)\Delta\},
\]

\[
 B_+=\{b\in B_0:d_G(b,R)\ge jq\}.
 \tag{3.2}
\]

If `G[A_+,B_+]` contains a bipartition-respecting injective `Q_k`, then `G` contains an injective `Q_d`.

#### Proof

Write source vertices as `(z,w) in {0,1}^j x {0,1}^k`. Let `E_0,O_0` be the parity classes in the face `z=0`, each of size `q`. Embed them using the smaller cube, with `E_0` in `A_+` and `O_0` in `B_+`.

**1. Place the reservoir even vertices adjacent to the already embedded face.**

There are exactly `jq` even vertices outside `E_0` with a neighbour in `O_0`:

\[
 (e_i,w),\qquad 1\le i\le j,\quad w\text{ odd}.
\]

Each has exactly one neighbour in `O_0`, namely `(0,w)`. Assign these even vertices successively to unused neighbours in `R` of the appropriate `O_0` image. That image has at least `jq` neighbours in `R`, and before the `t`-th assignment fewer than `jq` reservoir vertices have been used. Thus an unused choice exists.

There are `r-jq=(2^j-1-j)q>=0` other even vertices outside the face. Assign them bijectively to the remaining vertices of `R`. Every edge incident with `O_0` has now been checked: the within-face edges came from the smaller cube, and all its edges leaving the face were checked in this stage.

**2. Place the private odd neighbours of the face's even vertices.**

There are exactly `jq` odd vertices outside `O_0` having a neighbour in `E_0`:

\[
 (e_i,w),\qquad 1\le i\le j,\quad w\text{ even}.
\]

Each has exactly one neighbour in `E_0`; its other `d-1` neighbours are already mapped into `R`. The external even image has at least `D+(d-1)Δ` neighbours in `B_0`. Intersecting with the neighbourhoods of these `d-1` reservoir images deletes at most `(d-1)Δ` columns. Hence at least `D` candidates remain before injectivity exclusions.

At the `t`-th such assignment, starting from zero, only `q+t` columns have been used, leaving at least

\[
 D-q-t=jq-t>0
\]

choices. Assign a fresh candidate.

**3. Place all remaining odd vertices.**

There remain `m-D` odd source vertices. None has a neighbour in `E_0`, so all its `d` neighbours lie in `R`. Its common neighbourhood in `B_0` has size at least

\[
 |B_0|-d\Delta\ge m.
\]

Greedy distinct assignment finishes them.

We have placed exactly `q+r=m` even vertices and `q+jq+(m-D)=m` odd vertices. The even images are injective in the disjoint sets `A_+,R`; the odd images are distinct by construction; and the host bipartition is disjoint. The three stages cover every kind of cube edge. Thus all `2m` images and all `dm` required edges are accounted for. ∎

The condition on `B_+` is essential to this proof: simply planting a smaller cube in `B_0` and ignoring its edges to the nearly complete reservoir would not be a valid extension.

When `Δ=0`, the theorem recovers the complete-reservoir extension. For `k=1`, `q=1`, it fills the missing even vertex of an `(m-1)`-row reservoir from one suitable outside edge, but still requires all `d` appropriate neighbours and places the remaining odd vertices explicitly.

---

## 4. The complete borderline: using both colours rather than declaring a cube

### Proposition 4.1

Let `d>=2` and put

\[
 b_d=m+d(d-1).
\]

If `N>=3m+d(d-1)-1` and the host has a colour-`c` complete rectangle with sides of sizes `m-1` and `b_d`, then it contains a monochromatic `Q_d`.

**Proof.** Call the two sides `T,Z`. There are at least `m` vertices outside `T union Z`.

If one outside vertex has at least `d` colour-`c` neighbours in `Z`, use the complete-reservoir extension with `k=1,q=1,R=T` and any one of these edges as the smaller cube. This gives a colour-`c` `Q_d`.

Otherwise every outside vertex has at most `d-1` colour-`c` neighbours in `Z`. Choose `m` outside vertices for the even class of a complementary-colour cube. Every odd source row then has at least

\[
 |Z|-d(d-1)=m
\]

common complementary-colour neighbours in `Z`. Greedy distinct assignment gives that cube. ∎

Thus the actual common neighbourhood of any `(m-1)`-set has size at most `b_d-1` in a countercolouring of this size. Merely having `K_(m,m-1)` does not meet the displayed column bound: its missing vertices are **not** silently supplied. In the entropy application, a small actual common-neighbour pool can instead be charged as a small pool.

---

## 5. A genuine global nearly complete reservoir theorem

### 5.1 The smaller cube used in the descent

We use the following elementary bipartite dependent-random-choice calculation, proved here to specify what the descent actually assumes.

Let a bipartite graph have sides `X,Y`, of sizes `a_0,b_0`, where `b_0>=1` and `0<=p<=1`, with every `x in X` having at least `p b_0` neighbours in `Y`. For `k>=1`, put `q=2^(k-1)`. If

\[
 a_0p^{2k}-\binom{a_0}{k}
       \left(\frac{q-1}{b_0}\right)^{2k}\ge q,
 \tag{5.1}
\]

then this graph contains an injective, bipartition-respecting `Q_k`.

**Proof.** Sample `2k` columns independently with replacement, and let `V` be their common neighbourhood in `X`. Then

\[
 \mathbb E|V|\ge a_0p^{2k}.
\]

Call a `k`-set of rows bad if it has fewer than `q` common neighbours in `Y`. The expected number of bad `k`-sets contained in `V` is at most the second term in (5.1). Some sample therefore has `|V|` minus this number at least `q`. Delete at most one row for each bad set. The remaining set has at least `q` rows, and every `k`-subset of it has at least `q` common neighbours.

Map the `q` even vertices of `Q_k` into this set. Every odd vertex has a list of at least `q` columns, so greedy distinct assignment places all `q` odd vertices. No independence of these lists is used. ∎

### Theorem 5.2 — parameter-exact global reservoir completion

Let `d>=2`, `m=2^(d-1)`, and suppose disjoint `T,Z subset U` satisfy

\[
 |T|=m-u,\qquad |Z|=2m,\qquad
 d_{\bar c}(z,T)\le e\quad(z\in Z),
 \tag{5.2}
\]

where `u>=1` and `e>=0` are integers, and `N>=5m-u`.

Choose integers `1<=k<d`, `Δ>=0`, and put

\[
 q=2^{k-1},\qquad j=d-k,\qquad L=\lfloor m/d\rfloor.
\]

The following explicit conditions suffice for an actual monochromatic `Q_d`:

\[
\begin{aligned}
 q&\ge u+\left\lfloor\frac{2me}{\Delta+1}\right\rfloor, &(5.3a)\\
 d\Delta&\le m, &(5.3b)\\
 m-q-e&\ge jq, &(5.3c)\\
 (j+1)q+(d-1)\Delta&\le L+1, &(5.3d)\\
 m&\ge2q(2d)^{2k}. &(5.3e)
\end{aligned}
\]

#### Proof

At most `floor(2me/(Δ+1))` vertices of `T` have more than `Δ` wrong-colour neighbours in `Z`, since the total number of such edges is at most `2me`. By (5.3a), choose exactly `m-q` of the remaining vertices as `R`. Every member of `R` has at most `Δ` wrong-colour neighbours in `Z`.

This step accounts for the original deficit `u` **and** the `q-u` reservoir vertices left unused. The `q` replacement even vertices will belong to the smaller face, not to an assumed completed reservoir.

Every `z in Z` has at least `m-q-e>=jq` colour-`c` neighbours in `R`. Thus all of `Z` belongs to the set `B_+` in Theorem 3.1. Its column-size condition follows from (5.3b).

Put `X=U\(T union Z)`, so `|X|>=2m`.

* If at least `m` vertices of `X` have colour-`c` degree at most `L` into `Z`, map the even class into them. Every odd row has at least `2m-dL>=m` complementary-colour candidates in `Z`. This gives an injective colour-`bar(c)` cube.
* Otherwise at least `m` vertices of `X` have colour-`c` degree at least `L+1` into `Z`. Choose `m` of them as `X_0`. By (5.3d), these all belong to `A_+` in Theorem 3.1. Their colour-`c` density into `Z` is greater than `1/(2d)`.

In the second case, apply (5.1) to the colour-`c` graph on `X_0,Z`, with `a_0=m`, `b_0=2m`, `p=1/(2d)`. Its first term is at least `2q` by (5.3e). Also (5.3e) implies `q^2<=m`, and therefore its second term is at most

\[
 \binom mk\left(\frac{q-1}{2m}\right)^{2k}
 \le\left(\frac{q^2}{4m}\right)^k\le4^{-k}\le\frac14.
\]

So a colour-`c` `Q_k` exists in the **actual** graph `G[X_0,Z]`. Theorem 3.1 extends it through `R` to an injective colour-`c` `Q_d`. ∎

This is a terminating descent, not an assumed iteration: the smaller cube is already constructed by (5.1), and its lift is the complete construction of Section 3.

### Corollary 5.3 — a concrete polynomial-error range

For `d>=2048`, `N>=5m`, and

\[
 u\ge1,\qquad e\ge0,\qquad u+e\le d^2,
 \tag{5.4}
\]

every reservoir (5.2) gives a monochromatic `Q_d`.

**Parameter proof, valid for every such dimension.** Set

\[
 \Delta=\left\lfloor\frac{m}{4d^2}\right\rfloor,
 \qquad
 q=\text{the least power of two at least }u+8d^2e,
 \qquad k=1+\log_2q.
 \tag{5.5}
\]

Then

\[
 q<2(u+8d^2e)\le18d^4,
 \qquad k<6+4\log_2d.
 \tag{5.6}
\]

Since `Δ+1>m/(4d^2)`, (5.3a) holds; for `e=0` its floor term is simply zero. Condition (5.3b) is immediate.

The elementary inequality

\[
 m\ge24d^6\qquad(d\ge2048)
\]

holds at `d=2048` (indeed `24*2048^6<2^71<2^2047`) and continues by induction, since `(d+1)^6<2d^6` in this range. Hence

\[
 (j+1)q+(d-1)\Delta
 <18d^5+\frac{m}{4d}\le\frac md,
\]

which proves (5.3d). Also `(j+1)q+e<=m`, proving (5.3c).

For (5.3e), put `ell=floor(log_2 d)>=11`. The inequality

\[
 2^\ell-1\ge8\ell^2+40\ell+50
 \tag{5.7}
\]

holds at `ell=11` and is preserved on increasing `ell` by one: twice the right side plus one exceeds the next right side by `8ell^2+24ell+3`. From (5.6),

\[
 k(3+2\log_2d)
 <(4\ell+10)(2\ell+5)
 =8\ell^2+40\ell+50
 \le d-1.
\]

This proves `m>=2q(2d)^(2k)` and also ensures `1<=k<d`. All conditions of Theorem 5.2 hold. ∎

The numerical constant `2048` is only a convenient sufficient threshold for this **proved reservoir branch**, not a claimed threshold for the general Ramsey problem.

---

## 6. Pricing full positive incidences without naming a profile

Assume again that the **whole host** is a countercolouring, with `d>=2048`, `N>=5m`.

### 6.1 A global host-pool cap

For either colour and every `T subset U` with `|T|<=m-1`,

\[
 \boxed{\quad
 \left|\{z\in U\setminus T:d_c(z,T)\ge m-d^2\}\right|\le2m-1.
 \quad}
 \tag{6.1}
\]

Indeed, when `|T|<m-d^2` the set is empty. Otherwise put `u=m-|T|` and `e=|T|-(m-d^2)`, so `u>=1`, `e>=0`, and `u+e=d^2`. If the displayed set contained `2m` vertices, Corollary 5.3 would give a cube. This proves (6.1).

For the rest of Section 6 take `b=3m`, `a=N-3m`; the cap (6.1) itself is independent of that choice. Return to a fixed such host partition and a fixed **joint key** `κ`. Define the host sets

\[
 \mathcal D_{\kappa,c}
 =\{a'\in A:d_c(a',T_c)\ge m-d^2\},
 \qquad
 \mathcal D_\kappa=\mathcal D_{\kappa,R}\cup\mathcal D_{\kappa,B}.
 \tag{6.2}
\]

They are determined by the key and the host, not by a subsequently selected incidence profile. Equation (6.1) gives

\[
 |\mathcal D_{\kappa,c}|\le2m-1,\qquad
 |\mathcal D_\kappa|\le4m-2.
 \tag{6.3}
\]

For the full positive incidence system of an actual `f in F_κ`, put

\[
 \eta_\kappa(f)=
 \bigl|\{x\in E:\lambda_{x,R}(f)\ge m-d^2
                   \text{ or }\lambda_{x,B}(f)\ge m-d^2\}\bigr|.
 \tag{6.4}
\]

By (2.3),

\[
 \eta_\kappa(f)\le
 H_\kappa(f):=|\operatorname{im}(f)\cap\mathcal D_\kappa|.
 \tag{6.5}
\]

Every positive incidence is still retained in (2.1)–(2.2); (6.4) is a statistic of that full system. No source label or tree is additionally conditioned on to obtain (6.5).

### 6.2 Exact finite-population price

For a fixed host set of size `D`, the MGF of its occupancy by a uniform injection is

\[
 M_{a,m,D}(t)
 =\frac1{(a)_m}\sum_{i=0}^m
       \binom mi(D)_i(a-D)_{m-i}e^{ti}.
 \tag{6.6}
\]

Zero falling factorials handle the infeasible terms.

For each key and every `t>=0`, relative entropy against the exponentially tilted reference law gives

\[
 \boxed{\quad
 E_\kappa\ge
 t\,\mathbb E_{P_\kappa}\eta_\kappa(F)
 -\log M_{a,m,|\mathcal D_\kappa|}(t).
 \quad}
 \tag{6.7}
\]

**Proof.** For the reference law `Q_t(f)=mu(f) exp(t H_κ(f))/M`,

\[
 D(P_\kappa\Vert\mu)
 =D(P_\kappa\Vert Q_t)
    +t\mathbb E_{P_\kappa}H_\kappa-\log M.
\]

Use nonnegativity of KL and (6.5). This argument does not assume that the distribution of positive incidences is uniform. ∎

Assume `a>4m-2` and put

\[
 p=\frac{4m-2}{a},\qquad
 \theta=\frac1m\mathbb E_{F\sim\mu}\eta_{K(F)}(F).
\]

Averaging (6.7) over **all** key fibres, and using monotonicity of (6.6) in `D`, yields

\[
 H(K)\ge tm\theta-\log M_{a,m,4m-2}(t).
 \tag{6.8}
\]

The exact factorial-moment expansion gives

\[
 M_{a,m,4m-2}(t)
 =\sum_{i=0}^m\binom mi
       \frac{(4m-2)_i}{(a)_i}(e^t-1)^i
 \le(1-p+pe^t)^m.
 \tag{6.9}
\]

Here `(4m-2)_i/(a)_i<=p^i`; this is a without-replacement calculation, not an independent-host approximation.

If `theta>=p`, optimizing over `t>=0` proves

\[
 H(K)\ge m\left[
 \theta\log\frac\theta p+
 (1-\theta)\log\frac{1-\theta}{1-p}\right].
 \tag{6.10}
\]

For every `theta`, the choice `t=log(1/p)` gives the convenient consequence

\[
 \boxed{\quad
 \theta\le
 \frac{H(K)/m+\log2}{\log(a/(4m-2))}
 <\frac{4.50+\log2}{\log(a/(4m-2))}.
 \quad}
 \tag{6.11}
\]

Thus sufficiently many near-full positive demands really would cost a macroscopic amount of the **actual** key entropy. This is not the old `8m/d` pair price. The inequality direction is important: (6.11) is a restriction on a hypothetical countercolouring, not a proof that `theta` has a positive lower bound.

### 6.3 Insertion into the existing adaptive ledger, without double charging

There is also a joint positive/negative version at any actual prefix of (1.5). Let `S_g` be any subset of the `(n)_s` next-batch injections containing the support of the true completion-weighted law `pi_g`. For example, it can impose all of the available closed negative row constraints. Put

\[
 H_g(z)=|\operatorname{im}(z)\cap\mathcal D_\kappa|,
\]

\[
 Z_g(t)=\frac1{(n)_s}\sum_{z\in S_g}e^{tH_g(z)}.
\]

For every `t>=0`,

\[
 \boxed{\quad
 \delta_g\ge t\mathbb E_{\pi_g}H_g-\log Z_g(t).
 \quad}
 \tag{6.12}
\]

This follows by tilting the uniform reference **restricted to `S_g`**, with its normalization retained. At `t=0` it is the ordinary support-count price; with `S_g` the whole unused-pool injection space it is the positive occupancy price. Supremizing over `t>=0` gives a nonnegative price, since the `t=0` value is nonnegative.

It can be substituted into (1.5) and paid by its single terminating potential. The batch and `S_g` must be chosen from `κ,g` and the actual completion family, not from the unknown sampled completion. The conditional law is still `pi_g(z)=w_(g,z)/w_g`.

**No double charge is claimed.** The root occupancy lower bound and the old negative/pair lower bounds are bounds on the same KL loss; they cannot just be added. Formula (6.12), or a legitimate conditional decomposition, is needed for a joint price.

---

## 7. The attempted diffuse completion, with the full incidence information charged

The next attempted step was to price the rest of the positive incidences by keeping their entire profile, not by treating the Hall-tree labels independently. Here is the exact count reached.

For fixed `κ`, let

\[
 \mathcal I(F)=(R_{c,v}(F):c\in\{R,B\},\ v\in T_c)
\]

be the **full actual** profile. For an occurring profile `i`, let

\[
 n_i=|\{f\in\mathcal F_\kappa:\mathcal I(f)=i\}|,
 \qquad q_i=n_i/|\mathcal F_\kappa|.
\]

All the profiles here satisfy (2.4). For each of them use all its demands to form the simultaneous host domains

\[
 D_x(i)=A\cap
 \bigcap_{v\in P_{x,R}(i)}N_R(v)
 \cap\bigcap_{v\in P_{x,B}(i)}N_B(v).
 \tag{7.1}
\]

Their positive completion count is the rectangular permanent

\[
 Z_i^+=\sum_{f\in\operatorname{Inj}(E,A)}
               \prod_{x\in E}\mathbf1_{D_x(i)}(f(x)).
 \tag{7.2}
\]

This count uses the **same injective host assignment at every incidence**, so all overlaps and host collisions are retained. It is not a product of probabilities over tree edges, candidates, or rows.

The actual fibre with profile `i` is a subset of this positive completion set. The zero incidences, exclusions outside `T_c`, exact key-selection rule, and all remaining restrictions are retained in `n_i`, rather than asserted to disappear. Define

\[
 \sigma_i=\log(Z_i^+/n_i)\ge0.
\]

Since `I` is a deterministic function of the injection, ordinary entropy disintegration gives the exact identity

\[
 \boxed{\quad
 E_\kappa=
 \sum_iq_i\left[\log\frac{(a)_m}{Z_i^+}+\sigma_i\right]
 -H(\mathcal I\mid K=\kappa).
 \quad}
 \tag{7.3}
\]

Indeed, the expression in brackets is `log((a)_m/n_i)`, whose average is `E_κ+H(I|K=κ)`.

This is not a reintroduction of an unaccounted `Gamma`: (1.5) remains exact. It identifies the **real information cost of an additional refinement** if one freezes an incidence profile to use (7.1). Working directly with the unrefined completion counts avoids doing that conditioning, but then it still requires a bound on their joint support or their tilted count. Neither choice makes the cost vanish by declaration.

### Where the proof chain stops

The proved global chain is

\[
\begin{gathered}
 \text{no cube in either colour in the whole host}\\
 \Longrightarrow\text{minimal full incidence systems for every injection and partition}\\
 \Longrightarrow\text{global near-reservoir exclusion (6.1)}\\
 \Longrightarrow\text{the unrefined positive price (6.7)--(6.12),}\
 \text{together with the exact full-profile count (7.3).}
\end{gathered}
\]

The missing inference is **not** supplied by (2.5). That bound gives at least `(2d-2)|T_c|` positive incidences, counted with their actual unions. Even when `|T_c|` is comparable to `m`, its scale is `dm`, whereas the threshold in (6.4) is near `m` at an individual even label. The bound does not force a positive proportion of such labels. For small circuits, the candidate set may not even have enough elements to meet that threshold.

The remaining attempt would have to use (7.1)–(7.3), or the exact unrefined tilted counts, to obtain a strict entropy surplus from the remaining patterns or an actual augmentation. No estimate here shows that their positive completion loss exceeds their profile-selection information and the available key entropy. Nor has a legal rebuild of the embedding been extracted from those patterns.

This is a precise stopping point in the same proof chain, **not a new sufficient conjecture**. No assertion is made that all concentrated positive patterns already lie in the near-full reservoir range of Theorem 5.2. In particular, a large overlap among only a few host candidates is not an `(m-q)`-row reservoir. No new obstruction colouring is offered as a substitute for this missing implication.

All these conclusions hold for each original host partition. Optimizing over all partitions and both colour names is allowed but does not itself prove the missing lower bound or augmentation. Likewise the existing `8m/d` ceiling applies only to the old universal pair-price expression; it neither bounds the true KL production nor completes this new positive argument.

---

## 8. Fixed anchors: the exact law change and what minimality then says

The optional anchor move can be made without an entropy error as follows. Fix `T_0 subset B`, `|T_0|=t`, and a colour `c` **before sampling the injection**. Put

\[
 A_0=A\cap\bigcap_{v\in T_0}N_c(v),\qquad a_0=|A_0|\ge m.
\]

Condition `mu` on `F(E) subset A_0`. This produces exactly the uniform law on injections into `A_0`, but its cost relative to the original injection law is

\[
 E_{\rm pin}=\log\frac{(a)_m}{(a_0)_m}.
 \tag{8.1}
\]

For its canonical key fibres the exact averaged deficit, still measured against the original law, is

\[
 E_{\rm pin}+H_{\rm pin}(K).
 \tag{8.2}
\]

Alternatively, one can rebase (1.5) to `Inj(E,A_0)`; then the root key allowance is `H_pin(K)`, but every adjacency to an anchor is automatic and supplies **no new restriction** relative to that reference law. These are two descriptions of the same count, not an entropy saving.

Each colour-`c` row list contains `T_0`, so every minimal circuit in that colour has

\[
 |S_c|\ge t+1.
 \tag{8.3}
\]

There is a further exact endpoint fact: if `|S_c|=t+1`, then

\[
 T_c=T_0,\qquad L_{f,c}(y)=T_0\ (y\in S_c),\qquad
 R_{c,v}(f)=S_c\ (v\in T_0).
 \tag{8.4}
\]

Thus those positive incidences are all anchor incidences already paid for in (8.1), or already built into the rebased domain. Eliminating singleton/small circuits does not automatically provide additional positive entropy for free.

For completeness, fixed anchor sets with a large common neighbourhood are available when the host multiplier is sufficiently large depending on `t`: successively keep a majority-colour neighbourhood for `2t-1` selected vertices. One colour occurs at least `t` times, and the final set is adjacent in that colour to those `t` anchors; its size is at least `(N+1)/2^(2t-1)-1`. Padding the candidate pool to `3m` removes at most another `3m-t` vertices from this set. This is a legitimate fixed-parameter starting move, but (8.1)–(8.4) still apply. An injection-dependent choice of anchors would require its own actual conditioning law instead.

---

## 9. Verification and final status

Run from `/workspace/leanproject`:

```sh
python3 -u Submission/check_cube_positive_hall_circuit.py
```

Recorded output is in `Submission/CubePositiveHallCircuitVerification.txt`.

The audit uses integer and rational arithmetic. Entropy equalities and the tested KL inequalities are represented by rational coefficients of prime logarithms; inequalities are checked by clearing denominators and comparing integer products. The analytic all-dimensional proofs above do not rely on a numerical entropy tolerance.

The recorded checks include:

* **1,558** complete/near-complete reservoir extensions, including **756** with genuinely missing reservoir edges and **447** with missing edges at the already embedded smaller-face columns;
* **896** global complete-reservoir completions, with **550** direct-colour and **346** complementary-colour outcomes;
* **1,384** exact DRC common-neighbour/bad-set moment checks and **428** actual smaller-cube constructions;
* **2,332** literal cube embeddings in total, checking all vertices and **296,569** required original edges;
* **612** actual-host whole-cover entropy checks retaining `GOOD` injections, plus a type-compressed enumeration of all **40,320** full injections in an additional actual host relation;
* **2,028** exact positive-domain permanent counts and **1,710** full-profile entropy ledgers, including **18** fibres with a nonzero profile-information cost;
* **41,184** full positive candidate-neighbourhood incidences and **37,008** checks of the pointwise implication from positive load to membership in the key-determined host pool;
* **2,349** fixed-anchor entropy-rebasing/minimality checks;
* **632** exact hypergeometric MGF checks and **1,896** unrefined occupancy KL inequalities;
* **1,968** exact joint support/positive tilted-price identities at actual prefixes, including **75** nonuniform completion-weighted prefix laws;
* **14,371** integer checks of the near-reservoir parameters, with additional dyadic checks of the displayed all-dimensional inequality.

The small host relations are not asserted to be countercolourings at `N=C2^d`. The global cap (6.1) is proved from the actual reservoir extension, not assumed in those finite relation tests. The full incidence audit counts all injections in its ambient relation, including the `GOOD` sector where present. No asymptotic Ramsey conclusion is inferred from finite checks.

`Submission/Spec.lean` retains SHA-256

```text
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```

**Final status:** the near-complete reservoir branch now has a complete global two-colour proof and a usable, exactly charged positive-incidence entropy consequence. The attempted extension to all remaining full Hall-incidence patterns has not been proved. Therefore the requested arbitrary-colouring bound `R(Q_d)=O(2^d)` remains unresolved.
