# Mixed-signature norm support: compact saturation and the actual distance limit

## Status and exact scope

**The proposed mechanism closes for each fixed field in the question.** The finite exact norm-one ideal obstruction can be augmented by the relative logarithmic torus. Split-prime orientation classes have the required **harmonic Hecke distribution** on this compact group. Consequently almost every locally admissible norm element has an integral representation with arbitrarily small *fixed* relative logarithmic imbalance.

In particular, for fixed `F` of signature `(r,s)`, `r >= 1`, `e=r+2s`, and `E=F(i)`, the full maximal-order polydisks, projected over a **real F-place**, satisfy

\[
 D(P_R)\sim A(4R^2),\qquad
 \lim_{R\to\infty}\frac{D(P_R)\sqrt{\log |P_R|}}{|P_R|}=U(E/F).
\]

Here `A` and `U` have exactly the normalizations of `field_norm_constant_research.md` and `field_norm_constant_audit.md`. Thus this supplies the missing mixed-signature equality, rather than inferring it from a lower bound on an upper capacity.

**Inputs and boundaries.** The proof uses the audited fixed-field local norm-element box asymptotic and its fixed finite-prime divisibility laws, together with classical unitary Hecke L-function theory. The prime distribution needed for the new step is derived below, including the radial-pole check. No conjectural analytic input or field-uniform estimate is used. This is a mathematical argument, not a Lean formalization. It proves neither theorem of `Spec.lean`, which has not been changed. A subsequent independently audited elementary packing proof in `relative_unit_packing_bound.md` supplies the needed uniform lower bound for these actual limiting constants; it does not supply finite-height or arbitrary-subset uniformity.

A useful stronger formulation of the new result is the following. Choose the two E-embeddings `sigma_(j,+), sigma_(j,-)` over each complex F-embedding `tau_j`. For every fixed `a>0`, all but `o(A(X))` of the integral norm elements in the F-box have an integral exact-norm representation `z` such that

\[
 e^{-a/2}\sqrt{|\tau_j\delta|}
 <|\sigma_{j,\pm}z|
 <e^{a/2}\sqrt{|\tau_j\delta|}\quad (1\le j\le s).       \tag{0}
\]

At real F-places one automatically has `|sigma_v z|^2=tau_v(delta)`. The same density-one assertion holds relative to **locally admissible** integral elements, before integral representability is known. Every occurrence of `a` in this statement is fixed before the box tends to infinity; there is no asserted shrinking-window rate.

## 1. The audited inputs actually needed

Write `c` for the nontrivial automorphism of `E/F`, and `N` for the relative norm. At a real F-place, `c` acts as complex conjugation. At a complex F-place it interchanges the two coordinates; it is not coordinatewise complex conjugation there.

Let

\[
 \mathcal B_X=\{\delta\in O_F\setminus\{0\}:
   0<\tau_v\delta\le X\ (v\text{ real}),\quad
   |\tau_j\delta|\le X\ (j\text{ complex})\}.
\]

Let `L(X)` be the locally admissible elements in this box, and let `A_loc(X)=#L(X)`. Local admissibility means positivity at the real places, even valuations at finite inert primes, and the local quadratic norm condition at ramified primes. There is no condition at split finite primes or at complex infinite places. Let `A(X)` count those elements of this box which are norms of elements of `O_E`.

To avoid confusing an Euler product with the polydisk radius, put

\[
 \mathcal I=\prod_{\mathfrak p\ {\rm inert}}(1-q_{\mathfrak p}^{-2})^{-1},
 \qquad
 \mathcal R_{\rm ram}=\prod_{\mathfrak p\ {\rm ramified}}
                                  (1-q_{\mathfrak p}^{-1})^{-1}.
\]

Here `q_p=N_F p`, `t` is the number of finite ramified F-primes, `D_K=|disc K|`, and `kappa_K=Res_(z=1) zeta_K(z)`. The audited local count is

\[
 A_{\rm loc}(X)\sim C_{E/F}\frac{X^e}{\sqrt{\log(X^e)}},\qquad
 C_{E/F}=\frac{2^{1-t}(2\pi)^s}{\sqrt{\pi D_F}}
          \frac{\sqrt{\kappa_E}}{\kappa_F}
          \sqrt{\mathcal I\mathcal R_{\rm ram}}.          \tag{1}
\]

For **every fixed finite set T of split F-primes**, the same audited argument gives

\[
 \frac{\#\{\delta\in L(X):\mathfrak p\mid(\delta)
                              \text{ for every }\mathfrak p\in T\}}
      {A_{\rm loc}(X)}
 \longrightarrow\prod_{\mathfrak p\in T}\frac1{q_{\mathfrak p}}.
                                                               \tag{2}
\]

This law concerns distinct elements, not ideals or representations. In the audited twisted Euler series, imposing divisibility inserts the finite factor `product_(p in T) psi(p) q_p^(-z)`. Both leading F-characters, `1` and the quadratic character of `E/F`, take value 1 at every such prime. Hence the main-term multiplier is exactly the right side of (2). The mixed archimedean factor and the existing truncations are unchanged.

The previous finite-H proof already gives `A(X)~A_loc(X)`. The proof below only needs (1), (2), and the cyclic Hasse norm theorem: it will also reprove this integral saturation as part of the stronger balanced result. It does not require equidistribution of a delta-dependent obstruction, nor any divisibility law for sets of primes growing with X.

## 2. The compact group, including the exact-norm condition

### 2.1 Finite and infinite norm-one data

Let `I_E,I_F` be the fractional ideal groups and set

\[
 I^1=\ker(N:I_E\longrightarrow I_F),\quad
 T(F)=\{u\in E^*:Nu=1\},\quad
 U_T=T(F)\cap O_E^*.
\]

An ideal in `I^1` has zero valuations at nonsplit primes and opposite valuations at each split pair. Thus

\[
 I_E\longrightarrow I^1,\qquad \mathfrak a\longmapsto
                                  \mathfrak a/c\mathfrak a       \tag{3}
\]

is onto. Its image modulo exact norm-one principal ideals factors through the finite group `Cl(E)`. As in the audit, Hilbert 90 identifies its kernel on `Cl(E)` with the strongly ambiguous classes. In particular

\[
 H=I^1/\{(u):u\in T(F)\}=\operatorname{Cl}(E)/\operatorname{Am}_{\rm st}
                                                               \tag{4}
\]

is finite. Ordinary ambiguous classes would not suffice: they can discard the unit-norm obstruction.

At infinity write

\[
 E_\infty\simeq\mathbb C^r\times(\mathbb C\times\mathbb C)^s,
 \qquad
 T_\infty=\ker(N:E_\infty^*\to F_\infty^*)
          \simeq(S^1)^r\times(\mathbb C^*)^s.
\]

At a complex F-place the norm-one pair is `(t_j,t_j^(-1))`. Define the **weighted** relative logarithm

\[
 \beta:T_\infty\longrightarrow\mathbb R^s,\qquad
 \beta_j(t)=2\log|t_{j,+}|.                                \tag{5}
\]

Its kernel is the compact group `K_infty=(S^1)^(r+s)`. The lattice

\[
 \Lambda=\beta(U_T)\subset\mathbb R^s
\]

has full rank s, and its coordinate covolume is precisely `R_rel` in the two preceding reports. For s=0 use the zero-dimensional lattice and determinant 1.

For completeness, the rank is `(e-1)-(r+s-1)=s`: the norm image of the E-unit group contains the squares of the F-units. The Dirichlet logarithm lattice of exact relative units lies in the s-dimensional anti-invariant subspace and has rank s, hence is a full lattice there. Its log kernel consists of roots of unity. Since F has a real place, a torsion norm in F is necessarily +1, not -1. Thus the units used here really have **exact norm one**, and the weighted determinant is the audited `2 log`, not the unweighted determinant `2^(-s) R_rel`.

### 2.2 A full group and the phase-free quotient used for balancing

Here is an explicit convention for the full, phase-retaining norm-one Arakelov group:

\[
 \mathcal C_T=(I^1\times T_\infty)\big/
       \{((u),u_\infty^{-1}):u\in T(F)\}.                 \tag{6}
\]

The ideal factor is discrete. Its kernel over H is `T_infty/U_T`. The latter is compact: its logarithmic quotient is `R^s/Lambda`, with compact angular fiber. The relation subgroup in (6) is closed, since in each fixed ideal fiber it is either empty or a coset of the closed discrete unit group. Thus `C_T` is a compact Hausdorff abelian group, a finite extension of `T_infty/U_T`.

No angular restrictions are needed for the polydisks. We may quotient out the image of `K_infty`, obtaining the more economical group

\[
 \mathcal A_T=
 (I^1\times\mathbb R^s)\big/
       \{((u),-\beta(u)):u\in T(F)\}.                    \tag{7}
\]

Write its law additively, with representatives `[I,x]` (ideal multiplication in the first coordinate). There is an exact sequence of compact groups

\[
 0\longrightarrow\mathbb R^s/\Lambda
   \xrightarrow{\;y\mapsto[1,y]\;}\mathcal A_T
   \longrightarrow H\longrightarrow0.                 \tag{8}
\]

The identity component is the torus in (8); each of the finitely many components is open. One can also check Hausdorffness directly in (7): in a fixed ideal fiber the logarithms occurring in the relation subgroup form a coset of Lambda.

**Important:** (7) is a joint quotient, not an arbitrarily chosen direct product `H x (R^s/Lambda)`. In general there is no preferred splitting. For example,

\[
 [(u),0]=[1,\beta(u)]\quad(Nu=1),                        \tag{9}
\]

so the archimedean data of a principal switch have not been lost. Discarding phases in (7) does **not** discard exact element norms: every relation still requires `Nu=1` in F, not merely equality of absolute norms or membership in the norm-unit group.

For `a>0` let

\[
 W_a=\{[1,y]:\|y\|_\infty<a\}\subset\mathcal A_T.        \tag{10}
\]

It is an open neighborhood of zero in the whole group, since the identity component has finite index. Membership means that the finite obstruction is zero and that, after an exact norm-one unit adjustment, the logarithmic imbalance has a lift in the indicated cube. Injectivity of this cube in the torus is not required.

## 3. Split-prime classes: the Hecke argument and the pole check

For any fractional E-ideal define

\[
 x_{\mathfrak a}=[\mathfrak a/c\mathfrak a,0]\in\mathcal A_T.
\]

In particular, for a split pair `P,cP` over p,

\[
 x_P=[P/cP,0],\qquad x_{cP}=-x_P.                        \tag{11}
\]

There is no choice of a generator in this definition. We prove that every nonempty open subset of `A_T` has a divergent reciprocal-norm reservoir of such primes.

### 3.1 Every compact-group character gives a genuine Hecke character of E

Let `omega` be a continuous unitary character of `A_T`, and set

\[
 \psi_\omega(\mathfrak a)=\omega(x_{\mathfrak a}).         \tag{12}
\]

For `alpha in E^*`, (9) gives

\[
 \psi_\omega((\alpha))
   =\omega([1,\beta(\alpha/c\alpha)]).                  \tag{13}
\]

On `E_infty^*` define the inverse archimedean factor

\[
 \psi_{\omega,\infty}(x)
   =\omega([1,\beta(x/cx)])^{-1}.                       \tag{14}
\]

The product of (12) and (14) is trivial on every principal diagonal pair `((alpha),alpha_infty)`. Thus these formulas define a continuous unitary Hecke character of E, unramified at every finite prime. This construction applies to infinite-order logarithmic modes, not just finite class-group characters.

The map `omega -> psi_omega` is injective as a map to ideal-valued characters. Indeed, suppose (12) is identically 1. Equation (13) then annihilates all `beta(alpha/calpha)`. By weak approximation, `E^*` is dense in `E_infty^*`; the map `x -> x/cx` is onto `T_infty` (directly at each real or complex F-place), and beta is onto `R^s`. Therefore these logarithms are dense in `R^s`, and continuity gives `omega([1,y])=1` for every y. Surjectivity in (3) also gives `omega([I,0])=1` for every `I in I^1`. Hence omega is trivial.

### 3.2 No hidden radial norm character, anywhere on Re(z)=1

A unitary Hecke L-function can have a pole on `Re(z)=1` for a pure norm power. This possibility must not be suppressed under the slogan “nontrivial character”.

Suppose

\[
 \psi_\omega(\mathfrak a)=(N_E\mathfrak a)^{iv}
 \quad(v\in\mathbb R).
\]

For a positive rational integer m, `c(m)=m`, so (12) gives `psi_omega((m))=1`. On the other hand the proposed norm power gives

\[
 m^{2eiv}=1.
\]

Taking m=2 and m=3 forces `v=0`, since `log 2/log 3` is irrational. Injectivity from the preceding paragraph then forces omega to be trivial. Thus **no nontrivial character of `A_T` induces any pure radial norm power**, not even one with its pole displaced to `1+iv`.

Equivalently, the archimedean log type in (14) is anti-invariant under c and kills the F-directions, whereas a nonzero global radial type does not. The rational-principal-ideal argument also excludes a residual finite character disguised as a trivial ideal character.

### 3.3 The precise prime distribution needed, proved by Euler logarithms

The classical analytic input is the following fixed-character theorem: a unitary Hecke L-function is holomorphic and nonzero on `Re(z)=1` unless its character is a pure norm power, in which case the corresponding simple pole is the only exception there. In particular a nontrivial `psi_omega` from above is holomorphic and nonzero at 1. This is the standard unconditional Hecke nonvanishing theorem, with no uniformity in the field or the infinite type asserted.

For real `z>1`, the Euler logarithm gives

\[
 \sum_P\omega(x_P)(N_EP)^{-z}
    =\log L_E(z,\psi_\omega)+O_E(1)\qquad(z\downarrow1). \tag{15}
\]

The remainder consists of prime powers of exponent at least two and is absolutely bounded near 1; unitarity bounds its absolute value by the corresponding untwisted convergent series. The logarithm on the right is the Euler branch. Nonvanishing permits a bounded local branch near 1, differing by a fixed multiple of `2 pi i` if necessary. Consequently

\[
 \sum_P\omega(x_P)(N_EP)^{-z}
 =\begin{cases}
    \log(1/(z-1))+O_E(1),&\omega=1,\\
    O_{E,\omega}(1),&\omega\ne1.
   \end{cases}                                         \tag{16}
\]

Let `m_A` be normalized Haar measure on `A_T`. Finite character approximation on this compact abelian group now proves, for every continuous f,

\[
 \frac{\sum_P f(x_P)(N_EP)^{-z}}{\log(1/(z-1))}
       \longrightarrow\int_{\mathcal A_T}f\,dm_A
       \quad(z\downarrow1).                            \tag{17}
\]

To justify the approximation, the characters form a self-adjoint algebra separating points, and the normalized positive measures on the left have total mass tending to 1 by the trivial-character case. Only finitely many characters occur for each approximation. There is no infinite interchange requiring uniform Hecke estimates.

Here P runs over all finite E-primes. Inert primes contribute only

\[
 \sum_{\mathfrak p\ {\rm inert}}q_{\mathfrak p}^{-2z},
\]

which stays bounded as z decreases to 1. There are finitely many ramified primes. Thus both are negligible in (17). This is why restricting to primes over **split F-primes** costs no distributional obstruction.

For a nonempty open `U subset A_T`, choose a continuous function `0<=f<=1` supported in U with positive Haar integral. Let

\[
 \mathscr R(U)=\{\mathfrak p\text{ split in }E/F:
          x_P\in U\text{ for at least one }P\mid\mathfrak p\}.
\]

Every underlying p accounts for at most two E-primes, each of norm `q_p`. Hence

\[
 \sum_{\mathfrak p\in\mathscr R(U)}q_{\mathfrak p}^{-z}
 \ \ge\ \frac12\sum_{P\text{ over split primes}}
                         f(x_P)(N_EP)^{-z}
 \ \longrightarrow\ \infty.
\]

It follows that

\[
                 \sum_{\mathfrak p\in\mathscr R(U)}1/q_{\mathfrak p}
                 =\infty.                              \tag{18}
\]

This proves the required prime-reservoir distribution. Harmonic distribution is enough; no natural-density assertion or quantitative prime theorem is needed. The usual fixed-character Hecke prime-ideal theorem, together with the same radial check, would also give ordinary Haar prime equidistribution, but the proof here does not require that stronger formulation.

There is only one leading character in (16), because these are Hecke characters **of E**. This is different from the two leading F-characters in the audited local norm count. Neither a new factor 2 nor a class-number/torus-volume factor should be inserted into (1).

## 4. A robust finite net, and what its switches do to an actual ideal

### 4.1 Finite net lemma

Fix `a>0`. Choose a symmetric open neighborhood V of zero in `A_T` such that

\[
                         V-V\subset W_a.
\]

By compactness choose `g_1,...,g_m` with

\[
                   \mathcal A_T=\bigcup_{j=1}^m(g_j+V),
                   \qquad U_j=g_j+V.                    \tag{19}
\]

This is a **robust** net: for every choice `x_j in U_j` and every target `g in A_T`, some j satisfies

\[
                              g+x_j\in W_a.              \tag{20}
\]

Indeed choose j with `-g in g_j+V`; subtract this point from `x_j`. The difference lies in `V-V`.

This avoids a subset-sum or mixing theorem entirely. It will be enough for delta to have distinct split-prime divisors furnishing one orientation class in each `U_j`. Once a base ideal is chosen, **one** of these switches corrects its entire, possibly delta-dependent obstruction. No distribution of that obstruction needs to be known.

### 4.2 The exact balance obstruction

Let delta be locally admissible. Hasse supplies `z_0 in E^*` with **exact** norm delta. It need not be integral. Choose an archimedean balanced reference `b_delta in E_infty^*` as follows:

* at a real F-place, `b_v=sqrt(tau_v delta)>0`;
* at a complex F-place, `b_(j,+)=sqrt(|tau_j delta|)` and
  `b_(j,-)=tau_j delta/sqrt(|tau_j delta|)`.

Thus `N b_delta=delta_infty`, and both moduli over a complex place equal `sqrt(|tau_j delta|)`. All coordinates are nonzero. Put

\[
 \ell_0=\beta(z_{0,\infty}/b_\delta)\in\mathbb R^s.
\]

For any integral ideal J with `NJ=(delta)`, define

\[
              \gamma_\delta(J)=[J/(z_0),\ell_0]
                              \in\mathcal A_T.           \tag{21}
\]

The ideal quotient lies in `I^1`. If `z_0` is replaced by `z_0 v`, `Nv=1`, the two coordinates change by `((v)^(-1),beta(v))`, which is a relation in (7). Thus (21) is independent of the chosen fractional exact-norm element. The particular reference `b_delta` does not cause a phase problem: its logarithmic moduli are fixed, and phases are not being restricted.

The following equivalence retains **both** integrality and the exact norm:

> `gamma_delta(J) in W_a` if and only if J has a generator `z in O_E` with `Nz=delta` and `||beta(z_infty/b_delta)||_infty<a`.

For the forward implication, membership supplies a vector y with `||y||_infty<a` and `u in T(F)` such that

\[
              J/(z_0)=(u),\qquad \ell_0-y=-\beta(u).
\]

Set `z=z_0 u`. Then `(z)=J` is an integral ideal, so `z in O_E`; `Nz=delta` exactly; and `beta(z/b_delta)=y`. At a complex F-place the two coordinates of `z/b_delta` have product 1. Their logarithmic moduli are therefore `y_j/2` and `-y_j/2`, giving both inequalities in (0), not just a bound on their product. Conversely such a generator supplies exactly these relations. In particular, there is no replacement of delta by a norm-unit multiple. All exact relative-unit adjustments have already been incorporated into the quotient.

### 4.3 Integral one-factor switches

Suppose delta has **distinct** split-prime divisors `p_1,...,p_m` and orientations `P_j|p_j` such that `x_(P_j) in U_j`. Construct an integral ideal `J_0` with norm `(delta)`, putting the entire `p_j`-part on `cP_j` for each selected prime. This is possible:

* at an inert prime with valuation `2k` in `(delta)`, use exponent k in `J_0`;
* at a ramified prime with valuation k, use exponent k;
* at a split prime distribute its valuation arbitrarily, except for the prescribed selected primes.

For a selected prime with valuation `v>=1`, switching one factor replaces

\[
                  (cP_j)^v\quad\hbox{by}\quad P_j(cP_j)^{v-1}.
\]

The resulting ideal

\[
                         J_1=J_0\,P_j/cP_j
\]

is **integral** and still has norm `(delta)`. Moreover

\[
                  \gamma_\delta(J_1)=\gamma_\delta(J_0)+x_{P_j}.
                                                               \tag{22}
\]

Apply the robust net (20) to the actual target `gamma_delta(J_0)`. Some selected j puts (22) in `W_a`. Section 4.2 then produces an integral generator of exact norm delta satisfying (0).

The base ideal depends on the selected primes, but this is harmless: (20) holds for **every** target after all those choices have been made. This is the point that replaces an unsupported assertion about random orientations.

## 5. Density one, using finite reservoirs only

Fix the field and a, and hence the finite collection of opens `U_1,...,U_m`. Each `R_j=mathscr R(U_j)` has divergent reciprocal sum by (18). Choose finite subsets `T_j subset R_j`; overlap is allowed. For delta chosen uniformly from `L(X)`, let

\[
 M_j(\delta)=\#\{\mathfrak p\in T_j:\mathfrak p\mid(\delta)\},
 \qquad \mu_j=\sum_{\mathfrak p\in T_j}1/q_{\mathfrak p}.
\]

For these fixed finite sets, (2), including singleton and pair instances, gives

\[
 \mathbb E_X M_j\to\mu_j,\qquad
 \operatorname{Var}_X(M_j)\to
       \sum_{\mathfrak p\in T_j}\frac1{q_{\mathfrak p}}
                                \left(1-\frac1{q_{\mathfrak p}}\right)
       \le\mu_j.                                       \tag{23}
\]

If `mu_j>m`, Chebyshev therefore gives

\[
 \limsup_{X\to\infty}\Pr_X(M_j<m)
             \le\frac{\mu_j}{(\mu_j-m)^2}.              \tag{24}
\]

On the event `M_j>=m` for every j, choose distinct primes `p_j in T_j` dividing delta greedily. At stage j fewer than m primes have been used, and at least m are available in `T_j`. Choose an orientation of the new prime with `x_(P_j) in U_j`. This handles overlapping reservoirs and inverse orientations without assuming that they can be made disjoint. Section 4.3 now applies.

Let `A_a(X)` count locally admissible elements having the representation in (0). For any fixed finite choices `T_j` with every `mu_j>m`, the preceding sufficient condition gives

\[
 \limsup_{X\to\infty}\frac{A_{\rm loc}(X)-A_a(X)}{A_{\rm loc}(X)}
       \le\sum_{j=1}^m\frac{\mu_j}{(\mu_j-m)^2}.         \tag{25}
\]

The set of elements lacking a balanced representation on the left does not depend on the reservoirs chosen to bound it. Given any `eta>0`, (18) lets us enlarge the **finite** `T_j` until the right side is less than eta. Take the large-X limit with those sets fixed. Since eta is arbitrary, (25) proves

\[
                         A_a(X)\sim A_{\rm loc}(X).       \tag{26}
\]

As `A_a(X)<=A(X)<=A_loc(X)`, this also proves `A(X)~A_loc(X)` and `A_a(X)/A(X)->1`.

The limit order is explicitly:

1. fix `E/F` and the positive logarithmic window a;
2. choose the finite net (19);
3. for a desired exceptional proportion eta, choose finite reservoirs;
4. let X tend to infinity, using (2) only for these fixed primes;
5. then make eta arbitrarily small by enlarging the finite reservoirs.

There is no infinite sieve inside the box limit, no independence of a growing set, and no uniformity in a or the field. Nor are lower cutoffs on `|tau_j delta|` needed: the target in (21) is handled uniformly over the **whole compact group**, however large the unquotiented logarithms of delta are. The analytic treatment of very small absolute ideal norms remains the one already present in the audited box count.

Why does no factor involving the Haar volume of `W_a` survive? We count elements which have **at least one** suitable representation. Almost every delta supplies divisors in every member of a fixed reservoir net, even when these opens have small positive Haar measure. This is not the probability that one arbitrarily chosen representation happens to land in `W_a`.

## 6. Every fixed interior box and the actual planar limit

### 6.1 Fixed interior boxes

Fix `0<epsilon<1` and set

\[
 X_\epsilon(R)=(1-\epsilon)4R^2,\qquad
 a_\epsilon=-\tfrac12\log(1-\epsilon)>0,\qquad
 q_\epsilon=(1-\epsilon)^{1/4}<1.
\]

Apply (26) with the **fixed** window `a_epsilon` and the box parameter `X_epsilon(R)`. For every represented delta supplied by this theorem, (0) yields, at a complex F-place,

\[
 |\sigma_{j,\pm}z|
 < e^{a_\epsilon/2}\sqrt{|\tau_j\delta|}
 \le 2R e^{a_\epsilon/2}\sqrt{1-\epsilon}
 =2R q_\epsilon.                                       \tag{27}
\]

At a real F-place the bound is `2R sqrt(1-epsilon)<=2R q_epsilon`. Consequently **all but `o(A(X_epsilon(R)))` of the integral norm elements in this interior box have an integral representation bounded by `2R q_epsilon` at every E-embedding.** This is stronger than just boundedness by 2R.

### 6.2 Endpoint rounding

Let `rho_E` be a fixed covering radius of the maximal-order Minkowski lattice in the maximum-of-complex-moduli norm. If `max_sigma |sigma z|<=2R-2rho_E`, round `z/2` to a lattice point x. Both x and `x-z` lie in the radius-R polydisk because

\[
 \max_\sigma|\sigma x|,\ \max_\sigma|\sigma(x-z)|
       \le\tfrac12\max_\sigma|\sigma z|+\rho_E\le R.
\]

For the fixed epsilon above, (27) is within this rounding bound once

\[
                             R\ge\rho_E/(1-q_\epsilon).
\]

Thus almost all norm elements in **each fixed** interior box are norms of actual differences of two points of `P_R`. No claim is made at the exact product boundary without slack.

Project into an E-embedding above a real F-place `tau_0`. For a difference z, its squared planar length is `tau_0(Nz)`. The embedding `tau_0:F->R` is injective, so distinct norm elements give distinct squared lengths, and hence distinct nonzero distances. Projection of `O_E` itself is also injective. A projection over a complex F-place would not have this property for the relative norm and is not covered by the result.

Every actual difference has all E-moduli at most 2R and therefore its norm lies in `B_(4R^2)`. Combining the upper bound with the just-proved interior lower bound gives

\[
 D(P_R)\le A(4R^2),\qquad
 D(P_R)\ge A_{a_\epsilon}(X_\epsilon(R))
                         \sim A(X_\epsilon(R)).         \tag{28}
\]

For fixed field and epsilon, (1) gives

\[
 \frac{A(X_\epsilon(R))}{A(4R^2)}\longrightarrow(1-\epsilon)^e.
\]

First let R tend to infinity in (28), and **only then** let epsilon decrease to zero. This proves

\[
                              D(P_R)\sim A(4R^2).         \tag{29}
\]

### 6.3 The coefficient, with no logarithm or covolume change

The full complex-coordinate lattice has covolume `2^(-e) sqrt(D_E)`, so

\[
 n_R=|P_R|\sim\frac{(2\pi)^e}{\sqrt{D_E}}R^{2e}.
\]

Also `log n_R/log((4R^2)^e)->1`. Combining this with (1) and (29) gives

\[
 \boxed{\displaystyle
 \lim_{R\to\infty}\frac{D(P_R)\sqrt{\log n_R}}{n_R}
 =\frac{2^{1-t}}{\sqrt\pi}\left(\frac2\pi\right)^e
     (2\pi)^s\sqrt{\frac{D_E}{D_F}}
     \frac{\sqrt{\kappa_E}}{\kappa_F}
     \sqrt{\mathcal I\mathcal R_{\rm ram}}
 =U(E/F).}                                             \tag{30}
\]

In particular, the logarithm is still `log(X^e)` in the norm count. There is no extra `sqrt(e)` and no extra relative-regulator factor introduced by balancing.

## 7. What this does and does not settle

The audited algebraic identity now applies to the **actual fixed-field limiting constant**:

\[
 U(E/F)^2=\frac{2h_T R_{\rm rel}}{\pi w}
          \left(\frac8\pi\right)^e(2\pi)^s
          \frac{\sqrt{D_F}}{\kappa_F}\,\mathcal J,
 \quad
 \mathcal J=\mathcal I\prod_{\mathfrak p\ {\rm ramified}}
             \frac{q_{\mathfrak p}^{a_{\mathfrak p}/2}}
                  {2(1-q_{\mathfrak p}^{-1})}.           \tag{31}
\]

Here `h_T=|H|`, `w=|mu(E)|`, and `a_p` is the relative discriminant exponent. The earlier logical warning remains important: before (29), lower bounds on this expression were not lower bounds on actual distances. The new proof, not the lower-bound algebra, supplies that missing implication for these particular families.

This saturation proof alone supplies no lower bound for `h_T R_rel`. The subsequent companion proof `relative_unit_packing_bound.md`, independently audited in `mixed_norm_packing_audit.md`, gives `R_rel >= w 2^(-r)(4pi)^(-s)`. With (31), this yields `U^2 >= (2/pi)(4/pi)^r(32/pi^2)^s` for r,s>=1. Thus the specified actual mixed limiting constants are uniformly positive, including proportional mixed rank. Neither result gives a uniform all-sizes theorem or addresses arbitrary planar sets, subsets of the polydisks, other shapes, or nonmaximal orders.

The thresholds can depend very badly on the field, the window, and the reservoirs. This does not invalidate a fixed-field-then-large-size diagonal argument; it does not exclude varying-field sequences that remain in pre-asymptotic ranges. Neither a proof nor a disproof of the full sharp planar distinct-distances conjecture is asserted.

## 8. Sources, dependency boundary, and verification

### Immediate audited inputs

* `/workspace/leanproject/Submission/field_norm_constant_audit.md`, §§1–3, especially lines 169–233: local count, exact H, and the finite-prime law (E); §§5.1–5.2, lines 326–400: mixed box normalization, projection over a real place, and the weighted relative regulator; §5.3: remaining field-uniform limitations.
* `/workspace/leanproject/Submission/field_norm_constant_research.md`, lines 130–161: the exact mixed formula U and its regulator reformulation. The present file supplies the balance assertion that those reports explicitly did not prove.

### Classical inputs and inspected local source passages

* `/corpus/src/1411.7775/1411.7775.tex`, lines 18–35 (Browning–Newton): the cyclic Hasse norm theorem for field elements. We use it only for the fractional `z_0`; integrality is proved separately in §4.
* `/corpus/src/1610.00733/1610.00733.tex`, lines 265–315 (Biswas): strongly ambiguous versus ambiguous classes and the intervening norm-unit obstruction. Finiteness of H and its exact quotient are also proved directly above from (3) and Hilbert 90.
* `/corpus/src/1508.01969/1508.01969.tex`, lines 350–409 (Akhtari–Vaaler): relative units, their rank, the weighted logarithmic determinant, and the regulator ratio. This confirms the normalization in (5), (8), and (31).
* **Analytic input for §3:** classical Hecke analytic continuation and nonvanishing on the line 1 for unitary Hecke characters, with the pure norm-power exception. A source trail already used by the audit is `/corpus/src/1810.06024/1810.06024.tex`, lines 398–406 (Frei–Loughran–Newton), which refers to Iwaniec–Kowalski, *Analytic Number Theory*, Theorems 5.35 and 5.13 for zero-free regions and the prime number theorem. Its displayed Frobenian proposition is finite-order and is **not** itself a theorem covering our infinite log modes. Here the invocation is of the classical unitary Hecke theorem stated in §3.3; the construction of the relevant characters, injectivity, exclusion of radial poles, and deduction of the needed harmonic prime distribution are all supplied explicitly in §§3.1–3.3. No new uniform infinite-type theorem is presumed.
* The remaining asymptotic and class/regulator identities in (1), (2), and (31) are the derived and audited inputs of the two named reports. Their sources include `/corpus/src/1904.12845/1904.12845.tex`, lines 532–604, for the scalar analytic method, and `/corpus/src/2008.06124/2008.06124.tex` for the height/regulator estimates. We do not claim that any one source states the new balanced-support theorem.

### Checks made for this result

1. **Exact-norm signs in the quotient:** `[(u),0]=[1,beta(u)]`; changing `z_0` adds `((v)^(-1),beta(v))`; membership in `W_a` produces `z=z_0 u` with `Nu=1`. These three identities agree and do not merely produce a principal ideal of the right ideal norm.
2. **Actual integrality:** only a factor with positive valuation on `cP` is moved. Its replacement has nonnegative valuations at both primes. The resulting principal ideal is integral, which is exactly what implies `z in O_E`.
3. **Prime distribution obstruction:** the only possible hidden leading character would induce a trivial or radial Hecke ideal character. Weak approximation and the rational integers 2 and 3 rule out both cases for nontrivial omega.
4. **Overlapping reservoirs:** requiring at least m divisors in each finite reservoir makes the greedy selection of m distinct underlying F-primes valid; no pair is asked to carry incompatible initial orientations.
5. **Uniformity in the target, not in the field:** the finite-net inclusion (20) holds for every `gamma_delta(J_0)`. This avoids assuming any statistical independence between that obstruction and delta's prime factors.
6. **Window and endpoint factors:** with `a=-log(1-epsilon)/2`, the worst modulus ratio in (27) is exactly `(1-epsilon)^(1/4)<1`. The endpoint loss is `2 rho_E`, not `rho_E`. No limit with `epsilon=epsilon(R)` is taken.
7. **Coefficient check:** a symbolic simplification of `C_(E/F) * 4^e * sqrt(D_E)/(2*pi)^e` divided by the right side of (30) returned exactly 1. The conversion of weighted imbalance a to the modulus factor `exp(a/2)` was also checked. These computations check normalizations, not the analytic proof.
8. **File boundary:** `Submission/Spec.lean` was not modified. Its SHA-256 before this work was `c2fbaabe5ad8088f856ca97625747c7a01754f3c149dd6a493454e776de290db`; the final verification uses the same hash.

**Bottom line:** the missing mixed-signature support statement is a fixed-field theorem. Compactness, Hecke-distributed split-prime reservoirs, and an integral exact-norm one-factor switch give density-one balance in every fixed interior window. This identifies the actual polydisk distance limit with the audited U, and the companion packing proof bounds these limiting constants uniformly below. Uniform finite-height and arbitrary-planar-set estimates remain unproved.
