# Affine entrance laws: one fixed scale, profile rigidity, and a σ-finite lift

## Outcome and scope

This note independently checks the proposed entrance-law arguments against [AffinePairRigidityResearch.md](AffinePairRigidityResearch.md), especially §2.5, and the original operator conventions in [AffineAnnulusResearch.md](AffineAnnulusResearch.md). The conclusions are **conditional results about abstract laws**, not an unconditional LPF result or a complete criterion for the current.

* **One exact fixed scale suffices for pair rigidity.** IS + ANN + common rational-coordinate marginal \(F\) + \(R_a\nu=\nu\) for one integer \(a\ge2\) + coordinate AP-SI **at \(\nu\)** imply that every distinct rational pair has law \(F\otimes F\). The proof constructs a TV-continuous, log-periodic entrance family through \(\nu\); all its pair laws are product. It does **not** assert that the whole law is fixed by every \(R_k\).
* **Uniformly almost-periodic profiles suffice, profile by profile.** For a given entrance family with AP-SI at scale 1, a centered rational-pair correlation whose log-scale profile is Bohr uniformly almost periodic is identically zero. No almost-periodicity hypothesis is deduced for a general law.
* **The σ-finite globalization is valid for any given monotone entrance family.** Positivity supplies a measure-valued Stieltjes construction, and exact branch restriction identities supply compatible adelic localizations. Under the stated coordinate USI-AP, the lift has \(\operatorname{Law}(F_0\mid s,U)=F\) almost everywhere. This last argument supplies a **conditional marginal**, not conditional pair independence.

No `Spec` or Lean file is edited; none of these proofs is claimed to be Lean-formalized. The general IS + ANN + USI-AP criterion remains open outside the sufficient cases stated here and in the companion note.

## 1. Conventions

On \(\Omega=[0,1]^{\mathbb Q}\), write \(Z_q(z)=z_q\) and

\[
 (A_s z)_q=z_{q+s},\qquad (D_bz)_q=z_{bq},\qquad
 G_{k,r}=A_rD_{1/k},\qquad
 R_k\lambda=\frac1k\sum_{r=0}^{k-1}(G_{k,r})_*\lambda.
\]

Here \(s\in\mathbb Q\), \(b\in\mathbb Q_{>0}\), and \(k\) is a positive integer. In particular, \((G_{k,r}z)_q=z_{(q+r)/k}\). Direct coordinate evaluation gives

\[
 G_{k,r}G_{m,v}=G_{km,r+kv},\qquad
 R_kR_m=R_{km},\qquad
 A_1G_{k,r}=G_{k,r+1},\qquad G_{k,k}=G_{k,0}A_1.
 \tag{1}
\]

IS means \((A_1)_*\nu=\nu\); ANN means \(lR_l\nu-kR_k\nu\ge0\) as **full Borel measures** for integers \(l>k\ge1\). Every \(R_k\) preserves IS. For probabilities, use

\[
 d_{\rm TV}(\alpha,\beta)=\sup_E|\alpha(E)-\beta(E)|
 =\tfrac12|\alpha-\beta|(\Omega).
\]

Thus ANN implies

\[
 d_{\rm TV}(R_l\nu,R_k\nu)\le1-k/l\quad(l>k),
 \qquad
 |\alpha(H)-\beta(H)|\le2\|H\|_\infty d_{\rm TV}(\alpha,\beta).
 \tag{2}
\]

Common marginal \(F\) means \(\mathcal L(Z_q)=F\) at every rational coordinate. Coordinate AP-SI at an IS law \(\lambda\) means, for each bounded \(F\)-centered \(\psi\) and each fixed integer \(d\ge1\),

\[
 \mathbb E_\lambda\left|\frac1L\sum_{j=1}^L\psi(Z_{dj})\right|^2\longrightarrow0.
 \tag{3}
\]

Continuous tests suffice throughout: with common \(F\), centered \(L^2(F)\) approximation and Jensen extend (3) to bounded measurable tests. No SI for arbitrary cylinder products is assumed.

A **given monotone entrance family** means probabilities \((\nu_t)_{t>0}\) satisfying

\[
 (A_1)_*\nu_t=\nu_t,\qquad R_k\nu_t=\nu_{kt},\qquad
 M_t:=t\nu_t\text{ is increasing in }t.
 \tag{4}
\]

Increasing always refers to the order on full measures. Since \(M_t(\Omega)=t\), (4) automatically gives

\[
 |M_t-M_s|(\Omega)=t-s,\qquad
 d_{\rm TV}(\nu_t,\nu_s)\le1-s/t\quad(0<s<t).
 \tag{5}
\]

In particular, these families are TV-continuous, not just weakly continuous.

## 2. Constructing the entrance family from one fixed scale

Assume IS + ANN and \(R_a\nu=\nu\), where \(a\ge2\) is an integer. For fixed \(t>0\) and sufficiently large \(n\), put

\[
 m_n(t)=\lfloor ta^n\rfloor,\qquad \lambda_n(t)=R_{m_n(t)}\nu.
\]

Because \(R_{am}\nu=R_m\nu\) and
\(0\le m_{n+1}(t)-am_n(t)\le a-1\), (2) gives, whenever \(ta^n\ge2\),

\[
 d_{\rm TV}(\lambda_{n+1}(t),\lambda_n(t))
 \le\frac{a-1}{a\lfloor ta^n\rfloor}
 \le\frac{2(a-1)}{a\,ta^n}.
 \tag{6}
\]

The errors are summable. Completeness of finite measures in variation therefore gives probabilities

\[
 \boxed{\nu_t=\operatorname{TV}\!\lim_{n\to\infty}R_{\lfloor ta^n\rfloor}\nu,}
 \qquad d_{\rm TV}(\nu_t,\lambda_n(t))\le\frac2{ta^n}.
 \tag{7}
\]

The convergence is uniform for \(t\) in compact subsets of \((0,\infty)\). IS and common \(F\), when present, pass to the limit. The following identities hold at **every real \(t>0\)**:

\[
 \boxed{\nu_1=\nu,\qquad \nu_{at}=\nu_t,\qquad R_k\nu_t=\nu_{kt}.}
 \tag{8}
\]

The first two follow from \(R_{a^n}\nu=\nu\) and reindexing \(n\). For the third, compare \(R_{k\lfloor ta^n\rfloor}\nu\) with \(R_{\lfloor kta^n\rfloor}\nu\); their indices differ by at most \(k-1\), so (2) makes the error tend to zero. Pushforward and averaging are TV contractions.

For \(s<t\), apply ANN to \(m_n(s),m_n(t)\), divide the positive inequality by \(a^n\), and pass in variation to the limit. This proves \(M_s\le M_t\), hence (4)–(5). In particular, continuity is obtained from (5), **not** by declaring the step functions in (7) continuous.

Only AP-SI at the original law is required below. In fact it transfers uniformly to this entire entrance family: choose \(j\in\mathbb Z\) with \(a^{j-1}<t\le a^j\). Periodicity gives \(\nu_{a^j}=\nu\), and positivity gives

\[
 \nu_t\le(a^j/t)\nu\le a\nu.
 \tag{9}
\]

Thus the mean-square errors in (3) at any \(\nu_t\), including \(\nu_k=R_k\nu\), are at most \(a\) times those at \(\nu\). No second independent fixed scale is needed for the pair theorem.

## 3. The canonical stationary profinite joining

For **any** family (4), there is a unique probability \(\rho_t\) on \(\Omega\times\widehat{\mathbb Z}\) specified by

\[
 \boxed{\rho_t(E,\ U\equiv r\pmod k)
       =\frac1k(G_{k,r})_*\nu_{t/k}(E)}\qquad(0\le r<k).
 \tag{10}
\]

Indeed, refinement from \(k\) to \(km\) gives

\[
 \sum_{v=0}^{m-1}\frac1{km}(G_{km,r+kv})_*\nu_{t/(km)}
 =\frac1k(G_{k,r})_*R_m\nu_{t/(km)}
 =\frac1k(G_{k,r})_*\nu_{t/k}.
 \tag{11}
\]

The finite-level field marginal is \(R_k\nu_{t/k}=\nu_t\), and the residue marginal is uniform. The countable compact inverse limit, for example along factorial moduli, gives (10). The full field marginal is \(\nu_t\), and \(U\) is Haar; **independence of \(U\) and the field is not asserted**.

By (1) and IS, \(\rho_t\) is invariant under

\[
 S(z,u)=(A_1z,u+1).
 \tag{12}
\]

The sign is \(+1\), including the wraparound residue. This is exactly the joint-stationarity convention used by the entropy source.

## 4. Integer correlations, twisted primes, and Fourier extraction

Fix bounded \(\phi\), bounded \(F\)-centered \(\psi\), and \(h\in\mathbb Z\setminus\{0\}\). Write

\[
 C_t(h)=\mathbb E_{\nu_t}\phi(Z_0)\psi(Z_h),\qquad
 W(P)=\sum_{p\le P}\frac1p,\qquad
 \mathcal L_P b_p=\frac1{W(P)}\sum_{p\le P}\frac{b_p}{p}.
\]

The residue-zero identity at \(\rho_1\) is

\[
 \mathbb E_{\rho_1}p1_{\{p\mid U\}}\phi(Z_0)\psi(Z_{ph})=C_{1/p}(h).
 \tag{13}
\]

This is conditioning on the **event** \(p\mid U\), not conditioning on the entire variable \(U\). The unweighted expectation is \(C_1(ph)\).

### 4.1 The precise entropy input

The inspected source is Tao–Teräväinen, *The structure of correlations of multiplicative functions at almost all scales, with applications to the Chowla and Elliott conjectures*, arXiv:1809.02518, local file `/corpus/src/1809.02518/1809.02518.tex`:

* lines **378–380** specify joint stationarity;
* Proposition `eda`, lines **410–419**, is explicitly a general stationary-process theorem, with no multiplicativity hypothesis;
* lines **430–440** give the dyadic-to-prime-harmonic summation argument.

For jointly stationary random 1-bounded functions \(\mathbf g_i:\mathbb Z\to\mathbb D\) and a profinite integer \(U\), `eda` bounds the dyadic-prime mean of

\[
 \left|\mathbb E\prod_i\mathbf g_i(ph_i)(p1_{\{p\mid U\}}-1)\right|
\]

by \(\epsilon\), outside scales \(m\) with \(\sum_m1/m\ll_{h_i}\epsilon^{-4}\log(1/\epsilon)\). Its parameter called \(a\) is set to 1 here. Zero and negative integer shifts are permitted. The harmonic mass of the \(m\)-th dyadic prime block is \(O(1/m)\); bad blocks have bounded total harmonic mass for fixed \(\epsilon\), while \(W(P)\sim\log\log P\). Haar \(U\) bounds each absolute expectation by 2. Therefore the corresponding \(\mathcal L_P\)-average tends to zero.

Apply this to normalized \(\phi(Z_n),\psi(Z_n)\), with shifts \((0,h)\), in (12). We obtain

\[
 \boxed{\mathcal L_P|C_{1/p}(h)-C_1(ph)|\longrightarrow0.}
 \tag{14}
\]

We use the **general `eda` proposition and its summation**, not the arithmetic proposition `dollop` applied to nonmultiplicative tests.

### 4.2 AP-SI and fixed Mellin twists

Let \(Tg=g\circ A_1\) on \(L^2(\nu_1)\) and \(g=\psi(Z_0)\). AP-SI at \(\nu_1\) and the spectral theorem give

\[
 \sigma_g(\{\theta:d\theta\in\mathbb Z\})=0\quad(d\ge1),
 \qquad \sigma_g(\mathbb Q/\mathbb Z)=0.
 \tag{15}
\]

Unit-step SI alone would remove only the atom at zero. The spectral measure of \(\psi(Z_0)\) on \((\rho_1,S)\) is the same, since all its time correlations use the field marginal \(\nu_1\).

Put \(e(x)=e^{2\pi i x}\). Vinogradov's theorem gives \(\sum_{p\le x}e(p\alpha)=o(x/\log x)\) for irrational \(\alpha\). Partial summation against \(x^{-1+i\xi}\), whose derivative is \((-1+i\xi)x^{-2+i\xi}\), gives, for every **fixed** \(\xi\in\mathbb R\),

\[
 m_{P,\xi}(\alpha):=\mathcal L_P[p^{i\xi}e(p\alpha)]\longrightarrow0
 \quad(\alpha\notin\mathbb Q),\qquad |m_{P,\xi}|\le1.
 \tag{16}
\]

The integral of the error is \(o(\log\log P)\); no uniformity in \(\xi\) or \(\alpha\) is needed. Spectral dominated convergence using (15) now gives

\[
 \left\|\frac1{W(P)}\sum_{p\le P}p^{-1+i\xi}T^{ph}g\right\|_2\to0,
 \qquad \mathcal L_P[p^{i\xi}C_1(ph)]\to0.
 \tag{17}
\]

The same assertion holds on \(\rho_1\), and with primes restricted to a fixed residue class. In fact,

\[
 \frac1{W(P)}\sum_{\substack{p\le P\\p\equiv r\ (M)}}
 p^{-1+i\xi}e(ph\theta)
 =\frac1M\sum_{j=0}^{M-1}e(-jr/M)\,m_{P,\xi}(h\theta+j/M)\to0
 \tag{18}
\]

for irrational \(\theta\) and nonzero integer \(h\). Thus no SI for residue-weighted products is needed. Combining (14)–(17),

\[
 \boxed{\mathcal L_P[p^{i\xi}C_{1/p}(h)]\to0\quad(\xi\in\mathbb R\text{ fixed}).}
 \tag{19}
\]

### 4.3 Prime-harmonic log equidistribution and the integer theorem

A separate PNT calculation gives

\[
 \mathcal L_P[p^{i\gamma}]\longrightarrow
 \begin{cases}1,&\gamma=0,\\0,&\gamma\ne0.\end{cases}
 \tag{20}
\]

For \(\gamma\ne0\), partial summation with \(\pi(x)=\operatorname{Li}(x)+o(x/\log x)\) reduces the numerator to
\(\int_{\log2}^{\log P}e^{i\gamma v}\,dv/v+o(\log\log P)\). The integral is bounded. This proves harmonic equidistribution of \(\log p\) modulo any fixed positive period. **Harmonic weighting matters:** the ordinary prime average of \(p^{i\gamma}\) is asymptotic to \(P^{i\gamma}/(1+i\gamma)\), not to zero.

For the family of §2, \(f(u)=C_{e^u}(h)\) is continuous and periodic of period \(\ell=\log a\), by (5) and (8). For \(\xi_m=2\pi m/\ell\), (20) and uniform trigonometric approximation give

\[
 \lim_{P\to\infty}\mathcal L_P[p^{i\xi_m}f(-\log p)]
 =\frac1\ell\int_0^\ell f(u)e^{-i\xi_m u}\,du=\widehat f(m).
 \tag{21}
\]

Every coefficient is zero by (19). Fourier uniqueness for continuous periodic functions, for example Fejér approximation, gives \(f\equiv0\). Thus every distinct integer pair is independent at every \(\nu_t\), using IS to move its origin. The next argument is required for noninteger origins; a single affine branch need not be stationary.

## 5. Rational pairs and uniformly almost-periodic profiles

### 5.1 Finite-denominator masks, with all scale and sign factors

Fix \(M\ge1\) and distinct integers \(b,c\), of either sign, and put

\[
 D_t=\mathbb E_{\nu_t}\phi(Z_{b/M})\psi(Z_{c/M}),\qquad
 B_p=M\mathbb E_{\rho_1}1_{\{M\mid U\}}\phi(Z_{pb})\psi(Z_{pc}).
\]

For \(p\nmid M\), (10) at modulus \(Mp\) gives exactly

\[
 \boxed{D_{1/(Mp)}
 =M\mathbb E_{\rho_1}1_{\{M\mid U\}}p1_{\{p\mid U\}}
                  \phi(Z_{pb})\psi(Z_{pc}).}
 \tag{22}
\]

For each residue \(r\pmod M\), the random functions

\[
 \mathbf g_{1,r}(n)=1_{\{U+n\equiv rb\pmod M\}}\phi(Z_n),\qquad
 \mathbf g_2(n)=\psi(Z_n)
 \tag{23}
\]

are jointly stationary with \(U\) under (12). After norm normalization, apply `eda` with shifts \((b,c)\). For primes \(p\equiv r\pmod M\), the mask at \(n=pb\) equals \(1_{\{M\mid U\}}\). Restricting a nonnegative absolute-error average to one prime class only decreases it; sum over the finitely many classes. Consequently

\[
 \mathcal L_P\big[1_{p\nmid M}|D_{1/(Mp)}-B_p|\big]\to0.
 \tag{24}
\]

Deleting the finitely many primes dividing \(M\) does not affect any limit here; the denominator remains \(W(P)\).

Stationarity, composing the integrand with \(S^{-pb}\), yields

\[
 B_p=\mathbb E_{\rho_1}H_r\,\psi(Z_{p(c-b)}),\qquad
 H_r=M1_{\{U\equiv rb\pmod M\}}\phi(Z_0)
 \quad(p\equiv r\pmod M).
 \tag{25}
\]

In particular the residue is **\(+rb\)**, not \(-rb\). Apply (18) to \(g=\psi(Z_0)\), pair with the fixed bounded \(H_r\), and sum over \(r\). Equations (24)–(25) give

\[
 \boxed{\mathcal L_P[p^{i\xi}D_{1/(Mp)}]\to0
       \quad\text{for every fixed real }\xi.}
 \tag{26}
\]

For the periodic entrance family, let \(f(u)=D_{e^u}\). At \(\xi_m=2\pi m/\ell\), (20) gives

\[
 \lim_{P\to\infty}\mathcal L_P[p^{i\xi_m}f(-\log M-\log p)]
       =\boxed{M^{-i\xi_m}\widehat f(m)}.
 \tag{27}
\]

The nonzero phase \(M^{-i\xi_m}\) is essential to the identity but does not affect vanishing. Hence every coefficient is zero and \(D_t=0\) for all \(t>0\). Centering \(\psi\) and using common \(F\) proves

\[
 \boxed{\mathcal L_{\nu_t}(Z_q,Z_{q'})=F\otimes F
       \quad(t>0,\ q,q'\in\mathbb Q,\ q\ne q').}
 \tag{28}
\]

This proves the one-fixed-scale theorem, in particular at \(\nu_1=\nu\). It also gives \(J(\nu)=\mathbb E\operatorname{sgn}(Z_1-Z_0)=0\); for atomless \(F\), both strict ordering probabilities are \(1/2\). There was no rational-translation-invariance assumption and no application of an integer theorem to a nonstationary branch.

### 5.2 The exact Bohr generalization

Now take any **given** entrance family (4) with common \(F\) and AP-SI at \(\nu_1\), without a fixed scale. The proof of (26) still applies. Suppose the particular profile

\[
 f(u)=\mathbb E_{\nu_{e^u}}\phi(Z_{b/M})\psi(Z_{c/M})
\]

is **Bohr uniformly almost periodic on all of \(\mathbb R\)**: it is a uniform limit of finite sums \(\sum_j c_je^{i\lambda_j u}\) with real frequencies. Define its Bohr coefficient

\[
 c_f(\xi)=\mathcal M_{\rm B}(f(u)e^{-i\xi u}),\qquad
 \mathcal M_{\rm B}(H)=\lim_{T\to\infty}\frac1{2T}\int_{-T}^T H(u)\,du.
\]

For a trigonometric polynomial, (20) proves

\[
 \lim_{P\to\infty}\mathcal L_P[p^{i\xi}f(-\log M-\log p)]
       =M^{-i\xi}c_f(\xi).
 \tag{29}
\]

Both the sampling averages and Bohr coefficient functionals have norm at most one in the uniform norm, so uniform approximation proves (29) for \(f\). Equation (26) annihilates every coefficient. Bohr Fourier uniqueness then gives \(f\equiv0\). One justification of uniqueness is to approximate \(f\) uniformly by trigonometric polynomials: zero coefficients imply \(\mathcal M_{\rm B}|f|^2=0\), whereas a nonzero uniformly almost-periodic function has positive mean square by uniform continuity and relatively dense almost periods.

This is a **profilewise theorem**. If all centered rational-pair profiles have this property, all the pair laws in (28) follow. Mere continuity or a weaker mean-square notion of almost periodicity is not substituted for uniform almost periodicity. Neither the existence of an entrance through an arbitrary IS + ANN law nor almost periodicity of its profiles is proved here.

## 6. A rigorous σ-finite globalization of any given entrance family

This section needs only (4), not a fixed scale, common marginal, or SI.

### 6.1 Increasing joined measures and the Stieltjes extension

Set \(Y=\Omega\times\widehat{\mathbb Z}\) and \(K_t=t\rho_t\), with \(K_0=0\). Equation (10) gives

\[
 K_t(E,\ U\equiv r\pmod k)=(G_{k,r})_*M_{t/k}(E).
 \tag{30}
\]

For \(s<t\), the finite-level differences are positive and compatible. Their inverse-limit measure is \(K_t-K_s\), by uniqueness on cylinders. Thus \(K_t\) is increasing on the **whole** product Borel σ-algebra, with

\[
 |K_t-K_s|(Y)=t-s,\qquad d_{\rm TV}(\rho_t,\rho_s)\le1-s/t.
 \tag{31}
\]

There is a unique Borel measure \(\mu_0\) on \((0,\infty)\times Y\) such that

\[
 \boxed{\mu_0((0,t]\times C)=K_t(C)=t\rho_t(C).}
 \tag{32}
\]

Here is a measure-extension justification. On each \([0,T]\times Y\), which is compact metrizable, define a positive functional on continuous functions by Riemann–Stieltjes sums

\[
 \sum_i\int_Y H(s_i,y)\,d(K_{t_i}-K_{t_{i-1}})(y),
 \qquad s_i\in[t_{i-1},t_i].
\]

Uniform continuity of \(H\) and total increment mass \(T\) make these sums converge as the mesh tends to zero, independently of tags. Riesz representation gives a finite measure of mass \(T\). Its time marginal is Lebesgue measure, so endpoints have no atoms; approximation of interval indicators proves (32), first for continuous tests in \(y\), then for Borel sets. Uniqueness on cumulative rectangles makes these measures agree as \(T\) increases. This constructs the asserted σ-finite measure without an unproved disintegration formula.

Since each \(\rho_t\) has Haar residue marginal, the \((s,U)\)-marginal of \(\mu_0\) is

\[
 ds\,dU\quad\text{on }(0,\infty)\times\widehat{\mathbb Z},
 \qquad dU(\widehat{\mathbb Z})=1.
 \tag{33}
\]

**Important distinction:** (32) is a cumulative identity. In general \(\mu_0\ne ds\,\rho_s\). A time-disintegration kernel \(\kappa_s\) satisfies \(K_t(C)=\int_0^t\kappa_s(C)\,ds\), but its field marginal need not be the entrance law \(\nu_s\). No variation-norm differentiability is asserted.

### 6.2 Exact branch restrictions and the action conventions

Let \(\mathbb A_f=\bigcup_{n\ge1}n^{-1}\widehat{\mathbb Z}\) be the finite adeles, with additive Haar \(du\) normalized by \(du(\widehat{\mathbb Z})=1\). On
\(X=(0,\infty)\times\Omega\times\mathbb A_f\), define the Borel bijections

\[
 \mathsf A_q(s,z,u)=(s,A_qz,u+q),\qquad
 \mathsf D_a(s,z,u)=(as,D_{1/a}z,au)
 \quad(q\in\mathbb Q,\ a\in\mathbb Q_{>0}).
 \tag{34}
\]

Their algebra is

\[
 \mathsf D_a\mathsf A_q=\mathsf A_{aq}\mathsf D_a,
 \qquad \mathsf D_a\mathsf D_b=\mathsf D_{ab}.
 \tag{35}
\]

Put \(X_1=(0,\infty)\times\Omega\times\widehat{\mathbb Z}\). Equations (12) and (32) make \(\mu_0\) invariant under integer \(\mathsf A_m\). For each integer \(k\ge1\) and \(0\le r<k\), one has the exact identity of locally finite measures

\[
 \boxed{(\mathsf A_r\mathsf D_k)_*\mu_0
       =\mu_0\restriction\{U\equiv r\pmod k\}.}
 \tag{36}
\]

To check the time, branch, and normalization simultaneously, test a target cylinder
\((0,t]\times E\times\{U\equiv r+kv\pmod{km}\}\). Its preimage has time interval \((0,t/k]\), field test \(G_{k,r}^{-1}E\), and residue \(v\pmod m\). Its mass is

\[
 \frac{t}{km}(G_{k,r}G_{m,v})_*\nu_{t/(km)}(E)
 =\frac{t}{km}(G_{km,r+kv})_*\nu_{t/(km)}(E),
\]

exactly the right side of (36). Both measures are supported on the indicated residue; refinement and uniqueness on cylinders prove the identity on all Borel sets. There is **no extra factor \(k\)** in (36).

### 6.3 Compatible localization and global invariance

For positive integers \(n\), define

\[
 X_n=(0,\infty)\times\Omega\times n^{-1}\widehat{\mathbb Z},
 \qquad \mu_n=(\mathsf D_{1/n})_*\mu_0.
 \tag{37}
\]

If \(m=kn\), the inverse image of \(X_n\) under \(\mathsf D_{1/m}:X_1\to X_m\) is \(\{U\in k\widehat{\mathbb Z}\}\). Equation (36) at residue zero therefore gives

\[
 \mu_m\restriction X_n
 =(\mathsf D_{1/m})_*(\mu_0\restriction\{U\in k\widehat{\mathbb Z}\})
 =(\mathsf D_{1/m})_*(\mathsf D_k)_*\mu_0=\mu_n.
 \tag{38}
\]

Glue along the cofinal chain \(X_{n!}\). This gives a unique Borel measure \(\mu\) on \(X\) with \(\mu\restriction X_n=\mu_n\) for every \(n\). Explicitly it is the increasing limit of these restricted measures, extended by zero off their domains. The sets

\[
 Q_{T,n}=(0,T]\times\Omega\times n^{-1}\widehat{\mathbb Z}
 \quad\text{have mass }\mu(Q_{T,n})=nT,
 \tag{39}
\]

so integer \(T\) and factorial \(n\) give a finite-measure exhaustion.

The base measure is exactly \(ds\,du\). Indeed, under \(\mathsf D_{1/n}\), the time pushforward contributes \(n\), and the normalized Haar probability on \(n^{-1}\widehat{\mathbb Z}\), a subgroup of Haar volume \(n\), contributes \(1/n\). Equivalently, the rational product formula gives \(|a|_f=1/a\), so simultaneous scaling of \(s\) and \(u\) preserves \(ds\,du\).

Moreover,

\[
 (\mathsf D_{1/k})_*\mu_n=\mu_{kn},\qquad
 (\mathsf A_1)_*\mu_n=\mu_n
 \tag{40}
\]

(the latter uses \(\mathsf A_1\mathsf D_{1/n}=\mathsf D_{1/n}\mathsf A_n\)). Cofinality makes \(\mu\) invariant under \(\mathsf D_{1/k}\), hence also its inverse, and under \(\mathsf A_1\). The group relations then prove invariance under **all positive rational dilations and all rational translations**. Finally

\[
 F_0(s,z,u)=z_0,\qquad F_0\circ\mathsf D_a=F_0,
 \qquad Z_q=F_0\circ\mathsf A_q.
 \tag{41}
\]

No extension to a real affine action or strong continuity as rational parameters approach real limits has been assumed. In particular, no Mautner argument is available merely from these identities.

## 7. What coordinate USI gives on the lift

Assume now that the given entrance family has the coordinate estimates

\[
 \sup_{n\ge1}\mathbb E_{\nu_n}
 \left|\frac1L\sum_{j=1}^L\psi(Z_{dj})\right|^2
 \le e_{L,d}(\psi)^2\longrightarrow0
 \tag{42}
\]

for each bounded \(F\)-centered \(\psi\) and each fixed positive integer \(d\). Since \(\nu_n=R_n\nu_1\), this is the orbit USI-AP assumption. For any fixed real \(t>0\), choose an integer \(N\ge t\). Monotonicity gives

\[
 \nu_t\le(N/t)\nu_N,
 \tag{43}
\]

so (42) implies AP-SI at every fixed \(t\). There is no need to assert uniformity as \(t\downarrow0\). In fact separate AP-SI at each integer scale is enough for this transfer and for the conditional-marginal conclusion.

Each finite section \(Q_{T,n}\) is invariant under integer translations. Using (32) and (37), its normalized coordinate mean square is exactly

\[
 \frac1{nT}\int_{Q_{T,n}}
 \left|\frac1L\sum_{j=1}^L\psi(F_0\circ\mathsf A_{dj})\right|^2d\mu
 =\mathbb E_{\nu_{nT}}
 \left|\frac1L\sum_{j=1}^L\psi(Z_{ndj})\right|^2\longrightarrow0.
 \tag{44}
\]

The time is \(nT\), and the AP step is \(nd\). These factors cannot be dropped when working on a localized section.

Let \(H(s,u)=h(s)\chi(u)\), where \(h\) is bounded and \(\chi\) is a continuous character of the compact profinite group \(n^{-1}\widehat{\mathbb Z}\). Such a character has finite order, so \(H\) is invariant under \(\mathsf A_d\) for some positive integer \(d\). Stationarity and (44), or the mean ergodic theorem, imply

\[
 \int_{Q_{T,n}}H(s,u)\,\psi(F_0)\,d\mu=0.
 \tag{45}
\]

These tensor products span a dense subspace of the base \(L^2\) space. Thus the conditional expectation of \(\psi(F_0)\) given \((s,U)\) is zero on each finite section. Disintegration is legitimate on these standard Borel finite-measure spaces; the kernels agree on overlaps. A countable determining family of continuous tests on \([0,1]\), followed by the countable exhaustion (39), proves

\[
 \boxed{\operatorname{Law}_{\mu}(F_0\mid s,U)=F
       \quad\text{for }ds\,du\text{-almost every }(s,u).}
 \tag{46}
\]

This is a probability-kernel assertion over the σ-finite base, not a normalized global probability expectation. It determines no conditional two-coordinate law from USI alone: no estimate for a centered pair observable has been supplied. The globalization and (46) do **not** close the general pair-rigidity or current problem.

## 8. Audit ledger and remaining question

| Claim | Audited conclusion / indispensable qualification |
|---|---|
| \(\operatorname{TV}\lim_nR_{\lfloor ta^n\rfloor}\nu\) under one fixed scale | Exists with summable error (6)–(7); all real times obey (8), positivity, and TV continuity |
| One fixed \(R_a\), common \(F\), AP-SI only at \(\nu\) | All distinct rational pairs independent; no assertion of whole-law all-scale fixedness |
| Twisted prime averages | Every fixed real twist is allowed; use partial summation before spectral dominated convergence |
| Rational denominators | Entrance time \(1/(Mp)\), stationary residue \(+rb\), and Fourier phase \(M^{-i\xi}\) are all required |
| Bohr extension | Valid for uniformly almost-periodic profiles on the whole log-scale line; not asserted for arbitrary profiles |
| σ-finite extension | Valid for any **given** family (4); (31)–(38) supply positivity, measure extension, and gluing |
| Conditional field marginal | (46) holds under (42); this argument does not establish conditional pair independence |
| Continuity | TV continuity of the laws is proved; real-topology continuity of the rational field action is not assumed |
| General IS + ANN + USI-AP \(\Rightarrow J=0\) | Still unresolved; no LPF proof or complete criterion is claimed |

The atomic/countable-component reduction in [AffinePairRigidityResearch.md](AffinePairRigidityResearch.md), §3, remains applicable: its finite-fibre argument, collision exclusion, discrete-weight stabilization, and positive-submeasure SI transfer were also checked. Any hypothetical nonzero-current law for the full package can be reduced to one with a **purely nonatomic integer-ergodic component distribution**. By the theorem here, that reduced law cannot have any exact fixed scale \(R_a\), \(a\ge2\). If it has a given entrance family, any nonzero centered pair profile lies outside the Bohr uniformly almost-periodic case. These are restrictions on the remaining problem, not its solution.

### Verification and file boundaries

The probability, spectral, Fourier, and measure-extension arguments above were checked mathematically. An exact `Fraction` regression at `/tmp/affine-entrance-audit.py`, with output `/tmp/affine-entrance-audit.log`, passed **375,240 finite checks** of floor-index errors, branch/cylinder composition, negative-coordinate masks, stationary signs, and localization normalizations. Finite checks do not prove entropy decrement, Vinogradov/PNT, an infinite-dimensional extension, or Bohr uniqueness; the corresponding proofs or precisely identified standard inputs are given above. A SHA-256 manifest comparison verified that all 67 pre-existing files under `Submission` were unchanged and this note was the only addition; equation tags, math delimiters, and relative note links were also checked.

The checked entropy source is `/corpus/src/1809.02518/1809.02518.tex:378–380,410–440`. Other external inputs are classical Vinogradov equidistribution, PNT, the unitary spectral theorem, Fourier/Bohr uniqueness, compact inverse limits, and Riesz representation/disintegration on standard Borel spaces. No multiplicativity is imported into the stationary process theorem.

The only intended project output is `Submission/AffineEntranceResearch.md`; existing research notes are read-only inputs. `Submission/Spec.lean` retains SHA-256

`d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.
