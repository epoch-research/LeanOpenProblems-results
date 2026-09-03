# Affine pair rigidity: independent audits and the countable-component extension

## Outcome and scope

This note independently audits the proposed progress using exactly the conventions of [AffineAnnulusResearch.md](AffineAnnulusResearch.md) and [PadicAnnulusCounterexampleResearch.md](PadicAnnulusCounterexampleResearch.md). Agreement among previous researchers is not used as a proof. The results below are **conditional theorems about the stated abstract laws**, not unconditional statements about largest-prime-factor prefix laws. No `Spec` or Lean file is edited, and none of these arguments is claimed to be Lean-formalized.

The principal audited conclusions are:

1. **Fixed-point pair rigidity — proved.** IS, \(R_k\nu=\nu\) for every positive integer \(k\), common marginal \(F\), and coordinate AP-SI imply independence of every distinct integer pair. In fact **every distinct rational pair is independent**. The proof uses an exact profinite joining, the genuinely general stationary entropy-decrement proposition in arXiv:1809.02518, and the prime spectral theorem. The rational extension below is a finite-residue argument in that joining; it does not incorrectly apply the integer theorem to a nonstationary branch.
2. **Countable and atomic components — new extension, proved.** Under IS + ANN alone, a law with at most countably many integer-ergodic components is \(R_k\)-fixed for every \(k\). More generally, the **atomic part of the integer-ergodic decomposition of any law** satisfying IS + ANN is an \(R_k\)-fixed subprobability measure. Under USI-AP, its normalized law has all distinct rational pairs independent with marginal \(F\). The collision-energy and discrete-weight arguments in §3 resolve the proposed countable-component gap.
3. **Additional hypotheses that suffice — proved.** Two multiplicatively independent exact fixed scales imply all scales are fixed. A rational-translation stabilizer containing all denominators coprime to one fixed \(M\) implies integer-pair independence under ANN + USI-AP.
4. **Logarithmic orbit averages — proved, but a different law.** Every cluster point of the stated long logarithmic \(R\)-orbit averages is \(R_k\)-fixed. Uniform USI-AP passes to these limits, so their pair laws are product. This does **not** identify the original scale-1 law with a limit.
5. **Backward branch domination — false in general.** The quadratic Haar-character mixture in §6 satisfies IS + ANN + exact all-coordinate USI, but \((G_{k,0})_*\eta\not\ll\eta\) for \(k>1\). It has independent pairs and \(J=0\), including after Dickman quantile transport. It is not a counterexample to pair rigidity or to the arithmetic target.

Thus the general implication IS + ANN + USI-AP \(\Rightarrow J(\nu)=0\) is **not resolved here for the nonatomic component part**. The new component theorem genuinely removes the countable/atomic obstruction; it does not silently dispose of a nonatomic ergodic decomposition.

## 1. Conventions and hypotheses

Work on the compact metrizable space \(\Omega=[0,1]^{\mathbb Q}\), with coordinate maps \(Z_q(z)=z_q\). For \(s\in\mathbb Q\), \(a\in\mathbb Q_{>0}\), and integers \(k\ge1\), use

\[
 (A_s z)_q=z_{q+s},\qquad (D_a z)_q=z_{aq},\qquad
 G_{k,r}=A_rD_{1/k},\qquad
 R_k\lambda=\frac1k\sum_{r=0}^{k-1}(G_{k,r})_*\lambda.
\]

In particular, \((G_{k,r}z)_q=z_{(q+r)/k}\). Operators on measures are extended linearly to finite measures. Write

\[
 P_k\lambda=\frac1k\sum_{r=0}^{k-1}(A_{r/k})_*\lambda.
\]

The identities needed in this note are

\[
 \begin{aligned}
 G_{k,r}G_{m,t}&=G_{km,r+kt},& R_kR_m&=R_{km}=R_mR_k,\\
 D_kG_{k,r}&=A_{r/k},& (D_k)_*R_k&=P_k,\\
 G_{k,r}A_s&=A_{ks}G_{k,r},& R_k(A_s)_*&=(A_{ks})_*R_k.
 \end{aligned}
\]

The last covariance is useful for component fibres and must not be replaced by commutation with rational translations.

* **IS:** \((A_1)_*\nu=\nu\).
* **ANN:** \(lR_l\nu-kR_k\nu\ge0\) as full Borel measures whenever \(l>k\ge1\).
* **Coordinate AP-SI at a law:** for every bounded \(F\)-centered \(\psi\) and every fixed positive integer \(d\),
  \[
   \mathbb E_\nu\left|\frac1L\sum_{j=1}^L\psi(Z_{dj})\right|^2\longrightarrow0.
  \]
* **USI-AP:** the stronger orbit-uniform assertion
  \[
   \sup_{k\ge1}\mathbb E_{R_k\nu}
   \left|\frac1L\sum_{j=1}^L\psi(Z_{dj})\right|^2
   \le e_{L,d}(\psi)^2,\qquad e_{L,d}(\psi)\longrightarrow0.
  \]

Common marginal means \(\mathcal L_\nu(Z_q)=F\) for the coordinates under consideration. It is harmless to assume this at every rational coordinate, as for the actual affine laws. Some component restrictions below recover this assertion from SI rather than assuming that marginals pass to restrictions.

For probabilities,

\[
 d_{\rm TV}(\alpha,\beta)=\sup_E|\alpha(E)-\beta(E)|
 =\tfrac12|\alpha-\beta|(\Omega).
\]

Consequently a bounded test \(H\) has expectation difference at most \(2\|H\|_\infty d_{\rm TV}\). ANN gives

\[
 \nu\le kR_k\nu,\qquad
 d_{\rm TV}(R_l\nu,R_k\nu)\le1-\frac{k}{l}\quad(l>k).
\]

Every \(R_k\) sends IS laws to IS laws: \(A_1\) cycles the branches, with wraparound \(G_{k,k}=G_{k,0}A_1\). No rational-translation invariance or real-topology continuity of the rational action is assumed. The current is \(J(\lambda)=\mathbb E_\lambda\operatorname{sgn}(Z_1-Z_0)\), with \(\operatorname{sgn}(0)=0\). A product pair law gives \(J=0\); when \(F\) is atomless it also gives each strict ordering probability \(1/2\).

## 2. Fixed-point pair rigidity

### 2.1 Precise theorem

**Theorem 1.** Suppose \(\nu\) is IS, \(R_k\nu=\nu\) for every \(k\ge1\), has common rational-coordinate marginal \(F\), and satisfies coordinate AP-SI. Then

\[
 \mathcal L_\nu(Z_q,Z_{q'})=F\otimes F
 \qquad(q,q'\in\mathbb Q,\ q\ne q').
\]

Here coordinate AP-SI is enough: because the orbit is fixed, it equals USI-AP on this orbit. ANN is automatic, but the following proof uses the stronger exact fixed-point identities, not ANN as a replacement for them. Only coordinate observables require SI; arbitrary cylinder-product SI and full-system ergodicity are unnecessary.

### 2.2 Exact profinite joining and the stationarity sign

There is a probability \(\rho\) on \(\Omega\times\widehat{\mathbb Z}\), with coordinates \((Z,U)\), such that for every Borel \(E\subseteq\Omega\),

\[
 \boxed{\rho(E\times\{U\equiv r\pmod k\})
       =\frac1k(G_{k,r})_*\nu(E)}\qquad(0\le r<k).
\]

Indeed, compatibility between moduli \(k\) and \(km\) is exactly

\[
 \begin{aligned}
 \sum_{t=0}^{m-1}\frac1{km}(G_{km,r+kt})_*\nu
 &=\frac1k(G_{k,r})_*R_m\nu\\
 &=\frac1k(G_{k,r})_*\nu.
 \end{aligned}
\]

The finite-level measures are probabilities, their field marginal is \(R_k\nu=\nu\), and their residue marginal is uniform. The countable inverse-limit construction, for example along factorial moduli, supplies \(\rho\). Thus \(U\) is Haar on \(\widehat{\mathbb Z}\), but is **not asserted to be independent of the field**.

The joining is invariant under

\[
 S(Z,U)=(A_1Z,U+1).
\]

For residues other than the wraparound, this is \(A_1G_{k,r}=G_{k,r+1}\). At the wraparound use \(A_1G_{k,k-1}=G_{k,0}A_1\) and IS. The sign is \(+1\), consistent with the source's definition of joint stationarity.

For bounded \(\phi\), bounded \(F\)-centered \(\psi\), and integer \(h\ne0\), set

\[
 C(h)=\mathbb E_\nu\phi(Z_0)\psi(Z_h).
\]

The residue-zero cylinder gives the exact identity

\[
 \boxed{\mathbb E_\rho
    p1_{\{p\mid U\}}\phi(Z_0)\psi(Z_{ph})=C(h).}
\]

This is a weighted expectation, or equivalently a conditional expectation **given the event** \(p\mid U\). It is not an assertion that conditioning on the entire random variable \(U\) gives the constant \(C(h)\). Since the unconditioned field marginal is \(\nu\),

\[
 C(h)-C(ph)
 =\mathbb E_\rho\phi(Z_0)\psi(Z_{ph})(p1_{\{p\mid U\}}-1).
\]

### 2.3 What is actually supplied by the entropy source

The checked source is Tao–Teräväinen, *The structure of correlations of multiplicative functions at almost all scales, with applications to the Chowla and Elliott conjectures*, arXiv:1809.02518, local file

`/corpus/src/1809.02518/1809.02518.tex`, lines **410–440**.

The proposition labeled `eda` at lines 412–419 is explicitly a **general stationary-process statement**. It assumes random 1-bounded functions \(\mathbf g_i:\mathbb Z\to\mathbb D\), a profinite random integer \(\mathbf n\), and joint stationarity. It does not assume multiplicativity. For fixed integer shifts, its dyadic-prime average of

\[
 \left|\mathbb E\prod_i\mathbf g_i(ph_i)
                (p1_{\{p\mid\mathbf n\}}-1)\right|
\]

is at most \(\epsilon\) outside a set \(\mathcal M_\epsilon\) satisfying

\[
 \sum_{m\in\mathcal M_\epsilon}\frac1m
 \ll_{h_1,\ldots,h_j}\epsilon^{-4}\log(1/\epsilon).
\]

We take its parameter \(a=1\). The source permits zero and negative integer shifts. Normalize the nonzero sup norms of \(\phi,\psi\), take

\[
 \mathbf g_1(n)=\phi(Z_n)/\|\phi\|_\infty,\qquad
 \mathbf g_2(n)=\psi(Z_n)/\|\psi\|_\infty,
 \qquad(h_1,h_2)=(0,h),
\]

and use the joining just constructed. Vanishing sup norms are trivial cases.

Write

\[
 W(P)=\sum_{p\le P}\frac1p,\qquad
 \mathbb E^{\log}_{p\le P}a_p=\frac1{W(P)}\sum_{p\le P}\frac{a_p}{p}.
\]

The dyadic estimate implies

\[
 \boxed{\mathbb E^{\log}_{p\le P}|C(h)-C(ph)|\longrightarrow0.}
\]

For clarity, the conversion uses that the prime harmonic mass of the \(m\)-th dyadic block is \(O(1/m)\), while \(W(P)\sim\log\log P\). Exceptional blocks have bounded total harmonic mass depending on \(\epsilon\); good blocks contribute \(O(\epsilon)\) after normalization. The integrands have a uniform bound because Haar \(U\) gives \(\mathbb E|p1_{p\mid U}-1|\le2\). This is the same conversion used at source lines 430–440.

We are invoking `eda` and this summation argument, **not applying the arithmetic proposition `dollop` to nonmultiplicative coordinate tests**. No additional elementary entropy recurrence is needed or claimed here.

### 2.4 AP-SI removes the rational spectrum of a coordinate

Let \(T f=f\circ A_1\) on \(L^2(\nu)\), and put \(g=\psi(Z_0)\). AP-SI says

\[
 \left\|\frac1L\sum_{j=1}^LT^{dj}g\right\|_2\longrightarrow0
 \quad(d\ge1).
\]

By the spectral theorem, the spectral measure \(\sigma_g\) has no mass on \(\{\theta:d\theta\in\mathbb Z\}\), for every \(d\). Hence

\[
 \sigma_g(\mathbb Q/\mathbb Z)=0.
\]

Unit-step SI alone would only remove the atom at zero; the AP hypothesis is important here.

Vinogradov's prime equidistribution theorem gives, for every irrational \(\alpha\),

\[
 \frac1{\pi(P)}\sum_{p\le P}e^{2\pi i p\alpha}\longrightarrow0.
\]

Partial summation and the prime number theorem imply its prime-harmonic version

\[
 m_P(\alpha):=\frac1{W(P)}\sum_{p\le P}\frac{e^{2\pi i p\alpha}}p
 \longrightarrow0.
\]

Since \(|m_P|\le1\), spectral dominated convergence yields, for each integer \(h\ne0\),

\[
 \left\|\frac1{W(P)}\sum_{p\le P}\frac{T^{ph}g}{p}\right\|_2
 \longrightarrow0.
\]

It follows that \(\mathbb E^{\log}_{p\le P}C(ph)\to0\). Combined with §2.3 this gives \(C(h)=0\). IS moves arbitrary integer origins to zero, proving integer-pair independence.

The identical spectral conclusion holds for \(g(Z,U)=\psi(Z_0)\) on \(L^2(\rho,S)\): its time correlations and spectral measure are those on \((\nu,A_1)\). This observation permits the rational extension without requiring SI for residue-weighted products.

### 2.5 Rational extension: a complete finite-denominator argument

Fix \(M\ge1\) and distinct integers \(a,b\). Define

\[
 C_{M;a,b}=\mathbb E_\nu\phi(Z_{a/M})\psi(Z_{b/M}).
\]

For a prime \(p\nmid M\), the joining at modulus \(Mp\) gives

\[
 C_{M;a,b}
 =M\mathbb E_\rho1_{\{M\mid U\}}p1_{\{p\mid U\}}
                \phi(Z_{pa})\psi(Z_{pb}).
\]

Here the coprimality condition is used to identify the event with \(Mp\mid U\). The finitely many excluded primes have zero limiting prime-harmonic weight.

Put

\[
 B_p=M\mathbb E_\rho1_{\{M\mid U\}}\phi(Z_{pa})\psi(Z_{pb}).
\]

For each residue \(r\pmod M\), apply `eda` to the jointly stationary random functions

\[
 \mathbf g_{1,r}(n)=1_{\{U+n\equiv ra\pmod M\}}\phi(Z_n),
 \qquad \mathbf g_2(n)=\psi(Z_n),
\]

after norm normalization, with integer shifts \((a,b)\). For primes \(p\equiv r\pmod M\), the indicator in \(\mathbf g_{1,r}(pa)\) equals \(1_{M\mid U}\). Restricting a nonnegative absolute-error average to this prime class can only decrease it. Summing over the finitely many residues and multiplying by the fixed \(M\), we obtain

\[
 \mathbb E^{\log}_{\substack{p\le P\\p\nmid M}}
       |C_{M;a,b}-B_p|\longrightarrow0,
\]

where this display uses the original denominator \(W(P)\); deleting the finitely many primes does not change the limit.

Stationarity of \(\rho\), now shifting by \(-pa\), rewrites

\[
 B_p=\mathbb E_\rho H_r\,\psi(Z_{p(b-a)})
 \quad(p\equiv r\pmod M),\qquad
 H_r=M1_{\{U\equiv ra\pmod M\}}\phi(Z_0).
\]

For irrational \(\theta\), residue-restricted prime multipliers also tend to zero:

\[
 \begin{aligned}
 \frac1{W(P)}\sum_{\substack{p\le P\\p\equiv r\ (M)}}
       \frac{e^{2\pi i p(b-a)\theta}}p
 &=\frac1M\sum_{j=0}^{M-1}e^{-2\pi i jr/M}
              m_P((b-a)\theta+j/M)\\
 &\longrightarrow0.
 \end{aligned}
\]

Every frequency on the right is irrational. Apply spectral dominated convergence to \(g=\psi(Z_0)\) on the joining, then pair with the fixed bounded \(H_r\), and sum over \(r\). This proves \(\mathbb E^{\log}_{p\le P}B_p\to0\), so \(C_{M;a,b}=0\).

Every distinct rational pair has the form \((a/M,b/M)\). Centering \(\psi\) and using the common marginal, the last identity gives the product law. Bounded continuous product tests already determine that law. This completes Theorem 1.

**Branch audit.** The bound \((G_{M,r})_*\nu\le M\nu\) is legitimate when \(R_M\nu=\nu\). It can transfer suitable coordinate AP estimates. But a single branch need not be IS or \(R_k\)-fixed, so the integer theorem cannot simply be applied to it. The finite-residue proof above avoids that gap entirely. In particular, no rational invariance of \(\nu\) was introduced in proving rational-pair independence.

## 3. Integer-ergodic components: finite, countable, and atomic

This section needs **only IS + ANN**, until the explicit SI corollary. “Ergodic” always means ergodic for \(A_1\) on the full rational-coordinate space, not ergodic for every rational translation.

### 3.1 Ergodicity preservation and the component measure

**Lemma 2.** \(R_k\) sends an IS ergodic probability to an IS ergodic probability.

For a strictly \(A_1\)-invariant Borel set \(E\), all branches have the same probability on \(E\), since \(G_{k,r}=A_rG_{k,0}\). Moreover \(G_{k,0}^{-1}E\) is \(A_1\)-invariant because

\[
 G_{k,0}A_1=A_kG_{k,0}.
\]

Its probability under the original ergodic law is zero or one. Testing strictly invariant sets is sufficient for ergodicity of an invariant probability; almost-invariant sets have invariant representatives. This proves the lemma.

Let \(\mathscr E\) be the standard Borel space of IS ergodic probabilities, and write the unique ergodic decomposition as

\[
 \nu=\int_{\mathscr E}\theta\,d\pi(\theta),\qquad
 \tau_k(\theta)=R_k\theta.
\]

The maps \(\tau_k\) are Borel, commute, and satisfy \(\tau_k\tau_m=\tau_{km}\). The component distribution of \(R_k\nu\) is

\[
 \pi_k=(\tau_k)_*\pi.
\]

Uniqueness of ergodic decomposition for invariant finite measures transfers ANN to these distributions:

\[
 \boxed{l\pi_l-k\pi_k\ge0.}
\]

To justify positivity, decompose the positive invariant finite measure \(lR_l\nu-kR_k\nu\); adding its decomposition to that of \(kR_k\nu\) must give the decomposition of \(lR_l\nu\). Consequently

\[
 \pi\le k\pi_k,\qquad
 d_{\rm TV}(\pi_{k+1},\pi_k)\le\frac1{k+1}.
\]

This is an assertion about the **distribution of components**. ANN has not been asserted for each individual component.

### 3.2 Exact fibres: finite rational-translation orbits

**Lemma 3.** For \(\theta,\theta'\in\mathscr E\),

\[
 \boxed{R_k\theta=R_k\theta'
 \quad\Longleftrightarrow\quad
 \theta'=(A_{r/k})_*\theta\text{ for some }0\le r<k.}
\]

If the images agree, apply \((D_k)_*\) to obtain \(P_k\theta=P_k\theta'\). Both sides are finite mixtures of \(A_1\)-ergodic laws, because rational translations commute with \(A_1\). The component \(\theta'\), which occurs on the right, must occur on the left. Conversely, covariance gives

\[
 R_k(A_{r/k})_*\theta=(A_r)_*R_k\theta=R_k\theta.
\]

Thus every fibre has at most \(k\) elements, and two components can merge only if they are rational translates. This finite-fibre statement will also ensure that a nonatomic component distribution cannot acquire atoms after applying \(R_k\).

### 3.3 Audits of the ergodic and finite cases

If \(\nu\) itself is ergodic, then \(R_k\nu\) is ergodic and \(\nu\le kR_k\nu\). An invariant probability absolutely continuous with respect to an ergodic invariant probability equals it. Hence \(R_k\nu=\nu\).

If \(\nu\) has exactly \(N<\infty\) positive-mass components, \(\pi\le k\pi_k\) forces their set to be contained in its \(\tau_k\)-image. The image has at most \(N\) elements, so \(\tau_k\) permutes that finite set. Only finitely many component-weight arrangements can occur. The neighboring TV bound forces \(\pi_k\) to be eventually constant. If the eventual value is \(\lambda\), commutation gives \((\tau_m)_*\lambda=\lambda\). Applying the injective permutation \(\tau_n\), for large \(n\), to both \(\pi\) and \(\pi_m\) then yields \(\pi_m=\pi\).

Thus the supplied finite-component proof is valid. Finiteness is used in its positive minimum-distance argument; replacing “finite” by “countable” at that line alone would be invalid. The next argument supplies the missing replacement.

### 3.4 Countable components: collisions are impossible

**Theorem 4.** If an IS law satisfying ANN has at most countably many positive-mass ergodic components and no nonatomic component part, then

\[
 R_k\nu=\nu\qquad(k\ge1).
\]

Write

\[
 \pi=\sum_{i\in I}w_i\delta_{\theta_i},\qquad w_i>0,\quad\sum_iw_i=1,
 \qquad S_0=\{\theta_i:i\in I\}.
\]

First we prove that **no two distinct elements of \(S_0\) are rational translates**.

For a probability \(\beta\) on \(\mathscr E\), define its atomic collision energy

\[
 Q(\beta)=\sum_{\theta\in\mathscr E}\beta(\{\theta\})^2.
\]

This is the mass of the diagonal under \(\beta\otimes\beta\), so

\[
 |Q(\beta)-Q(\gamma)|\le2d_{\rm TV}(\beta,\gamma).
\]

Suppose distinct positive-mass atoms \(\theta_i,\theta_j\) are rational translates. For arbitrarily small \(\epsilon>0\), choose a finite subset \(F\subset I\), containing \(i,j\), with total mass greater than \(1-\epsilon\). Choose \(M\) divisible by denominators of rational offsets connecting every pair of rationally related laws in this finite set. There are only finitely many such choices to make.

* At \(n=Mt\), \(\tau_n\) merges every rational-translation class in \(F\): if \(\theta_v=(A_{r/M})_*\theta_u\), then \(\tau_n\theta_v=(A_{tr})_*\tau_n\theta_u=\tau_n\theta_u\).
* At \(n=Mt+1\), \(\tau_n\) is injective on \(F\). If two members merge, Lemma 3 says they are rational translates, so write them both as
  \[
   \theta_v=(A_{r/M})_*\theta_u=(A_{s/n})_*\theta_u.
  \]
  Invariance of \(\theta_u\) under \(A_{r/M-s/n}\), multiplied by \(n\) and combined with IS, gives invariance under \(A_{nr/M}\). Since \(n\equiv1\pmod M\), this is invariance under \(A_{r/M}\), contradicting distinctness.

Therefore, at these neighboring scales,

\[
 \begin{aligned}
 Q(\pi_{Mt})&\ge\sum_{u\in F}w_u^2+2w_iw_j,\\
 Q(\pi_{Mt+1})&\le\sum_{u\in F}w_u^2+2\epsilon.
 \end{aligned}
\]

For the second inequality, the image of the finite submeasure has collision energy exactly \(\sum_{u\in F}w_u^2\); adding a positive tail of mass at most \(\epsilon\) increases collision energy by at most \(2\epsilon\). ANN and the Lipschitz bound now give

\[
 2w_iw_j\le2\epsilon+\frac2{Mt+1}.
\]

First let \(t\to\infty\), then let \(\epsilon\downarrow0\). This contradicts \(w_iw_j>0\).

By Lemma 3, every \(\tau_n\) is consequently injective on \(S_0\). In particular, **the multiset of positive atom weights of every \(\pi_n\) is exactly the original multiset \(\{w_i\}\)**. There is no hidden sum of infinitely many incoming atomic masses.

### 3.5 Countable components: discrete weights replace a finite orbit

The set of possible numerical weights

\[
 D=\{0\}\cup\{w_i:i\in I\}
\]

is compact, and every positive element is isolated: summability leaves only finitely many weights above any positive threshold.

Given \(\epsilon>0\), choose a threshold so that atoms whose weights are at least that threshold carry mass greater than \(1-\epsilon\). Only finitely many distinct weight values are selected. Let \(\gamma>0\) be the minimum of their distances from the other elements of \(D\).

For all sufficiently large \(n\),

\[
 d_{\rm TV}(\pi_{n+1},\pi_n)<\gamma.
\]

At a point carrying any selected weight, its next weight must then be exactly the same: no different element of \(D\) lies close enough. These heavy atoms remain at the same points forever after that scale. Their total mass is greater than \(1-\epsilon\), so any two later \(\pi_n\)'s have TV distance at most \(\epsilon\). Thus

\[
 \pi_n\longrightarrow\lambda\quad\text{in total variation}
\]

for one probability \(\lambda\).

It remains to return to scale 1 without an illicit inverse on all laws. Fix \(m\). The domination \(\pi\le m\pi_m\) gives the inclusion of atomic supports

\[
 S_0\subseteq\tau_m(S_0).
\]

The map \(\tau_n\) is injective on \(\tau_m(S_0)\): equality of two such images is equality under \(\tau_{nm}\) of their preimages in \(S_0\), where injectivity was proved. Hence it is injective on the union of the supports of \(\pi\) and \(\pi_m\). Pushforward by this map is a TV isometry for these two atomic measures. It follows that

\[
 \begin{aligned}
 d_{\rm TV}(\pi,\pi_m)
 &=d_{\rm TV}((\tau_n)_*\pi,(\tau_n)_*\pi_m)\\
 &=d_{\rm TV}(\pi_n,\pi_{nm})\longrightarrow0.
 \end{aligned}
\]

Thus \(\pi_m=\pi\), and taking barycentres proves Theorem 4.

**Why this closes the harmonic-mass concern.** Finite fibres by themselves do not make a countable support finite or justify permutation inversion. The additional collision-energy comparison at \(Mt,Mt+1\) rules out all mergers of positive-mass components. Only after that step do the discrete-weight argument and the restricted TV isometry become valid.

### 3.6 The atomic component part of an arbitrary law

**Theorem 5.** Let \(\nu\) be any IS law satisfying ANN. Write its ergodic component distribution as

\[
 \pi=\pi_{\rm at}+\pi_{\rm na},\qquad
 \alpha=\pi_{\rm at}(\mathscr E),
 \qquad \nu_{\rm at}=\int\theta\,d\pi_{\rm at}(\theta).
\]

Then

\[
 \boxed{R_k\nu_{\rm at}=\nu_{\rm at}\quad(k\ge1).}
\]

Indeed, finite fibres from Lemma 3 imply that \((\tau_k)_*\pi_{\rm na}\) is nonatomic: the preimage of a singleton has at most \(k\) elements. Atomic measures stay atomic. Hence the atomic and nonatomic parts of \(\pi_k\) are exactly the separate pushforwards of these two parts, each preserving its total mass. Taking atomic parts of the positive inequalities \(l\pi_l-k\pi_k\ge0\) gives

\[
 l(\tau_l)_*\pi_{\rm at}-k(\tau_k)_*\pi_{\rm at}\ge0.
\]

If \(\alpha>0\), the normalized atomic distribution therefore satisfies the hypotheses of Theorem 4. The case \(\alpha=0\) is vacuous. This proves the assertion. The nonatomic restriction separately satisfies ANN as well.

**USI corollary.** If \(\nu\) also satisfies USI-AP and \(\alpha>0\), put \(\widehat\nu_{\rm at}=\nu_{\rm at}/\alpha\). It inherits the orbit estimate with rate

\[
 \alpha^{-1/2}e_{L,d}(\psi),
\]

because \(R_k\nu_{\rm at}\le R_k\nu\). Its integer-coordinate marginal is \(F\): the expectation of a stationary block equals the expectation of one coordinate, and its mean square tends to zero for every \(F\)-centered test. It is important to use this SI argument; a common marginal does not in general pass to an invariant restriction merely by domination.

Rational-coordinate marginals can be recovered by the same argument. For \(q=r/M\), reducing the origin modulo an integer if necessary, the universal branch bound

\[
 (G_{M,r})_*\widehat\nu_{\rm at}\le M R_M\widehat\nu_{\rm at}
\]

gives

\[
 \mathbb E_{\widehat\nu_{\rm at}}
 \left|\frac1L\sum_{j=1}^L\psi(Z_{q+dj})\right|^2
 \le\frac{M}{\alpha}e_{L,Md}(\psi)^2\longrightarrow0.
\]

Integer stationarity then identifies the marginal at \(q\) as \(F\). Theorem 1 applies and proves every distinct rational pair independent under \(\widehat\nu_{\rm at}\).

In particular, under the full package, a purely countable component law has all the asserted product pair laws. For a general law with \(0<\alpha<1\), writing \(\widehat\nu_{\rm na}=(\nu-\nu_{\rm at})/(1-\alpha)\),

\[
 J(\nu)=(1-\alpha)J(\widehat\nu_{\rm na}),\qquad |J(\nu)|\le1-\alpha.
\]

The normalized nonatomic remainder, when nonzero, also inherits USI-AP and common \(F\) by the same positive-submeasure and marginal arguments, with rate \((1-\alpha)^{-1/2}e_{L,d}\). Its ANN was proved by restricting the component inequalities above. Thus any nonzero-current counterexample to the full package could be reduced to one with a **purely nonatomic ergodic decomposition**.

This proves invariance and pair rigidity of the **atomic sublaw**, not pair rigidity of each individual ergodic component. On its supported atoms the \(R_k\)'s act by weight-preserving permutations; individual componentwise ANN has not been established or used.

## 4. Other sufficient hypotheses and the translate-mixture audit

### 4.1 Countable rational translates of an \(R\)-fixed law

The proposed preliminary result is valid, even if the base law is not ergodic. Suppose \(\eta\) is IS and \(R_k\eta=\eta\) for all \(k\), and

\[
 \nu=\sum_j w_j(A_{s_j})_*\eta,\qquad s_j\in\mathbb Q,
\]

is a probability satisfying ANN. Choose finitely many terms of total mass greater than \(1-\epsilon\), and let \(M\) be a common denominator of their offsets. Covariance gives, for those terms,

\[
 R_{Mt}(A_{s_j})_*\eta=\eta,\qquad
 R_{Mt+1}(A_{s_j})_*\eta=(A_{s_j})_*\eta.
\]

The tail costs at most \(\epsilon\) in TV in each comparison, so

\[
 d_{\rm TV}(\nu,\eta)
 \le2\epsilon+d_{\rm TV}(R_{Mt+1}\nu,R_{Mt}\nu)
 \le2\epsilon+\frac1{Mt+1}.
\]

Let \(t\to\infty\), then \(\epsilon\downarrow0\). Thus \(\nu=\eta\). This proof was checked independently; it does not assume that rational translations of \(\eta\) coincide. Theorems 4–5 go beyond this special representation and do not need to produce an \(R\)-fixed representative in advance.

### 4.2 Two multiplicatively independent exact fixed scales

Suppose \(\nu\) is IS and satisfies ANN, and

\[
 R_a\nu=R_b\nu=\nu,
 \qquad a,b\ge2,\qquad \log a/\log b\notin\mathbb Q.
\]

For any fixed integer \(k\ge1\), irrational rotation of logarithms gives positive integer sequences \(u_j,v_j\) tending to infinity with

\[
 \frac{a^{u_j}}{kb^{v_j}}\longrightarrow1.
\]

Commutation and the assumed fixed scales give

\[
 R_{a^{u_j}}\nu=\nu,\qquad R_{kb^{v_j}}\nu=R_k\nu.
\]

ANN compares these integer indices in whichever order they occur:

\[
 d_{\rm TV}(\nu,R_k\nu)
 \le1-\frac{\min(a^{u_j},kb^{v_j})}{\max(a^{u_j},kb^{v_j})}
 \longrightarrow0.
\]

Therefore every \(R_k\nu=\nu\). Under coordinate AP-SI and common \(F\), Theorem 1 gives all rational-pair laws. No inverse averaging operator or continuity of \(q\mapsto A_q\) is used.

### 4.3 Cofinite-denominator translation stabilizer

Suppose \(\nu\) satisfies IS + ANN + USI-AP and, for some fixed \(M\ge1\),

\[
 (A_{1/m})_*\nu=\nu\qquad\text{whenever }\gcd(m,M)=1.
\]

Then every distinct **integer** pair is independent. Here is the exact nearby-scale calculation.

For an integer \(h>0\), let \(C=\mathbb E_\nu\phi(Z_0)\psi(Z_h)\), with \(\psi\) centered, and let \(B=\|\phi\|_\infty\|\psi\|_\infty\). Choose \(K\equiv1\pmod M\) and set

\[
 m_r=K+Mr\quad(1\le r\le L).
\]

Each \(m_r\) is coprime to \(M\), so \(P_{m_r}\nu=\nu\). The exact projection identity gives

\[
 C=\mathbb E_{R_{m_r}\nu}\phi(Z_0)\psi(Z_{h m_r}).
\]

Compare \(R_{m_r}\nu\) with \(R_K\nu\), average over \(r\), and use the AP of step \(hM\) beginning at \(hK\) under the IS law \(R_K\nu\). Cauchy–Schwarz and ANN yield

\[
 \begin{aligned}
 |C|
 &\le\|\phi\|_\infty e_{L,hM}(\psi)
       +\frac{2B}{L}\sum_{r=1}^L\frac{Mr}{K+Mr}\\
 &\le\boxed{\|\phi\|_\infty e_{L,hM}(\psi)
       +B\frac{M(L+1)}K}.
 \end{aligned}
\]

First let \(K\to\infty\) through \(1\pmod M\), with \(L\) fixed; then let \(L\to\infty\). Negative lags and arbitrary integer origins follow by IS and exchanging tests. The argument asserts neither full rational-translation invariance nor original-law \(R_k\)-fixedness. It is compatible with the 3-adic companion model, whose stabilizer corresponds to denominators coprime to 3.

## 5. Long logarithmic \(R\)-orbit averages

Let \(1\le a\le b\) be integers and write

\[
 H_{a,b}=\sum_{k=a}^b\frac1k,\qquad
 \Lambda_{a,b}=\frac1{H_{a,b}}\sum_{k=a}^b\frac1kR_k\nu.
\]

Assume IS + ANN. For every fixed \(m\ge1\),

\[
 \boxed{d_{\rm TV}(R_m\Lambda_{a,b},\Lambda_{a,b})
       \le\frac{C_m}{H_{a,b}},}
\]

with \(C_m\) independent of \(a,b\).

**Full-measure estimate.** By commutation, the unnormalized numerator of \(R_m\Lambda_{a,b}\) is \(\sum_{k=a}^b k^{-1}R_{mk}\nu\). Compare its \(k\)-th summand with the block

\[
 \sum_{r=0}^{m-1}\frac1{mk+r}R_{mk+r}\nu.
\]

The mass discrepancy and the ANN variation error are summable in \(k\):

\[
 \begin{aligned}
 0\le\frac1k-\sum_{r=0}^{m-1}\frac1{mk+r}
 &\le\frac{m-1}{2m k^2},\\
 \sum_{r=0}^{m-1}\frac1{mk+r}
     |R_{mk+r}\nu-R_{mk}\nu|(\Omega)
 &\le\sum_{r=0}^{m-1}\frac{2r}{(mk+r)^2}
 \le\frac{m-1}{m k^2}.
 \end{aligned}
\]

Thus the signed variation error in replacing all blocks is \(O_m(\sum_{k\ge a}k^{-2})=O_m(1)\). The resulting block range is \([ma,m(b+1)-1]\). Replacing it by \([a,b]\) costs only the two endpoint harmonic sums

\[
 \sum_{j=a}^{ma-1}\frac1j+
 \sum_{j=b+1}^{m(b+1)-1}\frac1j=O_m(1).
\]

Divide by \(H_{a,b}\), with the probability-TV convention from §1, to obtain the claimed bound. This uses ANN within complete \(m\)-blocks and controls endpoints; multiplicative reindexing of the discrete harmonic sum is not an exact identity by itself.

If \(b/a\to\infty\), then \(H_{a,b}\to\infty\). Compactness and weak continuity of every \(R_m\) show that every cluster point \(\lambda\) is IS and satisfies \(R_m\lambda=\lambda\) for all \(m\).

If \(\nu\) has common \(F\) and USI-AP, convex averaging preserves each bound. For bounded continuous \(\psi\), the mean-square expression at a fixed \(L,d\) is a continuous cylinder test, so its bound passes to \(\lambda\). Approximation in \(L^2(F)\), using common marginals and Jensen, extends to bounded measurable tests if needed. Theorem 1 therefore gives all distinct rational pairs of \(\lambda\) law \(F\otimes F\).

In fact, for each fixed distinct rational pair, the pair laws of \(\Lambda_{a,b}\) themselves converge to \(F\otimes F\) whenever \(b/a\to\infty\): every subsequential cluster point has that same pair law. If \(F\) is atomless, the ordering test also converges, since its discontinuity set is the diagonal and that diagonal has zero limiting mass.

**Scope warning.** These are pair laws of logarithmic orbit averages and their cluster points. This proves neither \(\Lambda_{a,b}\to\nu\) nor pair independence of the original scale-1 law. The result also does not make the limiting full law rationally translation invariant; the 3-adic example already separates \(R\)-fixedness from that stronger property.

## 6. Quadratic countermodel to backward branch domination

### 6.1 Full-field construction and affine transport

Let \(\mathbb T=\mathbb R/\mathbb Z\) and

\[
 \mathcal H=\operatorname{Hom}(\mathbb Q_{\rm disc},\mathbb T).
\]

This is the compact metrizable group of all additive characters of **discrete** \(\mathbb Q\), with its Haar probability. Take independent

\[
 U\sim m_{\mathbb T},\qquad \chi\sim m_{\mathcal H},\qquad
 V\text{ with density }\tfrac12v^{-3/2}1_{v\ge1}\,dv.
\]

For each fixed \(v>0\), define \(\lambda_v\) as the law on \(\Omega\) of

\[
 Z_q=\operatorname{rep}_{[0,1)}(U+\chi(q)+vq^2).
\]

All coordinates are Borel functions on this latent space, and the index set is countable. This constructs a full law, not merely candidate pair distributions. The dependence on \(v\) is measurable, so the mixture

\[
 \eta=\int_1^\infty\lambda_v\,\tfrac12v^{-3/2}\,dv
\]

is well-defined and has mass one.

Each \(\lambda_v\) is invariant under every rational translation. For a shift \(s\), the transformed latent variables can be written

\[
 U'=U+\chi(s)+vs^2,\qquad
 \chi'(q)=\chi(q)+2vsq.
\]

Addition of the deterministic character \(q\mapsto2vsq\) preserves Haar on \(\mathcal H\); conditional on \(\chi\), the phase \(U'\) is still Haar. Thus the transformed pair has the original product Haar law.

For a branch \(G_{k,r}\), expansion of the square instead gives

\[
 U'=U+\chi(r/k)+vr^2/k^2,\qquad
 \chi'(q)=\chi(q/k)+2vrq/k^2,\qquad v'=v/k^2.
\]

Precomposition by \(q\mapsto q/k\) is an automorphism of \(\mathcal H\), and the added linear term is a character. The same conditional-Haar argument proves the full-law identity

\[
 \boxed{(G_{k,r})_*\lambda_v=\lambda_{v/k^2}}
 \qquad\text{for every branch }r.
\]

It follows by the substitution \(v=k^2w\) that

\[
 \boxed{kR_k\eta
   =\int_{1/k^2}^\infty\lambda_w\,\tfrac12w^{-3/2}\,dw.}
\]

The lower endpoint decreases with \(k\), so these finite measures increase. This proves **all full-law annuli**. IS is already supplied by rational-translation invariance.

### 6.2 Pair independence, exact USI, and current

For \(q\ne q'\), evaluation \(\chi\mapsto\chi(q'-q)\) maps Haar on \(\mathcal H\) to Haar on \(\mathbb T\). Conditional on \(\chi\), the first phase \(U+\chi(q)\) is Haar, so it is independent of that difference. Thus the two phases are independent uniforms, and adding the deterministic quadratic terms does not alter this assertion. Every distinct pair is independent uniform **conditional on \(V=v\)**, with a pair law independent of \(v\).

Consequently, for centered square-integrable \(\psi\) and any distinct rational \(q_1,\ldots,q_L\), every \(R_k\eta\) satisfies

\[
 \mathbb E_{R_k\eta}
 \left|\frac1L\sum_{j=1}^L\psi(Z_{q_j})\right|^2
 =\frac1L\int_0^1|\psi(u)|^2\,du.
\]

This is stronger than USI-AP, but remains a statement about coordinate tests, not arbitrary cylinder products. The adjacent pair law is the atomless product, so

\[
 J(\eta)=0,\qquad
 \eta(Z_1>Z_0)=\eta(Z_1<Z_0)=\tfrac12.
\]

### 6.3 Measurable recovery of the quadratic parameter

Define on the set of finite convergence

\[
 \mathcal V(z)=\lim_{n\to\infty}\frac{n^2}{2}
     \operatorname{rep}_{[0,1)}(z_0-2z_{1/n}+z_{2/n}),
\]

and set it to \(+\infty\) elsewhere. This is a measurable extended-real function. Under \(\lambda_v\), the character and constant terms cancel **modulo one**, giving

\[
 z_0-2z_{1/n}+z_{2/n}\equiv\frac{2v}{n^2}\pmod1.
\]

For all sufficiently large \(n\), \(0<2v/n^2<1\), so the displayed sequence is exactly \(v\). Hence \(\mathcal V=v\) almost surely under \(\lambda_v\). It is essential to take the circle representative of the second difference; an ordinary unwrapped second difference of the individual representatives would not have this property.

For \(k>1\),

\[
 \eta\{\mathcal V<1\}=0,\qquad
 (D_{1/k})_*\eta\{\mathcal V<1\}
 =\mathbb P(V<k^2)=1-\frac1k.
\]

Since \(D_{1/k}=G_{k,0}\), this proves

\[
 (G_{k,0})_*\eta\not\ll\eta,
 \quad\text{and in particular}\quad
 (G_{k,0})_*\eta\not\le k\eta.
\]

Thus ANN does not provide the backward branch domination required to construct the fixed-point joining with field marginal \(\nu\). Its valid forward inequality \(\eta\le kR_k\eta\) coexists with this failure. The law is not \(R_k\)-fixed for \(k>1\), as the recovered parameter distributions also show.

### 6.4 Dickman transport and exact scope

For a continuous strictly increasing distribution function \(F\) on \([0,1]\), with \(F(0)=0\) and \(F(1)=1\), apply \(F^{-1}\) at every coordinate. This includes the Dickman law \(F(x)=\rho(1/x)\), with \(F(0)=0\). The coordinate map is an invertible Borel map (indeed a homeomorphism on \([0,1]\)) commuting with all reindexings.

Therefore IS, ANN, pair independence, exact USI, and the failure of absolute continuity all transfer. The recovery statistic uses rank coordinates \(F(z_q)\) after transport. The ordering current stays zero. This model disproves **only the backward-domination inference**, not the target implication, and no realization as an LPF prefix law is claimed.

## 7. Audit ledger, sources, and verification

### Logical ledger

| Statement | Audited status | Essential limitation or input |
|---|---|---|
| IS + all \(R_k\)-fixed + common \(F\) + coordinate AP-SI implies integer-pair independence | Proved, Theorem 1 | Uses the general stationary entropy proposition and Vinogradov |
| The same hypotheses imply all rational-pair independence | Proved, §2.5 | Fixed denominator and finitely many residue-weighted stationary processes; no branch stationarity assumption |
| IS + ANN + ergodicity, or finitely many ergodic components, implies all \(R_k\)-fixed | Proved, §3.3 | Ergodicity is for the full rational field under \(A_1\) |
| IS + ANN + countably many ergodic components implies all \(R_k\)-fixed | Proved, Theorem 4 | Collision exclusion precedes discrete-weight stabilization and restricted inversion |
| Atomic component sublaw is \(R_k\)-fixed for any IS + ANN law | Proved, Theorem 5 | Finite fibres prevent nonatomic mass from creating atoms |
| The atomic sublaw has product pair laws under USI-AP | Proved | Normalize only when its mass is positive; SI supplies its marginals |
| Two independent fixed scales imply all fixed scales | Proved, §4.2 | ANN compares integer powers with asymptotically equal ratios |
| Stabilizer includes all denominators coprime to fixed \(M\) | Sufficient for integer-pair independence, §4.3 | Uniform orbit AP-SI and the stated order of limits are needed |
| Long logarithmic \(R\)-orbit averages have fixed cluster points and product pair limits | Proved, §5 | Not a conclusion about the original scale-1 law |
| ANN implies \((G_{k,0})_*\nu\le k\nu\) | False, §6 | Countermodel has \(J=0\), not a target disproof |
| General IS + ANN + USI-AP forces \(J(\nu)=0\) | Not proved here | Any remaining current is confined to the nonatomic component part |

The 3-adic companion remains a valid counterexample to deducing **whole-law rational translation invariance**. Its pair independence is consistent with, and now also covered by, Theorem 1. None of the new fixed-point or component conclusions repairs the rational-invariance shortcut on general laws.

### Sources actually checked

* `Submission/AffineAnnulusResearch.md`, §§1–2 and §6: operator order, full-measure ANN, TV normalization, USI-AP quantifiers, the projection obstruction, and the previously noted ergodicity preservation.
* `Submission/PadicAnnulusCounterexampleResearch.md`, especially §§5–9: the exact 3-adic stabilizer, full-law \(R_k\)-fixedness, pair independence, and the distinction from whole-law rational invariance.
* Tao–Teräväinen, arXiv:1809.02518, `/corpus/src/1809.02518/1809.02518.tex:410–440`: general stationary `eda`, its harmonic exceptional-set bound, and summation into logarithmic prime averages. The process stationarity convention was also checked at lines 378–380.
* Classical Vinogradov equidistribution of \(p\alpha\pmod1\) for irrational \(\alpha\), the spectral theorem for a unitary operator, and standard ergodic decomposition on a standard Borel system are the other external theorems used. The partial summation, residue restriction, fibre computation, and countable-component arguments are supplied above rather than attributed to an uninspected arithmetic theorem.

### Verification performed

The probability and limiting arguments above were checked mathematically. An additional Python 3 exact-arithmetic regression, using `Fraction` and saved outside `Submission`, passed **43,589 checks**:

| Finite regression | Checks |
|---|---:|
| Branch composition and joining-consistency index enumeration | 23,409 |
| \(D_kG_{k,r}\) and stationary residue cycling | 2,601 |
| Rational-shift covariance | 459 |
| Fixed-denominator prime identities, including negative indices | 11,382 |
| Quadratic branch expansion | 612 |
| Eventual parameter-recovery formula | 137 |
| Harmonic block coefficient bounds | 3,000 |
| Coprime finite-orbit noncollision arithmetic | 1,989 |

These finite checks verify conventions and exact identities, **not** entropy decrement, prime equidistribution, an infinite-component limit, or an arithmetic asymptotic by experiment. In particular, the new countable theorem rests on the proof in §§3.4–3.6, not on a finite simulation.

Only `Submission/AffinePairRigidityResearch.md` is an intended output. The two companion notes are read-only inputs; their historical unresolved statements are refined here rather than edited. `Submission/Spec.lean` retains SHA-256

`d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.

**Final scope:** audited conditional pair-rigidity theorems and a new atomic/countable-component rigidity theorem; no unconditional LPF or Erdős 371 conclusion, no nonzero-current countermodel satisfying the complete package, and no `Spec` modification.
