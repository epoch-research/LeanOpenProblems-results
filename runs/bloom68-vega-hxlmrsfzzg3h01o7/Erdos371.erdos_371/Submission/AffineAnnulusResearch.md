# Affine annuli, rational invariantization, and the signed-current obstruction

## Outcome and scope

This note audits a dynamical route for the normalized largest-prime-factor sequence and investigates its weaker, integer-stationary version. **It does not prove or disprove Erdős 371. No Spec or other Lean file is changed.**

> **Companion countermodel — rational-invariance route only.** [PadicAnnulusCounterexampleResearch.md](PadicAnnulusCounterexampleResearch.md) independently verifies a 3-adic law satisfying IS + ANN + USI-AP, with \(R_k\nu=\nu\) for every \(k\) and all distinct pairs independent with Dickman marginals, but \(\nu\perp(A_{1/3})_*\nu\). Its exact rational-translation stabilizer is \(\mathbb Q\cap\mathbb Z_3\). Thus whole-law rational translation invariance cannot be deduced from the abstract package alone. **Its current is zero:** this does not refute the implication (60), and it makes no claim about actual LPF laws or the arithmetic target.

The conclusions have deliberately different statuses:

1. **Proved conditional theorem.** Rational-translation invariance, prefix-annulus positivity, and **uniform-over-the-dilation-orbit** coordinate short-interval decorrelation imply independence of every distinct rational-coordinate pair. The proof, including the total-variation constants and order of limits, is in §3.
2. **Audited obstruction.** For an actual prefix law, the identity is
   \[
   (D_k)_*R_k\nu=P_k\nu=\frac1k\sum_{r=0}^{k-1}(A_{r/k})_*\nu,
   \]
   not \((D_k)_*R_k\nu=\nu\). Rational-translation invariance of the actual law has not been established.
3. **New partial result for the weaker package.** Integer stationarity, annuli, and uniform coordinate SI force locally averaged **invariantized** pair laws to converge to \(F\otimes F\):
   \[
   \mathcal L_{\frac1L\sum_{r=1}^L P_{K+r}\nu}(Z_0,Z_1)
       \longrightarrow F\otimes F
       \quad(L\to\infty,\ K/L\to\infty).
   \]
   There is also a rational-grid/AP version. Neither statement identifies these laws with the pair law of \(\nu\). See §6.2–§6.3.
4. **A precise failed countermodel.** An integer-stationary residue-biased field has Dickman marginals, current \(1/6\), and the strong uniform bound \(3\operatorname{Var}_F(\psi)/L\) for averages over *any* distinct coordinates, including every \(R_k\)-orbit AP. Nevertheless, consecutive \(R_k\) laws have total-variation distance **1**. It fails annuli, not SI (§6.5).
5. **The new question remains unresolved here:** no implication \(J(\nu)=0\), and no nonzero-current countermodel, has been proved for the complete package **integer stationarity + annuli + uniform coordinate AP SI**. The missing step is not hidden inside an invariantization or a passage to components.

The real-slope model and Haar-character model are checked separately in §4. Conditional implications for **actual ordinary-prefix ergodicity**, which use additional arithmetic input and not merely the structural package, are proved in §5.

## 1. The actual affine lift and its quantifiers

Put

\[
 f(n)=\frac{\log P(n)}{\log n}\quad(n\ge2),\qquad
 F(u)=\rho(1/u)\ (0<u\le1),\quad F(0)=0.
 \tag{1}
\]

Here \(F\) is the continuous, strictly increasing Dickman distribution function on \([0,1]\). Write \(Q_D=F^{-1}\) for its quantile map. Extend \(f\) boundedly at all other integer arguments.

On the compact metrizable space \(\Omega=[0,1]^{\mathbb Q}\), define, using the reduced representation \(q=b/a\), \(a>0\),

\[
 x(n)_{b/a}=f(an+b),\qquad
 \nu_X=\frac1X\sum_{n=1}^{X}\delta_{x(n)}.
 \tag{2}
\]

Endpoints can be taken integral. Fixed-multiplier stability says that \(f(cm)-f(m)\to0\) for each fixed positive integer \(c\). Consequently, changing the representation of a rational coordinate by a fixed common factor changes it by \(o(1)\) at large \(n\). This is an **asymptotic** statement about the lift, not equality of the finite values in different representations.

For \(s\in\mathbb Q\) and \(a\in\mathbb Q_{>0}\), let

\[
 (A_s z)_q=z_{q+s},\qquad (D_a z)_q=z_{aq},\qquad
 G_{k,r}=A_rD_{1/k},\qquad
 R_k\lambda=\frac1k\sum_{r=0}^{k-1}(G_{k,r})_*\lambda.
 \tag{3}
\]

Thus \((G_{k,r}z)_q=z_{(q+r)/k}\). All of these coordinate reindexings are continuous homeomorphisms; \(R_k\) is an averaging operator on measures.

If \(\nu_{X_j}\Rightarrow\nu\), then:

* \((A_m)_*\nu=\nu\) for every integer \(m\), by the bounded-endpoint shift argument.
* On each fixed finite set of coordinates,
  \(x(kn+r)-G_{k,r}x(n)\to0\). For \(q=b/a\), the unreduced affine form is \(ak n+ar+b\); any reduction uses only a fixed multiplier. Uniform continuity of cylinder tests and the residue decomposition of \([1,kX]\) give
  \[
  \boxed{\nu_{kX_j}\Rightarrow R_k\nu\qquad(k\ge1\text{ fixed}).}
  \tag{4}
  \]
  Once the original subsequence is fixed, this holds for every fixed integer \(k\); it does not require an additional independent choice of scale limits.
* Every rational-coordinate marginal is \(F\), using the fixed-progression one-variable Dickman law. Integer stationarity alone would not supply this assertion for noninteger coordinates.
* For integers \(l>k\), finite-prefix subtraction and (4) give the measure inequality
  \[
  \boxed{lR_l\nu-kR_k\nu\ge0.}
  \tag{5}
  \]
  Its mass is \(l-k\). It is positivity on the whole countable-coordinate space, not merely a bound on one selected pair test.

### 1.1 Uniform coordinate AP SI, not ergodicity

The inherited property needed below is: for each fixed positive integer \(d\) and each bounded centered coordinate test \(\psi\),

\[
 \int\psi\,dF=0,\qquad
 \sup_{k\ge1}\mathbb E_{R_k\nu}
 \left|\frac1L\sum_{r=1}^{L}\psi(Z_{dr})\right|^2
 \le e_{L,d}(\psi)^2,\qquad e_{L,d}(\psi)\longrightarrow0.
 \tag{6}
\]

We write \(e_L=e_{L,1}(\psi)\) when the test is understood. By integer stationarity, the same bound holds after any integer translation of the block.

For the actual sequence, the short-interval/AP input is initially available for cutoff tests and hence continuous coordinate tests. Boundedness upgrades averaged \(L^1\) errors to \(L^2\). Each fixed \(R_k\nu\) is a prefix limit at scales \(kX_j\), so the **same all-scale limsup bound** applies to every \(k\). This justifies the supremum in (6), with the original scale limit taken first. It is not a claim of uniform finite-\(X\) stability for multipliers growing with \(X\).

The continuous-test version extends to bounded measurable \(\psi\) by \(L^2(F)\) approximation: for any error function \(h\), stationarity and Jensen give

\[
 \sup_k\mathbb E_{R_k\nu}
 \left|\frac1L\sum_{r=1}^L h(Z_{dr})\right|^2
 \le\int |h|^2\,dF.
 \tag{7}
\]

Center the approximations as well. This proves the asserted extension of (6), without claiming SI for arbitrary cylinder products. In the abstract package, even the common integer-coordinate marginal \(F\) follows from the continuous-test version of (6): the expectation of the block equals the expectation of one coordinate, which must tend to its specified \(F\)-mean.

The mean ergodic theorem applied at a fixed scale says only
\(\mathbb E[\psi(Z_0)\mid\mathcal I_{A_d}]=0\). It does **not** say that the invariant sigma-algebra is trivial. One-coordinate means do not determine the invariant projections of pair or higher-order observables.

### 1.2 Current and the arithmetic target

Define

\[
 J(\lambda)=\mathbb E_\lambda\operatorname{sgn}(Z_1-Z_0),
 \qquad \operatorname{sgn}(0)=0.
 \tag{8}
\]

Pair independence implies \(J=0\), but is stronger than the requested signed cancellation. Equal continuous marginals alone do not rule out diagonal mass or imply reversal symmetry. For actual prefix limits, the supplied all-scale diagonal nonconcentration allows passage of the ordering test to the limit. Also, for \(n\ge3\), the signs of \(f(n+1)-f(n)\) and \(P(n+1)-P(n)\) agree; the elementary verification is in `FurstenbergObstructionResearch.md`, §1. Thus zero current for **every actual** prefix limit, together with that nonconcentration, would yield ascent density \(1/2\). Nothing below asserts this premise unconditionally.

## 2. Exact operator algebra and the TV convention

Composition is composition of maps on fields, in the order in (3). Direct coordinate evaluation gives

\[
 D_aA_s=A_{s/a}D_a,\qquad
 G_{k,r}G_{l,t}=G_{kl,r+kt}.
 \tag{9}
\]

As \((r,t)\) ranges over \([0,k)\times[0,l)\), \(r+kt\) ranges over \([0,kl)\). Therefore, on all measures,

\[
 \boxed{R_kR_l=R_lR_k=R_{kl}.}
 \tag{10}
\]

If a law is integer-stationary, so is \(R_k\) of that law: translation by 1 cycles the branches, and the wraparound uses \(A_kD_{1/k}=D_{1/k}A_1\).

Define the finite rational-translation average

\[
 P_k\lambda=\frac1k\sum_{r=0}^{k-1}(A_{r/k})_*\lambda.
 \tag{11}
\]

The identity \(D_kG_{k,r}=A_{r/k}\) gives, **without** rational invariance,

\[
 \boxed{(D_k)_*R_k\lambda=P_k\lambda,\qquad
 R_k\lambda=(D_{1/k})_*P_k\lambda.}
 \tag{12}
\]

On integer-stationary laws, \(P_k\) projects to invariance under \(A_{1/k}\); in particular \(P_k^2=P_k\). Also, on these laws,

\[
 P_kP_l=P_{\operatorname{lcm}(k,l)},
 \quad P_kR_l=(D_{1/l})_*P_{kl},
 \quad R_lP_k=(D_{1/l})_*P_{\operatorname{lcm}(k,l)}.
 \tag{13}
\]

These formulas already show why commuting the \(R_k\)'s does not make the rational invariantizations disappear.

For probabilities use

\[
 d_{\rm TV}(\alpha,\beta)=\sup_B|\alpha(B)-\beta(B)|
       =\tfrac12\,|\alpha-\beta|(\Omega).
 \tag{14}
\]

Thus the signed-measure variation norm is **twice** this distance, and for a bounded test \(H\),

\[
 \left|\int H\,d\alpha-\int H\,d\beta\right|
       \le 2\|H\|_\infty d_{\rm TV}(\alpha,\beta).
 \tag{15}
\]

From (5), \(R_l\nu=(k/l)R_k\nu+(1-k/l)\alpha_{k,l}\) for a probability \(\alpha_{k,l}\). Hence

\[
 \boxed{d_{\rm TV}(R_l\nu,R_k\nu)\le1-k/l\quad(l>k).}
 \tag{16}
\]

Pushforwards contract this distance, with equality for bijective measurable coordinate reindexings such as \(D_a\).

For later comparison, the **unconditional** consequence of pushing (16) by \(D_k\) is

\[
 d_{\rm TV}\left(P_k\nu,
   \frac1l\sum_{s=0}^{l-1}(A_{s/k}D_{k/l})_*\nu\right)
       \le1-k/l.
 \tag{17}
\]

Both averages in (17) are real parts of the identity. Neither may be replaced by the unaveraged law merely from integer stationarity.

## 3. Audited conditional theorem under rational translations

**Theorem.** Suppose \(\nu\) is invariant under every \(A_s\), \(s\in\mathbb Q\), satisfies (5), and satisfies (6) for \(d=1\), uniformly in \(k\). Then

\[
 \mathcal L_\nu(Z_q,Z_{q'})=F\otimes F
       \qquad(q\ne q',\ q,q'\in\mathbb Q).
 \tag{18}
\]

Only coordinate SI is needed; no full-system ergodicity or continuity of a rational action in a real topology is assumed.

**Proof.** Rational invariance makes \(P_k\nu=\nu\), so that

\[
 R_k\nu=(D_{1/k})_*\nu.
 \tag{19}
\]

Take \(l>k\). Pushing (16) through \(D_k\), and then, if desired, through \(D_{l/k}\), gives

\[
 d_{\rm TV}(\nu,(D_{k/l})_*\nu)\le1-k/l,
 \qquad
 d_{\rm TV}(\nu,(D_{l/k})_*\nu)\le1-k/l.
 \tag{20}
\]

In particular, consecutive annuli compare \(\nu\) and \((D_{k/(k+1)})_*\nu\) within \(1/(k+1)\). More generally, for any positive rational ratio \(a/b\), the bound is
\(1-\min(a,b)/\max(a,b)\), with integral representatives \(a,b\).

Let \(\phi\) be bounded, let \(\psi\) be bounded and \(F\)-centered, and put
\(B=\|\phi\|_\infty\|\psi\|_\infty\). Since dilation fixes coordinate 0, (15) and (20), with \(l=k+r\), give

\[
 \left|\mathbb E_\nu\phi(Z_0)\psi(Z_1)
       -\mathbb E_\nu\phi(Z_0)\psi(Z_{1+r/k})\right|
       \le 2B\frac{r}{k+r}\quad(r\ge1).
 \tag{21}
\]

This is uniform for \(1\le r\le L\), with error \(O(BL/k)\). On the other hand, rational translation invariance and (19) give the exact grid identity

\[
 \mathbb E_\nu\left|\frac1L\sum_{r=1}^L\psi(Z_{1+r/k})\right|^2
 =\mathbb E_\nu\left|\frac1L\sum_{r=1}^L\psi(Z_{r/k})\right|^2
 =\mathbb E_{R_k\nu}\left|\frac1L\sum_{r=1}^L\psi(Z_r)\right|^2
 \le e_L^2.
 \tag{22}
\]

Averaging (21) and using Cauchy–Schwarz in (22) yields

\[
 \boxed{
 \left|\mathbb E_\nu\phi(Z_0)\psi(Z_1)\right|
 \le\|\phi\|_\infty e_L
       +\frac{2B}{L}\sum_{r=1}^L\frac{r}{k+r}
 \le\|\phi\|_\infty e_L+B\frac{L+1}{k}.}
 \tag{23}
\]

**First send \(k\to\infty\) with \(L\) fixed, then \(L\to\infty\).** The right side tends to zero. Separate SI estimates at each fixed scale would not justify this order.

For a positive rational lag \(h\), use the ratio \((h+r/k)/h\) in (20). The error becomes at most \(2Br/(kh+r)\), and the grid beginning at \(h\) has the same bound (22). This proves independence at lag \(h\). Negative lags follow by stationarity and exchanging the two tests; arbitrary origins follow by rational translation. Products of bounded continuous tests determine the pair law, proving (18). QED.

### Where this proof stops for an actual integer-stationary law

Without rational invariance, (19), (20), and the **second** equality in (22) cannot be asserted in the displayed forms. Translation by 1 in the first equality of (22) is already allowed by integer stationarity; the missing step is identifying the fine-grid law under \(\nu\) with \(R_k\nu\). At a general rational lag \(h\), translation by \(h\) would need separate justification as well. The valid dilation comparison is (17); the fine-grid SI controls

\[
 \mathbb E_{P_k\nu}\left|\frac1L\sum_{r=1}^L\psi(Z_{r/k})\right|^2,
 \tag{24}
\]

not that expression under \(\nu\). Thus the obstacle is a residue average on the **whole law**, not a harmless endpoint discrepancy. Section 6 keeps that average throughout.

## 4. Two full-field model audits

### 4.1 Real slopes: annuli and separate-scale SI, but not uniform SI

Let \(U\) be Haar on \(\mathbb T=\mathbb R/\mathbb Z\), independently let \(V\) have probability density \(v^{-2}1_{v\ge1}\,dv\), and, for \(t>0\), let \(\nu_t\) be the law

\[
 Z_q=Q_D(\{U+qV/t\})\qquad(q\in\mathbb Q).
 \tag{25}
\]

All rational translations preserve this law: condition on \(V\) and translate the Haar phase. All coordinates have marginal \(F\). Direct application of the actual branches in (3) gives

\[
 R_k\nu_t=\nu_{kt}.
 \tag{26}
\]

Indeed, each branch has slope \(V/(kt)\), and its phase \(U+rV/(kt)\) is still conditionally Haar. With \(w=V/t\),

\[
 t\nu_t=\int_{1/t}^{\infty}\lambda_w\,\frac{dw}{w^2},
 \qquad \lambda_w=\mathcal L\bigl((Q_D(\{U+qw\}))_{q\in\mathbb Q}\bigr).
 \tag{27}
\]

This is an equality of finite measures. Its lower endpoint decreases as \(t\) increases, so \(t\nu_t\) is increasing. Thus this model satisfies all the annuli, not just a pairwise approximation to them.

For noninteger \(w\), conditional current is \(1-2\{w\}\): the rank increases on a set of phase length \(1-\{w\}\) and decreases on its complement. The exceptional integer slopes have zero probability. Therefore

\[
 \begin{aligned}
 J(\nu_1)
 &=\sum_{n=1}^{\infty}\left(
       \frac1n+\frac1{n+1}-2\log\frac{n+1}{n}\right)\\
 &=2\gamma-1=0.1544313298\ldots>0.
 \end{aligned}
 \tag{28}
\]

The partial sum through \(n=N\) is
\(H_N+H_{N+1}-1-2\log(N+1)\), proving the value without a numerical integration claim.

For each fixed \(t\) and each fixed nonzero rational AP step \(d\), the circle rotation by \(dV/t\) is irrational almost surely. The mean ergodic theorem on that rotation, followed by dominated convergence in \(V\), proves coordinate AP SI **at that scale**.

But as \(t\to\infty\), the whole field converges in finite-dimensional distribution to
\((Q_D(U))_{q\in\mathbb Q}\), a constant field. For any nonconstant centered continuous \(\psi\) and each fixed \(L\),

\[
 \lim_{t\to\infty}\mathbb E_{\nu_t}
 \left|\frac1L\sum_{r=1}^L\psi(Z_r)\right|^2
 =\int|\psi|^2\,dF>0.
 \tag{29}
\]

Consequently the \(R_k\nu_1=\nu_k\) orbit fails (6). Also, for every \(\eta>0\),
\(\nu_t\{|Z_1-Z_0|<\eta\}\to1\). There are no adjacent ties at any fixed \(t\), but diagonal nonconcentration is **not uniform in \(t\)**. This is not a countermodel to the requested structural package or the actual LPF inputs.

A fixed positive convex mixture of this family with a good SI family does not repair the defect: the nonnegative mean-square expression retains the positive-weight contribution in (29).

### 4.2 Haar characters: good whole law, bad componentwise/continuity shortcuts

Let \(\mathcal H=\operatorname{Hom}(\mathbb Q,\mathbb T)\), with the compact topology of pointwise convergence and Haar probability. Take \(\chi\) Haar in \(\mathcal H\), independently take \(U\) Haar in \(\mathbb T\), and set

\[
 Z_q=Q_D(\{U+\chi(q)\});\qquad\text{write its law as }\nu_H.
 \tag{30}
\]

For every nonzero rational \(h\), evaluation \(\chi\mapsto\chi(h)\) is an onto compact-group homomorphism, hence has Haar distribution. Thus every distinct pair of rank coordinates is independent Haar, and every distinct output pair has law \(F\otimes F\). The character map \(\chi(q)\mapsto\chi(q/k)\) is a compact-group automorphism. Consequently

\[
 (A_s)_*\nu_H=\nu_H,\qquad (D_{1/k})_*\nu_H=\nu_H,
 \qquad R_k\nu_H=\nu_H.
 \tag{31}
\]

Annuli are exactly \((l-k)\nu_H\). For every nonzero AP step, every \(k\), and every centered \(\psi\),

\[
 \mathbb E_{R_k\nu_H}\left|\frac1L\sum_{r=1}^L\psi(Z_{dr})\right|^2
       =\frac1L\int|\psi|^2\,dF.
 \tag{32}
\]

This model also has uniform adjacent diagonal nonconcentration.

Nevertheless, \(\chi\) is a recoverable invariant parameter of the integer shift: from the output one recovers \(U=F(Z_0)\) modulo 1 and
\(\chi(q)=F(Z_q)-F(Z_0)\) modulo 1. Conditional on \(\chi\), time translation is the circle rotation
\(U\mapsto U+\chi(1)\). Almost surely \(\chi(1)\) is irrational, so these conditional systems are ergodic and totally ergodic, but their adjacent currents are

\[
 J(\nu_H\mid\chi)=1-2\{\chi(1)\},
 \tag{33}
\]

nonzero almost surely. Dilations move the parameter \(\chi\); they do not preserve each component. Whole-law independence therefore cannot be passed to ergodic components. Componentwise annuli have not been established and are not being used.

Nor is this rational translation action strongly continuous for the **usual real topology** on \(\mathbb Q\). For any nonconstant centered coordinate test,

\[
 \|\psi(Z_{1/n})-\psi(Z_0)\|_{L^2(\nu_H)}^2
       =2\int|\psi|^2\,dF\qquad(n\ge1).
 \tag{34}
\]

Thus the numerical convergence \(1/n\to0\) supplies no Koopman strong convergence to the identity. A Mautner-style shortcut requiring this continuity, or requiring dilations to act on an individual component, is invalid here. The full-field use of Haar \(\operatorname{Hom}(\mathbb Q,\mathbb T)\) is important: the older model with a representative real slope \(V\in[0,1)\) is not automatically dilation-invariant at rational coordinates.

## 5. Additional conditional theorems for actual ordinary prefixes

These results concern the ordinary shift laws on \([0,1]^{\mathbb Z}\), denoted here by

\[
 \mu_X=\frac1X\sum_{n\le X}\delta_{(f(n+h))_{h\in\mathbb Z}},
 \qquad Tz=(z_{h+1})_h.
 \tag{35}
\]

They do not declare an arbitrary ergodic component of an affine model to be an actual prefix limit.

### 5.1 Prefix domination below an ergodic endpoint

Suppose \(\mu_{X_j}\Rightarrow\mu\) and \(\mu\) is \(T\)-ergodic. For every fixed \(0<c\le1\),

\[
 \mu_{\lfloor cX_j\rfloor}\Rightarrow\mu.
 \tag{36}
\]

Indeed, any subsequential limit \(\eta\) is stationary and satisfies \(\mu\ge c\eta\), by subtraction of prefixes. An invariant probability absolutely continuous with respect to an ergodic invariant probability must equal it. Compactness then proves convergence of the entire sequence in (36). The same argument shows, for each fixed \(B>1\), uniform weak convergence of \(\mu_Y\) to \(\mu\) for \(X_j/B\le Y\le X_j\): otherwise take a subsequence with \(Y_j/X_j\to c\in[1/B,1]\).

There is **no corresponding conclusion for larger endpoints** \(cX_j\), \(c>1\), from ergodicity of \(\mu\) alone. Domination then has the opposite direction and allows extra components.

### 5.2 Total ergodicity: residue conditionals really can be removed

Assume, additionally, that \(\mu\) is totally ergodic. Fix an integer \(k\). Form the normalized residue-conditioned laws at scale \(X_j\), with starting indices \(n\equiv r\pmod k\). Each limiting law \(\eta_r\) is \(T^k\)-invariant, and

\[
 \mu=\frac1k\sum_{r=0}^{k-1}\eta_r,
 \qquad \eta_r\le k\mu.
 \tag{37}
\]

Since \(\mu\) is \(T^k\)-ergodic, \(\eta_r=\mu\) for every \(r\). This is a justified removal of a residue condition, not ordinary stationarity being mistaken for it.

Let \(D_k^{\mathbb Z}z=(z_{kh})_{h\in\mathbb Z}\). Decimating the residue-0 law gives windows \((f(k(m+h)))_h\). Fixed-multiplier stability identifies its limit with the prefix law at \(X_j/k\), which is \(\mu\) by (36). Hence

\[
 (D_k^{\mathbb Z})_*\mu=\mu\qquad(k\ge1).
 \tag{38}
\]

All positive-lag pair correlations equal the lag-1 correlation. Average that equality over the lag and use the mean ergodic theorem under \(\mu\); the result is the product of the one-coordinate means. Thus every distinct **integer** pair has law \(F\otimes F\). This argument does not assert rational-translation invariance of the full affine lift.

### 5.3 Ordinary ergodicity suffices using arbitrarily slow logarithmic windows

For the actual \(f\), total ergodicity in the conclusion above can be weakened to ordinary ergodicity by using additional arithmetic information.

Theorem `theo_bincorr` of Teräväinen, arXiv:1710.01195, applies for **every** function

\[
 1\le\omega(X)\le\log(3X),\qquad\omega(X)\to\infty,
 \tag{39}
\]

however slowly it diverges. Applying it to the real multiplicative frozen smooth cutoffs \(1_{P(n)\le X^a}\), using their fixed-modulus AP distribution, gives, for each fixed \(h\ne0\) and \(a,b\in(0,1)\),

\[
 \frac1{\log\omega(X)}
 \sum_{X/\omega(X)<n\le X}
 \frac{1_{f(n)\le a}1_{f(n+h)\le b}}n
       \longrightarrow F(a)F(b).
 \tag{40}
\]

For completeness, moving versus frozen cutoffs cause no new uniformity assertion: throughout this window \(\log n/\log X=1+o(1)\). For any fixed \(\epsilon>0\), sandwich the moving thresholds between frozen exponents \(a\pm\epsilon,b\pm\epsilon\), apply the theorem, then let \(\epsilon\downarrow0\). Fixed shifts do not affect this sandwich. The theorem permits the multiplicative cutoffs to depend on \(X\); it is not being applied to the nonmultiplicative moving cutoff directly.

Now suppose just that the actual prefix limit \(\mu\) in (35) is ergodic. By §5.1, choose numbers \(\omega_j\to\infty\) sufficiently slowly, with \(\omega_j\le\log(3X_j)\), so that the prefix laws for **all** \(Y\in[X_j/\omega_j,X_j]\) tend uniformly weakly to \(\mu\). One can choose \(\omega_j\) nondecreasing by diagonalization and extend these values to a function as in (39).

For a bounded continuous cylinder test \(H\), Abel summation gives

\[
 \frac1{\log\omega_j}\sum_{X_j/\omega_j<n\le X_j}\frac{H(T^nf)}n
 =\frac1{\log\omega_j}
   \int_{X_j/\omega_j}^{X_j}\left(\int H\,d\mu_t\right)\frac{dt}{t}
   +O\!\left(\frac{\|H\|_\infty}{\log\omega_j}\right).
 \tag{41}
\]

The boundary terms are bounded prefix means; rounding produces no difficulty. Uniform prefix convergence makes (41) tend to \(\int H\,d\mu\). Thus these logarithmic-window laws converge to \(\mu\) itself. But (40) makes their distinct-coordinate pair laws converge to \(F\otimes F\). Therefore the ordinary-prefix limit \(\mu\) has independent distinct integer pairs.

**Scope of this deduction.** It uses the arbitrary-slow window theorem, not just global logarithmic density, one prescribed choice \(\omega=\log X\), or the abstract annulus/USI package. It is conditional on the **whole actual ordinary-prefix limit** being ergodic. It neither proves that all actual limits are ergodic nor applies (40) to arbitrary components. The nonreversible rotation components in §4.2 are consequently no contradiction.

## 6. The new integer-stationary question

### 6.1 Precise package being tested

Let \(\nu\) be a probability on \([0,1]^{\mathbb Q}\), with operators exactly as in (3). Assume:

* **IS:** \((A_1)_*\nu=\nu\);
* **ANN:** \(lR_l\nu-kR_k\nu\ge0\) for every integer \(l>k\ge1\);
* **USI-AP:** (6) for each fixed positive integer step \(d\), with one rate for the entire \(R_k\)-orbit at that step.

The target is \(J(\nu)=0\), not necessarily all-pair independence. The countermodel sought would need to satisfy these properties as full probability laws, not just provide pair marginals or Gram matrices. Requiring in addition all rational marginals to be \(F\), as actual laws have, does not affect any of the partial deductions below.

### 6.2 What nearby annuli and USI actually prove

For bounded \(\phi\), bounded \(F\)-centered \(\psi\), and \(B=\|\phi\|_\infty\|\psi\|_\infty\), set

\[
 c_m=\mathbb E_{P_m\nu}\phi(Z_0)\psi(Z_1)
     =\mathbb E_{R_m\nu}\phi(Z_0)\psi(Z_m).
 \tag{42}
\]

The second equality is exactly (12), with the average retained. By (16),

\[
 \left|c_{K+r}-\mathbb E_{R_K\nu}\phi(Z_0)\psi(Z_{K+r})\right|
       \le 2B\frac{r}{K+r}.
 \tag{43}
\]

The block \(Z_{K+1},\ldots,Z_{K+L}\) under \(R_K\nu\) obeys (6) by integer stationarity. Cauchy–Schwarz gives the rigorous replacement for (23):

\[
 \boxed{
 \left|\frac1L\sum_{r=1}^L c_{K+r}\right|
 \le\|\phi\|_\infty e_L
       +\frac{2B}{L}\sum_{r=1}^L\frac{r}{K+r}
 \le\|\phi\|_\infty e_L+B\frac{L+1}{K}.}
 \tag{44}
\]

This proves local Cesàro cancellation for the sequence of **\(P_m\)-correlations**, not for \(c_1\). No rational translation of \(\nu\) was used.

Each \(P_m\nu\) has marginal \(F\) at its integer coordinates: use (12) and the integer-coordinate marginals of \(R_m\nu\). Consequently (44), for all continuous product tests, proves

\[
 \mathcal L_{\bar\nu_{K,L}}(Z_0,Z_1)\Rightarrow F\otimes F,
 \quad
 \bar\nu_{K,L}=\frac1L\sum_{r=1}^L P_{K+r}\nu,
 \quad L\to\infty,\ K/L\to\infty.
 \tag{45}
\]

Products determine measures on the compact square. Since \(F\) is atomless, the diagonal has zero \(F\otimes F\) mass, so the ordering test also passes to this limit:

\[
 J(\bar\nu_{K,L})=\frac1L\sum_{r=1}^L J(P_{K+r}\nu)\longrightarrow0
 \quad\text{in the regime of (45)}.
 \tag{46}
\]

This step does not assume a uniform diagonal estimate for the separate \(P_m\nu\)'s; it uses the already identified weak limit of the averaged pair laws. The same argument also gives
\(\lim_{L\to\infty}\limsup_{K\to\infty}|L^{-1}\sum_{r=1}^L J(P_{K+r}\nu)|=0\).

If \(\nu\) were rationally invariant, every \(c_m\) would equal \(c_1\), and (44) would recover §3. Without that condition the equality is precisely what has not been proved.

### 6.3 The AP version and rationally invariant averaged limits

Fix a positive rational lag \(h=a/b\), with positive integers \(a,b\), and put
\(c_m(h)=\mathbb E_{P_m\nu}\phi(Z_0)\psi(Z_h)\). Restrict to \(m=b(K+r)\), so that \(mh=a(K+r)\) is an integer. Comparing \(R_{b(K+r)}\nu\) to \(R_{bK}\nu\) and using the step-\(a\) version of (6) gives

\[
 \boxed{
 \left|\frac1L\sum_{r=1}^L c_{b(K+r)}(a/b)\right|
       \le\|\phi\|_\infty e_{L,a}(\psi)
                       +B\frac{L+1}{K}.}
 \tag{47}
\]

The proof uses the actual average of the endpoint coordinates
\(aK+a,\ldots,aK+aL\) under \(R_{bK}\nu\). If the origin is another rational whose denominator divides \(b\), it may be shifted to 0 under each \(P_{b(K+r)}\nu\), because those **averaged** laws are invariant under that shift.

There is therefore a genuine, but different-law, consequence: by convex averages of invariantizations one can obtain a rational-translation-invariant law with all distinct rational-coordinate pairs independent. To see the quantifiers, enumerate continuous pair tests and their rational coordinates. At stage \(j\), choose \(b_j\) divisible by their first \(j\) denominators and by \(j!\). Choose \(L_j\) large enough for the finitely many AP errors in (47), with integer steps \(b_jh\), to be small; each of these steps is fixed during that choice. Then choose \(K_j\gg L_j\) and take

\[
 \lambda_j=\frac1{L_j}\sum_{r=1}^{L_j}P_{b_j(K_j+r)}\nu.
 \tag{48}
\]

Every \(\lambda_j\) is invariant under \(A_{1/b_j}\). Compactness, (47), and the diagonal choice show that any selected limiting law is rationally invariant and has the claimed pair laws. This argument **does not** assert a rate uniform over growing AP steps; the choices of \(L_j\) are made after the finite set of steps is fixed. It also does not say \(\lambda_j\Rightarrow\nu\), or make the limit an actual prefix law.

### 6.4 Why projection and asymptotic-regularity shortcuts remain incomplete

Several tempting inversions have exact algebraic obstructions.

* Although \(d_{\rm TV}(R_{K+1}\nu,R_K\nu)\le1/(K+1)\), pushing by \(D_K\) gives (17). It does not compare \(\nu\) directly with a small dilation of itself. The numerator-residue average on the right also remains present.
* \(R_l\) is not invertible on integer-stationary measures. For example, (13) gives
  \[
  R_lP_k\nu=R_l\nu\qquad\text{whenever }k\mid l.
  \tag{49}
  \]
  Thus this operator annihilates \(P_k\nu-\nu\). Commutation of the \(R_l\)'s supplies no inverse that recovers this difference.
* The two mixed expressions in (13) need not agree; they do agree when \(k,l\) are coprime. For \(g=\gcd(k,l)\), a useful exact form is
  \[
  R_lP_k\nu=(D_{k/g})_*R_{kl/g}\nu,
  \qquad P_kR_l\nu=(D_k)_*R_{kl}\nu.
  \tag{50}
  \]
  In particular, for each **fixed** \(k\), the orbit of \(P_k\nu\) inherits unit-step coordinate SI from the finitely many AP rates with steps dividing \(k\); at a fixed step \(d\), use steps \(d\) times those divisors. This is not a common SI rate as \(k\to\infty\), and annuli for \(P_k\nu\) do not follow by simply pushing annuli for \(\nu\).
* A weak limit of \(P_{n!}\nu\) is rationally invariant. But (13) prevents automatic passage of the original annuli through these projections, and (50) does not give the necessary uniform SI in \(n\). Even if both were separately established for a limit, it would be a new averaged law, not automatically \(\nu\).

The valid quantitative conclusions of the nearby-scale method are (44) and (47). An additional residue-alignment assertion, for example convergence of the relevant \(P_m\nu\) pair tests back to those of \(\nu\), would close this method. It has not been derived from IS+ANN+USI-AP. The assertion that finite rational grids approximate the original law has no topological justification: the rational action need not be strongly continuous, as (34) demonstrates.

**Whole-law shortcut ruled out, not the current conclusion.** The [3-adic companion audit](PadicAnnulusCounterexampleResearch.md), especially §§6–9, gives a full law satisfying this package with \(R_k\nu=\nu\) for all \(k\), yet \(\nu\perp(A_{1/3})_*\nu\) and \(d_{\rm TV}(P_3\nu,\nu)=2/3\). This is an exact counterexample to deriving rational translation invariance of the whole law from IS+ANN+USI-AP. Every distinct pair in that example already has law \(F\otimes F\), so it has \(J=0\): it does **not** refute the pair-test alignment assertion in the preceding paragraph or resolve (60).

### 6.5 A uniform-SI skew residue model, and the exact annulus failure

This example tests whether simply concentrating an orientation bias on one rational residue can evade §3.

Let \((U_n)_{n\in\mathbb Z}\) be the two-sided stationary Markov chain on \(\mathbb T\) with Haar marginal and transition

\[
 K(u,dv)=\theta\,\delta_{u+\alpha}(dv)+(1-\theta)\,dv,
 \qquad \theta=\tfrac12,\quad\alpha=\tfrac13.
 \tag{51}
\]

At each step, continue by a rotation with probability \(\theta\); otherwise reset to an independent Haar point. Independently take Haar variables \(W_q\) for all \(q\in\mathbb Q\setminus\mathbb Z\), and define a law \(\eta\) by

\[
 Z_q=\begin{cases}
 Q_D(U_q),&q\in\mathbb Z,\\
 Q_D(W_q),&q\notin\mathbb Z.
 \end{cases}
 \tag{52}
\]

This law is integer-stationary, has marginal \(F\) at every rational coordinate, and is not rationally invariant. Its adjacent current is

\[
 \boxed{J(\eta)=\theta(1-2\alpha)=\tfrac16.}
 \tag{53}
\]

There are no adjacent ties. Noninteger translates of the pair \((Z_0,Z_1)\) consist of two independent coordinates, with current zero.

Here uniform SI is especially strong. For centered \(\psi\), put \(\sigma^2=\int|\psi|^2dF\). The transition identity

\[
 K^h=\theta^h\,\text{rotation by }h\alpha
                      +(1-\theta^h)\,\text{Haar reset}
 \tag{54}
\]

implies the absolute covariance bound \(\theta^{|m-n|}\sigma^2\) between integer coordinates. All other distinct coordinates are independent of one another and of this chain. For **any** \(L\) distinct rational indices \(q_1,\ldots,q_L\), sum covariances using at most two integer indices at each positive integer distance from a given index. This gives

\[
 \mathbb E_\eta\left|\frac1L\sum_{i=1}^L\psi(Z_{q_i})\right|^2
 \le\frac{\sigma^2}{L}\left(1+2\sum_{h\ge1}\theta^h\right)
 =\frac{3\sigma^2}{L}.
 \tag{55}
\]

Every actual branch \(G_{k,r}\) sends distinct coordinates to distinct coordinates. Applying (55) branch by branch and then taking their average proves the same bound under every \(R_k\eta\), for every AP and in fact every set of distinct coordinates. Thus this candidate really passes uniform SI; it is not using a separate-scale argument.

The exact invariantized currents are

\[
 J(P_k\eta)=\frac1k\sum_{r=0}^{k-1}
       \mathbb E_\eta\operatorname{sgn}(Z_{1+r/k}-Z_{r/k})
       =\frac1{6k}.
 \tag{56}
\]

Only \(r=0\) sees the special integer chain. This explicitly demonstrates how averaged currents can vanish while the original current remains nonzero, **if annuli are dropped**.

The annuli fail maximally, however. The law \(\eta\) is mixing for the integer shift: it is the product of a mixing reset chain and countably many independent bilateral iid streams, one for each noninteger coset modulo \(\mathbb Z\). Also, \(R_k\) sends any integer-shift-ergodic law to an integer-shift-ergodic law. Indeed, if \(E\) is \(A_1\)-invariant, \(G_{k,0}^{-1}E\) is \(A_1\)-invariant because \(G_{k,0}A_1=A_kG_{k,0}\); all branches have the same probability on \(E\). That probability is 0 or 1.

Under \(R_k\eta\), the current at lag \(k\) is \(1/(6k)\): in the branch average precisely one residue yields two successive special-chain coordinates. Under \(R_{k+1}\eta\), the current at lag \(k\) is zero: two such coordinates differ by \(k/(k+1)\), so they cannot both belong to the special integer chain. The two stationary ergodic laws are therefore distinct, and the ergodic theorem for this bounded lag-current test separates them by a measurable invariant set. Consequently

\[
 \boxed{d_{\rm TV}(R_k\eta,R_{k+1}\eta)=1\qquad(k\ge1),}
 \tag{57}
\]

contrary to the annulus bound \(1/(k+1)\). Already \(\eta\le2R_2\eta\) fails.

There is a useful further warning: \(R_k\eta\) does converge weakly to the iid rational-coordinate law. For any fixed finite set of distinct rational indices, when \(k\) exceeds their diameter, at most one of their images in each branch can be an integer. Their joint law is then **exactly** product \(F\). Thus finite-cylinder convergence of neighboring scales can coexist with TV distance 1. It is not a substitute for full annulus positivity. Adjacent diagonal nonconcentration is uniform in this orbit as well: for \(k\ge2\) the adjacent pair is independent, and for \(k=1\) it is the single atomless-adjacent-pair law (51).

### 6.6 Another failed interpolation: rational floor clocks

A related attempt tries to avoid continuous real-slope collapse by using only rational speeds. It fails even the domination part of annuli.

Take a stationary chain \((Y_n)\) with almost surely unequal successive values, for example (51) after applying \(Q_D\). For a reduced positive rational \(s=a/b\), let \(\lambda_s\) be the field law
\(Z_q=Y_{\lfloor sq+\Theta\rfloor}\), where \(\Theta\) is independent and uniform on \(\{0,1/b,\ldots,(b-1)/b\}\). Integer translation permutes these phases, with integer shifts of the stationary chain, so \(\lambda_s\) is integer-stationary.

Here the residue average, rather than an illicit unaveraged dilation, gives exactly

\[
 R_k\lambda_s=\lambda_{s/k}.
 \tag{58}
\]

Indeed the phases are \(j/b+ar/(bk)\). Modulo 1 they are uniform on the grid of denominator \(bk/\gcd(a,k)\), which is the reduced denominator of \(s/k\); each occurs \(\gcd(a,k)\) times. Integer phase overflows are absorbed by stationarity of \(Y\).

The different speeds are measurably identifiable from the rationally observed step-function paths: all successive jumps are nonzero and their spacing is \(1/s\). Thus the \(\lambda_s\)'s are mutually singular on disjoint speed events. If a probability mixture \(\lambda=\sum_{s\in\mathbb Q_{>0}}w_s\lambda_s\) satisfied \(\lambda\le kR_k\lambda\) for all \(k\), the speed-\(s\) event would give

\[
 w_s\le k w_{ks}\quad\text{for every }k\ge1.
 \tag{59}
\]

For any \(w_s>0\), summing \(w_{ks}\ge w_s/k\) over distinct speeds \(ks\) contradicts finiteness of the mixture. Hence this rational-clock proposal supplies no annulus countermodel. Formula (58) explicitly includes the actual phase average; replacing it by a single root phase would be a different and incorrect construction.

## 7. What is and is not established

| Claim or model | Annuli | Uniform orbit coordinate SI | Conclusion/scope |
|---|---|---|---|
| Actual affine prefix laws | Yes | Yes, at each fixed AP step | Rational translation invariance and zero current are not proved here |
| Rationally invariant law satisfying the package | Assumed | Assumed | Every distinct rational pair is independent (§3) |
| Real slopes \(\nu_t\) | Yes | **No** | Nonzero current is not a counterexample to the package |
| Haar-character law \(\nu_H\) | Yes | Yes | Zero whole-law current; nonreversible ergodic components; no real-topology strong continuity |
| Special-residue reset-chain law \(\eta\) | **No**, consecutive TV = 1 | Yes, bound (55) | A precise obstruction to forgetting the projection, not a complete countermodel |
| Rational floor-clock probability mixtures | **No**, domination already impossible | Not needed for the rejection | Countable-speed mass obstruction (59) |
| Actual ordinary-prefix limit assumed ergodic | Actual-prefix input | Available, but not the decisive extra input in §5.3 | Independent integer pairs using arbitrary-slow logarithmic windows |

The unresolved structural implication is exactly

\[
 \text{IS + ANN + USI-AP}\quad\stackrel{?}{\Longrightarrow}\quad J(\nu)=0.
 \tag{60}
\]

The rigorous advance here is (44)–(48), not (60). All proposed shortcuts through \(P_k\), components, or continuity have their missing hypotheses displayed. No law with nonzero current has been claimed to satisfy all of IS, ANN, and USI-AP. No abstract law has been claimed to be an actual natural-prefix LPF law. In particular, nothing in this note is an actual LPF disproof or a completion of the existing Spec placeholders.

## 8. Sources and verification record

### Checked local sources

* `Submission/FurstenbergObstructionResearch.md`, especially §§1, 4, 5: actual prefix marginals and SI; the distinction between coordinate invariant projections and ergodicity; the integer-index affine rotation model; the residue condition in the actual dilation identity. Its topological non-unique-ergodicity conclusion concerns the orbit closure, not a theorem that all actual prefix laws are nonergodic.
* `/corpus/src/1710.01195/binary_correlations_arxiv2.tex`, J. Teräväinen, *On binary correlations of multiplicative functions*: `def1` at lines 34–39; `theo_bincorr` at lines 54–58, with arbitrary divergence of \(\omega\) and any fixed nonzero shift; the discussion of scale-dependent functions at lines 79–86; `le_mr` and its untruncated-function remark at lines 549–555; the fixed-AP smooth-number estimate `eqq90` at lines 665–669. Section 5.3 uses the stronger arbitrary-slow-window statement, not just `theo_density` on global logarithmic density.
* `/corpus/src/1904.05096/main.tex`, T. Tao–J. Teräväinen, *Value patterns of multiplicative functions and related sequences*: the **normalized** SI definition at lines 214–219 and the smooth-band application at lines 1127–1135. The input used here has the \(1/x\) averaged normalization in the definition; the isolated unnormalized integral display at line 1133 is not read as a claim that an unnormalized integral tends to zero. The normalized estimate is also explicit in the cited `le_mr` source.

### Verification performed

The proofs above are mathematical arguments, not Lean formalizations. Exact rational-arithmetic checks were run for the finite affine/residue identities:

* 731 checks of the branch composition convention, \(D_kG_{k,r}=A_{r/k}\), the complete \(R_kR_l\) residue enumeration, and \(P_kP_l=P_{\operatorname{lcm}(k,l)}\), for parameters through 17;
* 3,654 exact checks of the phase-multiplicity identity used in (58), for reduced speeds and branch moduli through 18;
* 400 further exact checks of both mixed-operator orders in (50) and the pushed-annulus average in (17), for parameters through 20;
* the reset-chain identities \(\theta(1-2\alpha)=1/6\) and \((1+\theta)/(1-\theta)=3\), with exact fractions, and finite-circle checks of the two lag-current computations distinguishing \(R_k\eta\) and \(R_{k+1}\eta\), through \(k=30\);
* a high-precision sanity check of the *proved* current formula (28): \(2\gamma-1=0.154431329803065721213024180165\ldots\); the interval sum through 10,000 differs by approximately \(1.66633338166\times10^{-9}\).

The Markdown audit checked balanced math delimiters and the unique sequential equation tags 1–60. A saved SHA-256 manifest was used to verify that every pre-existing top-level Submission file remained unchanged.

These finite/numerical checks certify conventions and normalizations, not an asymptotic solution of (60). The TV separation in (57), all infinite-field consistency assertions, and all limiting arguments are proved in the text rather than inferred from simulations.

`Submission/Spec.lean` retained SHA-256

`d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.

Only this new research note is intended as an output; no pre-existing Submission file is edited.
