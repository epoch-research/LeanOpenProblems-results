# A 3-adic countermodel to the whole-law rational-translation-invariance route

## Outcome and scope

**Independent audit: the proposed construction is valid.** With the operators and quantifiers in [AffineAnnulusResearch.md](AffineAnnulusResearch.md), §§1–2 and §6.1, it gives a Borel probability law on \([0,1]^{\mathbb Q}\) having:

* integer stationarity, and in fact exact rational-translation stabilizer \(\mathbb Q\cap\mathbb Z_3\);
* \(R_k\nu=\nu\) for every positive integer \(k\), so all full-law annulus inequalities hold;
* independent identically distributed coordinates at **every distinct pair** of rational indices, with uniform marginals or, after the invertible quantile transform, Dickman marginals;
* exact uniform coordinate SI with mean square \(L^{-1}\int|\psi|^2\,dF\), for every centered square-integrable test and any \(L\) distinct rational coordinates;
* nevertheless, \(\nu\perp(A_{1/3})_*\nu\).

This disproves only the abstract inference

\[
 \mathrm{IS+ANN+USI\text{-}AP}
 \quad\Longrightarrow\quad
 (A_s)_*\nu=\nu\quad\text{for every }s\in\mathbb Q.
\]

It does so even with all rational-coordinate Dickman marginals and pair independence. **The constructed current is \(J(\nu)=0\), not nonzero. This is not a disproof of \(\mathrm{IS+ANN+USI\text{-}AP}\Rightarrow J=0\), not a disproof of the rationally invariant conditional theorem in §3 of the companion note, and not a theorem or disproof about actual largest-prime-factor (LPF) prefix laws or Erdős 371.** No realization as an actual LPF law is claimed. No `Spec` or Lean file is edited, and the arguments here are mathematical proofs, not Lean formalizations.

## 1. The exact package and action convention

Let \(\Omega=[0,1]^{\mathbb Q}\), with its countable-product Borel sigma-algebra. For \(s\in\mathbb Q\), \(a\in\mathbb Q_{>0}\), and integers \(k\ge1\), \(0\le r<k\), use precisely

\[
 (A_s z)_q=z_{q+s},\qquad (D_a z)_q=z_{aq},\qquad
 G_{k,r}=A_rD_{1/k},\qquad
 R_k\lambda=\frac1k\sum_{r=0}^{k-1}(G_{k,r})_*\lambda.
\]

In particular, \((G_{k,r}z)_q=z_{(q+r)/k}\); reversing the composition order would be incorrect. The package being tested is:

\[
 \begin{aligned}
 \mathrm{IS}:&\quad (A_1)_*\nu=\nu,\\
 \mathrm{ANN}:&\quad lR_l\nu-kR_k\nu\ge0\quad(l>k\ge1),\\
 \mathrm{USI\text{-}AP}:&\quad
 \sup_{k\ge1}\mathbb E_{R_k\nu}
 \left|\frac1L\sum_{j=1}^{L}\psi(Z_{dj})\right|^2
 \le e_{L,d}(\psi)^2\longrightarrow0
 \end{aligned}
\]

for each fixed positive integer \(d\) and bounded measurable \(F\)-centered coordinate test \(\psi\). Here \(F\) denotes the specified one-coordinate distribution. ANN is positivity of measures on the entire field space, not merely a statement about pairs. USI-AP is uniform in \(k\), not a separate convergence assertion at each scale.

## 2. Latent probability space and measurability

Embed \(\mathbb Q\) in \(\mathbb Q_3\). Normalize the valuation by \(v_3(3)=1\), and write \(\lambda_3\) for additive Haar probability on \(\mathbb Z_3\). Take

\[
 U\sim\lambda_3,\qquad
 \chi\sim m_{\mathcal K},\qquad
 \mathcal K=\operatorname{Hom}((\mathbb Q^2,+)_{\mathrm{disc}},\mathbb T),
 \quad\mathbb T=\mathbb R/\mathbb Z,
\]

independently. The topology on \(\mathcal K\) is pointwise convergence. It is a closed subgroup of \(\mathbb T^{\mathbb Q^2}\): the equations \(\chi(0)=0\) and \(\chi(v+w)=\chi(v)+\chi(w)\) are closed. Since \(\mathbb Q^2\) is countable, \(\mathcal K\) is a compact metrizable abelian group and has normalized Haar probability \(m_{\mathcal K}\).

**The discrete domain matters.** This is Haar measure on the compact dual of discrete \(\mathbb Q^2\), not a requirement of real- or 3-adic continuity on the domain, and not a choice of two independent circle phases followed by arbitrary rational roots.

Every singleton of \(\mathbb Z_3\) has Haar measure zero: it lies in a coset modulo \(3^n\) of mass \(3^{-n}\), for every \(n\). Thus the countable set \(\mathbb Q\cap\mathbb Z_3\) is null. Work on the Borel, full-measure set

\[
 H=\mathbb Z_3\setminus\mathbb Q.
\]

For every \(u\in H\), simultaneously for every \(q\in\mathbb Q\), \(u+q\ne0\). Define

\[
 c_q(u)=3^{-v_3(u+q)}\in\mathbb Q_{>0},\qquad
 w_q(u)=\begin{pmatrix}c_q(u)\\q\,c_q(u)\end{pmatrix}\in\mathbb Q^2,
 \qquad
 Z_q(u,\chi)=\operatorname{rep}_{[0,1)}\chi(w_q(u)).
\]

Let \(\nu_{\rm unif}\) be the law of this field. One may assign a fixed field (for example, the all-zero field) on the omitted null set without changing the law. The same formulas for \(c_q,w_q\) make sense on \(\mathbb Q_3\setminus\mathbb Q\), when needed for algebraic identities.

Here is the measurability check. For fixed \(q\), each set \(\{u:v_3(u+q)=n\}\), \(n\in\mathbb Z\), is Borel, and on it \(w_q(u)\) equals the fixed rational vector \((3^{-n},q3^{-n})^T\). Evaluation at a fixed vector is continuous on \(\mathcal K\). Partitioning into these countably many sets proves that \((u,\chi)\mapsto\chi(w_q(u))\) is Borel. The representative map \(\mathbb T\to[0,1)\) is Borel (it need not be continuous). Countably many measurable coordinates give a Borel map into \(\Omega\). This constructs the full infinite-field law directly; no unverified finite-dimensional consistency assumption is needed.

## 3. Haar evaluation and change of character

Three elementary compact-group facts justify the probabilistic steps.

1. **A nonzero vector evaluates to Haar circle measure.** For \(v\in\mathbb Q^2\setminus\{0\}\), the continuous homomorphism
   \(E_v:\mathcal K\to\mathbb T\), \(\chi\mapsto\chi(v)\), is onto. Given a real lift \(\alpha\) of a desired circle value, choose a real linear functional \(\ell\) with \(\ell(v)=\alpha\). Then \(x\mapsto\ell(x)\pmod1\), restricted to \(\mathbb Q^2\), is a character with the desired evaluation. The pushforward of Haar probability through an onto continuous homomorphism is Haar probability, by translation invariance and uniqueness.
2. **Two independent vectors evaluate to product Haar measure.** If \(v,v'\) are linearly independent over \(\mathbb Q\), their rational determinant is nonzero, so they are also independent over \(\mathbb R\). Given real lifts \(\alpha,\beta\), solve \(\ell(v)=\alpha\), \(\ell(v')=\beta\). This proves that \(\chi\mapsto(\chi(v),\chi(v'))\) is onto \(\mathbb T^2\), and its Haar pushforward is product Haar measure. The real-linear characters used here witness surjectivity; they are not a substitute definition of the random Haar character.
3. **Rational invertible matrices preserve the Haar-character law.** If \(M\in\mathrm{GL}_2(\mathbb Q)\), then
   \[
   T_M\chi=\chi\circ M
   \]
   is a continuous automorphism of \(\mathcal K\), with inverse \(T_{M^{-1}}\), so \(T_M\chi\) is Haar. If \(M\) is deterministic and \(U'\) is a function of \(U\), it remains independent of \(U'\).

These statements apply to \(U\)-dependent vectors by first fixing \(u\) and then integrating against \(\lambda_3\). Independence of \(U\) and \(\chi\), together with the measurability in §2, justifies this use of Fubini/conditioning.

## 4. Every distinct pair is conditionally independent uniform

For \(q\ne q'\),

\[
 \det\bigl(w_q(u),w_{q'}(u)\bigr)
 =c_q(u)c_{q'}(u)(q'-q)\ne0.
\]

Consequently, for every \(u\in H\), the conditional law of \((Z_q,Z_{q'})\) is two independent uniforms on \([0,1)\). This conditional pair law does not depend on \(u\), so the unconditional pair law is also product Lebesgue measure. Each coordinate has the uniform marginal. **This is pairwise independence, not joint independence of all coordinates.** The three-coordinate event in §7 detects information invisible to every pair law.

## 5. Translation transport: the sign is positive

For rational \(s\), direct calculation gives

\[
 c_{q+s}(u)=c_q(u+s),\qquad
 w_{q+s}(u)=S_s w_q(u+s),\qquad
 S_s=\begin{pmatrix}1&0\\s&1\end{pmatrix}.
\]

The lower-left entry is \(+s\), not \(-s\). If \(s\in\mathbb Q\cap\mathbb Z_3\), then \(U+s\) is Haar on \(\mathbb Z_3\); it is still outside \(\mathbb Q\) almost surely. Also \(\det S_s=1\), so \(\chi\circ S_s\) is Haar and independent of \(U+s\). Coordinatewise,

\[
 (A_s Z(u,\chi))_q
 =\operatorname{rep}_{[0,1)}(\chi\circ S_s)(w_q(u+s)).
\]

The latent pair on the right has the original product law. Therefore

\[
 (A_s)_*\nu_{\rm unif}=\nu_{\rm unif}
 \qquad(s\in\mathbb Q\cap\mathbb Z_3).
\]

In particular, IS holds, as does invariance under every integer translation. No invariance of Haar probability on \(\mathbb Z_3\) under nonintegral 3-adic translations has been asserted.

## 6. Branch transport and the full annuli

Fix \(k\ge1\), and write

\[
 k=3^a m=t m,\qquad a=v_3(k)\ge0,\qquad t=3^a,\qquad 3\nmid m.
\]

For a fixed branch \(0\le r<k\), put \(U'=kU+r\). The valuation identity

\[
 U+\frac{q+r}{k}=\frac{U'+q}{k}
\]

gives

\[
 c_{(q+r)/k}(U)=t\,c_q(U'),\qquad
 w_{(q+r)/k}(U)=M_{k,r}w_q(U'),\qquad
 M_{k,r}=\begin{pmatrix}t&0\\r/m&1/m\end{pmatrix}.
\]

Indeed the second coordinate on either side is \((q+r)c_q(U')/m\). Thus the lower-left entry is \(+r/m\), and \(\det M_{k,r}=t/m\ne0\). It follows that the branch field \(G_{k,r}Z\) is obtained from the same construction using

\[
 U'=kU+r,\qquad \chi'=\chi\circ M_{k,r}.
\]

For this branch, \(\chi'\) is Haar and independent of \(U'\). Multiplication by the unit \(m\) preserves Haar probability on \(\mathbb Z_3\), so \(U'\) has normalized Haar law on the coset \(r+t\mathbb Z_3\). Denote that law by \(\lambda_{k,r}\). As a measure on \(\mathbb Z_3\),

\[
 d\lambda_{k,r}=t\,1_{r+t\mathbb Z_3}\,d\lambda_3.
\]

Each residue class modulo \(t\) appears exactly \(m\) times among \(0\le r<tm\). Hence

\[
 \frac1k\sum_{r=0}^{k-1}\lambda_{k,r}
 =\frac1t\sum_{j=0}^{t-1}\lambda_{k,j}
 =\lambda_3.
\]

This is exact Haar measure on \(\mathbb Z_3\), not just equality of one finite residue distribution. Moreover the transformed character has the **same** Haar law in every branch. If the branch is chosen uniformly and independently at the outset, the joint latent law after transport is

\[
 \frac1k\sum_{r=0}^{k-1}(\lambda_{k,r}\otimes m_{\mathcal K})
 =\lambda_3\otimes m_{\mathcal K}.
\]

This explicitly checks independence after the branch average, despite the dependence of \(M_{k,r}\) on \(r\). The null rational set remains null, and \(kU+r\) cannot be rational when \(U\) is not rational. Pushing the last identity through the measurable field map proves

\[
 \boxed{R_k\nu_{\rm unif}=\nu_{\rm unif}\quad(k\ge1).}
\]

When \(3\mid k\), one must average the cosets; a single branch is not being claimed to have the original latent law. When \(3\nmid k\), every branch already has that law. In all cases,

\[
 \boxed{lR_l\nu_{\rm unif}-kR_k\nu_{\rm unif}
       =(l-k)\nu_{\rm unif}\ge0\quad(l>k\ge1).}
\]

These are equalities and inequalities of full Borel measures on \(\Omega\).

## 7. A measurable separating event and the exact stabilizer

Write \(\mathbf e(x)=\exp(2\pi i x)\), and define the closed three-coordinate cylinder

\[
 B=\{z\in\Omega:\mathbf e(z_0-2z_1+z_2)=1\}.
\]

### Under the original law: probability zero

The three elements \(u,u+1,u+2\) occupy the three different residue classes modulo 3. Exactly one is a nonunit, whose finite valuation is at least 1; the other two have valuation zero. Thus exactly one of \(c_0,c_1,c_2\) is in \((0,1/3]\), and the other two equal 1. The vector

\[
 v(u)=w_0(u)-2w_1(u)+w_2(u)
 =\begin{pmatrix}c_0-2c_1+c_2\\-2c_1+2c_2\end{pmatrix}
\]

is nonzero: its second component being zero would force \(c_1=c_2\), and then its first being zero would force \(c_0=c_1\), contrary to the pattern just established. As an integer linear combination of evaluations,

\[
 Z_0-2Z_1+Z_2=\chi(v(U))\pmod1.
\]

For each fixed \(u\), §3 makes \(\chi(v(u))\) Haar on \(\mathbb T\), which has no atom at 0. Integrating gives

\[
 \boxed{\nu_{\rm unif}(B)=0.}
\]

### Under the positive shift by \(1/3\): probability one

The pushforward convention tests the original coordinates \(1/3,4/3,7/3\). For every \(u\in H\),

\[
 v_3(u+1/3)=v_3(u+4/3)=v_3(u+7/3)=-1.
\]

All three corresponding \(c\)'s are 3, and their vectors are exactly

\[
 w_{1/3}(u)=\begin{pmatrix}3\\1\end{pmatrix},\qquad
 w_{4/3}(u)=\begin{pmatrix}3\\4\end{pmatrix},\qquad
 w_{7/3}(u)=\begin{pmatrix}3\\7\end{pmatrix}.
\]

Their second difference is zero. The event holds for every character, so

\[
 \boxed{((A_{1/3})_*\nu_{\rm unif})(B)=1,
 \qquad \nu_{\rm unif}\perp(A_{1/3})_*\nu_{\rm unif}.}
\]

### All rational shifts

If \(s\in\mathbb Q\setminus\mathbb Z_3\), write \(v_3(s)=-b<0\). Since \(u+j\in\mathbb Z_3\), the unequal-valuation rule gives

\[
 v_3(u+s+j)=-b,\qquad
 w_{s+j}(u)=\begin{pmatrix}3^b\\3^b(s+j)\end{pmatrix}
 \quad(j=0,1,2).
\]

Again their second difference is zero, so \(((A_s)_*\nu_{\rm unif})(B)=1\). Combining this singularity with §5 proves the exact statement

\[
 \boxed{\operatorname{Stab}_{\mathbb Q}(\nu_{\rm unif})
 =\mathbb Q\cap\mathbb Z_3
 =\{a/b\in\mathbb Q:\text{the reduced positive denominator }b
                      \text{ is not divisible by }3\}.}
\]

Every rational shift outside the stabilizer gives a law singular to the original, not just a different law.

## 8. Quantile transport, Dickman marginals, exact SI, and zero current

Let \(F\) be a continuous strictly increasing distribution function on \([0,1]\), with \(F(0)=0\), \(F(1)=1\), and let \(Q_F=F^{-1}\). This includes the Dickman distribution from the companion note:

\[
 F_D(x)=\rho(1/x)\quad(0<x\le1),\qquad F_D(0)=0.
\]

Define \(T_F:\Omega\to\Omega\) by \((T_Fz)_q=Q_F(z_q)\), and set \(\nu_F=(T_F)_*\nu_{\rm unif}\). The coordinatewise map is a homeomorphism, with inverse \(y\mapsto(F(y_q))_q\). It commutes with every coordinate reindexing:

\[
 T_FA_s=A_sT_F,\qquad T_FD_a=D_aT_F,
 \qquad (T_F)_*R_k\lambda=R_k(T_F)_*\lambda.
\]

Thus IS, \(R_k\nu_F=\nu_F\), ANN, and the exact translation stabilizer all transfer. Every distinct pair under \(\nu_F\), also conditionally on \(U\), has law \(F\otimes F\). In particular this constructs the claimed law with all rational-coordinate Dickman marginals.

The separating event is recovered from **rank coordinates**, not from an untransformed second difference of quantiles:

\[
 B_F=\{y:\mathbf e(F(y_0)-2F(y_1)+F(y_2))=1\}=T_F(B).
\]

It is a closed cylinder, \(\nu_F(B_F)=0\), and \(((A_s)_*\nu_F)(B_F)=1\) for every \(s\in\mathbb Q\setminus\mathbb Z_3\). Invertibility, or this explicit event, is essential: an arbitrary noninjective coordinate factor need not preserve singularity.

For the uniform law take \(F(x)=x\); for the Dickman law take \(F=F_D\). In either case, if \(\psi\in L^2(F)\) and \(\int\psi\,dF=0\), then for any distinct \(q_1,\ldots,q_L\in\mathbb Q\),

\[
 \begin{aligned}
 \mathbb E_{\nu_F}\left|\frac1L\sum_{j=1}^L\psi(Z_{q_j})\right|^2
 &=\frac1{L^2}\sum_{i,j=1}^L
       \mathbb E_{\nu_F}\bigl[\psi(Z_{q_i})\overline{\psi(Z_{q_j})}\bigr]\\
 &=\frac1L\int|\psi|^2\,dF.
 \end{aligned}
\]

The off-diagonal terms vanish by pair independence. Since \(R_k\nu_F=\nu_F\), this yields the exact requested uniform statement

\[
 \boxed{\sup_{k\ge1}\mathbb E_{R_k\nu_F}
 \left|\frac1L\sum_{j=1}^L\psi(Z_{b+dj})\right|^2
 =\frac1L\int|\psi|^2\,dF}
 \qquad(b\in\mathbb Q,\ d\in\mathbb Q\setminus\{0\}).
\]

Thus one may take \(e_{L,d}(\psi)^2=L^{-1}\int|\psi|^2dF\), independently even of the step and origin. The same formula holds under any affine-reindexed law and each individual branch, because reindexing preserves distinctness of the tested coordinates. This concerns coordinate tests, not arbitrary higher-order cylinder observables.

There are no adjacent ties, and the entire \(R_k\)-orbit has uniform adjacent diagonal nonconcentration: the common adjacent law is the atomless product \(F\otimes F\), so

\[
 \sup_k(R_k\nu_F)\{|Z_1-Z_0|<\epsilon\}
 =(F\otimes F)\{|x-y|<\epsilon\}\longrightarrow0
 \quad(\epsilon\downarrow0).
\]

Finally, that product law is symmetric under exchanging its two coordinates. Hence

\[
 \boxed{J(\nu_F)=\mathbb E_{\nu_F}\operatorname{sgn}(Z_1-Z_0)=0,\qquad
 \nu_F(Z_1>Z_0)=\nu_F(Z_1<Z_0)=\tfrac12.}
\]

## 9. What the model says about invariantization

Retain the exact companion-note identity

\[
 P_k\lambda=\frac1k\sum_{r=0}^{k-1}(A_{r/k})_*\lambda
           =(D_k)_*R_k\lambda.
\]

For this model it reads \(P_k\nu_F=(D_k)_*\nu_F\), **not** \(P_k\nu_F=\nu_F\). If \(t=3^{v_3(k)}\), exactly \(k/t\) of the numerators \(0\le r<k\) have \(r/k\in\mathbb Z_3\). Those summands equal \(\nu_F\); all other summands give \(B_F\) probability one. Therefore

\[
 (P_k\nu_F)(B_F)=1-\frac1t,\qquad
 d_{\rm TV}(P_k\nu_F,\nu_F)=1-\frac1t,
 \quad d_{\rm TV}(\alpha,\beta)=\sup_E|\alpha(E)-\beta(E)|.
\]

For \(t>1\), the upper bound follows by writing \(P_k\nu_F=t^{-1}\nu_F+(1-t^{-1})\eta_k\) with \(\eta_k(B_F)=1\); the event \(B_F\) gives equality. For \(t=1\), all summands equal \(\nu_F\). In particular,

\[
 d_{\rm TV}(P_3\nu_F,\nu_F)=\tfrac23,
 \qquad R_k\nu_F=\nu_F\text{ for every }k.
\]

The failure can also be detected by the continuous cylinder
\(h_F(y)=\mathbf e(F(y_0)-2F(y_1)+F(y_2))\). The Haar calculation gives \(\int h_F\,d\nu_F=0\), while

\[
 \int h_F\,dP_k\nu_F=1-3^{-v_3(k)}.
\]

Consequently \(P_{n!}\nu_F\) cannot converge weakly back to \(\nu_F\). Nevertheless, every distinct pair under every \(P_k\nu_F\) already has law \(F\otimes F\). **This is a full-law obstruction only. It does not refute pair-test residue alignment or the zero-current conclusion.** The three-coordinate distinction is exactly why pairwise independence and coordinate SI leave this rational-invariance route unavailable.

## 10. Verification record and limitations

The mathematical checks above establish compact-group Haar evaluation, joint measurability, the two matrix transports with their signs and order, independence after branch mixing, full-law fixed points and annuli, all distinct-pair laws, exact SI, rank recovery after quantile transport, and singularity for every shift outside the claimed stabilizer. No asymptotic or numerical inference is used in any of these proofs.

An additional exact-arithmetic regression used Python `Fraction` arithmetic, with rational 3-integral probes **only to check algebraic identities away from poles**. Such probes are not samples of the Haar random variable used in the model; rational latent points have been excluded from that model. The checks passed as follows:

| Finite check | Successful checks |
|---|---:|
| Shift matrix identity, including positive and negative rational shifts | 747 |
| Branch matrix identity, all branches for \(1\le k\le54\) and \(k=81\) | 131,380 |
| Nonzero pair determinant formula | 440 |
| Base nonunit pattern and nonzero second difference | 6 |
| Nonintegral shifts: constant \(c\)'s and zero second difference | 42 |
| Multiplicity of branch residues modulo \(3^{v_3(k)}\), \(1\le k\le81\) | 81 |
| Uniformity of \(ku+r\pmod{3^n}\), \(1\le k\le81\), \(1\le n\le4\), enumerating all \(u\pmod{3^n}\), \(0\le r<k\) | 324 |

These finite checks are regression checks of conventions and exact residue arithmetic, **not** evidence for an asymptotic claim, a simulation of Haar characters, or a substitute for the probability proofs.

The source package was read directly from `Submission/AffineAnnulusResearch.md`, especially (3), (5), (6), (12), and §§6.1 and 6.4. The only companion-note edits are short, explicitly scoped cross-references at its top and in §6.4; its original text is retained verbatim. A pre-/post-edit hash comparison verified that every other pre-existing Submission file remained byte-identical. In particular, `Submission/Spec.lean` retains SHA-256

`d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.

**Final scope check:** there is a valid countermodel to deriving whole-law rational translation invariance from the abstract package. Its current is zero. The implication IS + ANN + USI-AP \(\Rightarrow J=0\) remains unresolved by this construction, and no claim about the LPF target or any `Spec` placeholder is proved or disproved here.
