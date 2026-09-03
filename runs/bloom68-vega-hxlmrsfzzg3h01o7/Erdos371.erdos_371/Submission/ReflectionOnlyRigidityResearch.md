# Reflection-only rigidity: an exact obstruction to the entropy-rate route

## Outcome — and the distinction that matters

This note tests the following **specific route**, not every possible entropy argument:

> Use the affine tower formula for entropy, annulus positivity, and/or vanishing time-normalized relative entropy to deduce reversibility, then use reversibility to kill the pair current.

There is an exact obstruction to this route, including in the component sector left by the previous notes.

**Theorems proved below.**

1. For the **full rational-coordinate system**, the proposed tower formula is correct:
   \[
   h_{R_k\nu}(A_1)=\frac1k h_\nu(A_1).
   \]
   IS + ANN consequently imply \(h_\nu(A_1)\in\{0,+\infty\}\). In particular, finite entropy forces **zero entropy**, not reversibility. The corresponding formula for a finite coordinate partition involves a join of the \(k\) fractional-coordinate partitions; it is not the same formula for the integer-coordinate entropy rate.
2. There is an explicit Borel law \(\nu_*\) satisfying **IS + full-measure ANN + exact USI**, with uniform marginals, such that:
   * its integer-ergodic component distribution is purely nonatomic;
   * on almost every component, **every prime is bad**: \(h_p=+\infty\) and \(s_p=0\) in the notation of `ProfiniteHeightResearch.md`;
   * \(R_k\nu_*\ne\nu_*\) for every \(k>1\);
   * its full-system Kolmogorov–Sinai entropy is zero;
   * it is **mutually singular to its reflected full law**;
   * nevertheless, every distinct rational pair is independent, and hence **its pair current is zero**;
   * for each fixed finite rational-coordinate observation, the forward/reflected block relative entropy is bounded independently of block length, so its time-normalized rate is zero;
   * its one-sided annulus relative-entropy bounds are saturated exactly.
3. A second explicit law, in the same nonatomic/all-primes-bad sector, has **nonzero pair current**, zero full-system entropy, bounded full reflection-relative entropy, and USI. It fails ANN by an explicit negative density on an open set. Thus a zero relative-entropy **rate** cannot be converted to zero pair current by a general Pinsker/coercivity argument, even with these other properties. This second law is **not** a counterexample to the full package.

Thus the decisive conclusion here is a **no-go result for the stated entropy-to-reversibility shortcuts**. The first construction is a genuine all-axiom model, but **not a nonzero-current model**. The second has nonzero current, but **not ANN**. No implication IS + ANN + USI \(\Rightarrow J=0\), and no counterexample to that implication, is claimed.

The main construction has precisely the residual **component geometry**, rather than an atomic, fixed-scale, or summable-bad-prime decomposition. Its zero pair profiles of course satisfy the previous Bohr profile criterion; that criterion is neither contradicted nor improved here. The construction tests whole-law entropy-to-reversibility, not the existence of a nonzero pair profile. No assertion about actual LPF prefix laws, or proof/disproof of Erdős 371, follows. Neither admitted target is used; no Lean file is changed.

## 1. Definitions and exact target

Work first on \(\Omega=[0,1]^{\mathbb Q}\), with

\[
 (A_s z)_q=z_{q+s},\qquad (D_a z)_q=z_{aq},\qquad
 G_{k,r}=A_rD_{1/k},\qquad
 R_k\nu=\frac1k\sum_{r=0}^{k-1}(G_{k,r})_*\nu.
 \tag{1}
\]

In particular, \((G_{k,r}z)_q=z_{(q+r)/k}\). The assumptions are:

* **IS:** \((A_1)_*\nu=\nu\).
* **ANN:** \(lR_l\nu-kR_k\nu\ge0\) as full Borel measures for integers \(l>k\ge1\).
* **USI:** for every bounded \(F\)-centered coordinate test \(\psi\) and each fixed integer \(d\ge1\),
  \[
   \sup_{k\ge1}\mathbb E_{R_k\nu}
   \left|\frac1L\sum_{j=1}^L\psi(Z_{dj})\right|^2\longrightarrow0.
   \tag{2}
  \]

All examples below have the same marginal \(F\) at **every rational coordinate**. We construct them for uniform \(F\). Applying a continuous strictly increasing quantile map coordinatewise gives, in particular, the Dickman marginal. This operation is invertible, commutes with reindexings, and preserves ordering signs.

Let

\[
 (Iz)_q=z_{-q},\qquad \nu^-=I_*\nu,
 \qquad K_\nu=\operatorname{Law}_\nu(Z_0,Z_1).
\]

For an IS law, \(K_{\nu^-}=K_\nu^{\mathsf T}\), the transpose of the pair law: stationarity identifies \((Z_0,Z_{-1})\) with \((Z_1,Z_0)\). Consequently full reflection invariance is sufficient, but much stronger than the requested

\[
 \mathbb E_\nu[\phi(Z_0)\psi(Z_1)-\psi(Z_0)\phi(Z_1)]=0,
 \quad\text{or merely}\quad
 J(\nu):=\mathbb E_\nu\operatorname{sgn}(Z_1-Z_0)=0.
 \tag{3}
\]

Equal marginals alone do not imply (3).

Write \(D(P\Vert Q)\) for probability relative entropy, using natural logarithms and the value \(+\infty\) when absolute continuity fails. Write \(h(\nu)=h_\nu(A_1)\) for **full-system** Kolmogorov–Sinai entropy, not differential entropy of the marginal and not automatically the entropy rate of the integer-coordinate factor.

## 2. What the affine tower really proves

### 2.1 Full-system entropy scales by \(1/k\)

**Theorem 1.** For every IS probability \(\lambda\) and every integer \(k\ge1\),

\[
 \boxed{h(R_k\lambda)=h(\lambda)/k.}
 \tag{4}
\]

The equality is in \([0,+\infty]\).

**Proof.** On \(\Omega\times\{0,\ldots,k-1\}\) with measure \(\lambda\otimes u_k\), use the constant-height tower

\[
 S(z,r)=
 \begin{cases}
 (z,r+1),&r<k-1,\\
 (A_1z,0),&r=k-1.
 \end{cases}
\]

Then \(S^k(z,r)=(A_1z,r)\), so the power rule and the finite invariant decomposition into levels give \(h(S)=h(\lambda)/k\). The factor map

\[
 \pi(z,r)=G_{k,r}z
 \tag{5}
\]

has pushforward \(R_k\lambda\) and satisfies \(\pi S=A_1\pi\). At the wraparound this is the exact identity \(G_{k,0}A_1=G_{k,k}\).

Each fibre of \(\pi\) contains at most \(k\) points: after specifying \(r\), the invertible reindexing \(G_{k,r}\) determines \(z\). Thus the factor has zero relative dynamical entropy. More explicitly, conditional on a full factor point, the name of any finite partition over any number of iterates has at most \(k\) possibilities; its conditional entropy is at most \(\log k\), independent of the length. The entropy addition formula therefore gives \(h(S)=h(R_k\lambda)\). This proves (4), including the infinite case. ∎

### 2.2 The finite-partition formula is different

Let \(\mathcal P\) be a finite partition of the coordinate value space, and write \(\mathcal P_q\) for its pullback by \(Z_q\). The same tower, grouping a name into complete \(k\)-blocks, gives

\[
 \boxed{
 h_{R_k\lambda}(A_1,\mathcal P_0)
 =\frac1k\,h_\lambda\left(A_1,
               \bigvee_{r=0}^{k-1}\mathcal P_{r/k}\right).
 }
 \tag{6}
\]

Indeed, a complete tower cycle based at level zero records exactly the partitions \(\mathcal P_{r/k}\). Starting at another level changes only the two incomplete endpoint blocks; their entropy is bounded by \(2k\log|\mathcal P|\), independently of the number of complete blocks. Dividing by time proves (6).

Thus it is incorrect to substitute the entropy rate of \((\mathcal P(Z_n))_{n\in\mathbb Z}\) for the full-system entropy in (4). USI for a single coordinate observable gives no identity identifying the join on the right of (6) with \(\mathcal P_0\).

### 2.3 Finite entropy and ANN force zero entropy

**Theorem 2.** IS + ANN imply

\[
 \boxed{h(\nu)=0\quad\text{or}\quad h(\nu)=+\infty.}
 \tag{7}
\]

**Proof.** Suppose \(h(\nu)<\infty\), fix \(k>1\), and put

\[
 \alpha=\frac{kR_k\nu-\nu}{k-1}.
\]

This is an IS probability by ANN. Entropy is affine on invariant probabilities, so (4) gives

\[
 \frac{h(\nu)}k=h(R_k\nu)
 =\frac{h(\nu)}k+\frac{k-1}{k}h(\alpha).
\]

Hence \(h(\alpha)=0\).

For the last step it is important not to assume ANN componentwise. Let \(\rho\) be the integer-ergodic component distribution of \(\nu\), and \(F_k\theta=R_k\theta\). The map \(F_k\) preserves ergodicity: an invariant event pulls back under \(G_{k,0}\) to an invariant event, and all tower branches give it the same probability. By uniqueness of ergodic decomposition, the component distribution of \(\alpha\) is

\[
 \delta=\frac{k(F_k)_*\rho-\rho}{k-1}\ge0.
 \tag{8}
\]

The component entropy function is measurable (use a countable generating family of finite partitions), and entropy disintegrates over the ergodic decomposition. Thus \(h(\alpha)=0\) says that \(\delta\) gives no mass to
\(E_+=\{\theta:h(\theta)>0\}\). But (4) makes \(F_k^{-1}E_+=E_+\), and hence (8) gives

\[
 0=\delta(E_+)=\rho(E_+).
\]

Therefore \(h(\nu)=\int h(\theta)\,d\rho(\theta)=0\). ∎

This is a consequence of **all** IS + ANN laws, not an extra sufficient hypothesis for pair rigidity. It is useful bookkeeping, but it is not an entropy-production theorem. Sections 4–5 exhibit a zero-entropy all-axiom law that is singular to its reflection.

## 3. Relative entropy: what ANN bounds, and what it does not

ANN gives \(R_k\nu\le(l/k)R_l\nu\), and therefore

\[
 \boxed{D(R_k\nu\Vert R_l\nu)\le\log(l/k)\qquad(l>k).}
 \tag{9}
\]

There is no corresponding reverse absolute continuity. Nor is either side of (9) a forward/reflected relative entropy. The construction below has equality in (9), infinite reverse relative entropy, and infinite full reflection-relative entropy, simultaneously with zero KS entropy and USI.

For comparison, Pinsker gives the genuinely relevant pair bound

\[
 D(K_\nu\Vert K_\nu^{\mathsf T})
 \ge2d_{\rm TV}(K_\nu,K_\nu^{\mathsf T})^2
 \ge2J(\nu)^2.
 \tag{10}
\]

The second inequality follows because the sign test has norm one and its expectations under the two pair laws are \(J\) and \(-J\). Similarly, an antisymmetric bounded test \(H\) gives the lower bound \(2|\mathbb E H|^2/\|H\|_\infty^2\).

But if \(P_N,Q_N\) are forward and reversed block laws, data processing supplies only

\[
 D(K_\nu\Vert K_\nu^{\mathsf T})\le D(P_N\Vert Q_N)
 \quad(N\ge2),
 \tag{11}
\]

not a bound of \(D(P_N\Vert Q_N)\) below by a positive multiple of \(N J(\nu)^2\). Dividing (11) by \(N\) destroys the information about a fixed pair. Section 6 gives an exact nonzero-current example with \(D(P_N\Vert Q_N)\le\log3\) for all \(N\). No numerical example or Markov approximation is involved.

## 4. A zero-entropy carrier with every prime bad

This carrier makes the main obstruction lie in the residual sector, rather than in the already removed summable-bad-prime case. It is a simultaneous all-prime version of the Haar-character construction; the common branch residue must be checked using the full profinite integer, not by assuming that \(R_k\) commutes with products.

### 4.1 Compact character spaces and the full field

Let \(\mathbb T=\mathbb R/\mathbb Z\) and

\[
 \mathcal H=\operatorname{Hom}(\mathbb Q_{\rm disc},\mathbb T),\qquad
 \mathcal K=\operatorname{Hom}((\mathbb Q^2)_{\rm disc},\mathbb T)
           \cong\mathcal H^2.
\]

These are compact metrizable groups with Haar probability. A nonzero rational vector evaluates a Haar character to a Haar circle variable. Two linearly independent vectors evaluate it to product Haar measure: the evaluation map is onto, as can be checked using real linear functionals, and an onto compact-group homomorphism sends Haar to Haar.

Take independent

\[
 U=(U_p)_p\sim\operatorname{Haar}(\widehat{\mathbb Z}),\qquad
 \chi_p\sim\operatorname{Haar}(\mathcal K)\quad(p\text{ prime}).
\]

Outside one null set, \(U_p+q\ne0\) for every \(p,q\): each \(U_p\) avoids the countable set \(\mathbb Q\cap\mathbb Z_p\). Set

\[
 c_{p,q}(u)=p^{-v_p(u+q)},\qquad
 w_{p,q}(u)=(c_{p,q}(u),q c_{p,q}(u)),\qquad
 B^{(p)}_q=\chi_p(w_{p,q}(U_p))\in\mathbb T.
 \tag{12}
\]

Every coordinate is Borel: partition by the countably many possible valuations and use evaluation at a fixed rational vector. Thus this defines a full countable-coordinate field. Write \(\beta\) for its law, with the prime channels retained.

For \(q\ne q'\),

\[
 \det(w_{p,q}(u),w_{p,q'}(u))
 =c_{p,q}(u)c_{p,q'}(u)(q'-q)\ne0.
\]

Consequently every two distinct site-vectors \((B^{(p)}_q)_p\) and \((B^{(p)}_{q'})_p\) are independent product-Haar variables, even conditional on the whole \(U\).

### 4.2 Stationarity, branches, and reflection

For integer translation, use

\[
 w_{p,q+1}(u)=S w_{p,q}(u+1),\qquad
 S=\begin{pmatrix}1&0\\1&1\end{pmatrix}.
\]

Thus the latent transformation is \(U\mapsto U+1\), \(\chi_p\mapsto\chi_p\circ S\), and it preserves the product probability. This proves IS.

For a branch \((k,r)\), put \(t_p=p^{v_p(k)}\), \(m_p=k/t_p\). Directly,

\[
 w_{p,(q+r)/k}(u)=M_{k,r,p}w_{p,q}(ku+r),\qquad
 M_{k,r,p}=\begin{pmatrix}t_p&0\\r/m_p&1/m_p\end{pmatrix}.
 \tag{13}
\]

These are invertible rational matrices. Conditional on the branch, all transformed characters still have their original independent Haar laws, independent of \(U'=kU+r\). The latter is normalized Haar on \(r+k\widehat{\mathbb Z}\). Averaging over the **common** \(r\in\{0,\ldots,k-1\}\) gives Haar on \(\widehat{\mathbb Z}\). This checks the correlations between primes as well as the individual prime marginals. Therefore

\[
 \boxed{R_k\beta=\beta\quad(k\ge1).}
 \tag{14}
\]

Reflection also preserves \(\beta\): take \(U\mapsto-U\) and precompose each character by \(\operatorname{diag}(1,-1)\), using
\(w_{p,-q}(u)=\operatorname{diag}(1,-1)w_{p,q}(-u)\).

### 4.3 The entire odometer is a measurable field factor

We prove recovery, rather than merely asserting that a latent odometer survives the field map.

Fix \(p,m\ge1\) (with \(p\) prime), \(n\in\mathbb Z\), and put \(a=p^m\). Let \(E_{p,m,n}\) be the event that all second differences of

\[
 B^{(p)}_n,B^{(p)}_{n+a},\ldots,B^{(p)}_{n+pa}
\]

vanish in \(\mathbb T\). For three equally spaced sites \(x,x+a,x+2a\), the rational vector second difference of \((c,xc)\) is zero **if and only if** the three \(c\)'s are equal. Indeed, its first component gives \(c_2-2c_1+c_0=0\); subtracting \(x\) times this equation from the second component gives \(2a(c_2-c_1)=0\).

Every nonzero such vector evaluates under Haar \(\chi_p\) to a variable with no atom at zero. There are only countably many triples under consideration. Off their union of null exceptional sets, the observed second differences vanish exactly when the corresponding vectors vanish. Hence \(E_{p,m,n}\) holds exactly when all \(p+1\) displayed valuations are equal.

If \(v_p(U_p+n)<m\), these valuations are all \(v_p(U_p+n)\). If \(v_p(U_p+n)\ge m\), among the first \(p\) values of \((U_p+n)/p^m+j\) exactly one is divisible by \(p\), whereas the others are units; the valuations are not all equal. This also works for \(p=2\), where the displayed list has three sites. Thus, almost surely simultaneously for every \(p,m,n\),

\[
 \boxed{1_{E_{p,m,n}}=1_{\{U_p+n\not\equiv0\pmod{p^m}\}}.}
 \tag{15}
\]

The unique residue \(r\pmod{p^m}\) for which \(E_{p,m,-r}\) fails recovers \(U_p\pmod{p^m}\). These recoveries are compatible and transform by \(U\mapsto U+1\) under the integer shift. The whole \(\widehat{\mathbb Z}\)-odometer is therefore a measurable factor of the observed field.

On almost every ergodic component of any stationary extension retaining this factor, its distribution is Haar: invariance by \(+1\) forces uniformity modulo every integer, hence Haar probability. Its characters give an eigenvalue of order \(p^m\) for every \(p,m\).

For completeness, an ergodic system with an order-\(p\) eigenvalue cannot have a preserving \(p\)th root of its transformation. If \(f\circ T=\zeta f\), normalize \(f^p\) to a nonzero constant. A preserving root \(S\), which commutes with \(T\), acts on the one-dimensional eigenspace by \(f\circ S=\eta f\). The constant \(p\)th power gives \(\eta^p=1\), whereas \(S^p=T\) gives \(\eta^p=\zeta\ne1\). Applied to \(A_{1/p}\), this proves that every such component has

\[
 \boxed{h_p=+\infty,\qquad s_p=0\quad\text{for every prime }p.}
 \tag{16}
\]

Thus its bad-prime reciprocal sum diverges.

### 4.4 The carrier has zero entropy

Write \(\chi_p(x,y)=a_p(x)+b_p(y)\). The latent integer action is

\[
 U\mapsto U+1,\qquad (a_p,b_p)\mapsto(a_p+b_p,b_p).
 \tag{17}
\]

The odometer is an inverse limit of finite cycles and has zero entropy. Each solenoid shear in (17) is an inverse limit of the toral shears obtained by evaluating at \(1/N!\). A toral shear has zero entropy: its iterates grow at most polynomially in Lipschitz norm, so a polynomial-size mesh suffices for an orbit-name cover at any fixed resolution; the exponential growth rate is zero. The same is true for every finite product of these factors. Taking their increasing generating inverse limit proves that the latent system has zero entropy. The observed field, being a factor, does too.

## 5. The all-axiom reflection-singular model

### 5.1 An oriented cubic parameter

Independently of the carrier, take \(C\) Haar on \(\mathbb T\) and \(a,b\) independent Haar on \(\mathcal H\). For a fixed real \(v\), let \(\lambda_v\) be the law of

\[
 X_q=C+a(q)+b(q^2)+v q^3\pmod1\qquad(q\in\mathbb Q).
 \tag{18}
\]

This is a Borel field, measurably depending on \(v\). Rational translation changes only the lower-degree Haar coefficients and the uniform constant. For example translation by \(s\) changes them to

\[
 \begin{aligned}
 C'&=C+a(s)+b(s^2)+v s^3,\\
 a'(x)&=a(x)+b(2sx)+3v s^2 x,\\
 b'(x)&=b(x)+3v s x.
 \end{aligned}
\]

The rational multiplication occurs in the character's argument, not by choosing rational roots of a circle value. The map on the two characters is an invertible rational triangular change followed by addition of deterministic characters. Conditional on them, the new constant is still independent Haar. This proves rational-translation invariance of \(\lambda_v\).

Expanding \((q+r)^3/k^3\) and making the analogous invertible rational change gives, for **each branch**,

\[
 \boxed{(G_{k,r})_*\lambda_v=\lambda_{v/k^3}.}
 \tag{19}
\]

For explicit coefficients, one can take

\[
 \begin{aligned}
 C'&=C+a(r/k)+b(r^2/k^2)+v r^3/k^3,\\
 a'(x)&=a(x/k)+b(2rx/k^2)+3v r^2x/k^3,\\
 b'(x)&=b(x/k^2)+3v rx/k^3.
 \end{aligned}
\]

Every pair of distinct coordinates of \(\lambda_v\) is independent uniform. The character part of their difference is a nonzero rational-vector evaluation, hence Haar; the constant \(C\) makes the first coordinate uniform independently of that difference. In fact three distinct coordinates are independent, by the invertible Vandermonde matrix for \(1,q,q^2\), although only pairs are needed here.

### 5.2 Pareto mixing and full annuli

Let \(V\) have density

\[
 f(v)=\frac13v^{-4/3}1_{\{v\ge1\}}.
 \tag{20}
\]

It has mass one. Retain all channels and define

\[
 \widetilde\nu_*=
 \int_1^\infty(\lambda_v\otimes\beta)\,\frac13v^{-4/3}\,dv.
 \tag{21}
\]

To get a **real-valued** field, fix a measure-preserving Borel isomorphism, modulo null sets, from the countable product of circles (one cubic channel and all prime channels) to \([0,1]\), and apply it separately at every rational site. A concrete choice interleaves the binary digits of the channel representatives by a fixed bijection of the countable digit positions. Exclude dyadic ambiguities; all coordinate marginals are product Haar, so the countable union of these exceptions is null. The inverse decodes each channel at each rational site. Denote the resulting real-field law by \(\nu_*\).

This encoding commutes with every coordinate reindexing and is invertible almost surely for all the laws used here. It preserves the relevant entropy and recovery statements.

Because (19) is independent of \(r\), the common branch average in the product is exactly

\[
 R_k(\lambda_v\otimes\beta)=\lambda_{v/k^3}\otimes\beta.
 \tag{22}
\]

This identity uses (14) and (19); it is **not** a general assertion that \(R_k\) preserves products. Substituting \(v=k^3w\) gives the full-measure identity

\[
 \boxed{
 kR_k\widetilde\nu_*
 =\int_{1/k^3}^\infty(\lambda_w\otimes\beta)\,
                    \frac13w^{-4/3}\,dw.
 }
 \tag{23}
\]

The lower endpoint decreases with \(k\). Thus (23) proves every full Borel annulus inequality, and those inequalities survive the encoding. IS has already been checked on each factor.

Conditional on \((V,U)\), any two distinct site-vectors are independent product-Haar variables, by §4.1 and §5.1. After encoding they are independent uniforms. This applies at every scale in (23). Hence, for every centered \(\psi\in L^2(F)\) and any distinct rational sites \(q_1,\ldots,q_L\),

\[
 \boxed{
 \mathbb E_{R_k\nu_*}
 \left|\frac1L\sum_{j=1}^L\psi(Z_{q_j})\right|^2
 =\frac1L\int|\psi|^2\,dF\quad(k\ge1).
 }
 \tag{24}
\]

This is stronger than the required USI, with exact constants. It also verifies directly that

\[
 \boxed{K_{\nu_*}=F\otimes F,\qquad J(\nu_*)=0.}
 \tag{25}
\]

Conditional one-coordinate marginals given \((V,U)\) are \(F\); here conditional pair independence is established by the explicit Haar calculation, **not inferred from conditional marginals or from USI**.

### 5.3 Recovery, nonatomic components, and singular reflection

Let \(\operatorname{pr}:\mathbb T\to[-1/2,1/2)\) be the signed representative. From the decoded cubic channel define

\[
 \mathcal V(z)=\lim_{n\to\infty}\frac{n^3}{6}
 \operatorname{pr}\bigl(X_{3/n}-3X_{2/n}+3X_{1/n}-X_0\bigr),
 \tag{26}
\]

with an arbitrary value where the finite limit fails. This is measurable. Character additivity cancels the constant, linear, and quadratic terms modulo one; the remaining circle element is \(6v/n^3\). For each fixed real \(v\), it lies in the signed representative interval for every sufficiently large \(n\). Thus the limit is **exactly** \(v\) under \(\lambda_v\), including for negative \(v\).

Translation does not change the cubic coefficient. Therefore \(\mathcal V\) is an integer-invariant observable almost surely, with the continuous density (20) under \(\nu_*\). Every ergodic component concentrates on one value of \(\mathcal V\), so an atom in the component distribution would give an atom in its \(V\)-pushforward. There are none. The component distribution is purely nonatomic.

The decoded carrier still recovers the whole odometer, so (16) holds on almost every component. Thus every prime is bad, and \(\sum_{p\text{ bad}}1/p=\infty\) on those components.

Under \(R_k\nu_*\), the recovered parameter has support \([1/k^3,\infty)\), and

\[
 (R_k\nu_*)\{\mathcal V<1\}=1-1/k>0\quad(k>1),
 \qquad \nu_*\{\mathcal V<1\}=0.
 \tag{27}
\]

There is no exact fixed scale.

Finally, reflection sends \(\lambda_v\) to \(\lambda_{-v}\): replace \(a\) by \(-a\), keep \(b,C\), and reverse the cubic coefficient. It preserves \(\beta\). Consequently

\[
 \nu_*\{\mathcal V>0\}=1,\qquad
 \nu_*^-\{\mathcal V<0\}=1.
\]

In particular,

\[
 \boxed{\nu_*\perp\nu_*^-,\qquad
        D(\nu_*\Vert\nu_*^-)=+\infty.}
 \tag{28}
\]

The separating statistic uses the whole rational field, not just an ordering pair. Equation (25) remains true: this is an obstruction to deducing **whole-law reversibility**, not a current counterexample.

### 5.4 Full-system entropy is zero

At a fixed \(v\), the latent action for (18) under translation by one is

\[
 \begin{aligned}
 C'&=C+a(1)+b(1)+v,\\
 a'(x)&=a(x)+2b(x)+3v x,\\
 b'(x)&=b(x)+3v x.
 \end{aligned}
 \tag{29}
\]

For each integer \(M\), evaluation of \(a,b\) at \(1/M\), together with \(C\), is a toral factor with linear part

\[
 \begin{pmatrix}1&M&M\\0&1&2\\0&0&1\end{pmatrix}.
\]

It is unipotent; the translations depending on \(v\) do not change the polynomial growth of iterates. The same orbit-cover argument as in §4.4 proves zero entropy. Factorials give an increasing generating sequence of these factors, so the whole fixed-\(v\) latent system has zero entropy. The parameter \(v\) itself is fixed by time translation. Entropy disintegration over this invariant parameter therefore gives zero entropy for its mixture. The independent carrier also has zero entropy, and the encoded field is a factor. Hence

\[
 \boxed{h(\nu_*)=0.}
 \tag{30}
\]

This verifies the claim directly; it does not assume that the desired conclusion follows from (7).

### 5.5 Every fixed finite-coordinate reflection-entropy rate is zero

Let \(B\subset\mathbb Q\) be finite. Let \(P_{B,N}\) and \(Q_{B,N}\) be the laws, under \(\nu_*\) and \(\nu_*^-\), of the coordinates at sites

\[
 \{q+j:q\in B,\ 0\le j<N\}.
\]

Choose an integer \(D\ge1\) with \(B\subset D^{-1}\mathbb Z\). On the **whole** lattice \(D^{-1}\mathbb Z\), (18) has the form

\[
 X_{j/D}=C+j A+j^2 B_0+j^3 W\pmod1,
 \tag{31}
\]

where \(C,A=a(1/D),B_0=b(1/D^2)\) are independent Haar circle variables and
\(W=V/D^3\pmod1\), independently. Write \(w_D\) for the density of \(W\). Periodizing (20) gives

\[
 w_D(t)=D^3\sum_{j\in\mathbb Z} f(D^3(j+t)),\qquad0\le t<1.
 \tag{32}
\]

For each fixed \(D\) this density is bounded above and bounded away from zero. For example its \(j=1\) term gives

\[
 w_D(t)\ge\frac{2^{-4/3}}{3D},
\]

while the possible \(j=0\) term is at most \(D^3/3\), and the terms \(j\ge1\) sum to at most \((3D)^{-1}\sum_{j\ge1}j^{-4/3}\). These are genuine bounds on the infinite periodization, not truncation estimates.

Reflection changes \(W\) to \(-W\) and preserves the Haar distribution of the three lower coefficients. Its latent coefficient relative entropy is therefore

\[
 C_D:=D(w_D(t)\,dt\Vert w_D(-t)\,dt)<\infty.
 \tag{33}
\]

The full carrier has the **same** law under reflection and is independent of the cubic channel. By product additivity and data processing from these latent variables, for every \(N\),

\[
 \boxed{D(P_{B,N}\Vert Q_{B,N})\le C_D.}
 \tag{34}
\]

It follows that

\[
 \boxed{\lim_{N\to\infty}\frac1N D(P_{B,N}\Vert Q_{B,N})=0}
 \quad\text{for every fixed finite }B.
 \tag{35}
\]

Any measurable finite-alphabet observation of these coordinates has the same bound by data processing. In particular (35) holds for the ordinary integer-coordinate process and all its finite quantizations.

There is no contradiction with (28). The constants depend on the rational resolution \(D\); observing arbitrarily small rational spacings recovers the sign of the **unwrapped** coefficient by (26). Also, (35) is explicitly a statement about fixed finite-coordinate observations. It is not a statement about arbitrary measurable partitions of the whole rational field: the invariant partition \(\{\mathcal V>0\},\{\mathcal V\le0\}\) already has infinite relative entropy against reflection at time zero. Relative-entropy rates cannot be extended across this change of observation sigma-algebra by the KS entropy approximation theorem.

### 5.6 The annulus relative-entropies are maximal, not zero

Under \(R_k\nu_*\), the recovered parameter density is

\[
 f_k(v)=\frac1{3k}v^{-4/3}1_{\{v\ge k^{-3}\}}.
\]

Conditional field kernels at a given \(v\) are the same at every scale, and \(v\) is recoverable. Hence for \(l>k\), the Radon–Nikodym derivative of \(R_k\nu_*\) relative to \(R_l\nu_*\) is \(l/k\) on \(\{\mathcal V\ge k^{-3}\}\), and zero elsewhere. Therefore

\[
 \boxed{
 D(R_k\nu_*\Vert R_l\nu_*)=\log(l/k),\qquad
 D(R_l\nu_*\Vert R_k\nu_*)=+\infty.
 }
 \tag{36}
\]

The TV bound is also saturated: \(d_{\rm TV}(R_k\nu_*,R_l\nu_*)=1-k/l\). Small consecutive forward relative entropies do not create a reversible probability-preserving scale action. This model even has the explicit entrance family, before encoding,

\[
 \widetilde\nu_{*,t}=\frac1t\int_{t^{-3}}^\infty
            (\lambda_w\otimes\beta)\,\frac13w^{-4/3}\,dw
 \qquad(t>0).
\]

These are probabilities, \(t\widetilde\nu_{*,t}\) is increasing, and (22) gives \(R_k\widetilde\nu_{*,t}=\widetilde\nu_{*,kt}\). Thus the entropy obstruction is not caused by the absence of an entrance extension; no operator \(R_t\) for noninteger \(t\) is being presumed.

## 6. A nonzero-current, zero-entropy-rate near-miss — with the ANN failure exposed

This construction identifies a different, precise false inference: that zero time-normalized reflection-relative entropy controls pair current for stationary USI processes. It can also be placed in the all-primes-bad sector. It is kept separate from the all-axiom construction above.

### 6.1 A tilted Haar-character channel

Take \(C\) uniform on \(\mathbb T\), and give \(a\in\mathcal H\) the probability density

\[
 w(a(1))=1+\frac12\sin(2\pi a(1))
 \tag{37}
\]

relative to Haar. Let \(\kappa\) be the law of

\[
 Y_q=C+a(q)\pmod1.
 \tag{38}
\]

The field recovers \(C=Y_0\) and \(a(q)=Y_q-Y_0\) modulo one. It is invariant under every rational translation: conditional on \(a\), such a translation only rotates \(C\). Every marginal is uniform.

Let \(\kappa_0\) denote the untilted Haar law. Every branch at scale \(k\) has the same law, with density

\[
 \frac{dR_k\kappa}{d\kappa_0}=w(k a(1)).
 \tag{39}
\]

Indeed, after writing \(a'(q)=a(q/k)\), the old \(a(1)\) is \(k a'(1)\). The phase translation in a branch leaves the independent uniform \(C\) unchanged in distribution. Since \(w\le3/2\) and the untilted field has independent rational pairs,

\[
 \mathbb E_{R_k\kappa}
 \left|\frac1L\sum_{j=1}^L\psi(Y_{q_j})\right|^2
 \le\frac{3}{2L}\int|\psi|^2
 \tag{40}
\]

for every centered test and any distinct rational sites, uniformly in \(k\).

Conditional on \(\alpha=a(1)\in(0,1)\), the ordering current is \(1-2\alpha\). Thus an exact integration gives

\[
 \boxed{J(\kappa)=\int_0^1(1-2\alpha)
       (1+\tfrac12\sin2\pi\alpha)\,d\alpha=\frac1{2\pi}>0.}
 \tag{41}
\]

For bounded product tests, there is the equally explicit identity

\[
 \boxed{
 \mathbb E_\kappa[
 \cos(2\pi Y_0)\sin(2\pi Y_1)
 -\sin(2\pi Y_0)\cos(2\pi Y_1)]
 =\mathbb E\sin(2\pi\alpha)=\frac14.
 }
 \tag{42}
\]

The latent integer transformation fixes \(a\) and rotates \(C\) by \(a(1)\), so its entropy, and that of the field, is zero. The same holds at every \(R_k\)-scale. Reflection replaces \(w(\alpha)\) by \(w(-\alpha)\); both densities lie between \(1/2\) and \(3/2\). Consequently

\[
 \boxed{D(\kappa\Vert\kappa^-)\le\log3.}
 \tag{43}
\]

Every block relative entropy is bounded by (43), whereas (41)–(42) are nonzero. The information cost is paid once in choosing the invariant rotation parameter; it need not be paid again at each time step. This is a stationary mixture of rotations, not a Markov-chain approximation. This disproves any general inequality asserting a positive lower bound for the time-normalized reflection-relative entropy in terms of the square of one of these currents.

### 6.2 Exact failure of ANN

Using the recoverable character coordinate, the density of \(2R_2\kappa-\kappa\) relative to \(\kappa_0\) is

\[
 2w(2\alpha)-w(\alpha)
 =1+\sin(4\pi\alpha)-\tfrac12\sin(2\pi\alpha).
 \tag{44}
\]

At \(\alpha=3/8\), it is

\[
 -\frac{\sqrt2}{4}<0.
\]

By continuity it is negative on an open interval of positive Haar measure. Thus \(2R_2\kappa-\kappa\) is not a positive measure. This is a full-law ANN failure, not a failure inferred from a finite experiment. The law \(\kappa\) is **not** a countermodel to IS + ANN + USI.

### 6.3 The same near-miss can have all the residual component geometry

Take the independent product \(\kappa\otimes\beta\), and encode the channel vector into a real value as in §5.2. Choose the binary-digit bijection so that the **first five output bits are the first five bits of the tilted channel**; then interleave all remaining bits bijectively. Call the real-field law \(\rho_*\).

At one coordinate the channels have product-Haar distribution, so the encoded marginal is uniform. Under every branch, the tilted channel law is independent of the branch residue by (39). Thus

\[
 R_k(\kappa\otimes\beta)=R_k\kappa\otimes\beta
\]

after branch averaging. Relative to the untilted product law its density is at most \(3/2\). That reference field has independent pairs at all rational sites, so (40) holds for **every centered test of the encoded real coordinate**. This proves USI for \(\rho_*\), not only for tests of one decoded channel.

The carrier recovery proves all primes bad on almost every ergodic component. The tilted channel recovers the invariant random character \(a\), whose \(a(1)\)-distribution is continuous; the component distribution is purely nonatomic. Projection to the tilted channel also shows that there is no exact fixed scale \(k>1\), and retains the explicit ANN failure (44). The product has zero KS entropy and

\[
 D(\rho_*\Vert\rho_*^-)\le\log3
\]

because the independent carrier is reflection invariant. In particular, all block reflection-entropy rates vanish.

The nonzero **integrated sign current** also survives this specified encoding, not just the decoded test (42). If the two tilted coordinates lie in different dyadic intervals of length \(2^{-5}\), their ordering is unchanged by the encoding. Their pair density is \(w(y-x)\le3/2\) relative to Lebesgue measure on the square. The probability of lying in the same such interval is at most \((3/2)2^{-5}\). The two sign tests differ by at most two. Therefore

\[
 |J(\rho_*)-J(\kappa)|\le3\cdot2^{-5}=\frac3{32}.
\]

Using the elementary bound \(\pi<4\) in (41),

\[
 \boxed{J(\rho_*)>\frac18-\frac3{32}=\frac1{32}>0.}
 \tag{45}
\]

This is an analytic bound, not a numerical counterexample. The pair has no diagonal atom since its law is boundedly absolutely continuous relative to the untilted product-pair law. **ANN still fails**: retaining a factor cannot repair the negative measure detected in (44).

## 7. Precisely what is excluded, and what still needs proof

### 7.1 The entropy-only implications excluded by the constructions

The examples and identities give the following exact ledger.

| Proposed inference | Exact obstruction |
|---|---|
| The tower divides the entropy rate of the integer-coordinate partition by \(k\) | The valid formula is (6), with the join of fractional-coordinate partitions |
| Finite full-system entropy plus ANN supplies positive entropy production unless the system is reversible | ANN forces the entropy itself to zero; \(\nu_*\) satisfies every axiom and is reflection-singular |
| IS + ANN + USI forces \(D(\nu\Vert\nu^-)=0\), or even finite | \(\nu_*\) has \(D(\nu_*\Vert\nu_*^-)=\infty\), in the purely nonatomic, all-primes-bad, no-fixed-scale sector |
| Small consecutive annulus relative entropies yield a reversible scale dynamics | \(\nu_*\) saturates the forward bounds (36) and has infinite reverse relative entropies |
| A zero time-normalized reflection-relative entropy forces zero pair current | \(\rho_*\) has bounded full reflection-relative entropy and current \(>1/32\); it satisfies IS and USI but explicitly fails ANN |
| Conditional one-coordinate marginals equal to \(F\) can be replaced by conditional pair independence | No such inference was used; (24) comes from a separate Haar evaluation calculation |

In particular, a proof that uses ANN only to obtain (4), (7), or a vanishing **time-normalized** entropy-production statement has not yet used enough information to justify the pair conclusion. The near-miss satisfies those entropy statements too. It must exploit full annulus positivity in an additional, genuinely pair-sensitive way. This is a logical obstruction to the specified proof strategy, **not a theorem excluding every conceivable use of entropy**.

### 7.2 What a successful relative-entropy argument would still have to establish

It would suffice to prove, directly from all three axioms, that

\[
 D(K_\nu\Vert K_\nu^{\mathsf T})=0,
\]

after an appropriate finite quantization and limiting argument, or to prove a valid all-axiom inequality coercive in \(J(\nu)\). None of (4), (7), (9), or (35) supplies it. In particular:

* Pinsker applies to an **unnormalized** probability relative entropy. Its use after division by block length needs a new linear-in-length lower bound, which is false for general stationary USI laws by (43)–(45).
* The field marginal of a scale/reflection joining cannot be altered silently. The one-sided domination in ANN does not give reverse branch domination or a probability-preserving inverse affine action on the original law.
* A full relative-entropy argument cannot aim to prove whole-law reflection invariance from the axioms: (28) is an all-axiom counterexample to precisely that intermediate conclusion. A pair-only argument could still work.

The prime-entropy input from the previous notes is not strengthened here. In particular, an estimate of the form \(\sup_d\mathbb E_p\mathrm{error}(d,p)\) must not be replaced by \(\mathbb E_p\sup_d\mathrm{error}(d,p)\). A scale choice depending on the prime needs its own argument. No good-prime selection, variable-scale diagonal, or passage from conditional marginals to pair independence is used in the proofs above.

### 7.3 Two elementary algebraic limits on the other suggested approaches

These observations are narrower than the entropy obstruction and are recorded only to delimit literal versions of those approaches.

* Every word in translations, positive rational dilations, and their inverses is still an orientation-preserving affine reindexing \(q\mapsto aq+b\), \(a>0\). No such single word swaps the ordered sites \(0,1\). This rules out a **literal affine involution** of the two sites, not an averaged joining or an operator identity on pair tests.
* An antisymmetric edge observable \(H(x,y)\) has a universal one-state potential \(H(x,y)=g(y)-g(x)\) if and only if all triangle sums vanish. Necessity is telescoping; sufficiency follows by fixing a base point. The sign observable has triangle sum \(1\) along \(x<y<z\), traversed \(x\to y\to z\to x\). For \(H=\phi(x)\psi(y)-\psi(x)\phi(y)\), the triangle sum is the oriented determinant of the three points \((\phi,\psi)\), and is generally nonzero. The same periodic-cycle test excludes a universal field coboundary \(H(Z_0,Z_1)=B\circ A_1-B\) on all rational fields. These periodic fields need not satisfy USI; this is **not** an impossibility theorem for a potential constructed only on an all-axiom law, or for an unbounded/nonlocal potential with separately justified integrability.

No more sufficient conditions for pair rigidity are proposed here. The remaining mathematical question is still specifically the antisymmetric pair statistic under **actual full ANN**, not entropy zero, not full-law reflection, and not a change of law by invariantization or logarithmic averaging.

## 8. Proof inputs, verification, and file boundary

The arguments use standard measurable ergodic decomposition, the power/addition/disintegration formulas for KS entropy, Haar measure on compact metrizable groups, elementary relative-entropy data processing and Pinsker, and countable-product probability constructions. The zero-entropy assertions are reduced explicitly to inverse limits of finite cycles and polynomial-growth unipotent toral maps. No arithmetic entropy theorem or paper-matching claim is used to fill a limiting step.

The essential infinite arguments have been supplied explicitly:

* a countable null-set exclusion makes all valuation and odometer recoveries simultaneous;
* the common residue average is Haar on the **whole** profinite integer, giving full-law branch identities;
* the Pareto integral is normalized and yields the exact full-measure inequality (23), not merely pair inequalities;
* the signed third-difference limit recovers the unwrapped cubic parameter for every finite \(v\), including reflected negative values;
* periodization (32) is bounded above and below by convergent infinite-series estimates, so (34) is uniform in block length;
* the encoder is an almost-sure Borel isomorphism and preserves all retained factors;
* the nonzero-current near-miss has a proved negative ANN density, not an untested annulus condition.

The prior definitions and reductions were read in `AffineAnnulusResearch.md`, `AffinePairRigidityResearch.md`, `AffineEntranceResearch.md`, and `ProfiniteHeightResearch.md`. The single-prime Haar-character calculation in `PadicAnnulusCounterexampleResearch.md` was used as a starting ingredient; the simultaneous-prime branch check, observed odometer recovery, cubic reflection obstruction, entropy computations, and explicit tilted near-miss are proved here.

**Final audit.** All 74 pre-existing files under `Submission` were checked byte-for-byte by SHA-256 against a manifest made before writing this note; none changed. This note is the only added file there. Math delimiters were checked for correct nesting, all 45 numbered equations have unique consecutive tags, and the cited local research files exist. Exact symbolic calculations independently rechecked the cubic expansion and third-difference cancellation, the integrals (41)–(42), and the negative ANN density (44). These algebra checks do not replace the full-measure, entropy, or limiting proofs above.

This is mathematical research, not a Lean formalization. `Submission/Spec.lean` remains untouched (SHA-256 `d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`), and neither admitted target was used. The result is an exact obstruction to the specified entropy route; the all-axiom zero-current implication and the ordinary LPF density target are **not resolved by this note**.

## Independent continuation audit

The main assistant independently checked the finite-to-one tower factor and the use of ergodic decomposition in Theorem 2; the common profinite residue average in (13)--(14); the exact second-difference recovery of all residue classes in (15); the root/eigenvalue argument; the cubic branch transformation, Pareto normalization, and third-difference recovery; and the fixed-lattice periodization bounds. The fixed-lattice bound is not a full-field relative-entropy bound. The near-miss's ANN failure remains explicit and prevents promoting its positive current to an all-axiom countermodel. Eight independent symbolic identities (cubic transform, third difference, the two current integrals, negative ANN density, Pareto normalization and rescaling, and an unrelated global-sieve constant) also passed, but the measure and entropy arguments above, not finite checks, are the mathematical justification. No target theorem follows from this audit.
