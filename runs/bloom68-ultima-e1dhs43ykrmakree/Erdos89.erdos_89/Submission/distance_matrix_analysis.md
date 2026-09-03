# Planar distance-matrix investigation

## Status

No proof or counterexample was obtained for the proposed universal amplification

\[
E(P)D(P)^2\ge c n^5,\qquad E(P)=\sum_d r_d^2.
\]

The results below are proved obstructions to specific spectral/kernel extraction strategies, plus exact support-weighted consequences of planarity. None is presented as a proof of the sharp Erdős conjecture. No Lean formalization was attempted.

## 1. Normalization and the missing nonuniformity theorem

Write the distinct positive squared distances as \(s_1,\ldots,s_D\), and let \(r_d\) count ordered pairs. Then

\[
M:=\sum_d r_d=n(n-1),\qquad E\ge M^2/D.
\]

The proposed amplification, combined with Guth–Katz's \(E\le C n^3\log n\), would give
\(D\ge\sqrt{c/C}\,n/\sqrt{\log n}\). Cauchy–Schwarz alone does not do this.

For \(\bar r=M/D\), define

\[
\mathrm{CV}^2=\frac{D\sum_d(r_d-\bar r)^2}{M^2}.
\]

Exactly,

\[
\frac{ED}{M^2}=1+\mathrm{CV}^2.
\]

Thus the proposed amplification asks for
\(1+\mathrm{CV}^2\ge c n^5/(DM^2)\asymp n/D\). It is a strong multiplicity-nonuniformity theorem, not merely another lower bound on support size. If \(D\ge\alpha n\), ordinary Cauchy–Schwarz already gives the amplification with a constant depending on \(\alpha\). The difficult regime is \(D=o(n)\).

## 2. Full-planar isospectral obstruction

### Lemma: independently rotating regular polygon orbits preserves the EDM spectrum

Let \(P\) be a disjoint union of regular \(k\)-gons of positive radius centered at the origin, for a fixed \(k\ge3\). Each orbit can have its own radius and rotation angle; rotations below are restricted to choices without point collisions. Put

\[
X=(p_i^T)_i,\quad q_i=|p_i|^2,\quad S=\sum_i q_i,\quad T=\sum_i q_i^2.
\]

Then

\[
X^T\mathbf1=0,\qquad X^Tq=0,\qquad X^TX=(S/2)I_2.
\]

Consequently the squared-distance matrix

\[
R=q\mathbf1^T+\mathbf1q^T-2XX^T
\]

has nonzero eigenvalues

\[
-S,\ -S,\ S+\sqrt{nT},\ S-\sqrt{nT},
\]

with the last eigenvalue omitted if all radii coincide. When at least two radii occur, \(\operatorname{rank}R=4\), and in every case the centered Gram matrix has rank two.

**Proof.** Each polygon orbit has zero first moment and isotropic second moment; its radius is constant. Therefore the three displayed moment identities hold. The spaces \(\operatorname{col}X\) and \(\operatorname{span}\{\mathbf1,q\}\) are orthogonal. On the former, \(R=-S I\). On the latter, the matrix in the basis \((\mathbf1,q)\) is
\(\begin{pmatrix}S&T\\ n&S\end{pmatrix}\), giving the claimed two eigenvalues. The orthogonal complement is killed. Strict Cauchy–Schwarz gives \(nT>S^2\) when the radii vary.

When q is constant, the same spectral conclusion follows directly from \(R=2q_1J-2XX^T\); the two-dimensional basis calculation above is used only for nonconstant q. In particular the spectrum, characteristic polynomial, all ordinary spectral moments, traces of exterior powers, and traces of ordinary matrix resolvents are unchanged by collision-free independent rotations of the polygon orbits.

### Elementary two-ring example with exact multiplicities

Let \(n=6m\). Use \(m\) equilateral-triangle orbits of radius 1 and \(m\) of radius 2. Every resulting set has

\[
\operatorname{spec}R=
\left\{-\frac{5n}{2},-\frac{5n}{2},\frac{(5+\sqrt{34})n}{2},\frac{(5-\sqrt{34})n}{2},0^{(n-4)}\right\}.
\]

* **Aligned:** arrange the orbits to make a regular \(3m\)-gon on each circle. There are at most \(3\lfloor3m/2\rfloor+1\le n\) distances. Hence \(E\ge n(n-1)^2\).
* **Generic rotations:** there are two within-triangle distance colors, each of ordered multiplicity \(n\). Each pair of distinct triangle orbits gives three other colors, each of multiplicity 6. Generic angles avoid all other equalities. Thus
  \[
  D=2+3\binom{2m}{2}=n^2/6-n/2+2,
  \qquad E=2n^2+108\binom{2m}{2}=8n^2-18n.
  \]

The genericity assertion follows by avoiding a finite union of proper real-analytic zero sets: between two orbits, the three squared distances are
\(a^2+b^2-2ab\cos(\theta_i-\theta_j+2\pi\ell/3)\). The only identities holding for all angles are precisely the orbit symmetries already counted.

Therefore genuinely planar, full-rank-four EDMs with exactly the same spectrum have energies whose ratio tends to infinity.

### The obstruction also applies to the sharp lattice example

A centered even-sided square grid decomposes into quarter-turn orbits of size four. Rotating the orbits independently leaves its EDM spectrum unchanged by the lemma. For generic rotations, every pair of different orbits contributes four colors of multiplicity 8. If there are \(m=n/4\) orbits, their energy contribution is
\(256\binom m2\le8n^2\). All within-orbit ordered edges number \(12m=3n\), so their energy is at most \(9n^2\). Generic angles keep the cross-orbit colors separate from all within-orbit colors. Thus

\[
E_{\mathrm{generic}}\le17n^2.
\]

The original square grid has \(E=\Theta(n^3\log n)\) and \(D=\Theta(n/\sqrt{\log n})\). Hence even the near-extremal lattice spectrum admits realizations with radically different distance multiplicities.

**Scope.** This rules out recovering energy up to constant factors from ordinary EDM spectral invariants. It does not refute the proposed product inequality and does not rule out arguments retaining the individual support matrices \(A_d\).

## 3. All-times Gaussian information is exact but unstable

Let \(K_t=[e^{-tR_{ij}}]\).

First, all-times Gaussian positivity is equivalent to conditional negative semidefiniteness of \(R\), not an additional planar condition. Indeed, for centered \(B=XX^T\),

\[
K_t=\operatorname{diag}(e^{-tq_i})
\left(\sum_{j\ge0}\frac{(2t)^j}{j!}B^{\circ j}\right)
\operatorname{diag}(e^{-tq_i})\succeq0.
\]

Conversely, for \(v\perp\mathbf1\), differentiating \(v^TK_tv\ge0\) at \(t=0^+\) gives \(-v^TRv\ge0\). Also \(K_t\circ K_u=K_{t+u}\), so all their Schur powers are already in the same family.

The full Gaussian family does retain the distance distribution:

\[
\operatorname{tr}K_t^2=n+\sum_d r_d e^{-2ts_d}.
\]

Uniqueness of finite exponential sums recovers the labels and multiplicities. The issue is not missing information but lack of uniform conditioning.

### Lemma: color extraction has no bound depending only on n and D

Consider the rectangle

\[
P_\varepsilon=\{(0,0),(1,0),(0,\sqrt{1+\varepsilon}),(1,\sqrt{1+\varepsilon})\},\qquad\varepsilon>0.
\]

Its squared distances are \(1,1+\varepsilon,2+\varepsilon\); its Gram rank is exactly two. Let \(A_h\) be the horizontal-edge adjacency matrix. If

\[
A_h=aI+bJ+\int_0^\infty K_t\,d\mu(t)
\]

for a finite signed measure \(\mu\), then

\[
\boxed{\|\mu\|_{\mathrm{TV}}\ge e/\varepsilon.}
\]

**Proof.** Subtract a vertical off-diagonal entry from a horizontal one. This gives
\(1=\int(e^{-t}-e^{-(1+\varepsilon)t})\,d\mu(t)\). But
\[
0\le e^{-t}-e^{-(1+\varepsilon)t}\le\varepsilon t e^{-t}\le\varepsilon/e.
\]

The result follows. It applies to arbitrary choices of positive times and to signed finite sums as well as integrals. Schur products do not escape it, since they just add the time parameters.

For normalized entrywise resolvents \(L_a=[a/(a+R_{ij})]\), exactly the same reasoning gives the lower bound \(4/\varepsilon\), because
\[
\frac{a\varepsilon}{(a+1)(a+1+\varepsilon)}\le\frac{\varepsilon}{4}.
\]

Thus a strategy that first extracts distance colors by uniformly bounded Gaussian or entrywise-resolvent filters cannot work: the obstruction already occurs with fixed \(n=4,D=3\) and nondegenerate planar geometry.

### Stronger continuity obstruction

If \(R_j\to R_0\) entrywise and all off-diagonal squared distances stay at least \(a>0\), then

\[
\sup_{t\ge0}\|K_t(R_j)-K_t(R_0)\|_{\max}
\le\frac{\|R_j-R_0\|_{\max}}{ea}\longrightarrow0.
\]

Generic polygon-orbit rotations can converge to the aligned configurations above, while preserving the ordinary EDM spectrum exactly. Their energies remain \(O(n^2)\), whereas the limiting aligned set can have energy \(\Omega(n^3)\), or \(\Theta(n^3\log n)\) for the square grid.

It follows that no functional continuous on all such Gaussian profiles can approximate \(E\) within universal two-sided constant factors. For a proposed constant factor, fix n large enough that the energy jump exceeds its square, then take the generic sequence. The count D also jumps, so this does not contradict the proposed product inequality or rule out using D as additional discontinuous input. This is a stability obstruction, not a proof that every exact, discontinuous use of the full Gaussian family must fail.

## 4. An exact support-weighted polynomial inequality

Let \(h_k\) be the dimension of evaluations on P of real polynomials in two variables of total degree at most k. Then \(h_k\le\binom{k+2}{2}\). For every real polynomial f of degree at most k,

\[
\boxed{
n^2f(0)^2\le h_k\left(nf(0)^2+\sum_d r_d f(s_d)^2\right).
}
\]

**Proof.** Let \(F_{ij}=f(|p_i-p_j|^2)\), and let U annihilate all polynomial evaluations of degree at most k. Every monomial in \(f(|x-y|^2)\) has total degree at most 2k and therefore has degree at most k on at least one side. Thus \(u^TFv=0\) for all \(u,v\in U\). Since U has codimension \(h_k\), the positive and negative inertia indices of F are each at most \(h_k\): a larger definite eigenspace would intersect U. Apply Cauchy–Schwarz to the eigenvalues of the sign of F having positive trace. Finally \(\operatorname{tr}F=nf(0)\) and \(\|F\|_F^2=nf(0)^2+\sum_d r_df(s_d)^2\).

For the exact support annihilator
\(f(s)=\prod_{d=1}^D(1-s/s_d)\), this gives

\[
n\le\binom{D+2}{2}.
\]

This is the classical quadratic few-distance bound, not the conjectured estimate. In particular, exact support annihilation requires degree D, while the available planar feature dimension is quadratic in D. The argument alone supplies no required \(n/D\) multiplicity-variance gain.

### Exact rank-two Schur-power identity

Write \(z_i=x_i+iy_i\). If v is real and annihilates all polynomial evaluations of total degree less than k, then

\[
(-1)^k\sum_d s_d^k v^TA_dv
=\sum_{a=0}^k\binom{k}{a}^2
\left|\sum_i v_i z_i^a\bar z_i^{k-a}\right|^2\ge0.
\]

Expand \((z_i-z_j)^k(\bar z_i-\bar z_j)^k\); only terms with degree k in both variables survive. Thus the compressed leading k-th Gaussian jet is PSD and has rank at most k+1. This is a genuine rank-two constraint, but it does not make subsequent Taylor coefficients PSD.

## 5. Explicit sign obstruction for Gaussian/exterior-power arguments

For the unit square, put \(u=e^{-t}\). Then

\[
K_t=\begin{pmatrix}1&u\\u&1\end{pmatrix}^{\otimes2},\qquad
\det K_t=(1-u^2)^4.
\]

The determinant is nonnegative but its exponential-polynomial coefficients alternate in sign. Moreover, for \(v=(1,-1,-1,1)^T\), which annihilates constants and linear coordinates,

\[
v^TK_tv=4(1-e^{-t})^2=4t^2-4t^3+O(t^4).
\]

Therefore even after removing the constant and rank-two linear modes, coefficientwise positivity beyond the leading nonzero jet is false. The inverse Gaussian matrix also has mixed signs off the diagonal: adjacent entries are proportional to \(-u\) and opposite-corner entries to \(u^2\).

## Verification and checked references

`verify_distance_analysis.py` performs exact arithmetic in Q(sqrt(3)) for generic two-ring sets with n=6,12,18,24,48,72, checking moments, color counts, and the formula \(E=8n^2-18n\). An aligned n=12 example has \((D,E)=(7,3096)\), versus \((20,936)\) for generic rotations with exactly the same EDM spectrum. It also checks the square identities symbolically, the conditional Schur-power identity for k=1,2,3, and exact spot checks of the support-weighted polynomial inequality.

The source corpus confirms the precise ordered-energy normalization in Guth–Katz, arXiv:1011.4105, Proposition `quadbound`; square-lattice sharpness and the Cauchy–Schwarz loss in Cilleruelo–Sharir–Sheffer, arXiv:1306.0242, Section 1; and the classical absolute few-distance bound in Petrov–Pohoata, arXiv:1912.08181. The above investigation does not relabel any of these known results as the sharp conjecture.

## Remaining gap

The amplification is neither proved nor disproved here. A successful proof would have to establish the missing global multiplicity variance using joint endpoint/support information. Ordinary EDM spectral invariants do not retain that information; all-times Gaussian kernels retain it but exact color extraction is arbitrarily ill-conditioned; naive coefficientwise positivity is false. The results are clean obstructions to those particular shortcuts, not an impossibility theorem for every use of rank-two realization.
