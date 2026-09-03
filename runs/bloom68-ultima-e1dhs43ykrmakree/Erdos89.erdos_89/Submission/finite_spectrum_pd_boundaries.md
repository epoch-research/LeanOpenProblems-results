# Finite positive-definite circular spectra: exact arithmetic and SOS boundaries

## Status

This note does **not** prove or disprove

\[
\frac{\sum_v A(v)}{A(0)}\ll D\sqrt{\log(2D)}
\tag{Q}
\]

for all finitely supported, nonnegative, positive-definite functions on
\(\mathbb R^2\), nor the point-set inequality \(ED^2\gg n^5\).
No full-PD counterexample to either is claimed.

Applying (Q) to \(A=a_P\) would give the sharp conjectural planar distinct-
distance lower bound \(D\gg n/\sqrt{\log n}\). No inspected standard theorem
is being asserted to accomplish that. The results below instead establish
precise boundaries of the proposed methods:

1. **An exponential gap on exactly the same radii.** For every \(D\), there
   are \(D\) odd integer radii supporting a strictly positive scalar Bessel
   profile of mass \(2^D\) and central mass 1. Nevertheless, the Turan ratio
   of **every finite PD spectrum with rational coordinates on those circles
   is at most 2**, sharply. No number of rational angular samples repairs
   that gap.
2. **A genuinely finite additive bound.** If there are \(N\) opposite pairs
   of nonzero frequencies, their rational rank is \(m\), and \(r=N-m\), then
   \[
   \frac{\sum A}{A(0)}\le
   \min\{N+1,\ r+\lfloor r/2\rfloor+2\}.
   \tag{R}
   \]
   In particular the exact constant for rationally independent frequency
   representatives is 2. A proposed exponential finite-angular lift needs
   exponentially many independent additive relations, not merely many angles.
3. **One circle does not bound Newton or SOS complexity.** There are
   nonnegative PD polynomials on one circle with arbitrarily large additive
   rank and arbitrarily many Newton vertices. Their minimum number of complex
   squared-modulus factors, even allowing arbitrary additional finite
   frequencies, is exactly \(\lceil m/2\rceil\).
4. **Palette-only continuous PD multiplier certificates have an exponential
   barrier.** This applies also to nonradial multipliers, not just to an
   explicitly radial Bessel calculation. Angle-specific certificates are
   not excluded.

These are proved statements, not replacement conjectures. Their limitations
are stated explicitly below. No Lean files were changed.

## 1. Which compact group actually carries the polynomial?

Throughout, \(A\) is nonzero, so positive definiteness implies \(A(0)>0\).
Let \(S=\operatorname{supp}A\), and let
\(\Gamma=\langle S\rangle_{\mathbb Z}\subset\mathbb R^2\). Here positive
definiteness means positive definiteness for the **discrete translation
group**; a nonzero finite-support function is not a continuous PD function
on the usual Euclidean plane.

The finitely generated torsion-free group \(\Gamma\) is isomorphic to
\(\mathbb Z^m\). For a group basis \(g_1,\ldots,g_m\), the map

\[
x\longmapsto (e^{i\langle g_1,x\rangle},\ldots,
                e^{i\langle g_m,x\rangle})
\]

has dense image in \(\mathbb T^m\): an annihilating integer character would
be an integer relation among the basis vectors. Thus

\[
T(x)=\sum_v A(v)e^{i\langle v,x\rangle}\ge0\quad(x\in\mathbb R^2)
\]

is equivalent to nonnegativity of the associated Laurent polynomial on
**all of \(\mathbb T^m\)**, and to positive definiteness of \(A\). Extending
\(A\) by zero from \(\Gamma\) to \(\mathbb R^2\) preserves PD, since each
finite quadratic form splits into blocks indexed by cosets of \(\Gamma\).
The normalized Haar mean of \(T\) is \(A(0)\).

Consequently, “two physical variables” does not justify two-variable
Fejer--Riesz or elliptic compact-two-torus arguments. For \(m>2\), the
physical Laplacian becomes the constant-coefficient operator

\[
-\sum_{a,b=1}^m \langle g_a,g_b\rangle
                \partial_{\theta_a}\partial_{\theta_b},
\]

whose coefficient matrix has rank at most two, not an elliptic Laplacian
on \(\mathbb T^m\).

## 2. An exact full-PD obstruction to rational angular lifting

### Theorem 2.1: the odd-radius palette has rational Turan constant 2

Let \(r_1,\ldots,r_D\) be positive odd integers. If \(A\) is finite,
nonnegative and PD, and

\[
\operatorname{supp}A\subseteq
\{0\}\cup\{v\in\mathbb Q^2:|v|\in\{r_1,\ldots,r_D\}\},
\]

then

\[
\boxed{\sum_v A(v)\le2A(0).}
\tag{2.1}
\]

The constant is attained with all \(D\) circles occupied.

**Proof.** Write a rational point on one of the circles as
\((a/c,b/c)\), with \(a,b,c\) relatively prime. The equation
\(a^2+b^2=r_j^2c^2\) implies that \(c\) is odd: if it were even, reduction
modulo 4 would force both \(a\) and \(b\) even. Choose one common odd
denominator \(q\) for the finite spectrum. For \(v\ne0\), write
\(qv=(a,b)\). Then

\[
a+b\equiv a^2+b^2=q^2r_j^2\equiv1\pmod2.
\]

At the single physical point \(x_*=(\pi q,\pi q)\), every nonzero spectral
character equals \(-1\). Therefore

\[
0\le T(x_*)=A(0)-\sum_{v\ne0}A(v),
\]

which proves (2.1). For sharpness take
\(T(x)=1+D^{-1}\sum_{j=1}^D\cos(r_jx_1)\). It is nonnegative, has central
coefficient 1, total coefficient mass 2, and all prescribed circles occur.
\(\square\)

The same proof works when all squared radii are odd integers, provided the
frequencies are rational. Similarity transports the statement to similar
copies of \(\mathbb Q^2\). It is **not** a theorem about arbitrary real
angular frequencies.

### Theorem 2.2: the exponential radial example can use these same radii

For every \(D\), one can choose increasing odd integers \(r_j\), with
arbitrarily large successive gaps, such that

\[
F_D(t)=1+\sum_{j=1}^D2^{j-1}J_0(r_jt)>0\qquad(t\ge0).
\tag{2.2}
\]

In particular, \(F_D(0)=2^D\).

**Proof.** The standard integral representation of \(J_0\) gives
\(|J_0|\le1\), \(J_0(t)\to0\), and
\(\min_{t\ge0}J_0(t)=-\beta\) for some \(0<\beta<1\).
The strict inequality follows because the average of
\(\cos(t\cos\theta)\) is never \(-1\), and the function tends to zero at
infinity. No numerical value of the minimum is needed.

Start with \(r_1=1\), so \(F_1\ge1-\beta>0\). Suppose
\(F_k\ge\varepsilon_k>0\), and put \(S=F_k(0)=2^k\). By continuity there
is \(\delta>0\) such that
\(F_k(t)\ge(1+\beta)S/2\) for \(0\le t\le\delta\).
Choose an odd integer \(R>r_k\), as large as desired, so that

\[
S\sup_{s\ge R\delta}|J_0(s)|\le\varepsilon_k/2.
\]

For \(t\le\delta\),
\(F_k(t)+S J_0(Rt)\ge(1-\beta)S/2>0\); for \(t\ge\delta\), it is at
least \(\varepsilon_k/2\). Set \(r_{k+1}=R\) and continue. \(\square\)

**The precise gap.** The positive measure

\[
\mu=\delta_0+\sum_{j=1}^D2^{j-1}\sigma_{r_j}
\]

has nonnegative Fourier transform, where \(\sigma_r\) is uniform
probability measure on the circle of radius \(r\). But if each
\(\sigma_{r_j}\) is replaced by *any* finite positive rational-coordinate
angular quadrature of mass 1, retaining central mass 1, the resulting
polynomial takes the value

\[
1-\sum_{j=1}^D2^{j-1}=2-2^D
\]

at the parity point from Theorem 2.1. Thus it is not PD for \(D\ge2\).
To repair it solely by increasing the central coefficient requires that
coefficient to be at least \(2^D-1\), and is sufficient by the triangle
inequality. The repaired ratio is at most 2.

This is a full finite-character witness, not a scalar radial relaxation
being asserted to be finite PD. Angular quadratures can converge locally
uniformly to (2.2), while their global negative values persist at escaping
physical points \(x_*\).

### A related sharp Gaussian filtration bound

For \(A\) on \(\mathbb Z[i]\), let \(m_2\) be the number of occupied values
of \(v_2(|v|^2)\), \(v\ne0\). Then

\[
\sum A\le2^{m_2}A(0).
\tag{2.3}
\]

Indeed, with \(\pi=1+i\), define
\(S_k=\sum_{v\in\pi^k\mathbb Z[i]}A(v)\) and
\(M_k=S_k-S_{k+1}\). Restrict PD to \(\pi^k\mathbb Z[i]\) and evaluate its
Fourier polynomial at the nontrivial character of the index-two quotient
\(\pi^k\mathbb Z[i]/\pi^{k+1}\mathbb Z[i]\). This gives
\(M_k\le S_{k+1}\), hence \(S_k\le2S_{k+1}\). Empty layers incur no factor,
and the last tail is \(A(0)\).

The dependence \(2^{m_2}\) is sharp, even for genuine autocorrelations. Take

\[
P_m=\left\{\sum_{j=0}^{m-1}\epsilon_j(1+i)^j:
                   \epsilon_j\in\{0,1\}\right\}.
\]

The least differing digit shows that its \(2^m\) points are distinct and
that its nonzero differences have exactly the valuations \(0,\ldots,m-1\).
Thus \(a_{P_m}\) has ratio \(2^m\). Its number of **Euclidean radii** is not
asserted to be \(m\). Replacing \(D\) by the number of valuation layers
would therefore be invalid.

## 3. A finite-spectrum additive-rank theorem

Choose one representative from each opposite nonzero frequency pair:
\(S=\{0,\pm v_1,\ldots,\pm v_N\}\). Put
\(m=\dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}\{v_j\}\) and
\(r=N-m\). Thus \(r\) is the rational dimension of the space of relations
among these \(N\) vectors (equivalently the rank of their integer relation
lattice).

### Theorem 3.1

For every finite nonnegative PD \(A\) with this support,

\[
\boxed{\frac{\sum A}{A(0)}\le
\min\{N+1,\ r+\lfloor r/2\rfloor+2\}.}
\tag{3.1}
\]

This does not require circular spectra or dimension two.

**First lemma: \(N\) opposite pairs give the bound \(N+1\).** Choose a
translation-invariant total order on \(\Gamma\cong\mathbb Z^m\), for example
lexicographic order on its coordinates. Every finite subgraph of its Cayley
support graph has a least vertex with at most \(N\) neighbors: precisely
one direction of each opposite pair is positive. Every induced subgraph
has this property, so greedy deletion and reverse insertion give an
\((N+1)\)-coloring.

For a finite set \(F\), realize the PSD matrix
\((A(p-q))_{p,q\in F}\) as a Gram matrix \((\langle u_p,u_q\rangle)\).
Vectors in any one color class are mutually orthogonal. If there are \(k\)
classes and \(w_j\) is the sum in class \(j\), then

\[
\sum_{p,q\in F}A(p-q)
 =\left\|\sum_{j=1}^k w_j\right\|^2
 \le k\sum_j\|w_j\|^2=kA(0)|F|.
\tag{3.2}
\]

Take coordinate boxes forming a Folner sequence in \(\Gamma\cong\mathbb
Z^m\). For each fixed displacement the overlap ratio tends to one, so
(3.2), divided by \(|F|\), tends to \(\sum A\le (N+1)A(0)\).

**Second lemma: compress the independent directions.** Choose
\(v_1,\ldots,v_m\) as a rational basis. Each remaining vector has a nonzero
rational coordinate linear form \(\ell_j(t_1,\ldots,t_m)\),
\(j=1,\ldots,r\). The polynomial \(H=\prod_j\ell_j\) is nonzero and has
total degree \(r\). Put \(q=\lfloor r/2\rfloor+1\). Since \(2q>r\), a
nonzero polynomial of degree at most \(r\) in each variable cannot vanish
on the whole grid

\[
\{-q,\ldots,-1,1,\ldots,q\}^m.
\]

(The usual one-variable root bound, applied inductively, proves this.)
Choose a grid point where \(H\ne0\), and let
\(\phi:\operatorname{span}_{\mathbb Q}S\to\mathbb Q\) send the chosen
basis to these coordinates. No nonzero frequency is sent to zero. The
images of the basis occupy at most \(q\) opposite pairs; the remaining
vectors add at most \(r\) more.

Push forward \(A\) along \(\phi\). The pushforward is nonnegative and PD:
its Fourier transform evaluates the original nonnegative polynomial at
characters of \(\Gamma\). Its total mass and central coefficient are
unchanged. Its finitely generated image in \(\mathbb Q\) is cyclic. Apply
the first lemma to its at most \(q+r\) opposite pairs. This gives
\((q+r+1)A(0)\), proving (3.1). \(\square\)

For example, the three frequencies \(u,v,u-v\) of an equilateral triangle
have \(N=3,m=2,r=1\), and the ratio 3 of
\(|1+e^{i\langle u,x\rangle}+e^{i\langle v,x\rangle}|^2\) attains (3.1).
For independent representatives, \(r=0\), and the exact bound is 2.

In particular, a hypothetical ratio \(2^D\) requires
\(r\ge(2/3)(2^D-2)\). This is a necessary condition on actual additive
relations, not a sufficient construction. A single circle can have
arbitrarily many relations, so (3.1) alone does not imply (Q).

### Generic angular perturbations destroy every ratio greater than 2

With independent representatives and fixed coefficients \(a_j>0\),

\[
\inf_x\left(a_0+2\sum_j a_j\cos\langle v_j,x\rangle\right)
 =a_0-2\sum_j a_j.
\tag{3.3}
\]

This follows from density in the full torus. In any prescribed open arcs
on any fixed nonzero circles, independent representatives can be chosen:
choose each new point outside the countable rational span of the preceding
ones. Thus any finite coefficient profile of ratio greater than 2 has
arbitrarily small **radius-preserving** angular perturbations which are
not PD. For total mass \(2^D\), central mass 1, the infimum is precisely
\(2-2^D\). In the independent case the infimum need not be attained at a
finite physical point; its negativity still contradicts nonnegativity.

More generally, if the groups generated by different shells form a direct
sum, then the ratio is at most the one-circle Bessel constant
\(1+1/\beta\), independent of \(D\). The minima of the shell polynomials
can then be attained independently on the product dual group. Each shell
has minimum at most \(-\beta\) times its off-central mass, by averaging at
the one-circle Bessel minimum. Sum these inequalities and use \(T\ge0\).

## 4. Exact one-circle Newton and SOS complexity

### Theorem 4.1

For every \(m\ge1\), there is a finite, coefficientwise nonnegative PD
polynomial with \(D=1\), ratio 2, additive rank \(m\), and \(2m\) physical
Newton vertices. In any representation as a sum of squared moduli of
finite exponential polynomials, the number of summands is at least
\(\lceil m/2\rceil\). This minimum is attained if additional half-frequencies
are allowed.

**Construction and proof.** Take distinct primes \(p_j\) and

\[
v_j=\left(p_j^{-1/2},\sqrt{1-p_j^{-1}}\right),\qquad
T_m(x)=1+\frac1m\sum_{j=1}^m\cos\langle v_j,x\rangle.
\tag{4.1}
\]

These are unit vectors. They are rationally independent because their
first coordinates \(\sqrt{p_j}/p_j\) are independent in the standard
multiquadratic basis. Clearly \(T_m\ge0\), \(A(0)=1\), and
\(A(\pm v_j)=1/(2m)\). Strict convexity of the circle makes all \(2m\)
nonzero frequencies vertices of the physical Newton polygon; on the group
torus the Newton polytope is the \(m\)-dimensional cross-polytope.

On that torus, the polynomial is
\(1+m^{-1}\sum_j\cos\theta_j\). It vanishes at
\(\theta_*=(\pi,\ldots,\pi)\), where its real Hessian is \(I_m/m\).
If \(T_m=\sum_{\ell=1}^k |Q_\ell|^2\), every \(Q_\ell\) vanishes there.
At a common zero, the Hessian of one squared complex modulus is a sum of
two rank-one real positive semidefinite forms, and has rank at most two.
Therefore \(m\le2k\).

Allowing the \(Q_\ell\) to use frequencies outside the original group does
not evade this argument. Adjoin all those finitely many frequencies to get
\(\Lambda\cong\mathbb Z^h\). The dual map
\(\widehat\Lambda\to\widehat\Gamma\) is a surjective torus homomorphism
with differential of rank \(m\). Lift \(\theta_*\); the pulled-back Hessian
still has rank \(m\). The identity holds on this whole torus by the density
argument of Section 1.

Finally,

\[
T_m=\frac2m\sum_{j=1}^m
             \cos^2\bigl(\langle v_j,x\rangle/2\bigr).
\]

Pair two real cosines as the real and imaginary parts of one complex
factor. This uses exactly \(\lceil m/2\rceil\) squared moduli. \(\square\)

**Scope.** This rules out bounding Newton complexity or the number of SOS
factors by any function of \(D\) alone. It does not rule out arguments
using arbitrarily many factors with a suitable weighted estimate, and it
is not a counterexample to (Q). Indeed these examples are already mixtures
of two-point nonnegative autocorrelations; no false nonnegative-factor
assumption is being made.

### A separate spectral-projection obstruction even on the square torus

Let \(\Pi_N\) project onto the Fourier modes
\(\{v\in\mathbb Z^2:|v|^2=N\}\). With normalized Haar measure,

\[
\|\Pi_N\|_{L^2\to L^\infty}=\sqrt{r_2(N)}.
\]

Cauchy--Schwarz gives the upper bound, and the reproducing kernel at zero
attains it. For \(N=5^k\), Gaussian factorization gives
\(r_2(5^k)=4(k+1)\). Thus even one eigenspace has unbounded projection
norm. This is an obstruction to a dimension-free **linear projection**
argument, not to a nonlinear estimate on the nonnegative-PD cone. In fact
(2.3) bounds the nonnegative-PD one-shell ratio here by 2.

## 5. The exact barrier for palette-only continuous PD multipliers

A common Turan certificate is a continuous real PD function \(h\) on the
usual plane such that \(h(0)=1\), \(h(v)\le0\) on the allowed nonzero
spectrum, and its Bochner measure \(\nu\) has atom \(c>0\) at zero. Then

\[
c\sum A\le\int T\,d\nu=\sum_v A(v)h(v)\le A(0).
\tag{5.1}
\]

Suppose this certificate depends only on the palette in the sense that
\(h(v)\le0\) on the **entire** \(D\) circles of Theorem 2.2. It need not be
radial. Integrate it against that theorem's measure \(\mu\):

\[
1\ge\int h\,d\mu=\int F_D(|x|)\,d\nu(x)
  \ge c F_D(0)=c2^D.
\]

Hence

\[
\boxed{c\le2^{-D};\qquad \text{the bound }1/c\text{ is at least }2^D.}
\tag{5.2}
\]

Thus the exponential barrier applies to every such continuous PD
multiplier, even a nonradial one. It is not avoided by rewriting the
scalar calculation as a positive convolution or spectral-filter argument.

**Important restriction.** A certificate tailored to the actual finite
angles is not covered. For the rational spectrum in Theorem 2.1,
\(h(v)=(1+\cos(\pi q(v_1+v_2)))/2\) has central Bochner atom \(1/2\) and
vanishes on that finite spectrum. It is not nonpositive on the entire
circles. So (5.2) does not obstruct all continuous angle-dependent methods.

## 6. Relation to existing theorems and ordinary distance-graph coloring

The following sources were inspected in the local source corpus; an online
literature search was unavailable.

* S. Gy. Revesz, **Turan's extremal problem on locally compact abelian
  groups**, arXiv:0904.1824. The packing bound gives
  \(\int f\le f(0)/\rho\) if a set of density \(\rho\) has difference set
  avoiding the permitted nonzero support. This is a real theorem, but
  obtaining \(\rho\gg1/(D\sqrt{\log D})\) is not supplied by it. Euclidean
  open-domain volume bounds cannot be applied to discrete circular spectra
  by assigning the union of circles its Lebesgue measure.
* F. Dai, D. Gorbachev, S. Tikhonov, **Nikolskii inequality for lacunary
  spherical polynomials**, arXiv:1905.00323, Theorem 1. The estimate retains
  a largest-degree factor: in their notation it is
  \((n^{d-1-\ell_0}m)^{1/p-1/q}\), with
  \(\ell_0=\min\{\ell,(d-1)/2\}\). These are spherical harmonics on a
  physical sphere, not plane exponentials whose *frequencies* lie on
  circles. This is not the requested shell-count-only theorem.
* B. Bukh, **Measurable sets with excluded distances**,
  arXiv:math/0703856. Widely separated scales give exponentially small
  measurable avoidance density. The paper explicitly distinguishes
  ordinary from measurable chromatic number and records Erdős's conjecture
  of polynomial growth of the former in the number of distances.
* J. Steinhardt, **On Coloring the Odd-Distance Graph**, arXiv:0908.1452,
  proves infinite **measurable** chromatic number; its concluding section
  explicitly leaves the nonmeasurable/sublattice passage unresolved.

There is a rigorous reason the last distinction matters here. Equation
(3.2) shows that for **any proper \(k\)-coloring**, measurable or not, of
the Cayley support graph of \(A\),

\[
\sum A/A(0)\le k.
\]

Consequently, a full finite-PD construction with ratio exponential in
\(D\) would force an exponential lower bound for the **ordinary** chromatic
number of a planar graph with \(D\) forbidden distances, contrary to the
polynomial-growth conjecture recorded by Bukh. A continuous Bessel profile
or a measurable density theorem does not do that. A merely super-
\(D\sqrt{\log D}\) but polynomial counterexample would not, by itself,
contradict that conjecture.

## 7. Verification and what remains

`verify_finite_spectrum_pd_boundaries.py` checks, using exact arithmetic:

* odd common denominators, exact circle equations and the common negative
  parity character for rational angular samples;
* the sharp Gaussian filtration inequalities on the actual digit sets;
* the nonzero rational compression used in Theorem 3.1 on a collection of
  finite test supports, and its sharp independent/triangle examples;
* the SOS identity and full-rank Hessian in Theorem 4.1;
* the circle multiplicity \(r_2(5^k)=4(k+1)\) in finite cases.

The infinite-dimensional and asymptotic assertions are proved above; they
are not inferred from numerical sampling. In particular no numerical
positivity check on a bounded physical window is treated as full PD.

The unrestricted finite-spectrum inequality (Q) remains open in this
investigation. What is settled here is that rational angular discretization
cannot lift even specially chosen exponentially large radial profiles;
small additive-relation rank cannot support such a lift either; and neither
bounded Newton/SOS complexity nor a palette-only continuous PD multiplier
can supply the missing theorem. None of this solves exact complete
positivity, assumes a nonnegative autocorrelation factor, or yields the
point-set energy inequality. No radius/height bound was assumed, and the
known compact-height PD energy estimate was not promoted to a bound on \(D\).
