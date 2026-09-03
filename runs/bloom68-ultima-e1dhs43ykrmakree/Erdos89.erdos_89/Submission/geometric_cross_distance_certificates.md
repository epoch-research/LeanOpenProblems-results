# Finite cross-distance certificates for disk localization

## Status

The proposed universal disk recurrence remains **unproved and undisproved** here:

\[
 K(P)^2\le M_{\rm disk}(P)^2+C,
 \qquad K(P)=|P|/D(P),
\]

where, for \(n=|P|\ge4\),

\[
 M_{\rm disk}(P)=\max_{\substack{Q=P\cap B,\ B\text{ a closed disk}\\
                      2\le |Q|\le n/2}} |Q|/D(Q).
\]

No counterexample to this recurrence, and no sharp Erdős lower bound, is claimed. In particular, this note does not revive the invalid three-parity-class/restored-annulus example.

The results obtained are:

1. A finite **cross-distance / parabolic-lens inequality**. Equal-distance triples to exterior centers have unique circumcenters and must occupy explicit thin lenses about their longest edges. The inequality uses the actual cross-distance support, not a union of within-cell palettes.
2. An exact **proper field-core inequality**: an exterior point sees at least half as many distances as there are points in a similarity image of a subfield plane. Consequently, a proper field core of density at least \(\alpha\) gives the requested disk recurrence with \(C=4/\alpha^2-4\). For a half-density proper core, \(C=12\).
3. An exact **one-point perturbation identity** for square grids. Moving one corner arbitrarily little can create \(n-1\) new distances, all distinct from the old palette. This rules out a distance-count-preserving general-position perturbation shortcut, not disk localization.
4. A genuine-grid obstruction even to an **actual-exterior-circumcenter** upper bound: for macroscopic admissible disks \(A\) and macroscopic exterior sets \(B\subset P\), the ratio \(T_B(A)/[|A|^2(M_{\rm disk}(P)^2+1)]\) is unbounded. Retaining actual centers, but counting their triples without suitable weights, still does not supply the needed budget.

All assertions concern actual Euclidean points. The general cross-distance inequalities make no label-spacing, integrality, or coefficient-recovery assumption. The restricted field-core theorem states its coordinate hypothesis explicitly; the obstruction examples are actual grids, not integrality hypotheses imposed on arbitrary point sets. These are partial results, not a near-proof of the universal recurrence. No historical-priority claim is made, and no Lean file was modified.

---

## 1. An exact finite cross-distance inequality

Let \(A,B\subset\mathbb R^2\) be finite, with

\[
 A\subset \overline B(c,r),\qquad
 B\subset \{p:|p-c|\ge R\},\qquad R>r\ge0.
\]

Write \(m=|A|\), \(s=|B|\), and

\[
 d=D(A,B)=|\{|a-p|:a\in A,\ p\in B\}|.
\]

Assume \(m,s\ge1\), so \(d\ge1\). Put \(h=R-r>0\).

### The lens statistic

For distinct \(a,b\in A\), let \(L=|a-b|\). For \(z\in A\setminus\{a,b\}\), put

\[
 t=\frac{(z-a)\cdot(b-a)}{L^2},\qquad
 v=\operatorname{dist}(z,\operatorname{line}(a,b)).
\]

Let \(\ell_h(a,b)\) count those \(z\) for which

\[
 \begin{gathered}
 z\notin\operatorname{line}(a,b),\qquad
 |a-z|<L,\quad |b-z|<L,\quad 0<t<1,\\
 2h v\le L^2t(1-t).
 \end{gathered}                                                    \tag{1.1}
\]

Define

\[
 \mathcal L_h(A)=\sum_{\{a,b\}\subset A}\ell_h(a,b).                 \tag{1.2}
\]

Thus only a triangle's unique longest edge can count it; no triangle is counted more than once. The last condition is a genuinely geometric parabolic-lens condition. The greatest permitted height over an edge of length \(L\) is \(L^2/(8h)\).

For positive integers \(d\), define the exact balanced-bin function

\[
 F_d(m)=(d-u)\binom q3+u\binom{q+1}3,
 \qquad m=qd+u,\quad 0\le u<d.                                    \tag{1.3}
\]

As usual \(\binom k3=0\) for integers \(0\le k<3\).

### Theorem 1

\[
 \boxed{\quad sF_d(m)\le \mathcal L_{R-r}(A).\quad}                 \tag{1.4}
\]

More precisely, if \(d_p=|\{|p-a|:a\in A\}|\), then

\[
 \sum_{p\in B} F_{d_p}(m)
 \le T_B(A)\le \mathcal L_{R-r}(A),                               \tag{1.5}
\]

where \(T_B(A)\) is the number of unordered noncollinear triples from \(A\) whose circumcenter belongs to \(B\).

If \(m>2d\), the following simpler finite inequality follows:

\[
 \boxed{\quad
 s\frac{m(m-d)(m-2d)}{6d^2}\le \mathcal L_{R-r}(A).
 \quad}                                                          \tag{1.6}
\]

In particular, if \(d\le m/4\),

\[
 d^2\ge\frac{s m^3}{16\mathcal L_{R-r}(A)},                        \tag{1.7}
\]

with the understanding that \(\mathcal L_{R-r}(A)=0\) makes \(d\le m/4\) impossible.

### Proof

Fix \(p\in B\). Its actual distances partition \(A\) into concentric-circle fibers of sizes \(k_{p,1},\ldots,k_{p,d_p}\). Therefore

\[
 \sum_j k_{p,j}=m,
 \qquad
 \sum_j\binom{k_{p,j}}3
   =\#\{T\subset A:|T|=3,\ \operatorname{cc}(T)=p\}.              \tag{1.8}
\]

Three distinct points on one circle cannot be collinear, and a noncollinear triple has exactly one circumcenter. Consequently the right-hand sides of (1.8), for different \(p\), count disjoint collections of triples. In fact their sum is exactly \(T_B(A)\).

The discrete function \(k\mapsto\binom k3\) is convex on nonnegative integers: its forward difference is \(\binom k2\). Moving one object from a bin at least two larger than another bin does not increase the sum. Hence the smallest possible sum for \(m\) objects in at most \(d\) bins is exactly \(F_d(m)\). This proves the first inequality in (1.5) and the lower bound \(sF_d(m)\).

It remains to prove the lens condition. Let \(a,b,z\in A\) have circumcenter \(p\in B\). Seen from \(p\), the containing disk \(\overline B(c,r)\) subtends an angle strictly less than \(\pi\), since \(|p-c|\ge R>r\). Thus the three circle points lie on a common arc of angular length less than \(\pi\). The two extreme points on that arc, say \(a,b\), form the unique longest side. The third point lies on its minor arc, and its projection onto the chord lies strictly between the endpoints.

Use chord coordinates

\[
 a=(-L/2,0),\quad b=(L/2,0),\quad p=(0,H),\quad z=(x,y).
\]

The chord midpoint is in \(\overline B(c,r)\), so

\[
 |H|=|p-(a+b)/2|\ge R-r=h.                                       \tag{1.9}
\]

The minor-arc point \(z\) has \(y\) opposite in sign to \(H\). The circle equation therefore gives

\[
 x^2+y^2+2|H||y|=L^2/4.
\]

It follows that

\[
 2h|y|\le L^2/4-x^2=L^2t(1-t),\qquad 0<t<1.                      \tag{1.10}
\]

Thus the triple contributes once to \(\mathcal L_h(A)\), via its unique longest side. This proves (1.4) and (1.5).

For \(m>2d\), the balanced bin sizes in (1.3) are at least two. The real polynomial \(x(x-1)(x-2)/6\) is convex on \([1,\infty)\). Applying Jensen to those balanced sizes yields

\[
 F_d(m)\ge d\binom{m/d}{3}
       =\frac{m(m-d)(m-2d)}{6d^2}.
\]

This proves (1.6). If \(d\le m/4\), then

\[
 m(m-d)(m-2d)\ge 3m^3/8,
\]

which gives (1.7). QED.

### Disjoint witnesses, not only a moment count

For each fixed \(p\in B\), there exist at least

\[
 \max\left(0,\left\lceil\frac{m-2d_p}{3}\right\rceil\right)       \tag{1.11}
\]

vertex-disjoint triples in \(A\) having circumcenter \(p\). Indeed, take \(\lfloor k_{p,j}/3\rfloor\) disjoint triples in each circle fiber and use

\[
 \sum_j\lfloor k_{p,j}/3\rfloor\ge (m-2d_p)/3.
\]

All these triples satisfy the same lens condition. Witness triples for different centers cannot be identical, although their vertex sets may overlap. This is actual endpoint-consistent geometric reconstruction, not an assertion of independence between rows.

### Balanced-cut consequence

Suppose \(A,B\subset P\) satisfy the above geometric separation and

\[
 |A|\ge\alpha n,\qquad |B|\ge\beta n,
 \qquad K(P)\ge4/\alpha.
\]

We may use \(d_0=D(P)\) instead of \(d\) in (1.4), since each pinned row has at most \(d_0\) fibers. Then \(d_0\le m/4\), and

\[
 \boxed{\quad
 \frac{\mathcal L_{R-r}(A)}{\binom m2}
 \ge\frac{\alpha\beta}{8}K(P)^2.
 \quad}                                                          \tag{1.12}
\]

Indeed (1.7), rearranged and divided by \(\binom m2\), gives at least
\(s m^2/[8(m-1)d_0^2]\ge sm/(8d_0^2)\).

This is a necessary geometric condition for a low-distance, spatially separated balanced cut. It does **not** imply disk contraction: an average count of points in thin lenses is not a local cardinality-to-distance ratio.

---

## 2. Proper field cores force linearly many actual cross-distances

### Theorem 2

Let \(F\subset\mathbb R\) be any subfield. Let \(T\) be any planar similarity, and let

\[
 A\subset T(F^2),\qquad p\notin T(F^2).
\]

Every circle centered at \(p\) contains at most two points of \(A\). Hence

\[
 \boxed{\quad D_p(A)\ge\lceil |A|/2\rceil.\quad}                  \tag{2.1}
\]

### Proof

Apply \(T^{-1}\), which preserves equality of distances. If three distinct points \(a_1,a_2,a_3\in F^2\) lay on a circle centered at \(p\), they would be noncollinear. Subtracting the first squared-distance equation from the other two gives

\[
 2p\cdot(a_i-a_1)=|a_i|^2-|a_1|^2\in F,\qquad i=2,3.
\]

This is a nonsingular two-by-two linear system over \(F\). Its unique solution belongs to \(F^2\), contrary to the assumption on \(p\). QED.

### Actual constant-loss disk recurrence for a restricted but broad family

Let \(P\) have \(n\ge4\) points. Suppose the field core

\[
 A=P\cap T(F^2)
\]

is proper and has \(|A|\ge\alpha n\), where \(0<\alpha\le1\). Choose \(p\in P\setminus A\). Then (2.1) gives

\[
 D(P)\ge |A|/2\ge\alpha n/2,
 \qquad K(P)^2\le4/\alpha^2.
\]

The closed diameter disk of a closest pair selects exactly that pair: any other point in the disk would be closer to at least one endpoint. Therefore \(M_{\rm disk}(P)\ge2\), and

\[
 \boxed{\quad
 K(P)^2\le M_{\rm disk}(P)^2+4/\alpha^2-4.
 \quad}                                                          \tag{2.2}
\]

For \(\alpha=1/2\), the loss is \(12\). No geometric separation between the core and the outlier is required. The outlier can be arbitrarily close to a core point.

Equivalently, the following exact coherence condition holds:

\[
 |P\cap T(F^2)|>2D(P)\quad\Longrightarrow\quad P\subset T(F^2).    \tag{2.3}
\]

Thus one cannot form a high-\(K\) counterexample by retaining a positive-density rational-grid core and adding even one point outside its rational similarity plane. This does not settle configurations lying entirely in that plane, nor high-rank configurations with no large proper field core.

### Coordinate-free reconstruction version

Let \(\operatorname{Circ}(A)\) be the set of circumcenters of noncollinear triples from \(A\). For arbitrary \(A\subset P\),

\[
 |A|\ge 2D(P)+2\quad\Longrightarrow\quad P\subset\operatorname{Circ}(A).
                                                                    \tag{2.4}
\]

For each \(p\in P\), at least \(|A|-1\) members of \(A\) are different from \(p\). They occupy at most \(D(P)\) positive-distance fibers. One fiber has at least three points. If \(p\notin A\), the weaker condition \(|A|\ge2D(P)+1\) suffices.

---

## 3. An exact one-point perturbation identity

Let

\[
 G_L=\{0,\ldots,L-1\}^2,\quad L\ge2,
 \qquad 0<\varepsilon\in\mathbb Q,\quad 0<2\varepsilon^2<1,
\]

and replace just the corner \((0,0)\) by \((\varepsilon\sqrt2,0)\):

\[
 P_{L,\varepsilon}=
 (G_L\setminus\{(0,0)\})\cup\{(\varepsilon\sqrt2,0)\}.
\]

### Theorem 3

\[
 \boxed{\quad D(P_{L,\varepsilon})=D(G_L)+L^2-1.\quad}              \tag{3.1}
\]

### Proof

First, deleting \((0,0)\) does not remove a grid distance. A vector \((a,b)\), with \(a,b>0\), is also realized by \((a,0)\) and \((0,b)\). Horizontal and vertical vectors can be realized on the row or column numbered 1. Thus

\[
 D(G_L\setminus\{(0,0)\})=D(G_L).
\]

The squared distance from the new point to \((a,b)\ne(0,0)\) is

\[
 a^2+b^2+2\varepsilon^2-2\varepsilon a\sqrt2.                      \tag{3.2}
\]

Equality between two expressions in (3.2) first gives equality of the irrational coefficients, hence equality of \(a\), and then equality of \(b^2\), hence of \(b\), because \(b\ge0\). So all \(L^2-1\) new cross-distances are distinct.

If \(a>0\), (3.2) is irrational. If \(a=0\), it is the noninteger rational number \(b^2+2\varepsilon^2\). Consequently none belongs to the old integer squared-distance palette. This proves (3.1). QED.

The perturbation size \(\varepsilon\sqrt2\) can tend to zero at any prescribed rate. Nevertheless, since the classical square-grid estimate is

\[
 D(G_L)=\Theta(L^2/\sqrt{\log L}),
\]

one has \(D(P_{L,\varepsilon})/D(G_L)=\Theta(\sqrt{\log L})\). The new distance values can be arbitrarily close to old values; their count does not become small. This rules out a continuity/general-position shortcut. It is not a counterexample to the disk recurrence: the perturbed set has bounded \(K\).

---

## 4. Exact limitations of the cross-distance estimate

Theorem 1 supplies no universal upper bound for \(\mathcal L_h(A)\) in terms of \(M_{\rm disk}\). In fact, even a proposed estimate of the form

\[
 \mathcal L_h(A)\le C|A|^2\bigl(M_{\rm disk}(P)^2+1\bigr)
                                                                    \tag{4.1}
\]

for \(h\) a fixed positive multiple of the diameter of \(A\) is false on ordinary planar grids.

For example, take the integer points in a large square \(P=\{0,\ldots,10N\}^2\), and let \(A\) be the grid points in its lower-left \(N\)-by-\(N\) square. Put \(h=N\). There is an open positive-volume set of noncollinear triples in the rescaled unit square satisfying (1.1) strictly: choose endpoints near \((1/10,1/5)\), \((9/10,1/5)\), and a middle point near \((1/2,1/4)\). The longest side is unique, and at the stated triple

\[
 2h v/N^2=1/10<4/25=L^2t(1-t)/N^2.
\]

Small fixed neighborhoods preserve all strict inequalities. Counting lattice points in their dilates gives

\[
 \mathcal L_N(A)\ge cN^6=\Omega(|A|^3).
\]

On the other hand, the established Guth–Katz lower bound, applied to every subset \(Q\subset P\), gives

\[
 M_{\rm disk}(P)^2=O((\log|P|)^2)=O((\log N)^2).
\]

This already contradicts (4.1); no sharp Erdős bound is being assumed. The same example can be made a separated balanced-annulus example with fixed constants: take \(c=(N/2,N/2)\), \(r=N\), \(R=2N\), and \(B=P\setminus B(c,2N)\). Then \(A\subset\overline B(c,r)\), \(B\) is exterior, \(|A|\) and \(|B|\) are fixed positive fractions of \(|P|\), and \(h=R-r=N\).

This is a valid obstruction to **that proposed unnormalized lens-count upper bound**, not a counterexample to disk contraction. A more selective or weighted use of actual circumcenters might avoid it, but no successful bound of that kind is supplied here.

### 4.1 The obstruction persists when the circumcenters must be actual points

One might try to avoid the overcount in \(\mathcal L_h\) by retaining the exact statistic \(T_B(A)\). The following stronger counterexample shows that an unweighted triple count still cannot be upper-bounded by the desired squared-ratio budget.

### Theorem 4

There is an explicit sequence of square-grid sets \(P\), with \(n=|P|\to\infty\), and sets

\[
 A=P\cap\overline B(c,r),\qquad
 B\subset P\cap\{p:|p-c|\ge2r\},
\]

such that both \(|A|\) and \(|B|\) are bounded below by fixed positive multiples of \(n\), \(2\le|A|\le n/2\), and

\[
 T_B(A)\ge c_1 n^2(\log n)^3.                                    \tag{4.2}
\]

Consequently

\[
 \boxed{\quad
 \frac{T_B(A)}{|A|^2(M_{\rm disk}(P)^2+1)}\longrightarrow\infty.
 \quad}                                                          \tag{4.3}
\]

Thus replacing \(\mathcal L_h\) by the count of triples whose circumcenters really belong to the exterior point set does **not** make an upper bound of the form (4.1) true.

### A finite cover inequality proving the assertion

Take \(L\) divisible by 8 and put

\[
 P_L=\mathbb Z^2\cap[-L,L]^2,\qquad
 P_0=\mathbb Z^2\cap[-L/2,L/2]^2.
\]

Let the 289 centers \(c_j\) be the grid

\[
 \{(-L+kL/8,-L+\ell L/8):0\le k,\ell\le16\}.
\]

Set

\[
 r=L/8,\quad A_j=P_L\cap\overline B(c_j,r),\quad
 B_j=\{p\in P_0:|p-c_j|\ge2r\}.
\]

The \(r\)-disks cover \(P_L\): the nearest center is within \(\sqrt2L/16<r\). Assign each point to one nearest center, with any fixed tie-break. Every \(A_j\) has \(\Theta(L^2)\) points and is admissible for \(M_{\rm disk}(P_L)\). For the lower bound, an inward quarter-disk of radius \(r\) lies inside the square, uniformly for every center; for the upper bound, the containing square has at most \((L/4+1)^2\) lattice points. Also

\[
 |B_j|\ge(L+1)^2-(L/2+1)^2\ge3L^2/4.                             \tag{4.4}
\]

Let

\[
 r_2(t)=|\{v\in\mathbb Z^2:|v|^2=t\}|,
 \qquad I_L=\{t\in\mathbb Z:(3L/8)^2\le t\le(L/2)^2\}.
\]

Then the following inequality is finite and exact:

\[
 \boxed{\quad
 \sum_{j=1}^{289}T_{B_j}(A_j)
 \ge |P_0|\sum_{t\in I_L}F_{289}(r_2(t)).
 \quad}                                                          \tag{4.5}
\]

To prove it, fix \(p\in P_0\) and \(t\in I_L\). All \(r_2(t)\) points \(p+v\), \(|v|^2=t\), belong to \(P_L\). Divide them into the 289 assigned cells. If a point is assigned to center \(c_j\),

\[
 |p-c_j|\ge |v|-|p+v-c_j|\ge3L/8-r=2r,
\]

so \(p\in B_j\). Every triple in one assigned cell belongs to \(A_j\) and has circumcenter exactly \(p\). The balanced-bin inequality gives at least \(F_{289}(r_2(t))\) such triples. Different \((p,t)\) cannot produce the same triple: three noncollinear points determine their circumcenter and circumradius. Assignment gives each counted triple a unique cell. Summing proves (4.5). Notice that no angular equidistribution of lattice representations is required.

For any fixed positive integer \(J\), the elementary finite bound

\[
 F_J(k)\ge \frac{k^3}{6J^2}-\frac{k^2}{2}                          \tag{4.6}
\]

follows from \(\sum_i k_i^3\ge k^3/J^2\), \(\sum_i k_i^2\le k^2\), and the formula for \(\sum_i\binom{k_i}3\).

The only number-theoretic input is the classical representation-moment estimate

\[
 \sum_{t\le X}r_2(t)^3\sim C_3 X(\log X)^3,\quad C_3>0,
 \qquad
 \sum_{t\le X}r_2(t)^2=O(X\log X).                                \tag{4.7}
\]

For clarity, the cubic exponent is 3, not an interpolation guess. For the multiplicative function \(R(t)=r_2(t)/4\), the Euler factors of \(\sum R(t)^3t^{-s}\) are

\[
 (1-2^{-s})^{-1},\qquad
 \frac{1+4p^{-s}+p^{-2s}}{(1-p^{-s})^4}\ (p\equiv1\pmod4),\qquad
 (1-p^{-2s})^{-1}\ (p\equiv3\pmod4).
\]

Factoring off \(\zeta(s)^4L(s,\chi_4)^4\) leaves an Euler product absolutely convergent for \(\Re s>1/2\) and positive at 1. The standard pole-order/mean-value theorem gives the first asymptotic in (4.7). The quadratic moment is the classical Ramanujan estimate. These are unconditional standard inputs; (4.5) and (4.6) are elementary finite inequalities.

Since \(I_L\) is a fixed-proportion interval at scale \(L^2\), (4.6)--(4.7) yield

\[
 \sum_{t\in I_L}F_{289}(r_2(t))\ge c L^2(\log L)^3
\]

for all sufficiently large \(L\). Hence (4.5) gives

\[
 \max_j T_{B_j}(A_j)\ge c L^4(\log L)^3
                      \asymp n^2(\log n)^3.
\]

Choose the first maximizing index \(j\). This specifies the counterexample sequence and proves (4.2), with \(A=A_j\), \(B=B_j\). Finally Guth--Katz, applied to every eligible disk subset, gives \(M_{\rm disk}(P_L)^2=O((\log n)^2)\), so the ratio in (4.3) is at least a positive constant times \(\log n\). QED.

This result refutes a particular *unweighted actual-cross-triple upper bound*. It does **not** refute the disk recurrence, and it does not show that all weighting schemes fail. It explains why Theorem 1 must not be advertised as a route that has already removed the logarithmic obstruction.

### What remains

The remaining universal problem is precisely to control actual distance-support loss under a balanced disk selection. Neither the proper-field-core dichotomy nor the parabolic-lens certificate proves

\[
 n\le D(P)\sqrt{M_{\rm disk}(P)^2+C}
\]

for arbitrary \(P\). No claim is made that a strip/lens population statistic can replace the local support ratio.

---

## 5. Verification

`verify_geometric_cross_distance_certificates.py` checks:

- the exact balanced-bin minimum by exhaustive small integer compositions;
- the exact cross-distance, circumcenter, and parabolic-lens inequalities for integer planar configurations, including a five-point Pythagorean arc where the first circumcenter bound is an equality;
- the vertex-disjoint witness bound;
- the field-core pinned-distance bound using exact coefficient tuples in \(\mathbb Q(\sqrt2)\) and \(\mathbb Q(\sqrt2,\sqrt3)\), including shifts of size \(10^{-40}\);
- the one-point perturbation identity by exact algebraic distance enumeration, as well as larger support-level checks;
- explicit growing-grid lower counts for the lens statistic;
- the finite cubic-bin bound and the exact Euler-factor algebra for the cubic representation moment;
- the finite 289-disk-cover construction, including admissible disk cardinalities, exterior-center membership, and distinct actual circumcenter witnesses.

These finite checks supplement the proofs above. They are not a search over every disk, and are not evidence for a universal constant-loss theorem or an unbounded disk defect.
