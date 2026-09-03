# Exact color-weighted operators for planar distances

## Status and scope

**The amplification `E D^2 >= c n^5` is neither proved nor disproved here.**

This investigation keeps the actual distance classes and their exact ordered multiplicities throughout. It gives four audited results about the proposed weighted route:

1. The natural rank-two trace/commutator estimate, even with the exact weights `1/r_s`, is exactly a scalar Cauchy–Schwarz inequality.
2. The exact color-averaging projection is Hilbert–Schmidt positive but generally not a positive map on matrices. **If it were positive, the points would lie on a circle and `D >= (n-1)/2`.** Thus this positivity shortcut cannot operate in the difficult sublinear-support regime.
3. On actual rational planar configurations, inverse-multiplicity weighted Schur multipliers and the color-averaging projection have norms at least `c n^(1/4)`, even though every multiplicity is 2 or 4 and `ED/[n(n-1)]^2 -> 1`. Analogous counterexamples hold for inverse-degree normalization. Conversely, on full square grids the inverse-multiplicity Schur norm stays bounded while both `n/D` and multiplicity variance grow. Thus these norms are not two-sided proxies for the missing gain.
4. With the actual weights `1/r_s`, weighted Cauchy row energy can be arbitrarily small relative to its Frobenius energy. The positive unweighted curvature symmetrization does not survive this weighting.

The large-Schur-norm examples have `D` quadratic in their total number of points. The row-cancellation examples have linear-or-larger support. The positivity obstruction, in contrast, applies to **every** planar set with `D < (n-1)/2`, including sufficiently large square grids. None of these statements rules out an argument using new joint endpoint/color information specifically in `D=o(n)`.

No Lean files were edited. The supplied `distance_matrix_analysis.md` was read; the accessible copy has no matrix-commutator section. `/memories/progress.md` was not readable and no memory tool was available.

## 1. Normalization and exact commutator calculus

Let `n>=2`, let the points `z_i` be distinct, and count ordered off-diagonal pairs:

\[
M=n(n-1)=\sum_{s\in S}r_s,\qquad E=\sum_s r_s^2,\qquad D=|S|.
\]

Write `Z=diag(z_i)`. The matrices `A_s` are real symmetric, have zero diagonal, and partition the support of `J-I`. Define

\[
(C_s)_{ij}=\frac{(A_s)_{ij}}{z_i-z_j}\quad(i\ne j),\qquad (C_s)_{ii}=0.
\]

All of the following are exact:

\[
 C_s^T=-C_s,\qquad
 C_s=\frac1s[Z^*,A_s],\qquad
 [Z,C_s]=A_s,\qquad
 [Z,[Z^*,A_s]]=sA_s.                                      \tag{1}
\]

Indeed, on a color-`s` entry, `(z_i-z_j)^{-1}=(bar z_i-bar z_j)/s`.

For the Hilbert–Schmidt inner product, `ad_Z^*=ad_(Z*)`. Since `Z` is normal, these two superoperators commute. Thus

\[
 \mathcal L=\operatorname{ad}_Z\operatorname{ad}_{Z^*}
\]

is a positive self-adjoint operator on matrix space, acting entrywise by multiplication by `|z_i-z_j|^2`. Its spectral support projections are `X -> A_s o X`, while the `A_s` themselves are orthogonal eigenvectors with

\[
 \langle A_s,A_t\rangle_F=\delta_{st}r_s,
 \qquad
 \langle C_s,C_t\rangle_F=\delta_{st}\frac{r_s}{s}.          \tag{2}
\]

Consequently, for arbitrary complex coefficients `a_s`,

\[
 A_a=\sum_s a_sA_s,\qquad C_a=\sum_s a_sC_s
\]

satisfy

\[
 [Z,C_a]=A_a,\quad
 \|A_a\|_F^2=\sum_s r_s|a_s|^2,\quad
 \|C_a\|_F^2=\sum_s\frac{r_s|a_s|^2}{s}.                  \tag{3}
\]

In particular, put

\[
 W=\sum_s\frac{A_s}{r_s},\qquad
 \mathcal C=\sum_s\frac{C_s}{r_s}.
\]

Then

\[
 [Z,\mathcal C]=W,\quad
 \mathbf1^TW\mathbf1=D,\quad
 \|W\|_F^2=\sum_s\frac1{r_s},\quad
 \|\mathcal C\|_F^2=\sum_s\frac1{s r_s}.                  \tag{4}
\]

These weights are exact, not extracted by a continuous filter.

### 1.1 Where the ordinary energy inequality sits

On Hilbert–Schmidt matrix space define

\[
 \mathcal T(X)=\sum_s\langle A_s,X\rangle_F A_s.
\]

Its nonzero eigenvalues are precisely `r_s`. Therefore

\[
 \operatorname{rank}\mathcal T=D,\qquad
 \operatorname{Tr}_{\mathrm{HS}}\mathcal T=M,\qquad
 \operatorname{Tr}_{\mathrm{HS}}\mathcal T^2=E.
\]

The Schatten rank/trace inequality is exactly

\[
 ED\ge M^2.                                                \tag{5}
\]

The inverse-multiplicity projection on the positive colors is

\[
 \Pi_0(X)=\sum_s\frac{\langle A_s,X\rangle_F}{r_s}A_s.
\]

It has Hilbert–Schmidt rank and trace `D`. These identities do not, by themselves, force an additional factor `n/D`: they are also the ordinary diagonal spectral calculus of arbitrary positive numbers `r_s`.

More specifically, on the radial cyclic subspace,

\[
 \langle f(\mathcal L)(J-I),g(\mathcal L)(J-I)\rangle_F
 =\sum_s r_s\overline{f(s)}g(s).                           \tag{6}
\]

An argument restricted to these radial quadratic forms is just scalar weighted Hilbert-space calculus. This observation is not an impossibility theorem for arguments that also use multiplication of matrices, coordinate evaluations, angular modes, or rank-two realization.

### 1.2 The rank-two trace estimate collapses exactly to scalar CS

Set `z_mean=n^{-1} sum_i z_i` and

\[
 V=\sum_i|z_i-z_{\rm mean}|^2,
 \qquad \sum_s s r_s=2nV.
\]

Cyclicity of trace gives

\[
 D=\operatorname{tr}(J[Z,\mathcal C])
   =\operatorname{tr}([J,Z]\mathcal C).
\]

The matrix `[J,Z]` has rank at most two and

\[
 \|[J,Z]\|_F^2=2nV=\sum_s s r_s.
\]

Thus the optimal direct Hilbert–Schmidt estimate is

\[
 \boxed{D^2\le
       \left(\sum_s s r_s\right)
       \left(\sum_s\frac1{s r_s}\right).}                 \tag{7}
\]

This is exactly scalar CS applied to `sqrt(s r_s)` and `1/sqrt(s r_s)`. The right side does not produce equal-distance energy `E`.

There is no missing rank-two improvement in this particular estimate. After centering `z`, the two nonzero singular values of `[J,Z]` are both `sqrt(nV)`: on the orthonormal input vectors `1/sqrt(n)` and `bar z/sqrt(V)`, its outputs are orthogonal and have that common norm. In particular its trace norm is `2sqrt(nV)`.

Equivalently, with `h=mathcal C 1`, skew-symmetry gives

\[
 \sum_i h_i=0,\qquad
 \sum_i z_i h_i=D/2,\qquad
 \|h\|^2\le\frac n2\|\mathcal C\|_F^2.                    \tag{8}
\]

For the last inequality choose a real orthogonal basis with first vector `1/sqrt(n)`. In a skew-symmetric matrix, the first row and first column have equal squared norms, so their combined contribution to Frobenius norm is twice the squared norm of that column. Applying CS to the middle identity in (8) recovers (7), with exactly the same constant.

### 1.3 The always-positive weighted graph Laplacian

There is also an unconditional positive form. Let `q=W1` and

\[
 L_W=\operatorname{diag}(q)-W\succeq0.
\]

Because every off-diagonal entry of `W` is positive, its kernel is exactly the constants. Its exact identities are

\[
 \operatorname{rank}L_W=n-1,\quad
 \operatorname{tr}L_W=D,\quad
 \|L_W\|_F^2=\sum_iq_i^2+\sum_s\frac1{r_s},\quad
 z^*L_Wz=\frac12\sum_s s.
\]

Positivity follows from `v^*L_Wv=(1/2)sum_(i,j) W_ij |v_i-v_j|^2`. Its rank/trace inequality gives

\[
 D^2\le(n-1)\left(\sum_iq_i^2+\sum_s\frac1{r_s}\right).
\]

But this particular inequality already follows without geometry from `sum_i q_i=D`, `sum_i q_i^2>=D^2/n`, and `sum_s1/r_s>=D^2/[n(n-1)]`. It supplies no additional variance factor. Other uses of the weighted Laplacian are not ruled out.

## 2. Positive color averaging would force the easy circle case

Include the zero color in the normalized projection:

\[
 \Pi(X)=\frac{\operatorname{tr}X}{n}I+
         \sum_s\frac{\operatorname{tr}(A_sX)}{r_s}A_s.     \tag{9}
\]

This is a complex-linear Hilbert–Schmidt orthogonal projection of rank `D+1`. It is self-adjoint as a superoperator, unital, trace preserving, and fixes `J`. Moreover

\[
 \langle X,\Pi(X)\rangle_F
 =\frac{|\operatorname{tr}X|^2}{n}
   +\sum_s\frac{|\operatorname{tr}(A_sX)|^2}{r_s}\ge0.     \tag{10}
\]

**But (10) does not mean that `X>=0` implies `Pi(X)>=0`.**

### Theorem 2.1

If the map `Pi` is positive on positive semidefinite matrices, every `A_s` is regular, the points lie on a circle centered at their centroid, and

\[
 D\ge (n-1)/2.                                             \tag{11}
\]

**Proof.** Fix an edge `(i,j)` of color `s` and apply `Pi` to the rank-one PSD matrix

\[
 X=(e_i-e_j)(e_i-e_j)^T.
\]

Its image is exactly

\[
 \Pi(X)=\frac2n I-\frac2{r_s}A_s.
\]

Positivity would imply `lambda_max(A_s)<=r_s/n`. But the Rayleigh quotient on `1` is `r_s/n`, so equality holds. Equality in the maximum Rayleigh quotient implies

\[
 A_s\mathbf1=(r_s/n)\mathbf1.                              \tag{12}
\]

Hence every distance graph is regular.

Let `R=sum_s s A_s` be the squared-distance matrix and center the points at zero. Equation (12) makes `R1` constant, whereas direct expansion gives

\[
 (R\mathbf1)_i=n|z_i|^2+\sum_j|z_j|^2.
\]

All `|z_i|` are therefore equal. The common radius is positive because the points are distinct and `n>=2`. A circle centered at one point of this common circle intersects the common circle in at most two points. Thus each color degree is at most two, `r_s<=2n`, and `n(n-1)<=2nD`. QED.

In this positive case ordinary CS already gives `ED^2 >= n^2(n-1)^3/2 >= n^5/16`. The obstruction is that positivity itself excludes the hard sublinear-support case.

### 2.2 Exact characterization of the positivity assumption

Let `V_R=span_R{I,A_s}`. Then

\[
 \boxed{\Pi\text{ is positive}\iff
        V_R\text{ is closed under squares}
        \iff V_R\text{ is a unital Jordan subalgebra}.}    \tag{13}
\]

Here closure under squares and under `(XY+YX)/2` are equivalent by polarization.

For completeness, if `Pi` is positive and unital, the usual self-adjoint Kadison inequality gives `Pi(B^2)>=Pi(B)^2`. An elementary proof writes `B=sum_j lambda_j E_j`, puts `F_j=Pi(E_j)>=0`, and uses the isometry `U x=(F_j^(1/2)x)_j` and the diagonal operator `Lambda=diag(lambda_j)`:

\[
 \Pi(B^2)-\Pi(B)^2
 =U^*\Lambda(I-UU^*)\Lambda U\succeq0.
\]

For `B` in the range, trace preservation makes this PSD difference have trace zero, hence `Pi(B^2)=B^2`.

Conversely, suppose the range is closed under squares. It contains every real polynomial in any of its self-adjoint elements. For `X>=0`, put `Y=Pi(X)`. If `Y` had a negative eigenvalue, its negative spectral projection `F` would be a real polynomial in `Y` and belong to the range. Hilbert–Schmidt self-adjointness would give

\[
 0>\operatorname{tr}(FY)
  =\operatorname{tr}(F\Pi X)
  =\operatorname{tr}((\Pi F)X)
  =\operatorname{tr}(FX)\ge0,
\]

a contradiction. This proves (13).

Thus the missing positivity is an additional algebra-closure assumption, not a consequence of normality of `Z` or of (1).

### 2.3 Failure on actual square grids

For an `L x L` grid with `L>=3`, `n=L^2`. The longest squared distance `s=2(L-1)^2` consists of two disjoint opposite-corner edges, so `r_s=4` and `lambda_max(A_s)=1`. The preceding rank-one input gives

\[
 \Pi(X)=\frac2n I-\frac12A_s,
\]

which has eigenvalue `2/n-1/2<0`.

This is an exact-multiplicity obstruction on the standard low-distance examples, not a perturbation argument. Already the `20 x 20` grid has `(n,D)=(400,179)` and `D<(n-1)/2`; asymptotically grids have `D=Theta(n/sqrt(log n))`.

## 3. Exact weighted Schur multipliers can have polynomial norms

For a matrix `B`, let

\[
 \mathfrak M_B(X)=B\circ X,
 \qquad
 \|\mathfrak M_B\|_{\infty\to\infty}
 =\sup_{X\ne0}\frac{\|B\circ X\|_{\rm op}}{\|X\|_{\rm op}}.
\]

This is a norm of the **Schur multiplier**, not the ordinary operator norm of `B`.

### 3.1 Exact planar padding lemma

Start with a finite planar core all of whose positive distances are distinct. Select some core edges. For each selected edge of length `ell`, add two points at distance `ell` from one another, so that this is their only prescribed distance equality. The additions can be chosen with rational coordinates if the core coordinates and selected lengths are rational. Then selected colors have exactly two unordered edges (`r=4`); every other color has exactly one (`r=2`).

Here is a proof that audits the avoidance assertion. In the construction below all selected core edges are horizontal. Before its gadget is added, the selected length occurs on exactly that one old horizontal edge. Add the vertical pair `t, t+i ell`. Fixing the orientation, every unwanted equality is a proper circle or line condition on the translation `t`. A possible identity between `|t-a|^2` and `|t+i ell-b|^2` would require `b-a=i ell`; this is impossible because the only old edge of length `ell` is horizontal. All other equality conditions are plainly nonconstant. Choose `t` in an open rectangle avoiding the finitely many forbidden curves. Rational choices exist. This argument can be iterated because every unplanned new distance is kept distinct from all old and new distances.

In particular all translations may be chosen in `(2,3) x (0,1)`. If selected lengths are near one and the core is near `[0,1]`, the complete configurations have diameter less than four. This is exact control of collisions, not the claim that a continuous uncolored quantity detects them.

### 3.2 Hadamard construction and norm lower bound

Let `m=2^k>=4`. Use the symmetric Walsh matrix

\[
 H_{ij}=(-1)^{i\cdot j},\quad 0\le i,j<m,
 \qquad HH^T=mI,\quad \sum_{ij}H_{ij}=m.
\]

Take two collinear core clusters `A={a_i}` and `B={b_j}` with all distances distinct and every cross length near one. An explicit rational choice is

\[
 B_0=2^{4m},\qquad
 a_i=-2^i/B_0,\qquad
 b_j=1+2^{m+j}/B_0.
\]

Internal differences are distinguished by their binary valuations; cross lengths are distinguished by their two nonzero binary digits and exceed one. Thus all core distances are indeed distinct.

Apply the padding lemma precisely to the cross edges with `H_ij=-1`. Their number is

\[
 q=m(m-1)/2,
 \qquad N=2m+2q=m^2+m                                  \tag{14}
\]

for the total number of points. On the core cross block the exact inverse-multiplicity weights are

\[
 W_{AB}=\frac38J_m+\frac18H.                              \tag{15}
\]

Test the Schur multiplier on the block matrix supported from `B` to `A` with block `H`. Its input operator norm is `sqrt(m)`. Its output block is

\[
 W_{AB}\circ H=\frac38H+\frac18J_m.
\]

The Rayleigh quotient on `1/sqrt(m)` is `(m+3)/8`, since `sum H_ij=m`. Consequently

\[
 \boxed{\|\mathfrak M_W\|_{\infty\to\infty}
       \ge\frac{m+3}{8\sqrt m}\ge\frac{\sqrt m}{8}
       \ge cN^{1/4}.}                                    \tag{16}
\]

In contrast, `||M_W||_(2->2)=max_s 1/r_s=1/2`.

The same construction applies to the scale-invariant weighted phase kernel

\[
 U=\sum_s\frac{\sqrt{s}\,C_s}{r_s}.
\]

Every tested difference `a_i-b_j` is negative real, so `U_AB=-W_AB` **exactly**. Hence (16) also holds for `M_U`. It is not an inverse-separation artifact.

It also gives a lower bound for the weighted Cauchy multiplier on this well-separated block. If the two clusters lie in `[-epsilon,0]` and `[1,1+epsilon]`, then

\[
 \mathcal C_{ij}=-\frac{W_{ij}}{b_j-a_i}
\]

on that block. The error after Schur multiplication by `H`, relative to `-W_AB o H`, has entries of absolute value at most `epsilon`, hence operator norm at most `m epsilon`. Taking `epsilon<=1/16` gives

\[
 \|\mathfrak M_{\mathcal C}\|_{\infty\to\infty}
 \ge\sqrt m/16.
\]

All tested distances are between one and `1+2epsilon`, and the complete construction can have diameter below four. The phase-kernel version is the more intrinsic scale-free obstruction.

### 3.3 The exact color-averaging projection also has large norm

Use the self-adjoint test matrix with core blocks `X_AB=H`, `X_BA=H^T`, all other entries zero. Its operator norm is `sqrt(m)`. Formula (9) gives

\[
 (\Pi X)_{AB}=2(W_{AB}\circ H)=\frac34H+\frac14J_m.
\]

Compression to this block yields

\[
 \boxed{\|\Pi\|_{\infty\to\infty}
       \ge\frac{m+3}{4\sqrt m}\ge cN^{1/4}.}             \tag{17}
\]

This contrasts with `||Pi||_(2->2)=1`. More generally, the same test for any fixed Schatten exponent `p>2` gives growth at least `c m^(1/2-1/p)`; Hilbert–Schmidt self-adjointness gives the dual-exponent bounds. Thus the distinction is not confined to the operator-norm endpoint.

The exact global multiplicities in this construction are particularly informative. Put `Q=binom(N,2)`. There are `q` colors of ordered multiplicity four and `Q-2q` of ordered multiplicity two. Hence

\[
 D=Q-q,\qquad E=4Q+8q,\qquad M=2Q,
\]

and

\[
 \frac{ED}{M^2}
 =1+\frac{q(Q-2q)}{Q^2}=1+O(1/N).                         \tag{18}
\]

Therefore no universal bound of the form

\[
 \|\mathfrak M_W\|_{\infty\to\infty}
 \ \text{or}\ \|\Pi\|_{\infty\to\infty}
 \le C\,(ED/M^2)^a(\log N)^b
\]

can hold for fixed real `a` and fixed nonnegative `b`. These norms can be polynomially large while multiplicity variance tends to zero. Any weighting nonconstant on the positive even multiplicities admits the same two-level-mask obstruction, by adding fixed numbers of copies of the prescribed core lengths. When a length is copied more than once, choose each new pair direction to avoid the finitely many old directed edges of that length; the translation-avoidance proof then applies unchanged.

**Scope:** these examples have `D~N^2/2`, so their amplification is already trivial. They disprove global norm estimates, not estimates explicitly restricted to `D=o(N)` or suitably selected rich colors.

### 3.4 Inverse-degree normalization has the same obstruction

Let `k_s(i)=sum_j (A_s)_ij` and use zero inverses at inactive vertices. Put

\[
 P_s=K_s^\dagger A_s,\qquad
 Q_s=K_s^{\dagger/2}A_sK_s^{\dagger/2},\qquad
 K_s=\operatorname{diag}(k_s(i)).
\]

Each active row of `P_s` sums to one, so `sum_s P_s` has row sum equal to the exact pinned support size. Each `Q_s` is a symmetric contraction. The commutator identities survive:

\[
 [Z,K_s^\dagger C_s]=P_s,\qquad
 [Z,K_s^{\dagger/2}C_sK_s^{\dagger/2}]=Q_s.               \tag{19}
\]

To produce a two-level mask, start with the same core. For a cross edge `(a_i,b_j)` with `H_ij=-1` and length `ell`, add one point at distance `ell` from `a_i` and one at distance `ell` from `b_j`. Choose their angles successively to avoid every other equality. On a fixed circle each forbidden equality has finitely many solutions, unless it is the one prescribed distance to the center, so this is possible, with rational coordinates using rational circle parametrization.

The selected color is now exactly the three-edge path `new--a_i--b_j--new`, with ordered multiplicity six. Both core degrees are two. Unselected core colors have degrees one. Thus, on the cross block, both aggregate normalizations have exactly

\[
 \left(\sum_s P_s\right)_{AB}
 =\left(\sum_s Q_s\right)_{AB}
 =\frac34J_m+\frac14H.
\]

Their Schur multiplier norms are at least `(m+3)/(4sqrt(m))`, by the identical test. The total size is still `N=m^2+m`. Every color has multiplicity two or six; the weights have not been replaced by averages.

### 3.5 Calibration in the difficult regime: bounded norms on square grids

The opposite behavior occurs on the actual near-extremal grids. For `P={0,...,L-1}^2`, `L>=2` and `n=L^2`, the exact inverse-multiplicity matrix satisfies

\[
 \boxed{\frac14\le\|\mathfrak M_W\|_{\infty\to\infty}
        \le\frac{\pi^2}{6}.}
\]

The same bounds hold for the phase kernel `U`.

Here is a direct proof of the upper bound. Any matrix `B` obeys

\[
 \|\mathfrak M_B\|_{\infty\to\infty}
 \le\max_i\left(\sum_j|B_{ij}|^2\right)^{1/2}.
\]

Indeed factor `B_ij=<xi_i,eta_j>` with `xi_i` the conjugate of row `i` and `eta_j=e_j`; the maps `Ve_i=e_i tensor xi_i` and `Te_j=e_j tensor eta_j` give `M_B(X)=V^*(X tensor I)T` and the claimed norm bound.

For a nonzero grid displacement `(a,b)`, the vectors `(a,b)` and `(-a,-b)` alone supply

\[
 r_{a^2+b^2}\ge 2(L-|a|)(L-|b|).
\]

Thus every row of `W`, even after overestimating its allowable displacements by the whole difference box, has squared norm at most

\[
 \frac14\left(\sum_{a=-(L-1)}^{L-1}
             \frac1{(L-|a|)^2}\right)^2
 \le\frac14\left(2\sum_{k=1}^{\infty}\frac1{k^2}\right)^2
 =\left(\frac{\pi^2}{6}\right)^2.
\]

The phase kernel has exactly the same entrywise absolute values. The longest-distance entry, of weight `1/4`, proves the lower bound by testing a single matrix unit.

Using the standard grid counts already recorded in `distance_matrix_analysis.md`,

\[
 D=\Theta(n/\sqrt{\log n}),\qquad
 E=\Theta(n^3\log n),\qquad
 ED/M^2=\Theta(\sqrt{\log n}).
\]

Therefore the weighted Schur norms are bounded even though both `n/D` and multiplicity variance grow. Together with (16)--(18), this rules out using `||M_W||` or the phase-multiplier norm as a two-sided proxy for multiplicity variance. In particular a lower bound by any fixed positive power of `n/D` is false even in the difficult support regime. This does not rule out a norm estimate with additional endpoint/color information or additional logarithmic factors.

## 4. Weighted Cauchy row energy has genuine cancellation

### 4.1 The exact triangle expansion loses positivity

For symmetric real edge weights `w_ij`, let `C_ij=w_ij/(z_i-z_j)` off the diagonal and `h=C1`. Then

\[
 \|h\|^2=\|C\|_F^2+\sum_{\{i,j,k\}}\Gamma_{ijk},          \tag{20}
\]

where, writing `a=|z_i-z_j|^2`, `b=|z_i-z_k|^2`, `c=|z_j-z_k|^2`,

\[
 \Gamma_{ijk}=
 w_{ij}w_{ik}\frac{a+b-c}{ab}
 +w_{ij}w_{jk}\frac{a+c-b}{ac}
 +w_{ik}w_{jk}\frac{b+c-a}{bc}.                            \tag{21}
\]

This follows by expanding each row norm; for example

\[
 2\operatorname{Re}\frac1{(z_i-z_j)\overline{(z_i-z_k)}}
 =\frac{a+b-c}{ab}.
\]

For constant weights, (21) is a nonnegative multiple of squared Menger curvature. For `w_ij=1/r_(d_ij)` it need not be nonnegative.

An actual full-planar example is

\[
 P=\{0,1,3,100i,3+100i\}.
\]

The squared lengths `1,4,9` have ordered multiplicities `2,2,4`. For the triangle `{0,1,3}`, (21) is

\[
 \frac1{12}-\frac14+\frac1{24}=-\frac18.                  \tag{22}
\]

The global sign can also be audited explicitly. In the family `{0,1,3,ti,3+ti}` with `t>3`, the colors `1,4,t^2+1,t^2+4` have ordered multiplicity two, and `9,t^2,t^2+9` have ordered multiplicity four. Substituting these seven exact weights into (20)--(21) and simplifying gives

\[
 \|\mathcal C\mathbf1\|^2-\|\mathcal C\|_F^2
 =-\frac{t^6-15t^4-146t^2-158}
          {8(t^2+1)(t^2+4)(t^2+9)}.
\]

At `t=100` this is exactly

\[
 -\frac{8184414261}{65665605904}<0.
\]

The ratio of those two squared norms is approximately `0.8091094041`. Thus even the global diagonal-domination inequality fails, not merely a choice of triangle decomposition.

### 4.2 A positive form that is valid, but has no uniform coercivity

Let `L_s=K_s-A_s` be the unnormalized graph Laplacian of one color. Exactly,

\[
 C_s\mathbf1=\frac1sL_s\bar z,
 \qquad z^*L_sz=\frac{r_s s}{2}.
\]

Consequently

\[
 \frac{\|C_s\mathbf1\|^2}{\|C_s\|_F^2}
 =\frac{z^*L_s^2z}{r_s s}
 =\frac12\frac{z^*L_s^2z}{z^*L_sz}.                        \tag{23}
\]

This is a genuine positive graph-Laplacian form. It also shows precisely why no uniform lower bound follows: the embedding may live in low Laplacian modes.

For a unit-spaced path of `m` points, the unit-color ratio in (23) is `1/(m-1)`. For the shortest-distance cycle of a regular `m`-gon scaled to have side one, it is `2sin^2(pi/m)`: the coordinate vector is an eigenvector of the cycle Laplacian with eigenvalue `4sin^2(pi/m)`.

### Theorem 4.3: exact inverse-multiplicity weights do not repair coercivity

For the complete actual distance palette and `mathcal C=sum_s C_s/r_s`,

\[
 \boxed{\inf_P
 \frac{\|\mathcal C\mathbf1\|^2}{\|\mathcal C\|_F^2}=0.}  \tag{24}
\]

The infimum may be taken over full-planar configurations with integer coordinates.

**Proof with explicit color counts.** Fix `m>=3` and start with the real core `{0,1,...,m-1}`. For each `k=2,...,m-1`, add `T` horizontal pairs of separation `k`, placing every pair in its own cluster. If the clusters are enumerated by `ell=1,...,T(m-2)`, use the pair

\[
 \{i\ell(R+2m),\ k+i\ell(R+2m)\}.
\]

All inter-cluster distances are at least `R`, and take `R>m`. The exact small-color multiplicities are

\[
 r_1=2(m-1),\qquad
 r_{k^2}=2(m-k+T)\quad(2\le k<m).                         \tag{25}
\]

No cross-cluster pair changes (25). The total size is `N=m+2T(m-2)`.

Decompose the weighted Cauchy matrix as `mathcal C=C_0+B+K`, where `C_0` is the retained unit path, `B` contains all other within-cluster entries, and `K` contains inter-cluster entries. The supports are disjoint, and

\[
 \|C_0\|_F^2=\frac1{2(m-1)},\qquad
 \|C_0\mathbf1\|^2=\frac1{2(m-1)^2}.                     \tag{26}
\]

Using the full, padded multiplicities in (25),

\[
 \|B\|_F^2=\sum_{k=2}^{m-1}
       \frac1{2k^2(m-k+T)}<\frac1{2T}.
\]

The internal blocks have at most `m` vertices, hence `||B1||^2<=m||B||_F^2`. Regardless of any additional coincidences among the long distances, `r_s>=2` and their lengths are at least `R`, giving

\[
 \|K\|_F^2\le\frac{N^2}{4R^2},\qquad
 \|K\mathbf1\|^2\le\frac{N^3}{4R^2}.                    \tag{27}
\]

For fixed `m`, let `T` tend to infinity and take, for example, `R=N^2T`. Both error matrices tend to zero in Frobenius norm and in row-sum norm. The ratio in (24) therefore tends to `1/(m-1)`, by (26). Then let `m` tend to infinity. QED.

A similar suppression construction around a regular polygon gives limiting ratio `2sin^2(pi/m)`, but the integer-path construction already proves (24).

These examples do not violate the trace identity `sum_i z_i h_i=D/2`: their coordinate variance is large. They do show that a claim such as `||mathcal C 1||^2 >= c ||mathcal C||_F^2`, or positive triangle-by-triangle domination of the Frobenius term, is false with the exact requested weights. The constructed vertical progression also supplies at least `T(m-2)` distinct distances, so this example is not in `D=o(N)`.

## 5. What has and has not been ruled out

The following particular proposed steps are impossible:

* Treating (9), or the corresponding color space, as automatically positive/conditionally expected from normality of `Z` and planar realization. Positivity would force a circle and linear support; the exact map is nonpositive on low-distance grids.
* Uniform polylogarithmic Schatten/operator-norm bounds for `M_W`, the weighted phase multiplier, or `Pi` on all planar configurations. The exact two-level padding gives polynomial lower bounds. The same issue survives natural inverse-degree normalization.
* Using the unweighted positive Cauchy-curvature symmetrization after inserting `1/r_s`, or a uniform lower comparison of the resulting row energy with its Frobenius energy.
* Obtaining an amplification merely by the trace against `J`, normality, rank two of `[J,Z]`, and Hilbert–Schmidt CS. The resulting inequality is exactly (7).

This is **not** an impossibility theorem for all color-dependent operator arguments. In particular:

* The polynomial Schur-norm counterexamples have large support. A support-restricted estimate, or an estimate after justified selection of rich colors, is not refuted by them.
* Rank-two realization, angular correlations, and mixed products of different `A_s` contain information not captured by the radial quadratic calculus (6).
* The valid positive form (23) is not coercive uniformly, but more global uses of the complete family could still impose constraints.

The remaining numerical deficit is exactly

\[
 \frac{ED}{M^2}
 =1+\frac{D\sum_s(r_s-M/D)^2}{M^2}
 \ \stackrel{\rm needed}{\gtrsim}\ \frac nD
 \qquad(D=o(n)).
\]

No inequality proving that deficit, and no proof of `n<=C D sqrt(log n)`, has been obtained. Establishing it would require additional joint endpoint/color control in the difficult regime; none of the audited identities above supplies it. The task has not been replaced by another named unproved lemma.

## 6. Verification

`verify_color_weighted_operators.py` uses exact integer/Fraction distances and never numerical collision tolerances. It checks:

* commutator entries and the exact inverse-multiplicity Frobenius identity;
* idempotence, trace preservation, and the fixed matrices `I,J` for (9);
* the explicit PSD-input/indefinite-output grid witness and exact displacement multiplicity inequalities underlying the bounded grid Schur norms;
* the signed triangle, the exact global five-point row-energy deficit, and its symbolic rational-function identity for all parameters `t>3`;
* rational/integer planar padding for `m=4,8,16`, including every global color count, all weights in the core block, and formulas (14)--(18);
* an exact Walsh certificate at `m=256`;
* the inverse-degree construction, including all global multiplicities and exact core degrees;
* exact internal path energies and rigorous cross-block error bounds giving actual full-planar ratios below `0.016` for the displayed large explicit construction.

`color_weighted_operator_verification.txt` records the passing output. The floating-point norm calculations are only sanity checks: every claimed lower bound is separately proved by the exact Walsh/Rayleigh calculation. Finite computations are not presented as evidence for the unproved amplification.
