> **Update:** The asymptotic ordinary-embedding gap in this historical report is now resolved in `CubeParityPentagonResolution.md`: the red graph contains a cube on more than one tenth of all host vertices. This family cannot disprove Erdős 181. The affine bounds below remain valid, but the assertions that the ordinary asymptotic deficit is unresolved are superseded.

# Parity-tensor pentagons: a sharp affine benchmark, but no all-map resolution

## Outcome and scope

**This investigation does not produce an unbounded-ratio Ramsey counterfamily and does not rigorously exclude the parity-tensor candidate.** In particular, it does not establish either a constant-loss ordinary cube embedding or divergence of the ordinary dimension deficit. The endpoint requested in the task remains unresolved here; the results below are partial, not a substitute sufficient conjecture.

The concrete conclusions are:

* For every `t >= 2`, there are explicit ordinary injective **`Q_(2t)` in both colours**. The construction works for odd `t` as well as even `t`.
* **Every `F_5`-affine binary subset-sum injection into `F_5^t` has dimension at most `2t`, irrespective of edge colours.** A self-contained positive-Fourier-kernel argument proves this. Thus the construction is exactly optimal within that parametrization class.
* The preceding upper bound is **not an upper bound on ordinary cubes**. Its proof depends on a linear kernel that does not exist for an arbitrary injection.
* Both simple colour graphs are exactly half-regular. Neither has a monochromatic complete pair with both sides a fixed positive fraction of `5^t` as `t` tends to infinity. Thus the complete-first-level-pair argument from the lexicographic example really is unavailable here.
* The symplectic representation and the source-square identity hold for every map. However, the five-point-alphabet restriction prevents importing an ambient symplectic cube. An explicit legal red square also disproves the coordinatewise integer-lift step used for Cartesian tori.

Let `D_t^R,D_t^B` be the maximum ordinary injective cube dimensions in the respective colours, and `D_t = max(D_t^R,D_t^B)`. What is proved for **unrestricted ordinary embeddings** is only

\[
\boxed{\qquad
2t\le D_t^R,D_t^B\le\lfloor t\log_2 5\rfloor
\quad(t\ge2).
\qquad}                                                    \tag{0.1}
\]

The upper bound in (0.1) is just cardinality. Also `D_1^R=D_1^B=1`, and (0.1) determines `D_2^R=D_2^B=4` and `D_3^R=D_3^B=6`. Already at `t=4`, this investigation does not decide whether either colour contains `Q_9`.

An ordinary embedding throughout means an injection preserving **only source edges**. Additional host edges on the image are allowed. No independent-image requirement is imposed on either cube parity class. `Submission/Spec.lean` is unchanged.

---

## 1. The exact parity tensor, including its diagonal

Put

\[
 h(0)=h(1)=h(4)=1,\qquad h(2)=h(3)=-1,
\]

\[
 H_{ab}=h(a-b),\qquad
 S_t(x,y)=\prod_{i=1}^t h(x_i-y_i)=H^{\otimes t}(x,y).
                                                               \tag{1.1}
\]

For distinct vertices, sign `+1` is red and sign `-1` is blue. The artificial diagonal in `S_t` is always `+1`; it is not an edge of the host.

Each row of `H` sums to one, so each row of `S_t` sums to one. For `N=5^t`, the **simple** adjacency matrices are

\[
 A_R=(J+S_t)/2-I,\qquad A_B=(J-S_t)/2.                       \tag{1.2}
\]

Consequently both colours have degree exactly `(N-1)/2` and edge density exactly `1/2`. There is no sparse-AND-product interpretation.

### Spectrum and the absence of a linear-sized complete pair

The characters of `F_5` give eigenvalues

\[
 1\quad\text{(multiplicity 1)},\qquad
 1+\sqrt5\quad\text{(multiplicity 2)},\qquad
 1-\sqrt5\quad\text{(multiplicity 2)}.
\]

Writing `alpha=1+sqrt(5)` and `beta=sqrt(5)-1`, tensoring gives

\[
 \|S_t\|_{op}=\alpha^t=N^{\log_5\alpha},\qquad
 \log_5\alpha=0.7296702759\ldots .                          \tag{1.3}
\]

In fact, for `t>=1`,

\[
 \left\|A_c-\tfrac12(J-I)\right\|_{op}
 =\frac{\alpha^t-1}{2},\qquad c\in\{R,B\}.                 \tag{1.4}
\]

Indeed, the two centred matrices are `+/- (S_t-I)/2`; the largest positive eigenvalue of `S_t` is `alpha^t`, and its most negative eigenvalue is `-beta alpha^(t-1)`. The inequality `alpha^t-1 >= beta alpha^(t-1)+1` follows from `alpha-beta=2` and `alpha^(t-1)>=1`.

If disjoint sets `U,W` form a complete monochromatic pair, all their `S_t` entries are the same sign. Hence

\[
 |U||W|=|\mathbf1_U^T S_t\mathbf1_W|
 \le\alpha^t\sqrt{|U||W|},
\]

so

\[
 \boxed{\sqrt{|U||W|}\le\alpha^t=o(N).}                    \tag{1.5}
\]

In particular, no two fixed-positive-fraction pools can play the role of the root clusters in the lexicographic construction. This is a statement about complete pairs, **not an obstruction to a cube**, whose required edges are much sparser.

More directly, fixing first coordinates `a,b` leaves the cross sign

\[
 h(a-b)S_{t-1}(x',y'),
\]

rather than a constant sign. The dependence on the tails must not be discarded.

---

## 2. Explicit `Q_(2t)` in both colours, for every `t >= 2`

The useful observation is that certain two-coordinate directions generate **entire monochromatic five-point lines**. If a vector has exactly two nonzero coordinates, then:

* entries of equal quadratic-character type, for example `(1,1)` or `(1,-1)`, give sign `+1` for every nonzero scalar multiple;
* entries of opposite type, for example `(1,2)` or `(1,-2)`, give sign `-1` for every nonzero scalar multiple.

This follows directly from `h(a)=chi_5(a)` for nonzero `a`: the two factors acquire `chi_5(a)^2=1` under a common nonzero scalar multiplication. Zero coordinates contribute one.

### Monochromatic line bases

Use the following matrices over `F_5`; **columns** are the directions:

\[
 R_2=\begin{pmatrix}1&1\\1&-1\end{pmatrix},\qquad
 B_2=\begin{pmatrix}1&1\\2&-2\end{pmatrix},                \tag{2.1}
\]

\[
 R_3=\begin{pmatrix}1&0&1\\1&1&0\\0&1&1\end{pmatrix},
 \qquad
 B_3=\begin{pmatrix}1&0&2\\2&1&0\\0&2&1\end{pmatrix}.      \tag{2.2}
\]

Their determinants are respectively `-2,-4,2,9`, all nonzero modulo five. Every nonzero multiple of a column of `R_k` is red; every nonzero multiple of a column of `B_k` is blue.

Every integer `t>=2` is a sum of twos and threes. For even `t`, use only two-dimensional blocks. For odd `t>=3`, use one three-dimensional block and two-dimensional blocks for the rest. Let `M_c` be the resulting block-diagonal invertible matrix in colour `c`, and write its columns as `v_1,...,v_t`.

### The injection

For source bits `u_1,w_1,...,u_t,w_t`, set

\[
 \boxed{
 F_c(u,w)=M_c\,(u_1+2w_1,\ldots,u_t+2w_t)^T
          =\sum_{i=1}^t (u_i+2w_i)v_i.
 }                                                         \tag{2.3}
\]

**Injectivity.** Each pair `(u_i,w_i)` encodes a different member of `{0,1,2,3}` in `F_5`. The coordinatewise encoding is injective, and `M_c` is invertible. Thus all `2^(2t)` vertices have different images.

**Edges.** Flipping `u_i` changes the image by `+/-v_i`; flipping `w_i` changes it by `+/-2v_i`. Every one of these directions has colour `c`. This verifies every source edge, with no requirement on nonedges.

Thus (2.3) proves the lower bounds in (0.1) in both colours. The images occupy the fraction `(4/5)^t` of the host. That fraction tends to zero, so this construction itself is **not** a constant-loss result.

For additional structural context, the same basis identifies a spanning monochromatic copy of the Hamming graph `K_5 square ... square K_5`: any two vectors whose preimages under `M_c` differ in just one coordinate have colour `c`. This is a subgraph of the actual colour graph, not a description of all its edges.

---

## 3. Sharp upper bound for `F_5`-affine parametrizations only

### Definition of this restricted class

Here an `F_5`-affine binary subset-sum map is

\[
 f(\varepsilon)=a+\sum_{j=1}^d\varepsilon_j v_j,
 \qquad \varepsilon\in\{0,1\}^d,\quad v_j\in F_5^t.        \tag{3.1}
\]

The source is a binary cube, but the displayed addition and the extension below are over `F_5`. This is not the same meaning of affine as an affine map into the binary symplectic representation in Section 4.

### Theorem 3.1

If (3.1) is injective, then `d <= 2t`. **No monochromatic hypothesis is needed.** Therefore, for `t>=2`, the maximum monochromatic dimension within the class (3.1) is exactly `2t` in each colour.

### Proof by a positive Fourier kernel

Let `L:F_5^d -> F_5^t` have columns `v_j`, and let `K=ker L`. Injectivity of (3.1) is equivalent to

\[
 K\cap\{0,1,-1\}^d=\{0\}.                                \tag{3.2}
\]

Indeed, a difference of two binary vectors belongs to that ternary box, and every member of the box is such a difference.

Define a real function on `F_5` by

\[
 p(0)=1,\qquad p(1)=p(-1)=\frac{\sqrt5-1}{2},\qquad
 p(2)=p(-2)=0.
\]

With the unnormalized Fourier transform

\[
 \widehat p(k)=\sum_{x\in F_5}p(x)e^{-2\pi i kx/5},
\]

its values are exactly

\[
 \widehat p(0)=\sqrt5,\qquad
 \widehat p(1)=\widehat p(-1)=\frac{5-\sqrt5}{2},\qquad
 \widehat p(2)=\widehat p(-2)=0.                             \tag{3.3}
\]

They are all nonnegative. Put `P(z)=prod_j p(z_j)`. Its Fourier transform is the product of the transforms in (3.3), hence is nonnegative everywhere, and `hat P(0)=5^(d/2)`.

By (3.2), `P` vanishes at every nonzero element of `K`, so `sum_(z in K) P(z)=1`. Character orthogonality on the subspace `K` gives

\[
 1=\frac{|K|}{5^d}\sum_{\xi\in K^\perp}\widehat P(\xi)
   \ge\frac{|K|}{5^d}\widehat P(0)
   =|K|5^{-d/2}.                                          \tag{3.4}
\]

If `r=rank L<=t`, then `|K|=5^(d-r)`. Thus (3.4) says `1>=5^(d/2-r)`, proving `d<=2r<=2t`. QED.

This is the pentagon positive-kernel argument applied to a **linear kernel code**. It was proved above rather than imported as an unverified capacity assertion.

### Why this does not give the requested disproof

For an arbitrary injection `f:{0,1}^d -> F_5^t`, there is no linear extension `L` and no subspace `K` of size at least `5^(d-t)`. Neither the subgroup orthogonality formula nor that lower bound on `|K|` has an analogue supplied by injectivity alone. The monochromatic edge conditions do not create this kernel.

In particular, the statement

> “There is no affine `Q_(2t+1)`, and `5^t/2^(2t+1) = (5/4)^t/2` diverges”

is **not** a Ramsey counterexample. It only excludes a parametrization class. Claiming `D_t<=2t` from Theorem 3.1 would be an unsupported replacement of ordinary embeddings by affine ones.

---

## 4. Exact symplectic and square identities for all maps

Write `b(a,b)=1` when `a-b=+/-2` and zero otherwise, including `b(a,a)=0`. In `F_2^4`, let

\[
 \phi(0)=e_0,\quad\phi(1)=e_1,\quad\phi(2)=e_2,\quad
 \phi(3)=e_3,\quad\phi(4)=e_0+e_1+e_2+e_3.
\]

Define an alternating form with Gram matrix

\[
 G=\begin{pmatrix}
 0&0&1&1\\
 0&0&0&1\\
 1&0&0&0\\
 1&1&0&0
 \end{pmatrix}.                                           \tag{4.1}
\]

This matrix has rank four over `F_2`, and direct expansion gives

\[
 B(\phi(a),\phi(b))=b(a,b)\qquad(a,b\in F_5).               \tag{4.2}
\]

For the direct-sum form `B_t` on `F_2^(4t)` and the product map `Phi`,

\[
 S_t(x,y)=(-1)^{B_t(\Phi(x),\Phi(y))}.                     \tag{4.3}
\]

There is no switching function in (4.3). Crucially, the host vertices are only

\[
 \mathcal A^t\subset F_2^{4t},\qquad
 \mathcal A=\{e_0,e_1,e_2,e_3,e_0+e_1+e_2+e_3\},           \tag{4.4}
\]

not the whole binary space.

### The all-map square equation

Let `f` be any injection into the actual host and put `g=Phi o f`. A necessary condition for monochromaticity is that every source coordinate square satisfies

\[
 \boxed{
 B_t(g_{00}+g_{11},\ g_{10}+g_{01})=0.
 }                                                         \tag{4.5}
\]

The left side is the sum in `F_2` of the four edge labels. Four equal labels sum to zero.

More precisely, all equations (4.5) hold if and only if there is a vertex potential `pi` with

\[
 B_t(g(u),g(v))=\pi(u)+\pi(v)
 \quad\text{on every source edge}.                         \tag{4.6}
\]

To see the converse direction, define `pi` by summing edge labels along a path from a root. Backtracks contribute zero, and swapping consecutive coordinate steps changes a path by a coordinate square. These operations connect paths with the same endpoints, so (4.5) makes the sum path-independent. The reverse implication follows by telescoping. The potential is unique up to an additive constant.

For a square-compatible map, monochromaticity in Boolean colour `c` (`c=0` red, `c=1` blue) is therefore exactly

\[
 \pi(u)=c\sum_j u_j+k.                                    \tag{4.7}
\]

This identity is valid for all maps. It does **not** show that a square-compatible injection is affine, does not bound its entropy, and does not give a low-dimensional classification. It is not used as an unproved all-map obstruction.

### Why the ambient symplectic constructions do not transfer

An ambient cube or nonlinear shear in `F_2^(4t)` must still have **every vertex in (4.4)**. The existing switched-symplectic constructions do not prove that containment. The product alphabet has size `5^t`, not `2^(4t)`.

There is also a useful warning about the word “affine.” The set `A` contains no affine binary two-plane: the sum of any four distinct members is the fifth, which is nonzero. If an affine binary subspace lies in `A^t`, each block projection consequently has dimension at most one. Its total dimension is at most `t`.

Thus an injection affine **in the coordinates of (4.4)** has dimension at most `t`, even without a colour condition. Yet Section 2 has ordinary cubes of dimension `2t`. Those maps are already nonlinear in these binary coordinates. Binary-affine exclusion is therefore even less informative here than the `F_5`-affine bound in Section 3.

---

## 5. An explicit failure of the torus-lift mechanism

The Cartesian-torus all-map argument relies on every source edge having a unique short increment and every source square having zero integer winding. The parity condition has neither the same allowed increment set nor the required square conclusion.

Already for `t=2`, assign the four successive vertices of a source `Q_2` to

\[
 (0,0),\ (1,1),\ (2,2),\ (3,3).                           \tag{5.1}
\]

Every pair of distinct points on the diagonal line has red sign, since it contributes `h(a-b)^2=1`. Thus (5.1) is a valid ordinary red square. Its extra diagonal edges are harmless.

Take representatives of the successive differences in `{-2,-1,0,1,2}`. In each target coordinate the four oriented increments are

\[
 1,\ 1,\ 1,\ 2,
\]

whose sum is `5`, not zero. Therefore these edge increments cannot integrate to a single-valued integer lift of the source square. Appending fixed coordinates gives the same example in every `t>=2`.

This is an exact counterexample to transferring that proof step, not a numerical indication. The scalar colour contributions cancel between coordinates; one cannot demand separate coordinate homomorphisms to a looped pentagon. Similarly, allowing only edges changing one target coordinate would replace the parity graph by a much smaller Cartesian subgraph.

---

## 6. Endpoint audit: what remains unresolved

Let

\[
 \delta_t=t\log_2 5-D_t.
\]

The established unrestricted bounds yield only

\[
 0\le\delta_t\le t\log_2(5/4)
                  =0.3219280948\ldots\,t
 \quad(t\ge2),                                            \tag{6.1}
\]

or, in integer form,

\[
 0\le\lfloor t\log_2 5\rfloor-D_t
      \le\lfloor t\log_2(5/4)\rfloor.                     \tag{6.2}
\]

Both a bounded deficit and an unbounded deficit are consistent with these bounds. The sharp affine theorem supplies **no positive lower bound on the ordinary deficit**.

For clarity about the Ramsey ratio: if the actual ordinary maximum is `D_t`, the colouring avoids `Q_(D_t+1)` and its ratio is

\[
 \frac{5^t}{2^{D_t+1}}=2^{\delta_t-1}.                     \tag{6.3}
\]

Showing this unbounded requires an unbounded **lower** bound on `delta_t`. Section 2 provides only an upper bound on it. Reversing this logical direction would turn the affine calculation into a false disproof claim.

No estimate in this report excludes all nonlinear injections above `2t`, and no construction here reaches `floor(t log_2 5)-O(1)`. The complete-pair obstruction (1.5), the exact square condition (4.5), and the binary affine-subspace bound concern different, explicitly stated properties; they are not asserted to imply such an all-map estimate.

**Final mathematical status:** this one parity-tensor candidate is neither established as an unbounded-ratio counterfamily nor ruled out. The useful proved result is the exact `2t` affine benchmark, together with checks that prevent importing the lexicographic, Cartesian-torus, or full ambient-symplectic conclusions into this host. The main Erdős 181 assertion remains untouched.

---

## 7. Verification and files

`check_cube_parity_pentagon.py` is an exact certificate checker, not a search for embeddings. Its output is saved in `CubeParityPentagonVerification.txt`. It verifies:

* the base row sums and exact annihilating polynomial `(X-1)(X^2-2X-4)`;
* all 25 symplectic Gram identities, binary rank four, and the no-affine-plane assertion for the alphabet;
* invertibility of all four block matrices and the colour of every nonzero multiple of every column;
* injectivity and **every required edge** of both explicit `Q_(2t)` for `t=2,...,7`, a total of 291,264 checked cube edges;
* exact half-degrees for `t=1,...,5`, with the red diagonal correctly removed;
* the Fourier values (3.3) using exact arithmetic in `Q(sqrt(5))`;
* the red source square with integer winding five.

The all-dimensional assertions rest on the proofs above, not on extrapolation from these checks. No numerical search for `D_t` was performed and no Lean proof of either the global assertion or its negation is claimed.

`Submission/Spec.lean` retains SHA-256

```
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```
