# Switched binary symplectic hosts: ordinary cubes, nonlinear shears, and the remaining gap

## Status

**No disproof of `R(Q_d) <= C 2^d` is obtained. No constant-loss embedding theorem for every Boolean switching is obtained either.** The arbitrary-switching candidate remains unresolved by this investigation. `Spec.lean` is unchanged.

There are, however, constructive ordinary-injection results, not just objections to a counting estimate:

1. A nonlinear shear produces **spanning `Q_r` in both colours** for a large class of arbitrary-degree switchings (Theorem 4.1).
2. **Every quadratic Boolean switching** on a nondegenerate symplectic space of even dimension `r >= 6` has **`Q_(r-1)` in both colours** (Theorem 5.2).
3. For every sufficiently large even `r` there are switchings of **maximal algebraic degree `r`**, with **no nonzero direction having even an affine first derivative**, which have **`Q_(r-1)` in both colours but no affine-coordinate cube of dimension `ceil(2 log_2 r)+2`** (Theorem 6.1). In particular, for every fixed loss `ell >= 1`, there are arbitrarily large such hosts with no affine-coordinate `Q_(r-ell)` and with ordinary `Q_(r-ell)` in **both** colours.

The last result is an explicit ordinary-injection checkpoint against the proposed affine/high-degree heuristic. It does **not** eliminate all arbitrary switchings. Sections 2 and 7 state exactly what remains to be proved for that larger family.

All results here concern the specified nondegenerate alternating binary form. They are not assertions about arbitrary switched Cayley colourings or arbitrary Hadamard matrices.

---

## 1. Setup and exact spectral normalization

Let `V = F_2^r`, with `r>=2` even, and let `B` be nondegenerate alternating. For an arbitrary function `g:V -> F_2`, write

\[
 C_g(x,y)=B(x,y)+g(x)+g(y),\qquad x\ne y.
 \tag{1.1}
\]

Colour `1` is red and colour `0` is blue. All additions inside Boolean formulas are in `F_2`. An ordinary colour-`c` copy of `Q_d` means an **injective** map

\[
 f:\mathbb F_2^d\longrightarrow V,
 \qquad C_g(f(t),f(t+e_i))=c
 \quad\text{for every }t,i.
 \tag{1.2}
\]

There is no condition on cube nonedges, and neither parity image is required to be an independent set or an affine subspace.

For the proposed Ramsey disproof, it would be necessary, for every fixed loss `ell`, to find arbitrarily large even `r` and a switching `g` for which **neither** colour contains `Q_(r-ell)`. A failure of an affine parametrization is not this statement.

Put `N=2^r` and

\[
 H_{xy}=(-1)^{B(x,y)},\qquad
 D_{xx}=(-1)^{g(x)},\qquad S=DHD.
\]

Character orthogonality gives

\[
 H^2=NI,\qquad S^2=NI,\qquad \|S\|_{op}=\sqrt N.
 \tag{1.3}
\]

In particular, the diagonal is `S_xx=1`, regardless of `g`. The simple-graph adjacency matrices are exactly

\[
 A_1=(J-S)/2,\qquad A_0=(J+S)/2-I.
\]

Consequently,

\[
 A_1-\tfrac12(J-I)=(I-S)/2,
 \qquad A_0-\tfrac12(J-I)=-(I-S)/2,
 \tag{1.4}
\]

and both reference-half norms are at most `(sqrt(N)+1)/2`. If `p_c` is the actual edge density, then

\[
 |p_c-1/2|\le\frac{\sqrt N+1}{2(N-1)},\qquad
 \|A_c-p_c(J-I)\|_{op}\le\sqrt N+1.
 \tag{1.5}
\]

Thus these hosts really do satisfy a fixed square-root spectral bound, including the diagonal and density corrections. This alone does not supply the endpoint embedding. The previous theorem in `CubeSpectralBenchmark.md`, applied to a colour of density at least one half, supplies only

\[
 d=r-2\log_2 r-O(1),
\]

not `r-O(1)`. None of the constructive results below relies on that previous theorem.

For comparison, the exact graph lift is

\[
 \widehat V=V\oplus\mathbb F_2^2,\qquad
 \widehat B((x,a,b),(y,a',b'))=B(x,y)+ab'+a'b,
\]

\[
 j_g(x)=(x,g(x),1),\qquad
 \widehat B(j_g(x),j_g(y))=C_g(x,y).
 \tag{1.6}
\]

An ambient cube in `widehat V` is not a cube in the host unless all its vertices lie in `j_g(V)`. No such containment is inferred here.

---

## 2. The exact ordinary-injection checkpoints

### 2.1 Square equations, potentials, and both colours

Fix an injective map `f:F_2^d -> V`, with `d>=1`, independently of `g`. Define its edge label

\[
 b_f(uv)=B(f(u),f(v)).
\]

There exists a vertex potential `pi_f` with

\[
 b_f(uv)=\pi_f(u)+\pi_f(v)
 \tag{2.1}
\]

on every cube edge if and only if every coordinate square has zero label sum. Explicitly, for the four images of a square,

\[
 B(f_{00}+f_{11},\ f_{10}+f_{01})=0.
 \tag{2.2}
\]

Indeed, expanding (2.2) is precisely the sum of the four edge labels. Coordinate squares generate the binary cycle space of the cube: cancelling backtracks and interchanging consecutive coordinate steps reduces every closed walk using squares. Thus zero square sums make path sums independent of path and define `pi_f`. Conversely, every potential telescopes around every square. The potential is unique up to a constant because the cube is connected.

Write `chi(t)=sum_i t_i` for cube parity. For a square-compatible injection, the **exact** colour-`c` condition is

\[
 \boxed{
 g(f(t))=\pi_f(t)+c\chi(t)+k
 \quad\text{for all }t,\text{ for some }k\in\mathbb F_2.
 }
 \tag{2.3}
\]

Thus, allowing either colour, `g o f + pi_f` must be constant on each of the two parity classes, with the two constants allowed to differ. This is a condition on the actual values of `g` at the actual injective image, not on freely chosen switch bits.

For a uniformly random switching and a fixed injection:

* if (2.2) fails, its monochromatic probability is zero;
* if (2.2) holds, its probability in a specified colour is `2^(1-2^d)`;
* its probability in either colour is exactly `2^(2-2^d)`.

The last four patterns are distinct for `d>=1`. In particular, assigning probability `2^(-d 2^(d-1))` to such a fixed framework would be wrong: the random variables are vertex switch bits, not independent edge colours.

These identities do **not** bound the number or structure of square-compatible ordinary injections. A genuine random-switch disproof would have to control the union of their events, including their large overlaps. No sufficient upper bound or structural classification of that union is proved here.

### 2.2 A parity embedding gives an exact two-colour Hall problem

Let `E,O` be the cube parity classes. Fix an injection `a:E -> V`, and put `s_u=g(a(u))`. For `y in O`, choose a neighbour `u_0` of `y` and define

\[
 L_y=\{z\in V:
 B(a(u)+a(u_0),z)=s_u+s_{u_0}
 \text{ for every }u\in N(y)\setminus\{u_0\}\}.
 \tag{2.4}
\]

This affine system can be inconsistent. If it is consistent and its rank is `rho_y`, then

\[
 |L_y|=2^{r-\rho_y},\qquad \rho_y\le d-1.
\]

The actual list in colour `c` is

\[
 \boxed{
 \mathcal C_y^c=(L_y\setminus a(E))\cap
 \{z:B(a(u_0),z)+g(z)=c+s_{u_0}\}.
 }
 \tag{2.5}
\]

For this fixed parity embedding, an ordinary colour-`c` extension exists **if and only if** the family `(C_y^c)_(y in O)` has a system of distinct representatives, equivalently satisfies Hall's condition. The removal of `a(E)` handles cross-parity collisions; distinct representatives handle collisions within `O`.

Both colours use the same affine flat, and exactly

\[
 \mathcal C_y^0\ \dot\cup\ \mathcal C_y^1=L_y\setminus a(E).
 \tag{2.6}
\]

For `d=r-ell`, consistency gives an ambient flat of dimension at least `ell+1`. It does **not** give a nonempty list in a predetermined colour, and does not give Hall expansion. Choosing a favourable colour separately for every `y` does not give a monochromatic cube. Equations (2.4)--(2.6) retain both the switch-bit constraint and the ordinary-injection requirement.

### 2.3 What the affine calculation actually says

For an affine injection

\[
 f(t)=a+\sum_{i=1}^d t_i v_i
\]

with independent `v_i`, a potential is

\[
 \pi_f(t)=\sum_i B(a,v_i)t_i+
              \sum_{i<j}B(v_i,v_j)t_it_j.
 \tag{2.7}
\]

Taking a coordinate derivative verifies (2.1). Hence an affine-coordinate monochromatic cube imposes the quadratic restriction (2.3) on `g o f`.

There are at most `2^(r(d+1))` affine injections. A union bound for unrestricted random `g` therefore gives

\[
 \Pr(\text{an affine-coordinate monochromatic }Q_d)
 \le 2^{r(d+1)+2-2^d}.
 \tag{2.8}
\]

This does exclude affine-coordinate `Q_(r-ell)` with high probability for each fixed loss. It says nothing comparable about ordinary injections. Theorem 6.1 below demonstrates a much sharper affine/ordinary separation in actual switched hosts.

---

## 3. A nonlinear shear lemma with injection built in

Choose a quadratic refinement `q` of `B`, normalized by `q(0)=0`:

\[
 q(x+y)=q(x)+q(y)+B(x,y).
\]

Set `h=g+q`. The colouring is then

\[
 C_g(x,y)=q(x+y)+h(x)+h(y).
 \tag{3.1}
\]

This is a rewriting of the given colouring, not a new colouring.

### Lemma 3.1 (shear on an affine domain)

Let `A=a+U` be an affine subspace, let `0 != v in U`, and suppose

\[
 h(z+v)=h(z)\quad(z\in A).
 \tag{3.2}
\]

Suppose `u_1,...,u_k` is a basis of `U` such that, for a fixed colour `c`,

\[
 q(u_i)=c,\qquad B(u_i,v)+q(v)=1
 \quad(1\le i\le k).
 \tag{3.3}
\]

Then

\[
 \boxed{
 f_c(t)=z(t)+h(z(t))v,
 \qquad z(t)=a+\sum_i t_i u_i
 }
 \tag{3.4}
\]

is an ordinary colour-`c` copy of `Q_k`, using **every vertex of `A` exactly once**.

**Proof.** The map `T(z)=z+h(z)v` preserves `A`. By (3.2), `h(T(z))=h(z)` and `T(T(z))=z`. Thus `T` is an involution of `A`, so (3.4) is injective and onto `A`.

For an edge `z,z+u_i`, put `delta=h(z)+h(z+u_i)`. Then

\[
 T(z)+T(z+u_i)=u_i+\delta v,
\]

and, using (3.1),

\[
 \begin{aligned}
 C_g(T(z),T(z+u_i))
 &=q(u_i+\delta v)+\delta\\
 &=q(u_i)+\delta\bigl(q(v)+B(u_i,v)+1\bigr)=c.
 \end{aligned}
\]

Only cube edges are asserted to have colour `c`. This proves an ordinary copy, not necessarily an induced one. `QED`

### Lemma 3.2 (the required basis, including degenerate restrictions)

Let `q` be a quadratic form on a binary space `U`, with polar form `B_U`. Suppose

* `rank(B_U) >= 4`;
* `q(v)=0`;
* `v` is not in the radical of `B_U`.

For each `c in F_2`, the set

\[
 K_c=\{u\in U:B_U(u,v)=1,\ q(u)=c\}
 \tag{3.5}
\]

spans `U`, and therefore contains a basis of `U`.

**Proof.** Choose `w` with `B_U(v,w)=1`. Replacing `w` by `w+q(w)v` makes `q(w)=0`. Split off this nondegenerate hyperbolic plane:

\[
 U=\langle v,w\rangle\perp T.
\]

The restriction to `T` has rank `rank(B_U)-2 >= 2`. The elements of `K_c` are exactly

\[
 w+(c+q(t))v+t\quad(t\in T).
 \tag{3.6}
\]

Their span contains `w+cv` and every `q(t)v+t`. Choose `t,t' in T` with `B_U(t,t')=1`. The sum of the three vectors corresponding to `t,t',t+t'` is `v`. The span therefore contains `v`, all of `T`, and `w`, hence all of `U`. This argument does not assume that the whole restriction `B_U` is nondegenerate. `QED`

---

## 4. Arbitrary-degree switchings with spanning cubes in both colours

### Theorem 4.1 (global invariant-direction theorem)

Let `r>=4` be even. If there is a nonzero `v` such that

\[
 q(v)=0,\qquad h(x+v)=h(x)\quad\text{for every }x\in V,
 \tag{4.1}
\]

then the switched host has a **spanning ordinary `Q_r` in each colour**.

**Proof.** Apply Lemma 3.2 to `U=V`, separately for `c=0,1`, and then apply Lemma 3.1 with `A=V`. Each embedding is a linear bijection followed by the explicitly invertible shear. `QED`

In terms of `g` alone, a sufficient condition independent of the choice of refinement is

\[
 D_vg(x):=g(x+v)+g(x)=B(v,x)\quad\text{for all }x.
 \tag{4.2}
\]

Indeed, a refinement can always be chosen with `q(v)=0`, and then (4.2) is exactly (4.1). The hypothesis is sufficient, not necessary.

### Explicit coordinates

In standard symplectic coordinates

\[
 V=\langle e_1,f_1,\ldots,e_m,f_m\rangle,\quad r=2m,
 \qquad q(x)=\sum_{j=1}^m x_{e_j}x_{f_j},
\]

take `v=e_1`, with `m>=2`. Let `h` be **any** Boolean function independent of the `e_1` coordinate. For colour `c`, put `a_0=f_1+ce_1`. The following `r` vectors are a basis:

\[
 a_0;\quad a_0+e_j,\ a_0+f_j\ (2\le j\le m);\quad
 a_0+e_1+e_2+f_2.
 \tag{4.3}
\]

Each has `q`-value `c` and pairs to `1` with `e_1`. To check independence, their span contains every `e_j,f_j` for `j>=2`; the sum of the last vector, `a_0+e_2`, `a_0+f_2`, and `a_0` is `e_1`; it then contains `f_1`. There are exactly `r` vectors.

Let `L_c` be the associated linear bijection. The full embedding is

\[
 f_c(t)=L_c(t)+h(L_c(t))e_1.
 \tag{4.4}
\]

It is generally very nonlinear. For example, `h` may have degree `r-1`, or may be an arbitrary truth table on the other `r-1` coordinates. In particular, taking `h` to depend on only one Lagrangian half is far from necessary.

This theorem removes this subclass as a Ramsey counterexample family even at zero dimension loss. It is not an assertion that an arbitrary Boolean `h` has an invariant direction.

---

## 5. Every quadratic switching has a half-spanning cube in both colours

First, the unswitched construction can be sharpened by one dimension relative to the elementary quadratic lift with a fixed extra coordinate.

### Lemma 5.1 (unswitched `Q_(r-1)` in both colours)

For every even `r>=4`, the colouring `B(x,y)` has an ordinary `Q_(r-1)` in each colour, both on the same affine hyperplane.

**Proof.** Write

\[
 V=W\oplus\mathbb F_2^2,\qquad \dim W=D=r-2,
\]

\[
 B((z,a,b),(z',a',b'))=B_0(z,z')+ab'+a'b,
\]

and choose standard hyperbolic `q_0` on `W`. The bijection

\[
 F:W\oplus\mathbb F_2\longrightarrow\{b=1\},\qquad
 F(z,t)=(z,q_0(z)+t,1)
 \tag{5.1}
\]

satisfies, for **all** pairs,

\[
 B(F(z,t),F(z',t'))=q_0(z+z')+t+t'.
 \tag{5.2}
\]

Thus this hyperplane is isomorphic to a binary Cayley colouring with connection function `Q(z,t)=q_0(z)+t`.

Let `u_1,...,u_D` be a hyperbolic basis of `W`, with `B_0(u_1,u_2)=1`; each `q_0(u_i)=0`. A basis of colour `0` is

\[
 (u_i,0)\ (1\le i\le D),\qquad (u_1+u_2,1),
\]

and a basis of colour `1` is

\[
 (0,1),\qquad (u_i,1)\ (1\le i\le D).
\]

Subset sums of either basis give a bijective `Q_(D+1)` in the corresponding Cayley colour. Composing with `F` proves the claim, with injection explicit. `QED`

### Theorem 5.2 (all quadratic Boolean `g`)

Let `r>=6` be even and let `g:V -> F_2` have algebraic degree at most two. Then the switched host contains **`Q_(r-1)` in both colours**.

**Proof.** Adding a constant to `g` changes no edge colour, so normalize `g(0)=0`. Let `G` be its polar form,

\[
 G(x,y)=g(x+y)+g(x)+g(y).
\]

This is alternating. There are three cases.

#### Case 1: `G=0`

Then `g` is linear. Nondegeneracy gives `t` with `g(x)=B(t,x)`, and

\[
 B(x,y)+g(x)+g(y)=B(x+t,y+t).
\]

Translate the two embeddings from Lemma 5.1.

#### Case 2: `G=B`

The colouring is exactly the Cayley colouring

\[
 C_g(x,y)=g(x+y).
\]

Both level sets of a nondegenerate binary quadratic form in dimension at least four span the space. Here is a short verification that does not assume a classification of quadratic forms. There is a nonzero vector `v` with `g(v)=0`: if `g(a)=1`, choose `b` independent of `a` in `a^perp`; either `g(b)=0`, or `g(a+b)=0`. Lemma 3.2 now gives a basis in each level set. Subset sums give **spanning `Q_r` in both colours**, more than required.

#### Case 3: `G` is neither `0` nor `B`

There is a nonzero `v` such that the two linear functionals

\[
 P_v:=G(v,\cdot)+B(v,\cdot),\qquad B(v,\cdot)
 \tag{5.3}
\]

are nonzero and distinct, hence independent over `F_2`.

To justify existence, define the linear operator `T` by `B(Tv,x)=G(v,x)`. If every `Tv` belonged to `{0,v}`, linearity would force `T=0` or `T=I`: otherwise take a nonzero killed vector and a nonzero fixed vector and examine their sum. Those two possibilities are precisely `G=0` and `G=B`, excluded here.

Choose a quadratic refinement `q` of `B` with `q(v)=0`; adding a suitable linear form to any refinement achieves this. Put `h=g+q`, and let

\[
 U=\ker P_v,\qquad A=\{x:P_v(x)=h(v)\}.
 \tag{5.4}
\]

These have dimension `r-1`. Since both polars are alternating, `v in U`. Since `P_v` and `B(v,.)` are independent, `v` is not in the radical of `B|_U`.

The restriction of a nondegenerate alternating form to a hyperplane has a one-dimensional radical, so

\[
 \operatorname{rank}(B|_U)=r-2\ge4.
 \tag{5.5}
\]

For completeness, if `u` represents the functional `P_v=B(u,.)`, then `U=u^perp` and its radical is exactly `<u>`; alternation ensures `u in U`.

The polar of `h` is `G+B`, so, with the normalization `h(0)=0`,

\[
 D_vh(x)=h(v)+P_v(x)=0\quad(x\in A).
 \tag{5.6}
\]

For each colour `c`, Lemma 3.2 supplies a basis `u_i` of `U` with `B(u_i,v)=1` and `q(u_i)=c`. Choose `a in A` and use

\[
 f_c(t)=a+\sum_i t_i u_i+
 h\!\left(a+\sum_i t_i u_i\right)v.
 \tag{5.7}
\]

By Lemma 3.1 this is a colour-`c` cube of dimension `r-1`, bijective onto `A`. In particular, no assertion that an ambient lifted cube lies in the graph of `g` is needed. `QED`

**Dimension audit.** In the generic case the affine domain has dimension `r-1`, not `r`; its restricted polar rank is `r-2`, not `r-1`. Splitting off `<v,w>` leaves rank `r-4`, which is why the proof assumes `r>=6`. The embedding remains injective on the entire affine domain. Cases 1 and 2 work already for `r>=4`.

It follows that quadratic switchings cannot supply the required two-colour avoidance for any fixed loss `ell>=1` once `r>=6`.

---

## 6. Maximal degree, no affine derivatives, no large affine-coordinate cubes — and ordinary cubes in both colours

The invariant-direction hypothesis can be destroyed by one switch-bit change without destroying the constant-loss ordinary cubes.

### Theorem 6.1 (strong affine/ordinary separation)

For every even `r>=8`, put

\[
 d_0=\lceil 2\log_2 r\rceil+2\le r.
\]

There is a Boolean switching `g` such that:

1. `g` has algebraic degree exactly `r`;
2. for every nonzero `w`, the derivative `D_w g` is **not affine**;
3. neither colour has an affine-coordinate `Q_(d_0)`;
4. **both colours have ordinary injective `Q_(r-1)`**.

Here “affine-coordinate” refers to the parametrizing injection `t -> a+sum t_i v_i`. It does not merely refer to the vertex set being affine.

**Proof.** Use the explicit standard coordinates of Section 4 and `v=e_1`. Choose `h_0` uniformly from the Boolean functions on `V/<v>`, pull it back to `V`, and fix a point `x_*`. Define

\[
 g_0=q+h_0,\qquad g=g_0+\mathbf1_{\{x_*\}}.
 \tag{6.1}
\]

#### Ordinary cubes in both colours

For every choice of `h_0`, Theorem 4.1 gives a spanning cube `f_c` in each colour of `g_0`. Changing the one value at `x_*` changes only edges incident with `x_*`.

In each spanning cube, take a coordinate face avoiding `f_c^{-1}(x_*)`. Its image is an injective `Q_(r-1)` avoiding `x_*`, all of whose edge colours are unchanged. This proves property 4 for **every** outcome of the random choice, not merely with positive probability.

#### Maximal degree and absence of affine derivatives

The sum of `h_0` over `V` is zero in `F_2`, since its values come in equal pairs. The sum of `q` is also zero since its degree is less than `r`. The one-point perturbation gives

\[
 \sum_{x\in V}g(x)=1.
 \tag{6.2}
\]

For a Boolean function, this sum is exactly the coefficient of the product of all `r` variables in its algebraic normal form. Hence `deg(g)=r`.

If `D_wg` were affine for some nonzero `w`, it would descend to an affine function on the quotient `V/<w>`. Every affine function on this quotient has even weight because its dimension `r-1` is at least two. But summing the derivative over one representative from each pair gives

\[
 \sum_{V/\langle w\rangle}D_wg
 =\sum_{x\in V}g(x)=1,
\]

a contradiction. This proves properties 1 and 2. In particular, these examples have neither constant first derivatives nor globally affine corrected derivatives of the form (4.2).

#### Excluding all affine-coordinate cubes, without excluding ordinary cubes

Fix an affine injection `f:F_2^d -> V`, a colour `c`, and the constant `k` in (2.3). That condition prescribes a specific value of `h_0` at every point of `f(F_2^d)`. This set meets at least `2^(d-1)` distinct cosets of `<v>`, since each coset contains two points. If the prescriptions conflict within a coset their probability is zero; otherwise their probability is at most `2^(-2^(d-1))`.

Union over the two colours, the two constants, and all affine injections gives

\[
 \boxed{
 \Pr(\text{an affine-coordinate monochromatic }Q_d)
 \le 2^{r(d+1)+2-2^{d-1}}.
 }
 \tag{6.3}
\]

The perturbation in (6.1) is fixed, so it does not affect this independence calculation.

The assertion `d_0<=r` can be checked uniformly over the stated even dimensions: `2^((r-2)/2)>=r` holds at `r=8`, and increasing `r` by two doubles the left side while increasing the right side by two. Thus `2 log_2 r<=r-2`, and taking the ceiling gives `d_0<=r`.

For `d=d_0`,

\[
 2^{d_0-1}\ge2r^2,
 \qquad r(d_0+1)+2\le r(r+1)+2<2r^2
 \quad(r\ge8).
\]

Thus (6.3) is strictly less than one. Some `h_0` excludes every affine-coordinate monochromatic `Q_(d_0)`, while all outcomes already satisfy properties 1, 2, and 4. `QED`

### Consequence for the proposed lower-bound mechanism

For every fixed `ell>=1`, arbitrarily large even `r` satisfy `r-ell>=d_0`. A larger affine-coordinate cube would contain an affine-coordinate `Q_(d_0)` as a face. The hosts from Theorem 6.1 therefore have

\[
 \begin{gathered}
 \text{no affine-coordinate }Q_{r-\ell}\text{ in either colour},\\
 \text{an ordinary }Q_{r-1}\text{ in both colours}.
 \end{gathered}
\]

They satisfy the same square-root spectral bound as every switching. Maximal degree, absence of affine derivatives, and absence of all large affine-coordinate cubes can therefore coexist with exactly the ordinary near-spanning cubes that a Ramsey lower bound would have to exclude.

This is **not** a Ramsey counterexample or an upper bound for all switchings. It is a proved family of genuine nonlinear embeddings showing why those particular proposed rigidity diagnostics cannot suffice.

A useful deterministic robustness variant is immediate: changing `g_0` at `t` vertices preserves, in each colour, an ordinary

\[
 Q_{\,r-\lceil\log_2(t+1)\rceil}
\]

whenever the displayed dimension is nonnegative. Partition either original spanning cube into `2^k>t` coordinate faces of dimension `r-k`; one face avoids the changed vertices.

---

## 7. What remains unresolved for an arbitrary switching

The preceding results are constructive ordinary-copy theorems for substantial subclasses, including high-degree functions without affine first derivatives. They do not imply that every Boolean function belongs to one of these subclasses.

To finish a **positive** result for the full candidate family, one would need, for some absolute `ell_0`, to produce for every `g` an ordinary injection of `Q_(r-ell_0)` in at least one colour. For example, a direct proof through Section 2.2 would need a parity injection and one common colour for which the actual lists (2.5) satisfy Hall. Neither the rank bound nor the complementary partition (2.6) supplies this. A direct use of Section 2.1 would need to find an injection obeying both the square equations and the prescribed values of `g` in (2.3).

To finish a **negative** result, one would need, for every fixed `ell`, an actual `g` excluding **all** ordinary injections in **both** colours. A counting proof could in principle control the union of the events (2.3), but it must range over all square-compatible ordinary injections and retain the dependence between their events. No sufficient bound for that union is established here. Counting affine maps, assuming that every compatible map is affine up to a bounded-dimensional correction, or choosing the switch bits independently of the image would not prove the required avoidance.

In particular:

* The usual augmented symplectic cube does not automatically lie on the graph of an arbitrary `g`.
* A large affine flat of candidates does not guarantee a point with the required `g` value.
* Nonempty lists of varying favourable colours do not give one monochromatic cube.
* Homomorphisms without the Hall/injection condition do not answer the question.
* The shear hypothesis is not available for a general truth table; Theorem 6.1 also shows that merely failing that hypothesis is not an obstruction to an ordinary cube.
* No all-dimensional rigidity theorem for arbitrary square-compatible injections is claimed.

**Conclusion:** the arbitrary switched-symplectic candidate is not disproved and not eliminated. The useful advances are the exact ordinary-copy criteria, the nonlinear shear construction, the all-quadratic both-colour theorem, and a maximal-degree affine/ordinary separation with the actual ordinary copies explicitly certified. The global Ramsey conjecture remains untouched.

---

## 8. Verification and preserved specification

`check_cube_switched_symplectic.py` checks the displayed constructions, not a search for Ramsey counterexamples. Its output is saved in `CubeSwitchedSymplecticVerification.txt`. The checks include:

* all 256 invariant quotient truth tables at `r=4`, constructing and checking both spanning cubes (512 cubes);
* the corresponding 512 one-point-perturbed half-spanning cubes, with injection, edge colours, odd weight, and absence of affine derivatives checked;
* explicit higher-degree shear instances at `r=6,8,10`;
* both unswitched half-spanning embeddings at `r=4,6,8,10`;
* 174 quadratic-construction audits at `r=6,8,10`, covering affine, Cayley, and generic-polar cases;
* the square/potential criterion and the exact four switching patterns on tested fixed frameworks;
* the two-colour affine-flat/list identity, including exclusion of the first parity image;
* the Hadamard identity and the sign of the probabilistic existence exponent.

These finite checks audit signs, coordinates, dimensions, and injectivity. The all-dimensional statements rest on the proofs above, not on extrapolation from the checks. No Lean proof of the global assertion or its negation is claimed.

`Submission/Spec.lean` retains SHA-256

```
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```
