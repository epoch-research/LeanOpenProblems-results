# Ordinary cube embeddings: a quantitative fibre-surplus theorem

## Status

This is a **partial result**, not a resolution of the parity-pentagon candidate. It strengthens the parent observation about `K_5 square ... square K_5` from an exclusion to a sharp quantitative necessary condition on **every ordinary injection**, including nonlinear ones. It also gives a stronger, colour-specific bound for the original coordinate axes.

No construction above dimension `2t`, constant-loss construction, or improved upper bound on `D_t` is obtained. In particular, `Q_9` at `t=4` remains unresolved.

### Concrete new necessary conditions

Let `f : Q_d -> F_5^t` be injective, and put `m=2^d`.

1. In **any fixed invertible linear coordinate system**, at least
   \[
   \boxed{\quad 2^{d-1}(d-2t)\quad}                         \tag{1}
   \]
   source edges change at least two coordinates. This is meaningful when `d>2t`. More precisely there is an exact nonnegative-defect identity below. The underlying upper bound of `tm` on the number of one-coordinate edges is sharp.

2. If `f` is monochromatic in the actual parity-pentagon colouring, then in the **original coordinates** at least
   \[
   \boxed{\quad 2^{d-1}(d-2t)+t\left\lceil\frac{2^d}{5}\right\rceil\quad}       \tag{2}
   \]
   source edges change at least two coordinates. Both colours satisfy this bound.

For a putative `Q_9` in `F_5^4`, there are 512 vertices and 2304 required edges. Formula (1) requires **at least 256 edges outside any fixed coordinate Hamming graph**. In particular this applies to each audited monochromatic Hamming subgraph obtained from the block matrices. Formula (2) requires **at least 668 edges changing two or more original coordinates**. These are different edge classifications; the two numbers should not be added.

The proof uses injectivity and the small fibres of the actual alphabet, not affine parametrization, inducedness, or a linear kernel.

---

## 1. The local cube edge capacity for at most five vertices

For `U subset V(Q_d)`, write `e(U)` for the number of source cube edges with both endpoints in `U`.

**Lemma.** If `|U|<=5`, then
\[
 e(U)\le |U|.                                               \tag{3}
\]
For nonempty `U`, equality holds exactly when:

* `|U|=4` and the induced source graph on `U` is a coordinate square;
* `|U|=5` and that graph is a coordinate square with one pendant vertex.

**Proof.** The cube is bipartite and two distinct cube vertices have at most two common neighbours. For the latter fact, a common neighbour implies that the two vertices differ in exactly two coordinates, and the only possible common neighbours flip one of those two coordinates.

For one, two, or three vertices the edge maxima are respectively `0,1,2`, strictly below the number of vertices. For four vertices, bipartiteness gives at most four edges; equality is `K_(2,2)`, a cube square. Every four-cycle of a cube is a coordinate square: its two incident source directions at one vertex must be the same two at the other vertices.

For five vertices, a bipartition of sizes one and four gives at most four edges. A bipartition of sizes two and three gives at most six, but six would be a `K_(2,3)`, contradicting the common-neighbour bound. Thus the maximum is five. Equality is `K_(2,3)` minus one edge, namely a four-cycle with a pendant vertex. Conversely both stated graphs have as many edges as vertices. The empty case is immediate. QED.

The familiar five-vertex edge-isoperimetric values are therefore
\[
 (a(0),a(1),a(2),a(3),a(4),a(5))=(0,0,1,2,4,5).
\]
The proof above is independent of the dimension of the source cube.

---

## 2. The exact fibre-surplus identity

Fix **any** invertible `M` over `F_5`, and put `z(v)=M^(-1)f(v)`. Translation of the coordinate system is also harmless. Call a source edge **Cartesian** if its two `z`-images differ in exactly one coordinate. All other source edges are called **extra**; injectivity excludes distance zero.

For `i in {1,...,t}` and `a in F_5^(t-1)`, define
\[
 U_{i,a}=\{v:z(v)_{-i}=a\}.
\]
Here `z(v)_{-i}` means the tuple with coordinate `i` deleted. Injectivity gives
\[
 |U_{i,a}|\le 5.                                           \tag{4}
\]
For each `i` these fibres partition the `m` source vertices.

Every source edge induced within `U_(i,a)` changes only coordinate `i`. Conversely a Cartesian edge belongs to exactly one such fibre edge set. Thus, if `E_cart` and `E_extra` denote the respective edge counts,
\[
 E_{\rm cart}=\sum_{i,a}e(U_{i,a}).                         \tag{5}
\]
Define
\[
 \Delta_M(f)=\sum_{i,a}\bigl(|U_{i,a}|-e(U_{i,a})\bigr).
\]
The local lemma gives `Delta_M(f)>=0`. Since `sum_(i,a)|U_(i,a)|=tm`, equation (5) gives the **exact identity**
\[
 \boxed{
 E_{\rm extra}
   =\frac{dm}{2}-tm+\Delta_M(f)
   =2^{d-1}(d-2t)+\Delta_M(f).
 }                                                         \tag{6}
\]
In particular,
\[
 \frac{E_{\rm extra}}{|E(Q_d)|}\ge\frac{d-2t}{d}
 \qquad(d>2t).                                             \tag{7}
\]

**Equality information.** `Delta_M(f)=0` if and only if every nonempty fibre has four or five source vertices and induces one of the two unicyclic graphs in the lemma. This follows term by term; there is no cancellation in the defect.

**Sharpness of the edge-capacity constant.** Use the audited injection
\[
 f(u,w)=M(u_1+2w_1,\ldots,u_t+2w_t)^T
\]
with `d=2t`. In `M`-coordinates every nonempty fibre is exactly the four vertices encoding one bit pair, with the source graph `Q_2`. Consequently `Delta_M(f)=0`, every source edge is Cartesian, and `E_cart=tm`. When `M` is either audited monochromatic line basis, this is a monochromatic example in the actual host. Thus the universal coefficient `t` in `E_cart<=tm` cannot be reduced, even restricted to monochromatic embeddings.

This sharpness does **not** assert attainability of (6) with zero defect when `d>2t`.

### Relation to the parent Hamming observation

If all source edges lie in a given coordinate Hamming graph, `E_extra=0` in (6), immediately giving `d<=2t`. Unlike the square-propagation proof, this proof also controls arbitrary injections with many exceptional edges. A surplus of `s=d-2t>0` needs at least `s*2^(d-1)` exceptions, not merely one.

For the actual host, choose any of the red or blue line bases from Section 2 of `CubeParityPentagonAttempt.md`. The corresponding Hamming graph is a spanning monochromatic subgraph. Formula (6) then counts exactly how many required cube edges must use additional parity-pentagon edges outside that subgraph. It applies regardless of how nonlinear the proposed embedding is.

---

## 3. Stronger forest bound in the original coordinate fibres

Now assume every required source edge has the same colour, and take `M=I`. On any original coordinate line, the red host graph is a five-cycle: the allowed nonzero differences are `+/-1`. The blue host graph is another five-cycle, with allowed differences `+/-2`.

Fix an original fibre `U_(i,a)` with `k>0` source vertices. Injectivity identifies its source edges with a subgraph of the appropriate five-cycle. The source graph is bipartite, so this subgraph cannot contain that five-cycle. A subgraph of a cycle containing no cycle is a forest. Hence
\[
 e(U_{i,a})\le |U_{i,a}|-1.                                \tag{8}
\]
This reasoning does not require an induced host embedding: unused host edges are simply absent from this source-edge subgraph.

Let
\[
 r_i=|\{a:U_{i,a}\ne\varnothing\}|
\]
be the number of occupied original coordinate fibres in direction `i`. Summing (8),
\[
 E_{\rm cart}\le tm-\sum_{i=1}^t r_i.
\]
Each fibre holds at most five vertices, so `r_i>=ceil(m/5)`. Therefore
\[
 \boxed{
 E_{\rm extra}\ge
 2^{d-1}(d-2t)+\sum_i r_i
 \ge 2^{d-1}(d-2t)+t\lceil 2^d/5\rceil.
 }                                                         \tag{9}
\]
The slightly weaker normalized form is
\[
 \frac{E_{\rm extra}}{|E(Q_d)|}\ge 1-\frac{8t}{5d}.
\]
As usual, a negative right side supplies no information.

For `t=4,d=9`, equation (9) gives
\[
 256+4\lceil512/5\rceil=256+412=668.
\]
The bound in (9) is not asserted for arbitrary transformed coordinates, where coordinate lines need not be pentagons; the audited monochromatic bases, for example, have complete monochromatic coordinate lines.

---

## 4. Exact remaining gap

These theorems give **lower bounds on the required use of extra edges**. The parity-pentagon host has many such edges. No upper bound on their possible use by an ordinary cube has been proved here. In particular, the exact identity (6) does not imply that its left side is zero or small.

To obtain the requested dimension obstruction by this route one would need a further genuinely all-map restriction on those additional parity edges, strong enough to conflict with (6) or (9). No such restriction is supplied. Conversely, the edge counts do not construct a cube satisfying them.

Accordingly, the unrestricted dimension bounds remain
\[
 2t\le D_t^R,D_t^B\le\lfloor t\log_2 5\rfloor \qquad(t\ge2).
\]
Neither divergence of `t log_2(5)-D_t` nor its boundedness has been established. `Q_9` at `t=4` is still open in this work. The reported progress is the sharp quantitative nonlinear fibre-surplus theorem, not a Ramsey disproof or a claim that the affine bound constrains arbitrary embeddings.

---

## 5. Verification

Run:

```
python3 Submission/check_cube_parity_fibre_surplus.py
```

Saved output: `Submission/CubeParityFibreSurplusVerification.txt`.

The checker uses integer arithmetic only and performs no embedding search. It checks:

* all 6885 subsets of at most five vertices in `Q_4`, including the edge maxima and equality degree sequences;
* all 244 nonempty vertex/edge subgraphs of the two host five-cycles, verifying the forest bound for the bipartite ones;
* ordinary injectivity, every required edge, and zero fibre defect in the audited red and blue `Q_(2t)` examples for `t=2,3,4,5` (12,736 required edges total);
* the exact identity (6) on a fixed, explicitly **uncoloured** base-five injection of `Q_9` into `F_5^4`. This control has 1122 red and 1182 blue cube edges, so it is emphatically not a monochromatic construction;
* the unchanged SHA-256 of `Submission/Spec.lean`:

```
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```

The finite checks supplement the dimension-independent proofs above; no extrapolation from `Q_4` is used to prove the local lemma.
