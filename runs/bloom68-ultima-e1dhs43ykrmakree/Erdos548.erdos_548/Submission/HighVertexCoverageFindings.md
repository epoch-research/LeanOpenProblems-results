# High-vertex coverage: positive theorems and an adaptive low-degree repair

## Outcome and scope

**The unrestricted question is not settled here.** I obtained neither a proof that every high vertex of every critical host is covered by every target tree, nor a full-critical counterexample, even conditional on ordinary containment. In particular, none of the earlier fixed-root, fixed-edge-endpoint, or color-role counterexamples is being presented as an uncovered vertex.

There are genuine coverage theorems, rather than just proposed missing statements:

1. **Every high vertex of a critical host is covered by every spider.** This follows from the *rooted obstruction characterization* in Fan–Hong–Liu, not merely their unrooted spider theorem. Its exceptional cases still cover the specified host vertex. A self-contained path argument gives more: every vertex of a `W_k` graph lies on a `k`-edge path.
2. **Every high vertex of every complete multipartite host of average degree greater than `k-1` is covered by every `k`-edge tree.** A prescribed nonleaf in a smaller tree color class can be put at the prescribed high vertex. Criticality is unnecessary.
3. **Every high vertex of a critical clique-join host `K_a ∨ (disjoint union of cliques)` is covered by every target.** This includes high vertices in wings, not just the universal vertices.
4. **Bipartite critical hosts have coverage for all trees whose color-class sizes differ by at most two.** Balanced trees in this class cover *every* host vertex, not just high ones.
5. A low-maximum-degree, all-role two-wing obstruction admits an **explicit adaptive repair by one boundary edge**. Full incidence criticality forces such an edge. This also gives a conditional coverage theorem for connected minimum-degree extensions of the obstruction, and an infinite family of genuine critical hosts illustrating the repair outside the high-`Delta(T)` regime.

The last result uses the tree role host-dependently: an edge leaving one wing class puts the **center** at `s`; an edge leaving the other puts a **hub** there. It is a concrete global rearrangement, not preservation of an arbitrary old embedding.

All embeddings below are non-induced injective homomorphisms. No Spec or shared Lean file was modified. No new Lean formalization is claimed.

## 1. Exact assumptions and logical distinctions

Let

\[
 a=\frac{k-1}{2},\qquad e(G)=a|G|+\eta,\quad \eta>0,
\]

and assume `e(G[U]) <= a|U|` for every proper induced vertex set `U`. There is no need below to restrict `eta` to a normalized half-unit or unit.

For every nonempty `X`,

\[
 I_G(X)=e(G)-e(G-X)\ge a|X|+\eta>a|X|.                 \tag{1}
\]

In particular, `G` is connected, `|G|>=k+1`, `delta(G)>=ceil(k/2)`, and there is a vertex of degree at least `k`. Moreover,

\[
 \sum_{v\in X}(2d_G(v)-d_{G[X]}(v))=2I_G(X)>(k-1)|X|,
\]

so `G` satisfies `W_k`.

Fix a high vertex `s` and write

\[
 R_s(G,T)=\{u\in V(T):\text{some embedding }f:T\to G\text{ has }f(u)=s\}.
\]

The question is exactly whether `R_s(G,T)` is always **nonempty**. It does not require a particular vertex, a particular edge endpoint, a leaf, a leaf-parent, a center, or a whole color class to belong to `R_s`.

The already established exact-apex/CL theorem gives coverage whenever

\[
 \Delta(T)\ge\lfloor k/2\rfloor+1:
\quad d_G(s)\ge k,\quad
 \delta(G-s)\ge\lceil k/2\rceil-1\ge k-\Delta(T).
\]

The earlier `AdjacentRootFlexibilityFindings.md` example has `R_s={hub}` and is therefore **covered**. The critical low-degree wing example is also covered. Neither answers the present question negatively.

## 2. Paths: coverage of every vertex in W_k

**Theorem 1.** Every vertex of a finite `W_k` graph lies on a path of `k` edges.

Here the marked host vertex need not have high degree.

### Endpoint inequality

Let `J` have `m` vertices and a Hamiltonian path. Let `E` be the set of all possible endpoints of Hamiltonian paths in `J`. Then, for every `v in E`,

\[
 2d_J(v)-d_{J[E]}(v)\le m-1.                          \tag{2}
\]

Take a Hamiltonian path `x_0,...,x_(m-1)=v`, put `A=N_J(v)`, and put

\[
 B=\{x_{i+1}:x_i\in A\}.
\]

Path rotation gives `B subset E`; also `|B|=|A|` and `x_0 in E-B`. If `epsilon` is the indicator of `x_0 in A`, then

\[
 |A\cup B|\le m-1+\epsilon,\qquad
 |A\cap E|\ge |A\cap B|+\epsilon.
\]

Subtracting proves (2).

### Keep the marked vertex, not an endpoint role

Choose a longest path `P` **containing the marked vertex** `s`, and let `J=G[V(P)]`. Every Hamiltonian rerouting of `J` retains `s`. Consequently no attainable endpoint has a neighbor outside `V(P)`, since that would give a longer path still containing `s`.

Thus the potentials in (2) are the ambient `G`-potentials on `E`. Applying `W_k` to `E` gives `k<=|P|-1`. Take a `k`-edge subpath containing `s`. This proves the theorem.

This is exactly where freeing the tree role helps: reroutings need not preserve `s` as an endpoint, but they preserve its membership in the copy.

## 3. Spiders: the rooted obstruction theorem already gives coverage

**Theorem 2.** If `G` satisfies (1), then every vertex `s` of degree at least `k` is contained in a copy of every `k`-edge spider.

A spider has at most one vertex of degree greater than two. The following is a consequence of the characterization in Section 3 of:

> Genghua Fan, Yanmei Hong, Qinghai Liu, *The Erdős–Sós Conjecture for Spiders*, arXiv:1804.06567.

The local source is `/corpus/src/1804.06567/1804.06567.tex`. The relevant theorem is labelled `thm-spider-T1`, at lines 188–192; the explicit exceptional structure is obtained at lines 289–296. This is a literature consequence, not a new proof of their characterization.

Their hypothesis is incident density `I_G(X)>(k-1)|X|/2`, exactly supplied by (1). For a high vertex `s`, their theorem either embeds the spider with its center at `s`, or gives an even-edge exceptional case:

* all legs have even length; and
* the host has a complete bipartite block with side sizes at least `k/2+1` and `k/2`, **containing `s`**.

For the all-two-edge-legs spider, the theorem gives such a `(k+1)`-vertex block containing `s` directly. For the other all-even spiders, the conclusion at the end of its proof is a whole-host structure `H(n-k/2,k/2)`, with complete cross edges; choose a block containing `s`. The displayed statement in the local source uses an undefined `H_0` in this latter case; the proof's explicit `H(n-k/2,k/2)` conclusion is the structure used here.

An all-even spider has color-class sizes `k/2+1,k/2`. It embeds **spanningly** in this block. Hence its copy contains `s`, whichever side contains `s`. The non-center exceptional case is therefore *not* a coverage obstruction.

### A low-Delta example illustrating the distinction

Let `k=2m`, `m>=3`, and

\[
 G=K_{m,b},\qquad b=m(2m-1)+1.
\]

Then

\[
 e(G)=\frac{k-1}{2}|G|+\frac12,
\]

and every proper induced subset is sparse. Indeed, for a subset with side counts `x,y`, if `x<=m-1` then `xy-(m-1/2)(x+y)<=0`; if `x=m` and the subset is proper, then `y<=b-1=m(2m-1)` and its surplus is again nonpositive.

Take the spider with `m` legs of length two and let `s` be in the `m`-vertex host part. Its degree is `b>=k`. The hub and all leaves belong to the `(m+1)`-vertex tree color class, so **none of them can map to `s`**. Every one of the `m` degree-two subdivision vertices can map to `s` by the bipartite injection. Thus `s` is covered even though it can be neither hub nor leaf. Here `Delta(T)=m=k/2`, outside the strict high-Delta theorem.

This is a positive illustration, not a counterexample to coverage.

## 4. Every high vertex in a dense complete multipartite host

**Theorem 3.** Let `G` be complete multipartite with `2e(G)>(k-1)|G|`. Let `T` be a `k`-edge tree, `k>=2`, with color classes `A,B`, where `alpha=|A|<=beta=|B|`. For **every** high host vertex `s` and **every** nonleaf `p in A`, there is a full embedding with `p -> s`.

In particular, every high host vertex is covered by every target. The case `k=1` is immediate.

### A selection fact

If `1<=h<alpha` and `p in A` is a nonleaf, there is a set `U subset A` such that

\[
 p\in U,\quad |U|=h,\quad \sum_{u\in U}d_T(u)\ge2h.   \tag{3}
\]

If there are at least `h` nonleaves in `A`, choose `h` of them including `p`. Otherwise take all nonleaves and fill with leaves. In the latter case the selected degree sum is

\[
 k-(\alpha-h)\ge\alpha-1+h\ge2h.
\]

Here `k>=2alpha-1` and `alpha>=h+1`. The set `U` is independent.

### Proof retaining the prescribed s

Put `n=|G|`, `t=n-k>=1`. If the host part sizes are `c_i`, a part is high exactly when `c_i<=t`. Let `H` be the union of high parts and let `h=|H|>0`.

**Case `h>=alpha`.** Begin with the entire host part containing the **specified** `s`, and add high parts until their union `X` first has at least `alpha` vertices. Then

\[
 \alpha\le |X|\le\alpha+t-1=n-\beta.
\]

(The same bound holds if the initial part already has at least `alpha` vertices.) The two unions of host parts `X,V(G)-X` have a complete interface. Embed `A` into `X` with `p -> s`, and `B` into its complement.

**Case `h<alpha`.** Every low part has size at most `t+h`. To see this, the total high surplus above degree `k-1` is

\[
 \sum_{c_i\le t}c_i(t+1-c_i)\le ht.
\]

A low part of size `b>=t+h+1` would alone contribute deficit

\[
 b(b-t-1)\ge bh>ht,
\]

contradicting the strict positive degree-sum surplus. For `L=V(G)-H` it follows that

\[
 \delta(G[L])\ge(n-h)-(t+h)=k-2h.                    \tag{4}
\]

Choose `U` by (3). The forest `F=T-U` has `e(F)<=k-2h` and `|F|=k+1-h<=|L|`. The unmarked consequence of CL embeds it into `G[L]`. Map `U` bijectively onto `H`, arranging `p -> s`. All deleted tree edges go from `U` to `F`, and all required host cross edges are present. This completes the embedding.

The smaller tree color class has a nonleaf when `k>=2`, so the coverage conclusion follows. This strengthens the earlier *some high leaf-parent* argument by retaining an arbitrary specified high vertex throughout both branches.

## 5. Every high vertex in a critical clique-join host

**Theorem 4.** Suppose a critical host has the form

\[
 G=K_b\vee\bigl(K_{c_1}\ \dot\cup\cdots\dot\cup\ K_{c_q}\bigr).
\]

Then every high vertex of `G` is covered by every `k`-edge tree.

The case `k=1` is immediate, so let `k>=2`. Let `S` be the universal `b`-clique. The single-clique case is immediate, so assume `b>=1` and there are wing vertices.

For each wing `C`, criticality applied to deleting `C` gives

\[
 \binom{|C|}{2}+b|C|>\frac{k-1}{2}|C|,
 \qquad |C|\ge k-2b+1.                              \tag{5}
\]

Now fix a high vertex `s`.

* If `s in C` is in a wing, then `d(s)=b+|C|-1>=k`. The clique `S union C` has at least `k+1` vertices. Embed `T` into a `(k+1)`-subset containing `s`.
* Suppose `s in S`. Let `A` be a smaller tree color class and choose a nonleaf `p in A`. If `b>=|A|`, put `A` into `S` with `p -> s` and put the other color class in any unused vertices. Images of `A` are universal.
* If `b<|A|`, use (3) with `h=b`. The forest `T-U` has at most `k-2b` edges. By (5), the disjoint union of host wings has minimum degree at least `k-2b` and enough vertices. Embed the forest by CL, and map `U` onto `S` with `p -> s`.

This proves coverage at **every** high vertex. The component incidence bound is actually used in (5); this is not a minimum-degree-only replacement of criticality.

## 6. Bipartite targets close to balanced

**Theorem 5.** Let `G` be bipartite, let `T` have color-class sizes `alpha<=beta`, and suppose

\[
 \delta(G)\ge\max\{\alpha,\beta-1\},\qquad d_G(s)\ge k.
\]

Then a full copy of `T` contains `s` as a leaf-parent.

The larger tree color class contains a leaf `ell`: otherwise its degree sum would be at least `2beta>alpha+beta-1=k`. Delete such a leaf, with parent `p`. The two remaining color-class sizes are `alpha,beta-1`. Colored greedy embedding therefore embeds `T-ell` with `p -> s`, in whichever host color orientation is appropriate. At most `k-1` neighbors of `s` are occupied, so its high degree restores `ell`.

For a critical host, `delta(G)>=ceil(k/2)`. Consequently the theorem applies whenever the tree color-class sizes differ by at most two. More explicitly:

* `k=2r+1`: colors `(r+1,r+1)` or `(r,r+2)`;
* `k=2r`: colors `(r,r+1)`.

For the balanced odd-edge case, ordinary colored greediness embeds the full tree from **any prescribed tree vertex at any host vertex**. This last assertion is restricted to these bipartite, balanced instances; it does not revive general whole-color root availability.

## 7. A genuine all-role obstruction below density, and its adaptive repair

This section targets a natural way to try to build a conditional counterexample: place a high vertex in a two-wing tree-free region and put ordinary target copies in a remote reservoir. The result shows exactly why the following low-degree obstruction cannot be isolated from that reservoir in a critical host.

### 7.1 The target and the two-wing trap

Choose odd `ell>=3` and `t>=ell`. Let `T=T_(ell,t)` consist of a center `z`, `ell` neighbors `u_1,...,u_ell`, and `t` leaves at each `u_i`. Put

\[
 k=\ell(t+1),\qquad
 p=\frac{(\ell+1)t}{2}-1,\qquad q=(\ell-1)t.
\]

Then `Delta(T)=t+1<=k/2`.

Construct `H` from two disjoint wings

\[
 H[C_i]=K_{q,p},\qquad C_i=A_i\dot\cup B_i,
 \quad |A_i|=q,\ |B_i|=p,
\]

and a vertex `s` adjacent to all of `A_1 union A_2`, and to no `B_i`. There are no other edges. Its marked degree is `2q>=k`; its minimum degree is at least `ceil(k/2)`.

This is a tight-capacity variant of the familiar two-biclique examples in Besomi–Pavez-Signé–Stein, *Maximum and minimum degree conditions for embedding trees*, arXiv:1808.09934, Section 2. The coverage result here is the explicit repair below, not the below-density obstruction itself.

**Nevertheless `H` has no copy of `T`, and in particular no role at `s`.** This is a complete role check:

* **Center at `s`:** at least `(ell+1)/2` hubs must enter one `A_i`. Their leaves need `((ell+1)/2)t=p+1` vertices of `B_i`, impossible.
* **Hub at `s`:** the large component of `T-s` must lie in one wing. Its center and the leaves of the other `ell-1` hubs need `1+(ell-1)t=q+1` positions in that wing's `A_i`, impossible.
* **Leaf at `s`:** `T-s` is connected and has a color class of size `ell*t>max(p,q)`, so it cannot fit in one wing.
* A copy avoiding `s` would lie in a wing, but `T` has a color class of size `ell*t+1>max(p,q)`.

**This graph is not a counterexample to the question.** It is below the required density and fails even `W_k` on an entire wing. Its only purpose here is to state and then repair an actual all-role obstruction, not another fixed-root obstruction.

### 7.2 One fresh boundary edge is enough

**Theorem 6 — adaptive repair.** Suppose `G` contains `H` as an induced subgraph. If some vertex of `C_1 union C_2` has a neighbor `w` outside `H`, then `G` contains `T` **covering `s`**.

There are two constructive cases. Assume the edge leaves wing 1.

**Edge `xw` with `x in A_1`: put the center at `s`.** Put `(ell+1)/2` hubs into `A_1`, including one at `x`, and the remaining hubs into `A_2`. For the first group, use all `p` vertices of `B_1` and use `w` as one leaf of the hub at `x`. These are exactly `p+1` leaf positions. The other group needs `((ell-1)/2)t<=p` leaves in `B_2`.

**Edge `xw` with `x in B_1`: put a hub at `s`.** Put the center at any `a_0 in A_1` and the other `ell-1` hubs in `B_1`, including one at `x`. Their leaves need exactly `q` positions: use `A_1-{a_0}` and `w`, assigning `w` to the hub at `x`. Put the `t` leaves of the hub at `s` in `A_2`.

Every image set is explicitly disjoint and every required edge is either a complete wing edge, an edge at `s`, or the single new edge `xw`. No property of an old target copy is used.

### 7.3 Full criticality forces the usable edge

For either wing, its incidence count *inside H* is

\[
 I_H(C_i)=q(p+1).
\]

It is strictly below `a|C_i|`, where `a=(k-1)/2`. In fact

\[
\begin{aligned}
4\bigl(a(p+q)-q(p+1)\bigr)
={}&(\ell^2-\ell+2)t^2\\
 &+(3\ell^2-6\ell+1)t-2(\ell-1)>0.                 \tag{6}
\end{aligned}
\]

Thus if `G` is critical and `H` is induced in it, (1) forces

\[
 e_G(C_i,V(G)-V(H))
 \ge a(p+q)+\eta-q(p+1)>0.                         \tag{7}
\]

An edge provided by (7) is **exactly** an edge usable in Theorem 6. Consequently:

> **Every critical host containing this induced marked two-wing trap has a target copy covering its marked high vertex.**

This is a completed density-to-reembedding argument for the entire displayed low-Delta family. There is no unresolved attachment assertion in the argument: both endpoint types of the forced boundary edge have explicit full embeddings.

### 7.4 A conditional version not requiring full average degree

Suppose `G` is connected, contains `H` induced, and `delta(G)>=t+1`. If `G` is a **proper** extension of `H`, then it covers `s` by `T`.

If a boundary edge leaves a wing, use Theorem 6. Otherwise all boundary edges of `H` leave `s`. Choose such an edge `sw`. Every other neighbor of `w` is outside `H` (a wing neighbor would be a wing boundary edge), so `w` has at least `t` fresh outside neighbors. Put `z` at `s`, one hub at `w` with its `t` leaves outside, and `(ell-1)/2` hubs in each old `A_i`, with their leaves in `B_i`.

Since `H` itself is `T`-free, this proves the precise conditional assertion

\[
 \bigl[G\text{ connected},\ \delta(G)\ge t+1,\ H\text{ induced in }G,
 \ T\subseteq G\bigr]
 \Longrightarrow s\text{ is covered by }T.          \tag{8}
\]

The minimum-degree condition matters for an extension attached only at `s`: just adding a pendant vertex to `s` need not repair the trap.

## 8. An actual critical family realizing the low-degree repair

The preceding repair is not vacuous in critical graphs. The following explicit family has a unique maximum `s`, the target already embeds avoiding `s`, and a covering copy is supplied by the repair.

Take odd `ell>=3`, set

\[
 t=\ell+1,\quad k=\ell(\ell+2),\quad r=(k-1)/2,
 \quad q=\ell^2-1,\quad h=(r+1)/2.
\]

The trap from Section 7 now has `p=r`. Orient its edges as follows, separately in each wing.

1. Choose `h` vertices of `A_i`. Orient their edges from `s` to them, and orient all their `r` wing edges from `A_i` to `B_i`.
2. For each remaining `A_i` vertex, orient its edge toward `s` and reverse exactly one of its `r` wing edges, so that this edge goes `B_i -> A_i`. Distribute these reversed edges cyclically over `B_i`.

Every `A_i` vertex now has outdegree `r`; the outdegree of `s` is `r+1`. Every `B_i` is reachable from `s`, as is every remaining `A_i`. Let `c_y` be the number of reversed edges leaving `y in B_i`; it is at most two.

For every `y in B_1 union B_2`, add `r-c_y` private ports and orient the corresponding edges `y -> port`. The number of ports is

\[
 N=2r^2-2q+r+1>2r.
\]

On the ports put the `r`th power of an `N`-cycle, oriented forward at cyclic distances `1,...,r`. Each port now has outdegree `r`, and every vertex is reachable from `s`.

### Full criticality, not just a minimum-degree check

For any proper vertex set `U`, this orientation gives

\[
 e_G(U)=r|U|+\mathbf1_{s\in U}-\operatorname{out}(U)\le r|U|.
\]

If `s in U`, reachability supplies at least one outgoing arc; otherwise the inequality is immediate. Summing outdegrees gives `e(G)=r|G|+1`. Hence the graph is fully critical.

Its parameters and degrees are

\[
 |G|=2r^2+3r+2,\quad e(G)=r|G|+1,
\]

\[
 d(s)=2q,\quad d(A)=r+1,\quad d(y)=q+r-c_y\ (y\in B),
 \quad d(\text{port})=2r+1=k.
\]

Since `q>r`, `s` is the unique maximum and `d(s)>=k`.

| ell | k | n | e | d(s) | Delta(T) |
|---:|---:|---:|---:|---:|---:|
| 3 | 15 | 121 | 848 | 16 | 5 |
| 5 | 35 | 631 | 10,728 | 48 | 7 |
| 7 | 63 | 2,017 | 62,528 | 96 | 9 |

All targets are outside the strict high-Delta regime. A `B`–port edge gives the full covering embedding of Section 7.2 with a **hub at `s`**. The center remains unavailable there: `N(s)` and the neighbors of all `A_i` vertices are unchanged from the trap, so its center-role capacity obstruction persists. No assertion that these are the *only* available roles is made.

Ordinary containment avoiding `s` is also explicit. Choose a target leaf `ell_0` with parent `u`, a private port `v`, and its `B`-parent `y`. The port graph has minimum degree `k-1`; greedily embed `T-ell_0` there with `u -> v`, and put `ell_0 -> y`. This copy avoids `s` and uses no unproved ES assertion.

**These are covered examples, not counterexamples.** They demonstrate how a real full-critical boundary repairs a low-degree all-role trap, while still allowing some named roles to be impossible.

### An even-parameter full-critical instance with Delta(T)=4

There is also a smaller-parameter realization of the *exact* trap at `ell=t=3`:

\[
 k=12,\quad \Delta(T)=4,\quad n=83,\quad e=457
   =\frac{11}{2}\,83+\frac12,\quad d(s)=12.
\]

Start with the two `K_(6,5)` wings and their marked vertex `s`. Add 60 ports, five private ordinary ports and one private exceptional port for each of the ten `B` vertices. On the ports `P_0,...,P_59`, put all cyclic-distance `1,...,5` edges and all antipodal edges `P_i P_(i+30)` except those for `i=0,...,4`. The exceptional ports are `P_0,...,P_4,P_30,...,P_34`; assign one to each `B` vertex. Partition the other 50 ports into its five-per-vertex ordinary lists. Join each `B` vertex to its six ports.

A doubled-edge orientation gives an exact half-integral criticality certificate. For `s`–`A` edges, exceptional `B`–port edges, and reservoir edges, orient one of the two copies in each direction. Orient both copies of each `A`–`B` edge toward `B`, and both copies of each ordinary `B`–port edge toward the port. The weighted outdegree is **12 at `s` and 11 everywhere else**, and every vertex is reachable from `s`. Consequently

\[
 2e_G(U)=11|U|+\mathbf1_{s\in U}-\operatorname{out}(U)
 \le11|U|\quad(U\text{ proper}),
\]

while `2e(G)=11n+1`. This proves full criticality. The underlying graph is simple; the doubled orientation is only its certificate.

A `B`–port edge supplies the covering copy from Section 7.2. An ordinary copy entirely in the reservoir has center `P_0`, hubs `P_1,P_2,P_3`, and their respective leaf triples

```
(P_56,P_57,P_58),  (P_59,P_4,P_7),  (P_5,P_6,P_8).
```

All listed edges have cyclic distance at most five. This `s` is high but **not** the unique maximum; uniqueness is not assumed in the question. Again, it is a covered low-Delta example, not a counterexample.

## 9. Verification and artifacts

Run

```
python3 Submission/HighVertexCoverageChecks.py
```

The saved output is `Submission/HighVertexCoverageChecks.log`. The checker constructs copies and checks injectivity, all tree edges, and every prescribed image. It does not infer a general theorem from a search.

The completed audit includes:

* **237,853 prescribed-high-vertex multipartite copies**, testing both the grouping and deficit/forest branches, including nonmaximum high vertices and every smaller-color nonleaf prescription in the tested range;
* constructive clique-join and bipartite leaf-deletion checks;
* **1,465 exceptional-spider block copies**, including the side where the center cannot be prescribed;
* **380 internal-role copies** in eight half-integral critical biclique examples, with all induced-subset count types checked;
* **28 exact two-wing parameter audits**, including all three forbidden role types in the isolated trap and the exact positive charge deficit (6);
* **116 full fresh-boundary-edge repairs** and **28 apex-only extension repairs**;
* **three root-reachable critical orientation certificates**, with the unique maximum checked and both a covering and an avoiding copy constructed, plus the doubled-quota certificate for the `k=12`, `Delta(T)=4` example;
* **206 independent integer maximum-closure/min-cut tests** for the 121- and 83-vertex critical examples: the unrestricted maximum surplus is one (scaled by two for the even parameter), and the maximum over subsets omitting any specified vertex is zero. Thus every proper induced subset of both graphs is independently certified sparse;
* **548 Hamiltonian endpoint-potential checks** and **883 marked-vertex path-coverage checks**, auditing Theorem 1 on the small atlas through six vertices.

There are **244,149 edge-by-edge verified full tree copies** in this audit. These finite checks support the explicit proofs; they are not a claim of exhaustive general coverage testing.

All existing `Submission/*.lean` files were checksum-compared with their pre-investigation versions and were unchanged. `Spec.lean` retains SHA-256

```
674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103
```

## 10. What is and is not concluded

The arbitrary-role formulation survives all the constructions discussed here. It is proved in the domains above, including nontrivial low-Delta cases and a conditional ordinary-containment extension theorem. The old refutations of prescribed roles do not refute it.

**For an arbitrary critical host and an arbitrary nonspider tree below the exact-apex threshold, neither the universal coverage statement nor its conditional-on-containment version has been established here.** No unrestricted ES proof, no full-critical uncovered high vertex, and no implication from mere separator sizes or lower-parameter deletion density is asserted.
