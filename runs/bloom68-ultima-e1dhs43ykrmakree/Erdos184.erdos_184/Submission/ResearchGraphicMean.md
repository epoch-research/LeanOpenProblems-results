# Graphic full-cycle-space means: an exact recursion and a localization theorem

## Status — no universal constant has been proved or refuted

For a finite even simple graph, let `c` be the minimum **vertex-simple-cycle partition** number, let `cf` be its exact fractional version, and put

\[
 a(G)=\frac1{|Z(G)|}\sum_{H\in Z(G)}c_f(H),
\]

where **every** even edge subset, including the empty set, is sampled uniformly.

**This note does not prove any finite universal `K` in `c(G) <= K a(G)`. It also does not give a graphic counterexample to `K=2`.** Neither placeholder in `Spec.lean` is filled. In particular the results below are not an Erdős–Gallai proof.

The new results are structural, rather than a search table:

1. **The retained-anchor affine reduction is realizable for arbitrary graphic factors.** An explicit chain-and-closing-edge construction preserves simplicity. Consequently, for every `K>=2`, the universal graphic assertion is equivalent to
   \[
   c(G)-1\le K(a(G)-1/2)
   \quad\text{for all nonempty even simple }G.
   \]
   This specializes and independently checks the reduction in `ResearchUniformFractional.md`; it does not supply the inequality.

2. **There is an exact distributional recursion across two-terminal separations.** The state is the law of the whole fractional path-traffic profile, in each of the two boundary-parity fibers. Series and parallel composition have explicit operators on these laws. They apply to arbitrary two-terminal factors, not only series-parallel leaves. They do not make any simple-path or simple-cycle rounding assumption.

3. **The two conditional means cannot replace that profile law.** Two explicitly specified even graphic networks have the same two conditional means, the same terminal degrees, and the same numbers of vertices and edges, but attaching the same two terminal paths gives different full-code means:
   \[
   2723/1024\ne2669/1024.
   \]
   Both outputs have `c=cf=4` and satisfy `K=2`. A separate all-size family has an unbounded difference between its marked-zero and marked-one conditional means while satisfying `c=2a` exactly.

4. **Vertex-cap localization gives a general lower bound on the actual full-code mean.** For a connected even graph partitioned into connected vertex sets `S_i` with connected complements, cap each complement to a vertex to obtain `G_i`, and let `Q` be the multigraph quotient of the partition. Then
   \[
   \boxed{
   a(G)\ \ge\ \sum_i\left(a(G_i)-\frac{|\delta_G(S_i)|}{4}\right)
                 +1-2^{-\beta(Q)}.}
   \tag{0.1}
   \]
   The cap marginals and quotient marginal are genuinely uniform cycle-space marginals. No hereditary monotonicity is used.

   This proves, by a short analytic seven-star certificate, that **every old Petersen ring `R_t`, `t>=2`, satisfies `c(R_t)<=2a(R_t)`**, despite its unbounded `c/cf` ratio. An additional exact finite degree certificate strengthens the whole-family conclusion to
   \[
   \boxed{c(R_t)\le\tfrac{13}{8}a(R_t)\qquad(t\ge2).}
   \tag{0.2}
   \]
   These are bounds for the entire family, not extrapolations from small rings. No exact value of `a(R_t)` is asserted.

5. **Even vertex splitting has two distinct hazards.** On one explicit family, a single codimension-one split increases `a` by an unbounded amount. Another split decreases `a` without changing `c`. Also, the mean on the split graph is not in general the conditional mean of the old cost function on its cycle-space hyperplane. These facts rule out particular monotonicity and bounded rank-payment shortcuts, not a suitably chosen adaptive filtration.

The only new repository files are this note and **`ResearchGraphicMeanCheck.py`**. The checker uses exact rational arithmetic and the Python standard library. `Spec.lean`, the parent `Check.py`, and all existing notes/checkers were protected by a pre-work hash manifest and preserved. There was no new corpus lookup or source audit. Existing deterministic path-profile and splice arguments are explicitly distinguished from the new full-code averaging statements below.

---

## 1. Conventions and elementary bounds

For an even edge set `H`, the fractional program is

\[
 c_f(H)=\min\left\{\sum_C x_C:
      x_C\ge0,\quad \sum_{C\ni e}x_C=1\ (e\in H),\quad
      C\subseteq H\text{ a simple cycle}\right\}.
 \tag{1.1}
\]

Its dual is

\[
 \max\left\{\sum_{e\in H}y_e:
      \sum_{e\in C}y_e\le1\text{ for every simple }C\subseteq H\right\},
 \qquad y_e\in\mathbb R.
 \tag{1.2}
\]

The prices are unrestricted in sign. Empty costs are zero. Auxiliary multigraphs are loopless; a pair of parallel edges is a circuit. Replacing each edge of such a multigraph by a private two-edge path gives a **simple graph** and bijections on circuits, even subsets, and both kinds of partitions. It therefore preserves `c`, every corresponding `cf(H)`, and `a`. No simple-graph rank bound is applied directly to a multigraph core.

For any even graph and vertex `v`, every fractional partition satisfies

\[
 \sum_{C\ni v}x_C=d_H(v)/2.
 \tag{1.3}
\]

Every edge of an even graph is a nonzero coordinate functional on its cycle space, since it occurs in the all-ones word. Its uniform marginal is consequently `1/2`. Hence

\[
 a(G)\ge\tfrac14\Delta(G).
 \tag{1.4}
\]

Also, combining fractional partitions of complementary even subsets gives

\[
 c_f(G)\le c_f(H)+c_f(G\setminus H),\qquad c_f(G)\le2a(G).
 \tag{1.5}
\]

This is not an integral rounding theorem. In particular, the Petersen rings show why replacing `c_f(G)` by `c(G)` in the first inequality is unjustified.

A useful rooted quantity is

\[
 \rho(G,v)=a(G)-d_G(v)/4.
 \tag{1.6}
\]

By (1.3), it is exactly the expected minimum fractional mass of cycles **avoiding** `v`, not a heuristic degree correction. It is nonnegative. Moreover,

\[
 \rho(G,v)=0
 \quad\Longleftrightarrow\quad
 \text{every simple cycle of }G\text{ contains }v.
 \tag{1.7}
\]

For the forward implication, a cycle avoiding `v`, sampled as the entire word `H`, has positive residual cost one and positive probability. The reverse implication follows directly from (1.3). This zero case has `c(G)=d_G(v)/2=2a(G)`.

For auxiliary networks whose whole edge set is not even, the notation for a mean, when used, still averages `cf` only over their even subsets. The target universal assertion remains restricted to even simple graphs.

---

## 2. The affine reduction really is graphic

Take vertex-disjoint even simple graphs `G_i`, each with a marked edge `e_i=u_iv_i`, `1<=i<=t`. Delete all marked edges. Identify `v_i` with `u_(i+1)` for `i<t`, and add one new edge

\[
 p=u_1v_t.
\]

This is a chain of marked-edge-deleted factors, closed by **one retained edge**. It is even: each intermediate identification combines two odd terminal degrees, and the closing edge corrects the two end degrees. It is simple: the factor interiors are disjoint and the new closing edge has no old mate. The case `t=1` just restores the original marked edge.

A simple cycle avoiding `p` is local to one factor. A simple cycle containing `p` consists of `p` and one simple `u_i`–`v_i` path in each factor. Capping these paths with `e_i` gives one marked simple cycle in every factor. These are all the circuits; in particular no closed trail is being substituted for a simple cycle.

Every even subset of the new graph corresponds uniquely to factor words `H_i` with a common marked bit `g`. For every such word,

\[
 \begin{aligned}
 c(H)&=\sum_i c(H_i)-(t-1)g,\\
 c_f(H)&=\sum_i c_f(H_i)-(t-1)g.
 \end{aligned}
 \tag{2.1}
\]

For `g=1`, an integral partition has exactly one marked cycle; glue or unglue it. In a fractional partition, the marked-cycle mass is exactly one. Couple the factor marked-cycle distributions of mass one by their product and retain the local cycles. Conversely, projection gives exact-load factor partitions. A signed dual certificate has the old prices off the marks and

\[
 y_p=\sum_i y^{(i)}_{e_i}-(t-1).
 \tag{2.2}
\]

A crossing cycle has price at most `t-(t-1)=1`, and all local inequalities are retained.

The common bit `g` is fair. Conditional on it, all factor words are independent uniform words in their specified fibers; unconditionally each factor marginal is uniform on its full cycle space. Therefore

\[
 \boxed{
 c(G)=1+\sum_i(c(G_i)-1),\qquad
 a(G)=\tfrac12+\sum_i(a(G_i)-\tfrac12).}
 \tag{2.3}
\]

In particular, `t` copies of one factor give

\[
 c_t=t(c-1)+1,\qquad a_t=t(a-1/2)+1/2.
 \tag{2.4}
\]

If the unshifted universal inequality holds, divide it for (2.4) by `t` and let `t` grow. This yields the shifted inequality. Conversely, for `K>=2`, the shifted inequality gives `c<=Ka+1-K/2<=Ka`. A single simple cycle already requires `K>=2`.

Thus the unshifted and shifted universal formulations are equivalent **within the class of even simple graphic graphs**, not just when an unspecified matroid gluing happens to be graphic. Articulation sums add `c` and `a`; series expansions preserve them. These are decomposition reductions, not evidence that the irreducible pieces satisfy the target.

---

## 3. Exact full-code recursion at a two-terminal interface

### 3.1 The correct state is a law of profiles

Let `N` be a connected two-terminal network with distinct terminals `s,t`. Define the two affine fibers

\[
 Z_b(N)=\{H\subseteq E(N):
       d_H(w)\equiv0\ (w\ne s,t),\quad
       d_H(s)\equiv d_H(t)\equiv b\pmod2\}.
 \tag{3.1}
\]

Both fibers have size `2^beta(N)`, where `beta(N)=|E(N)|-|V(N)|+1`: the zero fiber is the cycle space and the one fiber is its translate by any terminal path.

For a particular trace `H`, let

\[
 F_H(p)=\min\left\{\sum_C x_C:
  \begin{array}{l}
   x_C,z_P\ge0,\quad \sum_Pz_P=p,\\
   \sum_{C\ni e}x_C+\sum_{P\ni e}z_P=1\ (e\in H)
  \end{array}\right\},
 \tag{3.2}
\]

where `C` ranges over contained simple cycles and `P` over contained **simple** terminal paths. Set it to `+infinity` if infeasible. Paths do not contribute to the objective in this definition.

The function is convex and piecewise linear on its feasible interval. `F_H(0)=cf(H)` when `b=0`; `F_H(1)` is feasible when `b=1`, because deleting any contained terminal path leaves an even graph. In the **fractional** profile, do not impose `p=b (mod 2)`: for example three parallel terminal paths can be covered fractionally by pair-cycles with path mass zero. Parity is a necessary condition for an **integral** path-count profile, a different object.

Write `mu_N^b` for the probability law of the entire function `F_H`, for uniform `H in Z_b(N)`. This retains correlations among the costs at different traffic values and among their feasible domains.

### 3.2 Series operator

Suppose `N=N_1 circ N_2` is a series composition with disjoint interiors and one identified terminal. For every trace,

\[
 F_H(p)=F_{H_1}(p)+F_{H_2}(p).
 \tag{3.3}
\]

Every simple global path uses one terminal path in each factor; every cycle is local. Equal fractional path masses are coupled by product coefficients, divided by the common mass when it is positive. The concatenated paths are simple because only the identified vertex is shared.

Conditioning the output boundary parity to be `b` forces both child parities to be `b`. The two child fibers are independent and uniform. Thus

\[
 \mu_N^b=\operatorname{Law}(F_1+F_2),
 \qquad F_i\text{ independent with law }\mu_{N_i}^b.
 \tag{3.4}
\]

### 3.3 Parallel operator

Suppose `N=N_1 parallel N_2`, again with disjoint interiors. Define

\[
 \mathcal P(f_1,f_2)(p)=
 \min\left\{f_1(p_1)+f_2(p_2)+h:
       \begin{array}{l}
       p_1,p_2,h\ge0,\quad h\le\min(p_1,p_2),\\
       p=p_1+p_2-2h
       \end{array}\right\}.
 \tag{3.5}
\]

Then `F_H=mathcal P(F_(H_1),F_(H_2))` exactly. A crossing simple cycle is one path from each child. A global simple terminal path lies entirely in one child. Conversely, take submeasures of the child path distributions of mass `h` and couple them; all resulting crossing cycles are genuinely simple. Retain the unpaired paths and all local cycles. Every individual edge load is preserved.

In the uniform fiber of output parity `b`, choose a fair bit `B`. Independently conditional on `B`, sample

\[
 F_1\sim\mu_{N_1}^{B},\qquad F_2\sim\mu_{N_2}^{B\mathbin\oplus b}.
\]

The output law is

\[
 \boxed{\mu_N^b=\operatorname{Law}(\mathcal P(F_1,F_2)).}
 \tag{3.6}
\]

Indeed, each of the two child-parity choices has the same number `2^(beta(N_1)+beta(N_2))` of trace pairs. This proves uniformity, not merely a convenient sampling scheme.

For an even root network,

\[
 a(N)=\mathbb E_{F\sim\mu_N^0}F(0).
 \tag{3.7}
\]

The deterministic operators are consistent with the path-profile argument in `ResearchRounding.md`. The new content here is their **exact two-fiber probability law** for the full cycle space, together with the failure of scalar closure below. The formulas hold with arbitrary factors; no integrality statement for an arbitrary factor is inferred from the series-parallel case.

### 3.4 A marked-edge deletion identity

If `N` is closed by one new retained edge `e=st`, set

\[
 M_b(N)=\mathbb E_{H\in Z_b(N)}F_H(b).
\]

Conditioning on `e=0` gives cost `F_H(0)`. Conditioning on `e=1` gives cost `1+F_H(1)`, since the marked-cycle mass is one. Hence

\[
 \boxed{a(N+e)=\tfrac12\bigl(M_0(N)+M_1(N)+1\bigr).}
 \tag{3.8}
\]

This is an exact deletion/fiber recursion, but it does not make `(M_0,M_1)` a sufficient state for other attachments.

---

## 4. An analytic obstruction to scalar conditional-mean recursion

### 4.1 A useful exactly solvable family

Let `B(m_1,...,m_L)`, `L>=3`, be a cyclic chain of bundles: between successive junctions of a cycle put `m_i` parallel edges. For actual simple graphs replace each of these edges by a private two-edge path.

Every even subset has selected counts `q_i` of the same parity. Its circuits are local pairs of parallel edges or global cycles taking one edge from every bundle. Put `r=min_i q_i`. Taking `r` edge-disjoint global cycles and pairing the remaining edges locally proves

\[
 \boxed{
 c(H)=c_f(H)=\frac{\sum_iq_i-(L-2)r}{2}.}
 \tag{4.1}
\]

Here is an all-circuit signed dual, independently certifying the fractional equality. Choose a minimizing bundle `j`, give each selected edge off `j` price `1/2`, and each selected edge in `j` price `(3-L)/2`. Local pair prices are at most one, and every global cycle has price exactly one. The objective is (4.1). Negative prices occur when `L>=4`.

In a uniform **full-code** word, a common parity bit is fair; conditional on it, the selected subsets in the bundles are independent uniform subsets of that parity. Thus

\[
 \boxed{
 a(B)=\frac14\sum_i m_i-\frac{L-2}{2}\,\mathbb E\min_i q_i.}
 \tag{4.2}
\]

If the full multiplicities have the same parity, the full graph is even and (4.1) applies to it. Since `E min q_i <= min_i E q_i = min_i m_i/2`, this entire family satisfies `c(B)<=2a(B)`. These formulas are not counterexamples to the target.

For an open series chain of bundles, its actual fractional profile on a trace is

\[
 F_H(p)=\frac12\sum_i q_i-\frac L2p
 \tag{4.3}
\]

on the feasible interval

\[
 \max_i\mathbf1_{q_i=1}\ \le p\le\min_iq_i.
\]

For `q_i>=2`, uniform residual loads on the local pair-cycles realize every `0<=p<=q_i`. A one-edge bundle forces `p=1`, and an empty bundle forces `p=0`. The common terminal path mass can be coupled across the series chain. This proves the profile and its domain, including fractional traffic values of the wrong integer parity.

If every full bundle has size at least two, each edge is fair in either parity fiber. Therefore the open chain has

\[
 M_0=\tfrac14\sum_i m_i,\qquad
 M_1=\tfrac14\sum_i m_i-L/2.
 \tag{4.4}
\]

### 4.2 Same means, terminal degrees, size and nullity; different attached means

Take the two open four-link chains

\[
 N_A=(2,2,6,2),\qquad N_B=(2,4,4,2).
\]

Both have terminal degrees two, five core vertices, twelve core edges, and nullity eight. After the private-path replacement they are simple even networks with seventeen vertices and twenty-four edges. Both have

\[
 c(N_A)=c(N_B)=6,\qquad a(N_A)=a(N_B)=3,
 \qquad (M_0,M_1)=(3,1).
\]

Attach the same bundle of two terminal paths in parallel. The resulting even simple graphs correspond to

\[
 G_A=B(2,2,6,2,2),\qquad G_B=B(2,4,4,2,2).
\]

Both have nineteen vertices, twenty-eight edges, nullity ten, and `c=cf=4`.

In the common odd fiber their minimum selected bundle size is one. In the even fiber it is two exactly when every bundle is nonempty. The latter probabilities are respectively

\[
 (1/2)^4(31/32)=31/512,
 \qquad (1/2)^3(7/8)^2=49/512.
\]

Consequently

\[
 \mathbb E\min q_i=1/2+31/512
 \quad\text{or}\quad1/2+49/512,
\]

and (4.2) gives

\[
 \boxed{a(G_A)=2723/1024,\qquad a(G_B)=2669/1024.}
 \tag{4.5}
\]

Their difference is `27/512`. Thus a rule using only the two conditional means, even together with terminal degrees, size and nullity, cannot compute the mean after parallel attachment. The random feasible traffic and its correlation with the costs matter. This does **not** rule out inequalities or richer finite states; it rules out exact closure by these specified scalars.

The smaller unpadded example `(2,6)` versus `(4,4)`, closed by two paths, gives `(M_0,M_1)=(2,1)` and means `545/256` versus `527/256`, also with full cost four.

### 4.3 An unbounded marked-zero/marked-one imbalance, with `c=2a`

Take a chain of `ell>=2` bundles of size three and close it by one marked edge `e`. Its cycle-space dimension is `2ell+1`. Let `A_b=E[cf(H) | e=b]`, now including the marked edge in the state-one cost.

* If `e=0`, each link has zero or two selected edges, with probabilities `1/4,3/4`. All cycles are local, so `A_0=3ell/4`.
* If `e=1`, each link has one or three selected edges, with probabilities `3/4,1/4`. The marked-cycle mass is exactly one; the extra local pair at a three-edge link costs one. Thus `A_1=1+ell/4`.

Therefore

\[
 \boxed{A_0-A_1=\ell/2-1,\qquad
        a=(\ell+1)/2,\qquad c=c_f=\ell+1.}
 \tag{4.6}
\]

This rules out a bounded absolute difference of the two fibers, or a uniform inequality `A_0<=A_1+O(1)`. It does not refute the opposite one-sided inequality, and is not a counterexample to any `K>=2`.

---

## 5. Vertex-cap localization of the uniform mean

### Theorem 5.1

Let `G` be a connected even graph. Partition its vertices into `t>=2` nonempty sets `S_i` such that each induced `G[S_i]` and each induced `G[V\S_i]` is connected.

Let `G_i` have the vertices of `S_i` and one cap vertex `v_i`. Keep all internal edges and replace each boundary edge by an edge from its endpoint in `S_i` to `v_i`. It is an even graphic multigraph; parallel cap edges may be subdivided if desired. Let `Q` be the loopless quotient obtained by contracting every `S_i`, retaining all interpart edges. Then

\[
 \boxed{
 a(G)\ge\sum_i\rho(G_i,v_i)+1-2^{-\beta(Q)}
      =\sum_i a(G_i)-\frac{|E(Q)|}{2}+1-2^{-\beta(Q)}.}
 \tag{5.1}
\]

Here `beta(Q)=|E(Q)|-t+1` is a cycle-space dimension, not graphic rank.

### Proof: uniformity first

For a word `H in Z(G)`, take its internal and boundary trace on `S_i` and cap the latter. The resulting `H_i` is even. The map

\[
 Z(G)\longrightarrow Z(G_i)
\]

is a surjective linear map. To lift any cap word, its prescribed boundary edges give an even-cardinality set of odd-degree demands in the connected complement. A spanning-tree `T`-join in that complement supplies exactly these demands. Thus every cap word lifts, and all fibers have the same cardinality. **Each `H_i` has the full uniform distribution on `Z(G_i)`.** The cap words need not be mutually independent, and no independence is claimed.

Likewise, the restriction to interpart edges is a surjection

\[
 Z(G)\longrightarrow Z(Q).
\]

For a prescribed quotient word, its boundary demands have even cardinality in each part and can be filled inside the connected induced part. Hence the quotient word is uniform, and

\[
 \Pr(H\cap E(Q)\ne\varnothing)=1-2^{-\beta(Q)}.
 \tag{5.2}
\]

### Proof: a pointwise fractional inequality

Take any exact fractional simple-cycle partition `x` of `H`. Let `L_i` be the mass of its cycles lying wholly in `S_i`, and let `X` be the mass of all crossing cycles.

A crossing simple cycle can enter `S_i` more than once. Break its trace into its maximal paths in that part and cap **each path separately**. Each is a genuine cap cycle; a zero-internal-edge path becomes a parallel pair at the cap, also a circuit. No whole projected closed trail is counted as one simple cycle.

This gives an exact fractional partition of `H_i` of cost

\[
 L_i+\tfrac12|\delta_H(S_i)|.
\]

The second term is fixed by the boundary edge-load equations, regardless of how often a crossing cycle enters the part. Consequently

\[
 L_i\ge c_f(H_i)-\tfrac12|\delta_H(S_i)|.
 \tag{5.3}
\]

If any interpart edge is present, its exact load one forces `X>=1`. Summing (5.3), using `sum L_i+X=sum_C x_C`, and minimizing gives the pointwise inequality

\[
 \boxed{
 c_f(H)\ge\sum_i\left(c_f(H_i)-\tfrac12|\delta_H(S_i)|\right)
             +\mathbf1_{H\cap E(Q)\ne\varnothing}.}
 \tag{5.4}
\]

Average using the proved uniform marginals. Each boundary edge is fair, so its expected contribution in (5.3) is `1/4`. Each interpart edge appears at two caps. Equation (5.1) follows. ∎

### Scope of the theorem

For a two-edge cut, `beta(Q)=1`, the cap degree is two, and this recovers the exact splice formula `a=a_1+a_2-1/2`. At larger boundaries it is only a **lower bound**.

It gives no corresponding upper bound on the integral number of crossing simple cycles. In particular, contracting a region can turn a simple cycle into a closed trail that revisits a quotient vertex. It would be invalid to replace the last term of (5.4) by `cf(H_Q)` just by calling that trail a simple quotient cycle.

---

## 6. All Petersen rings satisfy the graphic mean target

This is a full-family application of Theorem 5.1, using no large-ring enumeration and no integrality claim about the old fractional Hamilton cover.

### 6.1 The fixed base graph and a seven-star probability certificate

Let `P` be the usual Petersen graph. Its lexicographically ordered edges label the vertices of `L=L(P)`:

```
0:01  1:04  2:05  3:12  4:16  5:23  6:27  7:34
8:38  9:49  10:57  11:58  12:68  13:69  14:79.
```

The graph `L` has fifteen vertices, thirty edges, degree four everywhere, and cycle-space dimension sixteen. Put

\[
 S=\{0,1,2,3,5,12,14\}.
\]

Its induced edges are

\[
 01,\ 02,\ 12,\ 03,\ 35.
\]

Thus the induced graph is a triangle with a two-edge tail attached at one triangle vertex, together with two isolated vertices. Its complement induces the path

\[
 4-13-9-7-8-11-10-6.
\]

Every vertex of `S` has a neighbor on that path. Therefore `L-A` is connected for every `A subseteq S`.

For a uniform even subset `H`, let `E_v` be the event `d_H(v)=4`. If `A subseteq S`, all incident edges at `A` must be selected for `intersection_(v in A) E_v`. For any edge set `D` of a connected graph, the rank of the coordinate projection of its cycle space onto `D` is

\[
 |D|+1-\kappa(L\setminus D).
 \tag{6.1}
\]

This is simply `beta(L)-beta(L\D)`. For the edges incident with `A`, deleting them isolates `A` and leaves a connected complement. Writing `e(A)=|E(L[A])|`, the projection rank is `3|A|-e(A)`. The all-ones prescription is feasible because `L` is even. Hence

\[
 \Pr\Bigl(\bigcap_{v\in A}E_v\Bigr)=2^{-3|A|+e(A)}.
 \tag{6.2}
\]

Inclusion–exclusion is now a seven-vertex polynomial calculation:

\[
 \Pr(\text{no }E_v,\ v\in S)
   =\sum_{A\subseteq S}(-1/8)^{|A|}2^{e(A)}
   =\frac{285}{512}\left(\frac78\right)^2
   =\frac{13965}{32768}.
 \tag{6.3}
\]

For clarity, the factor `285/512` has a short direct calculation. Condition on whether the triangle vertex attached to the tail belongs to `A`. When absent, the remaining four vertices form two disjoint induced edges, giving `(25/32)^2`. When present, its contribution is

\[
 -\frac18\cdot\frac58\cdot\frac{11}{16}.
\]

Their sum is `285/512`. The two isolated vertices give the factors `7/8`.

If every star in `S` is empty, the even subset lies in the complementary tree and must be empty. This has probability `2^-16`. Therefore

\[
 \mathbb E\left[\frac12\max_{v\in S}d_H(v)\right]
  =2-\frac{13965}{32768}-2^{-16}
  =\frac{103141}{65536}>\frac{25}{16}.
 \tag{6.4}
\]

For every word separately, price all edges at a maximizing vertex by `1/2` and all other edges by zero. Every contained simple cycle has price zero or one. Thus (6.4) is a legitimate mean of feasible dual values, and

\[
 \boxed{a(L)>25/16,\qquad \rho(L,0)>9/16.}
 \tag{6.5}
\]

This proof is analytic: the small induced graph and complementary path above suffice. It does not use the mean integral partition count, the hereditary maximum `p`, or an assumed fractional/integral equality on the restrictions.

### 6.2 Construction and a directly checked integral upper bound

Let `H=L-0`. Its four ports are `1,2` on the left and `3,4` on the right. For `t>=2`, take disjoint copies `H_i`, cyclically indexed, and add

\[
 (i,3)(i+1,1),\qquad (i,4)(i+1,2).
 \tag{6.6}
\]

This is the old connected simple 4-regular ring `R_t`, with `14t` vertices and `28t` edges. The only integral bound needed here is `c(R_t)<=t+2`, which can be checked directly, independently of the prior optimality proof.

In `L`, the following three simple cycles partition all thirty edges:

```
A = (0,1,2,10,14,9,13,4,12,11,8,7,5,6,3)
B = (0,2,11,10,6,14,13,12,8,5,3,4)
T = (1,7,9).
```

Delete `0` from `A` and `B`. They become paths from `1` to `3` and from `2` to `4`, respectively. Concatenating the first path through every block using the first connectors gives a simple cycle of length `14t`; doing the same with the second gives a simple cycle of length `11t`. Retain `T` in every block. These `t+2` cycles partition all edges. Each large cycle visits each block once along a simple path, so the construction has no hidden repeated-vertex issue.

### 6.3 The uniform mean bound for every `t`

Use the block vertex sets as the partition in Theorem 5.1. Each block and its complement are connected. Each capped graph is exactly `L`; its cap has degree four. The quotient is the doubled cycle on the `t` blocks, with the `t=2` case interpreted as four parallel edges. Its cycle-space dimension is `t+1`.

Consequently

\[
 \begin{aligned}
 a(R_t)&\ge t(a(L)-1)+1-2^{-(t+1)}\\
       &>\frac{9t}{16}+1-2^{-(t+1)}\\
       &\ge\frac{t+2}{2}.
 \end{aligned}
 \tag{6.7}
\]

The last step is `t/16>=2^(-t-1)`: equality holds at `t=2`, and the left side increases while the right side decreases. Combining with the explicit partition proves

\[
 \boxed{c(R_t)<2a(R_t)\qquad\text{for all }t\ge2.}
 \tag{6.8}
\]

The older exact values `c(R_t)=t+2`, `cf(R_t)=2` are consistent with this result; their exact integral lower bound is not needed for (6.8). The checker separately rechecks the four-Hamilton-cycle half-cover and its length dual, so the whole fractional value two is independently certified as well.

### 6.4 Optional exact finite strengthening, not an exact value of `a(L)`

Enumerating the full sixteen-dimensional cycle space gives these **maximum-degree**, not partition-cost, counts:

\[
 \#\{\Delta(H)=0\}=1,\quad
 \#\{\Delta(H)=2\}=13347,\quad
 \#\{\Delta(H)=4\}=52188.
\]

The checker reconstructs the incidence kernel, enumerates all `65,536` words, and checks the degree duals. It also independently identifies the simple cycles by DFS and by connected 2-regular supports. This certifies

\[
 a(L)\ge\mathbb E\Delta(H)/2=117723/65536,
 \quad \rho(L,0)\ge52187/65536.
\]

Thus, for the entire ring family,

\[
 \boxed{a(R_t)\ge\frac{52187}{65536}\,t+1-2^{-(t+1)}.}
 \tag{6.9}
\]

Multiplying the right side by `13/8` and subtracting `t+2` gives a positive quantity at `t=2`, namely `2591/262144`; its linear coefficient is positive and its subtracted exponential term decreases. This proves (0.2) for every `t>=2`.

Neither `117723/65536` nor (6.9) is asserted to be the exact fractional mean. There is no enumeration of a large ring's cycle space, no inference from a maximum to a mean, and no extrapolation from a finite list of ring sizes.

---

## 7. What a graphic vertex-split filtration must account for

Split a vertex into two vertices, each receiving an even number of its incident edges. When the split graph remains connected and the new parity equation is nonzero, its cycle space is a codimension-one subspace of the old cycle space. If `D` is the moved incident set, the new equation is `|H intersect D|=0 (mod 2)`.

Crucially, **the circuit set changes too**. A support-minimal word in the subspace can be a union of old circuits. Therefore the split graph's `cf` on a word need not be the old graph's `cf` on that same word.

Let `D_n=B(2,...,2)` have `n>=4` junctions, using the simple private-path realization if desired. Its full minimum is two. Formula (4.2) gives

\[
 a(D_n)=\frac{n+2}{4}-\frac{n-2}{2^{n+1}}.
 \tag{7.1}
\]

Indeed, in the odd common-parity fiber every word is one global cycle. In the even fiber each bundle is empty or doubled; a proper word costs its number of doubled bundles, whereas the full word costs two rather than `n`.

### 7.1 One even split can increase the mean without a bounded rank payment

At a junction, move both parallel edges leading to one neighbor to the new vertex. The graph becomes a doubled path with `n` links. Its code is exactly the old even-common-parity hyperplane, but now every selected doubled link is its own circuit. Thus

\[
 c(D'_n)=n,\qquad a(D'_n)=n/2,
\]

and

\[
 \boxed{a(D'_n)-a(D_n)
        =\frac{n-2}{4}+\frac{n-2}{2^{n+1}}.}
 \tag{7.2}
\]

The graphic rank increases by one and the cycle-space dimension decreases by one, but the change in `a` is unbounded. A parent rank upper bound on `a` is not a bounded-difference theorem.

The old conditional mean on this same hyperplane is instead

\[
 \mathbb E[c_f^{D_n}(H)\mid H\in Z(D'_n)]
       =n/2-(n-2)/2^n,
 \tag{7.3}
\]

not `a(D'_n)=n/2`. The full word alone already has old cost two and new cost `n`. This explicitly audits the distinction between a code restriction and its induced circuit structure.

### 7.2 Another even split decreases the mean while preserving the full minimum

Move one edge toward each neighbor to the new vertex. After series suppression, the graph is `D_(n-1)`. Its full minimum remains two, but

\[
 \boxed{a(D_n)-a(D_{n-1})
        =\frac14+\frac{n-4}{2^{n+1}}>0.}
 \tag{7.4}
\]

Thus arbitrary even splitting is not mean-monotone in either direction. These examples do not show that every available split is bad, and do not refute a filtration which proves a suitable choice theorem while controlling the change of simple circuits and of `c`.

---

## 8. Verification and exact scope

Run

```
PYTHONDONTWRITEBYTECODE=1 python3 Submission/ResearchGraphicMeanCheck.py
```

The checker uses only the Python standard library and `fractions.Fraction`. Its main audits are:

* independent incidence-kernel cycle-space generation and vertex-simple DFS cycles;
* the cyclic-bundle primal partitions and **signed** duals on every word in the displayed scalar-state examples;
* the exact two-fiber profile averages and both distinct attached means, including the equal-terminal-degree example;
* all-word checks of (4.6) for several lengths, with the all-length proof supplied above;
* the two vertex-split hyperplanes, their different circuit costs, and simple subdivisions;
* nontrivial pointwise localization inequalities, constant-size cap fibers, and quotient fibers on doubled-cycle partitions;
* a genuinely simple graphic retained-anchor gluing, checking all `256` words with primal partitions, signed duals, and uniform factor marginals;
* all `128` subset ranks in the analytic seven-star certificate, and an independent check from the full `65,536`-word Petersen line-graph code;
* the optional maximum-degree lower certificate — explicitly not an exact computation of `a(L(P))`;
* ring cap and quotient projection ranks, actual simple-cycle partitions, and actual fractional Hamilton half-covers at `t=2,3,4,5,8,16`;
* the algebraic monotonic estimates that make the ring bounds valid for **all** `t>=2`, without enumerating those rings' full codes;
* the prescribed specification hash and unchanged hashes of existing files during execution.

The general profile recursion and localization theorem have the proofs given above. Finite checks are audits of their explicit certificates, not substitutes for their general proofs. The pre-work hash manifest was also checked externally after the work; all pre-existing files matched.

---

## 9. The remaining universal burden

The new results isolate, but do not solve, the missing problem.

* **The law-valued recursion is exact, but no universal rounding/mean inequality has been proved for its arbitrary graphic atoms.** Keeping only the two conditional means loses information even on the explicit integrally solvable networks in Section 4. Keeping a full profile law avoids that loss, but is not itself a bound on `c`.
* **Localization lower-bounds `a`; it does not upper-bound the number of crossing simple cycles.** Its cap residuals are nonnegative and genuinely averaged, but the leftover indicator pays only for one crossing cycle. For a partition into singleton vertices, every cap residual is zero: the whole difficulty can lie in the crossing graph. There is no justified assembly theorem making that integral cost constant. Projected Eulerian trails cannot supply it.
* **A vertex-split induction needs a proved choice rule and actual cost comparison.** The old conditional cost on a hyperplane is not automatically the new graph's fractional cost, and the change can have either sign or be unbounded for a rank-one operation. The examples do not exclude an adaptive rule; none is established here.
* No critical-graph fixed-count implication, `c<=p` assertion, hereditary-mean monotonicity, max/mean comparison, non-graphic sampling transfer, or random-orientation conformality claim is used.

Accordingly, **both the universal graphic `K=2` question and the existence of any finite universal graphic `K` remain unresolved here**. The exact recursions, the general localization inequality, and the full-family Petersen-ring bound are the concrete progress; they must not be presented as a solution of the specification.
