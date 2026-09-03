# W_k global continuation: a valid one-defect start and a linear-size deletion-deck barrier

## Status — the unrestricted implication is still unproved

**I did not obtain a complete proof or a counterexample to**

\[
 W_k(G)\quad\Longrightarrow\quad
 \text{every }k\text{-edge tree embeds in }G.
\]

The results below are proved reductions, a genuinely global obstruction to a class of reembedding strategies, an explicit global repair of that obstruction, and a precise account of the remaining extraction problem. None of the missing extraction statements is being used as a theorem.

The principal new results are:

1. **A least-parameter counterexample would admit a one-defect punctured-tree forest at every high vertex.** This initialization uses only smaller-parameter W theorems, not a same-parameter ES hypothesis, not a prescribed-root induction hypothesis, and not a forest consequence of W that has not been proved.
2. **Allowing the missing tree vertex to vary does not make bounded-support forest reembedding sufficient.** There are fully critical hosts, satisfying the literal `Spec.lean` density bound, and subcubic targets for which a one-defect state in the *exact fixed-high-vertex forest deck* cannot reach any defect-zero state by any sequence of moves changing fewer than `k/5` tree-label values at a time. All host images and all missing-vertex roles may vary. The obstruction even survives allowing the distinguished high vertex to change.
3. **The obstructed instances have an explicit global repair.** One whole-component move changing exactly `k/5` labels, followed by valid hole pivots, produces a full covering copy. Thus these are not W, ES, or high-vertex-coverage counterexamples.
4. A replacement of W by minimum degree, a high seed, and just the **first nonseed activation** is false. A bounded-degree 120-edge tree gives an exact separator/capacity counterexample. In particular, two adjacent high vertices do not suffice under the W minimum-degree consequence alone.
5. There is a valid **target-sensitive leaf-blocker inequality**, using actual tree-neighborhood sets rather than the false uniform leaf-support inequality. It does not yet supply a common resistant host set.

Only this report, `WkGlobalContinuationChecks.py`, and its log were added. No Spec or shared Lean file was edited. No new Lean formalization is claimed.

---

## 1. Exact hypotheses and the fixed-high weighted problem

All graphs are finite, simple, and undirected. Containment is by an injective homomorphism, not necessarily an induced embedding. Write

\[
 p_G(v,X)=2d_G(v)-d_{G[X]}(v).
\]

Then

\[
 W_k(G):\qquad
 \forall\varnothing\ne X\subseteq V(G),\quad
 \max_{v\in X}p_G(v,X)\ge k.
\]

The `k=0` case is immediate for a nonempty host. For `k>=1`, a whole-host application gives a vertex of degree at least k. Singleton applications give `delta(G)>=ceil(k/2)`.

### 1.1 An exact weighted-apex equivalence

Fix a vertex s with `d_G(s)>=k`, and put

\[
 H=G-s,\qquad A=N_G(s),\qquad |A|\ge k.
\]

For every nonempty `X subset V(H)` and every `v in X`,

\[
 \boxed{p_G(v,X)=2d_H(v)-d_{H[X]}(v)+2\mathbf1_A(v).}       \tag{1}
\]

Consequently, under the already specified high-degree assumption on s,

\[
 \boxed{W_k(G)\iff
 \forall\varnothing\ne X\subseteq V(H),\ \exists v\in X:
 2d_H(v)-d_{H[X]}(v)+2\mathbf1_A(v)\ge k.}                 \tag{2}
\]

**Proof.** The degree in G exceeds the degree in H by exactly `1_A(v)`, while the induced degree in X is unchanged. This proves (1). Sets not containing s are handled by (1). If `s in X`, then

\[
 p_G(s,X)\ge d_G(s)\ge k,
\]

so such a set automatically has a witness. This proves both directions of (2). QED.

Thus the two-unit bonus on A is not merely a necessary deletion estimate. It is the exact remaining W condition once a high s is fixed.

### 1.2 The full variable-root forest deck

For every `u in V(T)`, let `F_u=T-u`. In each component of `F_u`, mark the unique former neighbor of u. A state is

\[
 (u,f),\qquad f\in\operatorname{Emb}(F_u,H).
\]

All components and all their images may be reembedded; u is not prescribed. Define

\[
 \operatorname{def}(u,f)
 =|\{v\in N_T(u):f(v)\notin A\}|.                         \tag{3}
\]

A state has defect zero **if and only if** adjoining `u -> s` gives a full T-copy. The role-free coverage question at s is therefore exactly the existence of a defect-zero state, with u chosen jointly with f.

One must not assume this deck is nonempty from a false forest version of W. For example, W_2 and sufficient host order do not force `2K_2`: a large star is a counterexample. The next section establishes the particular nonemptiness needed in a legitimate induction.

---

## 2. A rigorous one-defect initialization using only lower parameters

### Theorem 1 — initialization at every high vertex of a least-k counterexample

Suppose k is the least parameter for which the W tree-embedding statement fails. Let G satisfy W_k and let T be a missing k-edge tree. For **every** `s in V(G)` with `d_G(s)>=k`, the deck in Section 1.2 has a state of defect exactly one.

More specifically, its missing vertex p can be chosen to be the center of a pendant star of T. All the isolated components of `T-p` are marked into A; the only bad mark is in its remaining connected component.

### Proof

The one-edge case follows from the existence of a high vertex, so there is no least counterexample there. A star is also supplied directly by any high vertex. Thus T is not a star.

The nonleaf vertices of a nonstar tree induce a tree with at least two vertices. Choose an end p of that internal tree, and let q be its unique nonleaf neighbor. All other neighbors of p are leaves. Write

\[
 L=N_T(p)\setminus\{q\},\qquad \ell=|L|\ge1,
 \qquad d=d_T(p)=\ell+1\ge2.
\]

Then

\[
 R=T-(L\cup\{p\})
\]

is a nonempty tree containing q, with

\[
 |R|=k-d+1,\qquad e(R)=k-d\le k-2.                         \tag{4}
\]

For `H=G-s`, arbitrary one-vertex deletion gives `W_(k-2)(H)`: for every nonempty X in H, take a W_k witness in X and use (1), losing at most two. Hence H also satisfies `W_(k-d)`.

Minimality of k applies to the **strictly smaller** parameter `k-d`. It gives an embedding

\[
 g:R\longrightarrow H.
\]

No same-parameter induction is used. No root of R is prescribed, and R is a tree, not an arbitrary forest.

Since `|A|>=k`, there are at least

\[
 |A\setminus g(R)|\ge k-(k-d+1)=d-1=\ell                   \tag{5}
\]

unused vertices in A. Place the leaves of L there, injectively. Together with g this is an embedding `f:T-p -> H`. Every leaf mark lies in A. Its only other mark is q.

If `g(q) in A`, adjoining `p -> s` completes T, contrary to the choice of G,T. Therefore `g(q) notin A`, and this state has defect exactly one. QED.

### Consequence for a genuine proof by induction

A least-k counterexample cannot be dismissed because no suitable forest state has been initialized: one has been initialized at **every** high vertex. Equivalently, there is a full injection `V(T) -> V(G)` with `p -> s` that preserves all tree edges except the single edge `pq`.

This does **not** assert that an arbitrary such state can be repaired locally. Section 3 disproves precisely that type of assertion for the full variable-hole deck.

### Two elementary facts about one-defect states

Suppose `(u,f)` has one bad mark b.

* There is an unused allowed vertex: at least one of the k images is outside A, so `|A-f(F_u)|>=1`.
* The bad component is not isolated if there is no defect-zero state. Indeed, if b were a leaf of T, it would be an isolated component of `T-u`; move it to an unused member of A and finish.
* More generally, for every `y in A-f(F_u)`, a failed replacement of b by y supplies an actual nonedge:
  
  \[
  \exists w\in N_T(b)\setminus\{u\}:\quad y\not\sim_H f(w). \tag{6}
  \]
  Otherwise replacing b by y gives a defect-zero state.

The missed neighbor in (6) can depend on y. Turning these individual failures into one host set satisfying the resistant inequalities is not justified by (6) alone.

---

## 3. A linear-size barrier in the exact fixed-high deletion deck

This is not a prescribed-root obstruction. It allows every missing tree vertex, every component orientation, every valid host image, and every value of the defect along a reembedding sequence.

### Theorem 2 — variable-hole reembedding can require a k/5-label jump

For every odd integer `L>=3`, there are:

* a k-edge tree T with `k=5L` and `Delta(T)=3`;
* a fully critical graph G satisfying the literal Spec density bound;
* a high vertex s and `H=G-s`, `A=N_G(s)`;
* a one-defect state `(u_0,f_0)` in the full deck of Section 1.2;

such that **no sequence of valid deck states starting there and changing at most `L-1=k/5-1` tree-label values per step reaches a defect-zero state**.

A label value includes the hole symbol, so changing which vertex is missing is counted. The theorem permits arbitrarily long sequences and arbitrary changes of host image sets. It does not require roots, component images, or induced occupied subgraphs to remain fixed.

Nevertheless, a defect-zero state exists, and Section 3.6 gives a constructive repair using one L-label move and then ordinary hole pivots.

### 3.1 The target: five equally subdivided arms

Start with the double star having two adjacent degree-three hubs c,d, two leaves at c, and two leaves at d. Replace each of its five edges by a path of length L. The resulting tree has

\[
 k=5L,\qquad |T|=5L+1,\qquad\Delta(T)=3.                  \tag{7}
\]

Call the c--d path the middle path. The other four length-L paths are pendant arms. Let O,D be the bipartition, with `c in O`. Because L is odd, `d in D`, and

\[
 |O|=|D|=a:=\frac{5L+1}{2}.                               \tag{8}
\]

The targets have two branching vertices and hence are not spiders. Their maximum degree is far below the exact-apex threshold.

### 3.2 The host: a literal full-critical instance

Put

\[
 b=a(a-1)+1,\qquad G=K_{a,b},\qquad V(G)=P\dot\cup Q,
 \quad |P|=a,\ |Q|=b.
\]

Choose any `s in P`. Then

\[
 H=K_{a-1,b},\qquad A=N_G(s)=Q.                            \tag{9}
\]

Let `r=a-1=(k-1)/2`. The whole-host count is

\[
 |G|=a^2+1,\qquad e(G)=ab=r|G|+1.                        \tag{10}
\]

For a proper induced subset with `x` vertices of P and `y` of Q,

\[
 e_G(U)-r|U|=(x-r)y-rx.
\]

If `x<=r`, this is nonpositive. If `x=a=r+1`, properness gives `y<=b-1=a(a-1)`, and the surplus is

\[
 y-a(a-1)\le0.
\]

Thus **every proper induced subset is r-sparse**. This proves full criticality, with surplus exactly one, not just a degree or W certificate. It also verifies the precise `+1` density hypothesis in `Spec.lean`.

All high vertices lie in P:

\[
 d_G(p)=b\ge k\quad(p\in P),\qquad d_G(q)=a<k\quad(q\in Q).
\]

Activating P first and Q second certifies W_k directly, since the scores are b and `2a=k+1`. Equivalently, H has the exact weighted condition (2).

For example, `L=3` gives

\[
 k=15,\quad\Delta(T)=3,\quad G=K_{8,57},\quad
 n=65,\quad e=456=7\cdot65+1.
\]

Already here, moves changing at most two label values cannot repair the state below. Taking arbitrarily large odd L defeats every fixed bound and, asymptotically, every uniformly sublinear per-step support bound.

### 3.3 The orientation statistic is defined on every state

Use the following baseline color orientation:

\[
 O\longrightarrow P-\{s\},\qquad D\longrightarrow Q.
\]

For any state `(u,f)`, let

\[
 C(f)=\{v\in V(T)-\{u\}:f(v)\text{ is in the opposite host part
 from this baseline}\},\qquad m(f)=|C(f)|.                \tag{11}
\]

Each connected component of `T-u` has one of its two bipartite orientations. Therefore **C(f) is a union of whole components of `T-u`**. This holds for every state, regardless of its occupied host set.

A defect-zero state must have

\[
 \boxed{m(f)=0\quad\text{or}\quad m(f)=5L.}                 \tag{12}
\]

Indeed, all neighbors of u then map to Q. If `u in O`, this forces the baseline orientation in every component. If `u in D`, it forces the opposite orientation in every component. Conversely, every feasible endpoint-orientation state is defect zero: the other endpoint orientation with the wrong hole class would require a vertices of `P-{s}`, which has only `a-1` vertices.

### 3.4 A three-band lemma for the complete deletion deck

**Lemma.** For every `u in V(T)` and every union C of components of `T-u`,

\[
 \boxed{|C|\in [0,L]\ \cup\ [2L,3L]\ \cup\ [4L,5L].}      \tag{13}
\]

All intervals here are intervals of integers.

**Proof.** There are three exhaustive positions for the hole.

1. **The hole is a hub.** The component sizes are `L,L,3L`. Their subset sums are `0,L,2L,3L,4L,5L`.
2. **The hole is inside the middle path.** If its distance from c is `i`, with `1<=i<=L-1`, the two component sizes are
   
   \[
   2L+i,\qquad 3L-i.
   \]
   Each is strictly between `2L` and `3L`. Their other subset sums are 0 and `5L`.
3. **The hole is on a pendant arm but is not its hub.** Let j be its distance from the terminal leaf, so `0<=j<=L-1`. The component sizes are j and `5L-j`, with the zero component omitted when the hole is a leaf. Their subset sums lie in the two outside bands.

These cases prove (13). QED.

In particular, (13) applies to `m(f)` for **all** feasible forest embeddings, not just to selected rooted configurations.

### 3.5 A genuine one-defect state trapped in the middle band

Put the hole at c. Give the two c-pendant components the baseline orientation, and give the middle component the opposite orientation.

The middle component has `3L` vertices, with

\[
 |O\cap\text{middle}|=\frac{3L+1}{2},\qquad
 |D\cap\text{middle}|=\frac{3L-1}{2}.
\]

Baseline orientation of all `T-c` would use `a-1` vertices of `P-{s}`. Switching this component reduces that number by one. The proposed state therefore needs

\[
 a-2\text{ vertices of }P-\{s\},\qquad a+1\text{ vertices of }Q,
\]

so it is feasible. Complete bipartite adjacency supplies every forest edge.

The two pendant roots lie in Q, while the middle root lies in `P-{s}`. Hence

\[
 \operatorname{def}(c,f_0)=1,\qquad m(f_0)=3L.              \tag{14}
\]

Now extend any state map to all tree labels by giving its missing label the value `bottom`. Define the distance of two states to be the number of labels whose extended-map values differ. Then

\[
 |m(f)-m(g)|\le \operatorname{dist}(f,g).                  \tag{15}
\]

Changing membership in C requires changing that label's value, including a change to or from `bottom`.

The gap from the middle band to either outside band in (13) is L. Equations (13)--(15) imply that a move of distance at most `L-1` cannot leave the middle band. By induction, no sequence of such moves starting at (14) can leave it. But every defect-zero state is in an outside band by (12). This proves Theorem 2. QED.

This obstruction is not based on poor mixing, small stationary mass, a fixed leaf, or a fixed host image. It is a separation of the entire allowed state space by exact tree-component sizes.

**Changing the high host vertex also does not repair this particular locality problem.** All high vertices belong to P and all have the same allowed list Q. The statistic and the bands are unchanged if s is allowed to vary in P, even if that choice is not charged as a label edit.

### 3.6 An explicit global repair, with a sharp-size band-crossing move

Here is a complete covering construction starting from the trapped state.

1. Keep the hole at c. Switch the orientation of **one entire c-pendant arm**. This changes exactly L label values. The arm has one more D vertex than O vertex, so the switch increases the use of `P-{s}` from `a-2` to `a-1` and decreases the use of Q from `a+1` to a. There is one free `P-{s}` vertex available. Reuse the old arm images within each new color class, use that free vertex, and discard one old Q image. All changed forest edges remain complete cross edges.
   
   The resulting state has `m=4L` and defect two.
2. Let `c=x_0,x_1,...,x_L=ell` be the **other**, still-baseline c-pendant path. Move the hole successively from `x_i` to `x_(i+1)`, assigning `x_i` the old image of `x_(i+1)` and leaving other labels fixed.
   
   A general pivot of this form is legal exactly when the old image of the new hole is adjacent to the images of every neighbor of the old hole other than the new hole. For the first pivot, the other two c-branches are both switched, so this condition holds. For every later pivot, the old hole has degree two, with a switched rear segment and a baseline forward segment, so the condition again holds in the complete bipartite host.
   
   Each pivot changes two label values and adds one vertex to C(f).
3. At the terminal leaf ell, every occupied label is switched: `m=5L`. Since L is odd, `ell in D`; its sole neighbor maps to Q. The state has defect zero. Put `ell -> s`.

This is a full injective T-copy. It uses all a vertices of P, so in fact it covers every high vertex of G.

The first move changes L labels, exactly the lower bound needed to cross a band. A direct global repair is also possible by switching the entire middle component back to baseline; that changes `3L` labels and immediately gives defect zero. The shorter-support repair above illustrates that allowing a temporary increase from defect one to defect two can be useful.

### 3.7 Scope: what this does and does not rule out

The theorem rules out a universal assertion that **every** one-defect state can be repaired by bounded-support, or uniformly sublinear-support, moves. It still allows:

* a genuinely global minimization over the whole deck;
* deliberate whole-component reembeddings;
* an initializer guaranteed to land in a favorable local component;
* a proof that directly extracts a resistant host set without traversing states.

In particular, I do **not** claim that all states produced by Theorem 1 are trapped. The state (14) has its hole at a branching hub, not at a pendant-star center with adjacent leaves. In this complete bipartite family, suitable pendant-star initializations do repair. Thus this is a rigorous obstruction to an arbitrary-state local repair theorem, not a proof that every carefully initialized local strategy is impossible.

Most importantly, it is **not** a high-vertex-coverage counterexample: the full copy in Section 3.6 is explicit.

---

## 4. A different attempted reduction fails: the first activation is not enough

A tempting way to avoid the global state issue is to try to use only

\[
 \delta(G)\ge\lceil k/2\rceil,
 \quad H_0=\{v:d_G(v)\ge k\}\ne\varnothing,
\]

and the existence of a nonseed v with

\[
 d_G(v)+|N(v)\cap H_0|\ge k.                              \tag{16}
\]

If W activates beyond its seeds, it supplies (16). But the proposed reduction from the full activation process to its first nonseed step is false, even for bounded-degree targets.

### Theorem 3 — a first-trigger counterexample

There is a 120-edge tree T of maximum degree four and a graph G with

\[
 |G|=121,\quad\delta(G)=60,\quad H_0=\{s\},\quad
 d(s)=120,
\]

having a vertex t with

\[
 d(t)=119,\qquad |N(t)\cap H_0|=1,
\]

but containing no T.

### Construction

Let T be the complete rooted ternary tree of height four. Its level sizes are

\[
 1,3,9,27,81,
\]

so `|T|=121`, `e(T)=120`, and `Delta(T)=4`.

Let

\[
 G_0=K_2\vee(K_{59}\ \dot\cup\ K_{60}),
\]

with universal vertices s,t. Form G by deleting one edge `tb_0`, where `b_0` lies in the 60-clique. Then

\[
 e(G)=3719,\quad d(s)=120,\quad d(t)=119,
\]

and the other degrees are 60 or 61. Thus the claimed degree conditions and (16) hold.

It remains to prove that T does not even embed in the supergraph G_0.

### A complete two-vertex separator obstruction

Both graphs have 121 vertices, so a T-copy in G_0 would be spanning. Let U be the two tree vertices mapped to s,t. Every component of `T-U` must lie wholly in one of the two host cliques. Consequently all components must have size at most 60, and their sizes must have a subset sum of 59.

Write rho for the root of T; its three child subtrees each have size 40.

**Case 1: `rho in U`.** The other removed vertex w belongs to one 40-subtree. The other two 40-subtrees must go to different host cliques. The components of the affected `40-subtree - w` must therefore split into totals 19 and 20.

The possible component-size lists, according to the depth of w in that 40-subtree, are exactly

\[
 (13,13,13),\quad (27,4,4,4),\quad (36,1,1,1),\quad (39).
\]

None has a subset sum of 19.

**Case 2: `rho notin U`.** If both removed vertices lie in the same 40-subtree, the root component contains the other two and rho, hence has at least 81 vertices.

Otherwise the removals lie in two different 40-subtrees. The intact third subtree and rho already contribute 41 vertices to the root component. If either removed vertex is below its child-subtree root, at least 27 vertices of that 40-subtree remain attached to rho. The root component then has at least 68 vertices. Therefore both removed vertices must be child-subtree roots.

In that last possibility the component sizes are

\[
 41,13,13,13,13,13,13.
\]

The clique containing the 41-component would need an additional 18 or 19 vertices, neither a multiple of 13. This is also impossible.

The cases exhaust all U and prove noncontainment in G_0 and hence in G. QED.

### Why this is not a W counterexample

Let X be the 59-clique. Every vertex in it has ambient degree 60 and induced degree 58, so

\[
 p_G(v,X)=120-58=62<120\qquad(v\in X).                    \tag{17}
\]

Thus X is an explicit resistant set. The graph is also far below full incidence density.

The same proof shows that **minimum degree k/2 and two adjacent degree-k vertices do not suffice**, by using G_0 before its edge deletion. The full all-subsets content of W cannot be replaced by either of these local seed configurations.

---

## 5. A valid, nonuniform leaf-blocker inequality

The earlier uniform leaf-support bounds are false. There is nevertheless a useful exact shape-sensitive statement.

### Theorem 4 — every outside vertex supplies a tree-neighborhood blocker

Let G be T-free, let ell be a leaf of T with parent p, and let

\[
 U=T-\ell,\qquad f:U\hookrightarrow G,\qquad S=f(U).
\]

For `z outside S`, put

\[
 B_z=\{v\in U:z\not\sim_G f(v)\},\qquad
 P_f=\{v\in U:f(v)\sim_G f(p)\}.
\]

Then

\[
 p\in B_z,\qquad |P_f|=d_G(f(p)),\qquad
 \boxed{P_f\subseteq N_U(B_z).}                           \tag{18}
\]

In particular, writing `Delta=Delta(T)`,

\[
 \boxed{d_G(f(p))\le |N_U(B_z)|
 \le\sum_{b\in B_z}d_T(b)-1
 \le\Delta|B_z|-1.}                                     \tag{19}
\]

### Proof

If `f(p)` had a neighbor outside S, it would extend f at ell. Thus all its neighbors lie in S, giving `|P_f|=d_G(f(p))`; also `p notin P_f` because G is simple. If `p notin B_z`, z itself extends f, so `p in B_z`.

Suppose `v in P_f` has no U-neighbor in `B_z`. Replace its image by z. Every neighbor of v in U then has an image adjacent to z, so this is still an injective embedding of U. The parent p has not moved, since `v != p`. Place ell at the now-freed old image f(v), which is adjacent to f(p). This gives T, a contradiction. Hence every v in `P_f` has a U-neighbor in `B_z`, proving (18).

Taking the size of that tree-neighborhood union gives the first two bounds in (19). Since p belongs to `B_z`, deleting ell subtracts exactly one from the sum of tree degrees over `B_z`. The last inequality is the maximum-degree bound. QED.

### An exact consequence, not a resistance certificate

If `delta(G)>=ceil(k/2)`, every outside z misses at least

\[
 |B_z|\ge
 \left\lceil\frac{\lceil k/2\rceil+1}{\Delta(T)}\right\rceil \tag{20}
\]

vertices of the occupied set S. If z is high, `d(z)>=k=|S|` additionally gives

\[
 |N(z)\setminus S|\ge |B_z|.                              \tag{21}
\]

The exact neighborhood version (18) is stronger than its maximum-degree corollary and retains target shape information.

However, `B_z` is a **tree-label** set that depends on both z and f. Neither (18) nor (19) proves

\[
 2d_G(x)-d_{G[X]}(x)\le k-1\quad\text{for all }x\in X
\]

for one nonempty host set X. In particular, replacing `B_z` by an unproved common obstruction set would recreate the original gap. The statements above deliberately do not do that.

---

## 6. What remains after these reductions

### 6.1 A genuine global optimization is still available

In a least-k counterexample, fix any high s and minimize (3) over the **entire** variable-root deck. Theorem 1 proves the minimum is at most one. T-freeness makes it exactly one.

One can then, for example, minimize the size of the bad component over all minimum-defect states, allowing all component embeddings and u to change. This is a legitimate finite global choice. The linear-size barrier in Section 3 does not refute such a choice: it refutes replacing that choice by movement inside a bounded-support reconfiguration component.

I did not prove that a global minimum, with that tie-break or another, yields a resistant set. In particular:

* individual failed replacements as in (6) are not a common set certificate;
* the label blockers (18) do not supply ambient degree inequalities for all vertices of one host set;
* deleting the other occupied components does not preserve W at the parameter equal to the remaining tree's edge count;
* CL cannot be reapplied just because the components separately have possible roots in A;
* the first activation does not already settle the problem, by Theorem 3;
* the local deck obstruction is not evidence that the actual role-free embedding conjecture fails.

### 6.2 The exact unfilled extraction statement

A sufficient global lemma, in the exact fixed-high formulation, would be:

> Let `|A|>=k` and suppose the deck has a one-defect state but no defect-zero state. Extract a nonempty `X subset V(H)` such that, for every `v in X`,
> 
> \[
> 2d_H(v)-d_{H[X]}(v)+2\mathbf1_A(v)\le k-1.               \tag{22}
> \]

**This is unproved.** By (2), it contradicts the weighted W condition. Together with Theorem 1 and induction on k, it would prove the requested unrestricted W theorem. The proof would not need a same-parameter ES induction hypothesis.

For the weaker unrooted goal it would also suffice to optimize jointly over all high s and find a defect-zero state for at least one of them. Proving coverage at every high s is a stronger route, not something silently assumed necessary.

If one instead uses full criticality, it would suffice to extract a nonempty host set with

\[
 I_G(X)\le\frac{k-1}{2}|X|.
\]

No proof of that weaker summed extraction was obtained either. All uses of full criticality in this report are the explicit host certificates in Section 3; they are not being substituted for an unproved shape-selection theorem.

---

## 7. Verification and artifacts

Run

```
python3 Submission/WkGlobalContinuationChecks.py
```

The saved log is `Submission/WkGlobalContinuationChecks.log`. The checks audit explicit constructions and all finite color-pattern possibilities in the stated families, not unrestricted tree containment.

Completed audits include:

* 11,722 exact weighted-apex potential identities and 420 equivalences, including the two-unit deletion bookkeeping;
* 2,038 constructive pendant-star initializations, with a supplied smaller-tree embedding and both the zero-defect and one-defect outcomes checked;
* all 5,824 punctured-tree component-color patterns for odd `L=3,5,...,33`, allowing every hole role; 2,912 feasible patterns were realized in the appropriate complete bipartite H;
* 1,456 explicit defect-zero full copies from those patterns;
* all sixteen full-critical host certificates, with every proper induced-subset count type certified by the affine endpoint inequalities;
* all sixteen one-defect middle-band states, their exact part occupancies, and the `k/5` band gaps;
* sixteen explicit L-label component flips, 288 verified subsequent hole pivots, and sixteen completed copies covering every high vertex;
* 1,884 instances of the exact target-sensitive leaf-blocker inequality, including a minimum-degree-three tree-free trap with actual leaf-deleted embeddings;
* all 7,260 two-vertex deletions of the 121-vertex ternary target, independently verifying the separator capacity obstruction, and the exact degrees, first activation, and resistant clique of its host.

These finite audits are supplementary. The universal statements in Sections 1--5 are established by the proofs above, not inferred from the tests.

Every existing `Submission/*.lean` file was checksum-compared with its pre-investigation version and was unchanged. `Spec.lean` retains SHA-256

```
674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103
```

**Final mathematical status:** the unrestricted W_k theorem and the original full Erdős--Sós target remain unresolved by this continuation. The missing step is specifically the global resistant-set or low-incidence extraction in Section 6, not initialization of a suitable near-copy and not a missing justification for the explicit examples.
