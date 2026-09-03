# A fresh global Erdős–Sós attempt: saturation, Hall exchange, and weighted charging

## Status — the complete theorem is not proved

**I did not obtain a complete proof of the implication in `Submission/Spec.lean`, or a counterexample to it.** In particular, I have not proved that the known terminal certificates, the new packing lemmas below, or any union of them exhaust all critical hosts.

This attempt does establish several exact statements useful to a global proof:

1. **An exact surplus bound after saturation.** A least-order counterexample for a fixed target, maximized in edges, has
   \[
   0<\eta\le (k+1)/2-\Delta(T).
   \]
   Consequently a normalized least-order counterexample with `Delta(T)=floor(k/2)` is already **T-saturated**. For even k in this boundary case its order must be odd and its surplus exactly one half.
2. **Independent prescribed roots suffice for arbitrary nontrivial forests.** If a forest has e edges and no isolated components, every assignment of its component roots to distinct **independent** host vertices extends when the host minimum degree is at least e. This is a prescribed-root theorem in arbitrary hosts, not a triangle-free-host statement. The no-isolates qualification is necessary.
3. **Different-list star forests have a weighted Hall theorem.** For stars with positive leaf demands `a_i`, roots may have completely different lists. A weighted Hall condition on those lists, and degree at least `sum a_i` only at the root candidates, suffice. A failed leaf matching gives a root move that strictly decreases the number of edges among the roots. This is a terminating, genuinely joint reembedding argument.
4. **The one-leaf Hall obstruction has an exact canonical structure.** For a fixed embedding of the nonleaf core, if all but one leaf can be matched, the deficiency-one parent sets have a unique minimum. Exactly its parents can carry the missing leaf after a complete leaf rematching. There is an exact critical-incidence inequality for this block. However, an explicit critical split family shows that taking these canonical blocks over different core embeddings does **not** automatically yield a resistant host set.
5. **The proposed weighted recurrence has an exact covariance/nonneighbor decomposition.** This isolates the global charge that has to be controlled. It proves the recurrence for stars in all hosts, but both a nonnegative-covariance shortcut and a naive total-variation shortcut fail in actual critical hosts.

These are mathematical proofs, with independent finite audits. **No new Lean formalization is claimed. No Spec or shared Lean file was edited, and neither admitted declaration in `Spec.lean` was used.** The proofs do not assume unrestricted Erdős–Sós. Smaller-k ES is used only where explicitly indicated to initialize a partial copy.

---

## 1. Conventions and exact scope

Graphs are finite, simple, and undirected. An embedding is an injective homomorphism, not necessarily induced. T has k edges and k+1 vertices. Write

\[
 a=(k-1)/2,\qquad m=e(G)=a n+\eta.
\]

For a vertex set X, `I_G(X)` counts edges having at least one endpoint in X, with internal edges counted once. Proper-induced criticality gives

\[
 e_G(S)\le a|S|\quad(S\subsetneq V(G)),\qquad
 I_G(X)\ge a|X|+\eta\quad(X\ne\varnothing).                 \tag{1}
\]

In particular,

\[
 d_G(v)\ge a+\eta,\qquad \Delta(G)\ge k.                  \tag{2}
\]

The normalized surplus is in `{1/2,1}`. In Section 2, after maximizing edges, the surplus is deliberately **not assumed normalized**. The proper-set inequalities still hold there.

The literal specification requires `m >= a n + 1`. Its equivalence with the strict-average formulation is the supplied disjoint-doubling reduction; this report does not silently discard the half-unit case.

The existing exact-apex consequence of CL is used in the following precise form:

> If a target vertex u has degree d, a host vertex s has degree at least k, and `delta(G-s) >= k-d`, then T embeds with `u -> s`.

Indeed, `T-u` has k vertices, k-d edges, and one attachment root per component. Its common list is `N_G(s)`, of size at least k. This use of CL is already proved in the workspace.

---

## 2. Global route A: saturate a least-order counterexample without losing the surplus accounting

### Theorem 1 — bounded saturated surplus

Fix a k-edge tree T, k>=3. Suppose there is a T-free graph with more than `a n` edges. Among such graphs choose one of minimum order, and among those choose G with the maximum number of edges. Then:

* G is T-saturated: adding any missing edge creates T;
* every proper induced set is a-sparse;
* its surplus satisfies
  \[
  \boxed{0<\eta\le (k+1)/2-\Delta(T).}                    \tag{3}
  \]

**Proof.** A proper induced dense T-free graph would contradict the minimum order. If a missing edge could be added while remaining T-free, the result would still be a counterexample of that order and would contradict the maximal edge count.

Let `D=Delta(T)`. If `eta>(k+1)/2-D`, then

\[
 a+\eta>k-D,
\]

and (2), with integrality, implies `delta(G)>=k-D+1`. Choose s with `d(s)>=k`. Now

\[
 \delta(G-s)\ge k-D.
\]

The exact-apex theorem at a maximum-degree target vertex embeds T, a contradiction. This proves (3). QED.

### Corollary 1.1 — how much a normalized counterexample can be completed

Start with a normalized counterexample of the same minimum order, with surplus `eta_0`. Add edges as long as T-freeness is preserved. Every intermediate graph still has all proper induced sets a-sparse: otherwise it contains a smaller dense T-free graph. The process terminates in a saturated graph, and the number j of added edges satisfies

\[
 \boxed{j\le \left\lfloor (k+1)/2-\Delta(T)-\eta_0\right\rfloor.} \tag{4}
\]

If the right side is negative, no such normalized counterexample exists.

This is a legitimate extremal reduction, not an assumption that **edge normalization and saturation can always be imposed simultaneously**. In general they are different choices.

### Corollary 1.2 — the boundary maximum degree has no completion slack

If `Delta(T)=floor(k/2)`, then:

* for `k=2r+1`, (3) gives `eta<=1`; normalized surplus is already 1;
* for `k=2r`, (3) gives `eta<=1/2`; thus normalized surplus must be 1/2, which forces n odd.

In both cases (4) gives j=0. Hence a least-order normalized counterexample at this boundary is already T-saturated.

For even k and normalized surplus 1, the boundary case `Delta(T)=k/2` is therefore already covered by the exact-apex argument. This does **not** remove the half-unit minimal witnesses from the unrestricted theorem.

### What saturation supplies, and what it does not

In a saturated G, every nonedge xy has a T-copy in `G+xy` using xy. Suppose such a copy maps a target edge uv to xy. Replacing the image of u by some unused z would be a valid repair exactly when

\[
 z\sim y\quad\text{and}\quad
 z\sim f(w)\quad(w\in N_T(u)\setminus\{v\}).               \tag{5}
\]

Thus, in a T-free G, every unused neighbor z of y must miss at least one of the latter required images. The analogous assertion holds with x and y reversed. If u is a leaf, the latter set is empty, so y has no unused neighbor; in particular `d_G(y)<=k-1`.

These are simultaneous marked-neighborhood obstructions, not just edge-count obstructions. In the degree-`r+1` split-off situation from `CircuitLiftingGlobalFindings.md`, they are exactly the reason an internal virtual edge cannot simply be replaced by the deleted host vertex. Saturation gives many witnesses, but does not yet choose a witness whose entire tree interface lifts. I did not prove such a joint witness-selection theorem.

---

## 3. Global route B, first result: independent prescribed component roots

The next result replaces a common-list hypothesis by a genuine prescribed-root hypothesis, under an explicit independence condition. Its proof adapts the clique-reservoir argument of Goldberg–Magdon-Ismail (`/corpus/src/1011.3882/theorem.tex`) and the root-preserving swaps audited in `CommonMarkedForestCL.md`.

### Theorem 2 — independent-root forest embedding

Let F be a forest with p components `T_1,...,T_p`, **each having at least one edge**. Specify a root `r_i` in each component. Put

\[
 a_i=e(T_i)\ge1,\qquad e=\sum_i a_i.
\]

Let H have minimum degree at least e. If distinct prescribed host vertices `s_1,...,s_p` form an independent set, then there is an embedding of F in H with `r_i -> s_i` for every i.

In fact, the host order requirement is automatic: a prescribed root has at least e neighbors outside the p-element independent root set, so `|H|>=e+p=|F|`.

### Proof

Induct on p. For p=1, ordinary rooted greedy tree embedding applies.

Assume p>=2 and that no required embedding exists. A nontrivial rooted tree is called a **root-centered star** when its root is adjacent to every other vertex. An edge is a root-centered star with either root. Choose `T_1` to be a root-centered star if one exists; otherwise choose any component. Write

\[
 a=a_1,\quad R=\{s_1,\ldots,s_p\},\quad F_-=T_2\cup\cdots\cup T_p.
\]

#### A reserved clique through the first root

Consider any rooted copy of `T_1` avoiding `R-{s_1}`. Some vertex outside the copy must be adjacent to its entire image. Otherwise every remaining vertex loses at most a neighbors on deleting that `(a+1)`-vertex image. The remaining host has minimum degree at least e-a and retains the other prescribed independent roots; induction embeds `F_-`, a contradiction.

Such copies can always be grown from any connected partial rooted copy inside `H-(R-{s_1})`, since

\[
 \delta\bigl(H-(R-\{s_1\})\bigr)\ge e-(p-1)\ge a.          \tag{6}
\]

Starting from `{s_1}`, grow a clique through `s_1`: map a connected rooted subtree of `T_1` onto the current clique, extend to `T_1` using (6), and add the just-proved common neighbor. A common neighbor cannot be another prescribed root, since those roots are not adjacent to `s_1`. This constructs a clique of order a+2 through `s_1`, avoiding the other prescribed roots.

Choose an a-clique K through `s_1`. Choose a leaf ell of `T_1` different from its root, and embed `T_1-ell` bijectively into K with its root at `s_1`. Let x be the image of the leaf's parent. Choose

\[
 X\subseteq N_H(x)\setminus K,\qquad |X|=e-a+1.             \tag{7}
\]

This is possible because `d(x)>=e` and K contains only a-1 possible neighbors of x.

The other prescribed roots lie outside K, and `delta(H-K)>=e-a`. Induction gives a prescribed-root embedding g of `F_-` there. Let

\[
 B=g(V(F_-)),\quad Y=B\setminus X,\quad
 S=V(H)\setminus(K\cup B),\quad J=H[K\cup S].              \tag{8}
\]

Every such g must cover X. If it missed w in X, adding ell at w to the reserved copy would complete F. Therefore

\[
 X\subseteq B,\qquad |B|=e-a+p-1,\qquad |Y|=p-2.           \tag{9}
\]

#### If a root-centered star was selected, there is already a contradiction

Here x=`s_1`, so X contains none of `s_2,...,s_p`. All p-1 of those vertices belong to B, hence to Y. But `|Y|=p-2`.

We may therefore assume **none** of the components is a root-centered star. In particular every `a_i>=2`.

#### Root-preserving global reembedding in the nonstar case

Classify the components of `F_-` into four classes, with counts `q_1,...,q_4`:

1. all image vertices lie in X;
2. at least two lie in X and at least one in Y;
3. exactly one lies in X;
4. all lie in Y.

Counting the p-2 vertices of Y gives

\[
 q_1\ge1+\sum_{\text{class 3}}(a_i-1)+\sum_{\text{class 4}}a_i
      \ge1+q_3+2q_4.                                      \tag{10}
\]

Fix s in S. In a class-1 component, s must miss at least two image vertices. If it misses no vertex, any nonroot vertex could be moved to s, freeing a member of X. If it misses only a nonroot vertex, move that vertex. If it misses only the root image, move a nonroot vertex **not adjacent to the root**; such a vertex exists because this is not a root-centered star. Each move preserves the prescribed root and every required edge, contradicting the universal coverage of X.

In a class-2 component, s must miss at least one image vertex. Otherwise one of its at least two X-vertices that is not the root could be moved to s. No assertion is needed for classes 3 and 4. Consequently

\[
 \begin{aligned}
 d_J(s)&\ge e-|B|+2q_1+q_2\\
       &=a+q_1-q_3-q_4\\
       &\ge a+1+q_4\ge a+1.                              \tag{11}
 \end{aligned}
\]

Independence of the prescribed roots gives the additional estimate needed at `s_1`: it misses all p-1 other prescribed roots inside B, and hence

\[
 d_J(s_1)\ge e-(|B|-(p-1))=a.                             \tag{12}
\]

As K has only a-1 other vertices, `s_1` has a neighbor `s_0` in S.

Start the copy of `T_1` with its root at `s_1` and any child at `s_0`. Greedily extend this connected partial copy in J. A parent outside K has degree at least a by (11). A parent in K has an unused K-neighbor whenever the copy is incomplete: at most a vertices are then occupied, at least one of them is outside K, and K is an a-clique. Thus the copy extends to all a+1 vertices, while retaining its prescribed root and avoiding B. Together with g this embeds F, the final contradiction. QED.

### A useful degree formulation

Edges between distinct prescribed roots can never be used by F. Delete all such host edges. Therefore Theorem 2 also applies whenever

\[
 d_H(v)\ge e\ (v\notin R),\qquad
 |N_H(r)\setminus R|\ge e\ (r\in R).                       \tag{13}
\]

For example, `delta(H)>=e+Delta(H[R])` is a sufficient, though not necessary, numerical condition. Also, arbitrary component-root lists suffice whenever they admit an independent transversal: prescribe that transversal and apply Theorem 2. No earlier choice of branch images has to be preserved.

### Qualifications are real

* Independence cannot simply be omitted. In two triangles joined by a bridge between vertices 2 and 3, prescribe the two roots of `2K_2` at adjacent vertices 0 and 1 of the first triangle. The host minimum degree is 2, but their only possible leaf image outside the root set is vertex 2.
* **An isolated prescribed root invalidates the theorem even if all roots are independent.** In `C_4=0-1-2-3-0`, prescribe the end root of P3 at 0 and an isolated root at 2. The roots are independent and the forest has two edges, but there is no two-edge path starting at 0 and avoiding 2.

Unmarked isolated vertices can be placed afterward if enough host vertices remain. Arbitrary prescribed isolated roots cannot be treated that way.

---

## 4. Global route B, second result: a weighted Hall theorem for different-list stars

### Theorem 3 — rooted star packing from weighted root-list Hall

For `i=1,...,p`, let `T_i` be a star rooted at its center, with `a_i>=1` leaves. Put

\[
 e=\sum_i a_i.
\]

Give its root a host list `L_i`. Suppose:

1. every vertex in `union_i L_i` has host degree at least e;
2. for every set of indices Q,
   \[
   \boxed{\left|\bigcup_{i\in Q}L_i\right|
       \ge\sum_{i\in Q}(a_i+1).}                          \tag{14}
   \]

Then the whole star forest has a disjoint embedding with root i in `L_i`.

There is **no minimum-degree requirement on noncandidate host vertices**. In particular, arbitrary different lists of size at least `|F|=e+p` work in a host of minimum degree e.

### Proof by a decreasing global potential

Hall's theorem, applied to `a_i+1` labelled copies of list i, supplies pairwise disjoint reservoirs

\[
 A_i\subseteq L_i,\qquad |A_i|=a_i+1.                     \tag{15}
\]

Choose one current root `x_i` in each `A_i`, and put `R={x_1,...,x_p}`. Try to match all leaf slots into `V(H)-R`, with the slots at root i having neighborhood `N(x_i)-R`.

If this matching fails, Hall supplies a nonempty set Q of root indices such that, writing `a(Q)=sum_{i in Q}a_i`,

\[
 Y=\bigcup_{i\in Q}(N(x_i)\setminus R),\qquad |Y|\le a(Q)-1.\tag{16}
\]

For **every** i in Q,

\[
 \begin{aligned}
 d_{H[R]}(x_i)
 &\ge e-|Y|\\
 &\ge e-a(Q)+1\\
 &=\sum_{j\notin Q}a_j+1\ge p-|Q|+1.                      \tag{17}
 \end{aligned}
\]

On the other hand, the union of the Q-reservoirs has `a(Q)+|Q|` vertices. It contains exactly |Q| current roots and at most `a(Q)-1` vertices of Y. There is therefore

\[
 z\in\bigcup_{i\in Q}A_i\setminus(R\cup Y).
\]

Let i in Q be its reservoir index. Replace `x_i` by z. The new root is in its correct list and is distinct from the other roots. Moreover z is adjacent to **none** of the old roots indexed by Q: otherwise z would belong to Y. Thus its number of neighbors among the other current roots is at most `p-|Q|`, strictly less than (17) for the root it replaces.

Consequently the potential

\[
 \Phi(R)=e_H(R)
\]

strictly decreases. It is a nonnegative integer initially at most `binom(p,2)`. Repeat the matching attempt and the root replacement. After at most that many replacements the matching must succeed. Use its images for the leaves. QED.

### Why this is a genuine joint exchange argument

The construction does **not** preserve the previous leaf matching. It recomputes a complete matching after moving a root, and a Hall witness can involve arbitrarily many stars. The potential measures root-root conflicts, not the weight or distance of an intermediate tree embedding.

For example, in two disjoint K5 blocks, use four one-leaf stars and reservoirs

\[
 \{0,5\},\ \{1,6\},\ \{2,7\},\ \{3,8\}.
\]

Starting with roots `0,1,2,3` in one block, the algorithm has potentials

\[
 6\longrightarrow3\longrightarrow2,
\]

then a full leaf matching. The proof also works when most noncandidate vertices have degree one.

### Isolated components and the remaining forest interface

The assumption `a_i>=1` is used in (17). The weighted-Hall version is false with prescribed isolated components: in `P_3=0-1-2`, take an edge whose root list is `{0,2}` and an isolated root with list `{1}`. The weighted Hall inequalities with demands 2 and 1 hold, and the candidates for the nontrivial star have degree at least 1, but the edge cannot avoid the prescribed isolated vertex.

If instead **all** root lists have size at least the order of the entire forest, isolated components can be postponed and placed at unused list vertices. This gives the uniform-large-list extension for star forests, not the smaller weighted-Hall extension with arbitrary isolated-root lists.

For arbitrary nonstar components, moving the root to z in the proof would require reembedding its whole branch structure. A leaf matching does not certify that. Theorem 2 supplies a separate valid interface when the roots can be chosen independent, but I did not obtain a theorem merging these two mechanisms into an unrestricted density-funded forest induction.

### A tempting matroid shortcut is unavailable even for matching roots

Let H be two K4s on `{0,1,2,3}` and `{2,3,4,5}`, sharing the edge 23. Its minimum degree is 3. Call a root set R feasible if its vertices can be matched to distinct vertices outside R.

The sets

\[
 C_1=\{0,1,2\},\qquad C_2=\{0,1,3\}
\]

are infeasible: vertices 0 and 1 have the same sole available outside-root neighbor. Every proper subset of either set is feasible. For the nontrivial pairs, outward matchings are `0-2,1-3` for `{0,1}`, `0-1,2-4` for `{0,2}`, `1-0,2-4` for `{1,2}`, `0-1,3-4` for `{0,3}`, and `1-0,3-4` for `{1,3}`. But

\[
 (C_1\cup C_2)\setminus\{0\}=\{1,2,3\}
\]

is feasible, via the matching `1-0, 2-4, 3-5`. Thus feasible root sets do not satisfy matroid circuit elimination, even in a host satisfying `delta(H)=3=e(3K_2)`.

This does not refute Theorem 3. It explains why an ordinary matroid-transversal argument cannot be silently substituted for its Hall-driven root exchange.

---

## 5. Canonical one-leaf Hall blocks, and why their union is not yet a global certificate

### 5.1 The exact fixed-core reduction

Assume k>=2. Let L be the number of leaves of T, let I be its nonleaf core, and let P be the set of parents of leaves. For `p in P`, let `lambda(p)>=1` be its number of leaf children. Then

\[
 |I|=k+1-L,\qquad \sum_{p\in P}\lambda(p)=L.
\]

Fix an embedding `f:I -> G`. The remaining task is exactly a demand matching, with allowed sets

\[
 B_p=N_G(f(p))\setminus f(I).
\]

A full matching of the L leaf slots is equivalent to an extension to T.

In a hypothetical counterexample, smaller-k ES embeds `T-ell` for any chosen leaf ell. Restricting such an embedding to I gives a core f whose maximum leaf matching has size **exactly L-1**: it is at least L-1 from that partial copy, and cannot be L in a T-free graph. This uses a genuine smaller tree, not an unproved forest version of ES.

### Theorem 4 — the canonical deficiency-one block

For this fixed core f, define

\[
 d(Q)=\lambda(Q)-\left|\bigcup_{p\in Q}B_p\right|,
 \qquad \lambda(Q)=\sum_{p\in Q}\lambda(p).
\]

If the maximum matching has size L-1, then:

1. `d(Q)<=1` for every Q;
2. the nonempty family `{Q:d(Q)=1}` is closed under unions and intersections;
3. it has a unique nonempty minimum member `P_*`;
4. **a leaf at p can be the only missing leaf in some full rematching of the other leaves if and only if `p in P_*`.**

**Proof.** A matching missing just one slot proves the first assertion. Neighborhood cardinality is submodular, while lambda is modular, so d is supermodular. For two deficiency-one sets, the deficiencies of their union and intersection sum to at least two, and each is at most one. Both are therefore one. Their intersection cannot be empty because `d(empty)=0`. Finite intersection gives `P_*`.

Remove one demand slot at p. Every deficiency-one set loses one unit exactly when it contains p. All other deficits were nonpositive. Hall's theorem therefore covers all remaining slots exactly when p belongs to every deficiency-one set, equivalently to `P_*`. QED.

Alternating reachability from the unmatched slot in any maximum matching recovers this same minimum block; it is not dependent on which maximum matching was chosen. To see this, no unmatched right vertex is reachable, and every reached right vertex is matched to a reached slot. Every slot of a reached parent is reached as well, because the slots have identical neighborhoods. Thus the reached parents form a deficiency-one set. Conversely, every deficiency-one set contains the unmatched slot and has its entire neighborhood matched internally, so no alternating path starting there leaves it. The reached parent set is therefore contained in every deficiency-one set, and equals `P_*`.

### 5.2 An exact incidence charge for the canonical block

Put

\[
 X=f(P_*),\qquad Y=\bigcup_{p\in P_*} B_p.
\]

Then

\[
 |Y|=\lambda(P_*)-1,\qquad N_G(X)\subseteq f(I)\cup Y.       \tag{18}
\]

In any L-1 matching, all vertices of Y are occupied by leaf slots belonging to `P_*`. Define the **actual host incidence inside the embedded core**

\[
 b_f(X)=e_G(X)+e_G(X,f(I)\setminus X).
\]

The critical incidence inequality (1) gives the rigorous charge

\[
 \boxed{b_f(X)+|X|(\lambda(P_*)-1)\ge a|X|+\eta.}          \tag{19}
\]

Indeed, all edges incident with X go either into the core or into Y, and there are at most `|X||Y|` of the latter.

Writing `t=|P_*|` and `L_out=L-lambda(P_*)`, the crude simple-graph bound on `b_f` yields

\[
 \boxed{t(k-t-2L_{\rm out})\ge2\eta.}                     \tag{20}
\]

The more informative form is (19): the edges counted by `b_f` include **occupied host chords**, not just target-core edges. Replacing it by an unproved tree-degree bound would lose the very obstruction being charged.

### 5.3 A fully critical obstruction to an unconditional cross-core union rule

For r>=2, let

\[
 G_r=K_r\vee\overline K_{r^2+1},\quad A=V(K_r),\quad
 B=V(\overline K_{r^2+1}),\quad k=2r.
\]

These are the established genuine critical split hosts:

\[
 2e(G_r)=(2r-1)|G_r|+1,
\]

and for subset type `(x,y)` their doubled surplus is

\[
 x(x-2r)+(2x-2r+1)y\le0
\]

unless the entire host is selected. To check this directly: if `x<=r-1`, both terms are nonpositive; if `x=r` and the subset is proper, its surplus is `y-r^2<=0`. Thus `eta=1/2` and all proper-induced inequalities hold.

Let H be **any** r-edge tree, and let T be its full subdivision. Fix an original leaf ell of H, let q be its original neighbor, and let p be the subdivision vertex on `ell-q`.

Construct a bad core embedding as follows:

* map q and all subdivision vertices other than p bijectively into the r-clique A;
* map p and every other original nonleaf vertex into distinct members of B.

This preserves all core edges. Every leaf-parent other than p lies in A and sees all unused B vertices. The parent p lies in B and has all its neighbors A already occupied by the core. Thus exactly L-1 leaves can be matched, and

\[
 P_*=\{p\},\qquad Y=\varnothing,\qquad
 I_G(\{f(p)\})=r=a+\eta.                                  \tag{21}
\]

Permuting B moves this canonical singleton Hall block to **any** member of B. Conversely, a deficient parent set cannot contain an A-image: such an image sees every vertex outside the core, and

\[
 |G_r|-|I|=r^2-r+L\ge L.
\]

Therefore the union of canonical parent-image blocks over all deficiency-one core embeddings is exactly B. But

\[
 I_{G_r}(B)=r|B|>a|B|+\eta,\qquad
 2d_{G_r}(v)-d_{G_r[B]}(v)=2r=k\quad(v\in B).               \tag{22}
\]

Indeed, **every nonempty subset of B** has potential k at each of its vertices. No nonempty union or selection of these singleton parent blocks is a resistant set.

This works with a subcubic nonspider T: take H to be the five-edge double star with both hub degrees three; then `k=10`, `Delta(T)=3`, `n(G)=31`, `e(G)=140`, and `eta=1/2`.

There is an explicit repair, so this is **not** a T-free counterexample. Swap the core images of p and q. All subdivision vertices now lie in A and all original nonleaf vertices in B. Put the original leaves in unused B positions. This is a full T-copy.

**Logical scope.** The example refutes an unconditional claim that canonical Hall blocks from deficient core embeddings automatically combine into a density obstruction. It does **not** refute a theorem with the extra premise that every possible core embedding is deficient. Such a premise is available in a hypothetical T-free host, but I have not proved the necessary cross-core exchange/uncrossing theorem under that premise.

---

## 6. Global route C: isolate the missing weighted charge exactly

Retain the degree-corrected weights from the workspace. For a nontrivial tree R,

\[
 w_R(f)=\prod_{u\in V(R)}d_G(f(u))^{1-d_R(u)},\qquad
 Z(R,G)=\sum_{f\in\operatorname{Emb}(R,G)}w_R(f).
\]

In this section assume `k>=2`. Let ell be a leaf of T, p its parent, and `U=T-ell`, so U has k vertices and is nontrivial. For hosts with isolated vertices, set the quantities below to zero at those vertices. Critical hosts have none.

Define the rooted injectivity message

\[
 h_v=\frac1{d_G(v)}
      \sum_{\substack{f\in\operatorname{Emb}(U,G)\\f(p)=v}}w_U(f).\tag{23}
\]

It is the unconditioned tree-walk probability of injectivity given the root image v, not a claim of stationary marginals after conditioning. In particular,

\[
 Z(U,G)=\sum_v d_G(v)h_v.
\]

For a partial copy f, let

\[
 q_p(f)=|\{u\in U-\{p\}:f(u)\not\sim_G f(p)\}|,
\]

and put

\[
 M_p=\sum_{f\in\operatorname{Emb}(U,G)}
             \frac{w_U(f)}{d_G(f(p))}\,q_p(f)\ge0.          \tag{24}
\]

This measures **occupied nonneighbors of the specified parent**, rather than free neighbors.

### Theorem 5 — exact covariance/nonneighbor decomposition

For every host and every such T,U,p, with `c=k-1` and `epsilon=2m-cn`,

\[
 Z(T,G)=M_p+\sum_v(d_G(v)-c)h_v,                            \tag{25}
\]

and

\[
 \boxed{
 2mZ(T,G)-\epsilon Z(U,G)
 =2mM_p+c\left[n\sum_v d_G(v)h_v-2m\sum_v h_v\right].}    \tag{26}
\]

The bracket equals

\[
 \sum_{v<w}(d_G(v)-d_G(w))(h_v-h_w)
 =n^2\operatorname{Cov}_{v\text{ uniform}}(d_G(v),h_v).      \tag{27}
\]

**Proof.** The partial copy occupies k vertices. Its parent has exactly `k-1-q_p(f)` occupied neighbors, so its number of free neighbors is

\[
 d_G(f(p))-(k-1)+q_p(f).
\]

Insert this into the exact leaf-extension identity and sum to obtain (25). Substitute `Z(U,G)=sum d h` and `epsilon=2m-cn` to obtain (26). Expanding the unordered-pair sum gives (27). QED.

Thus general (CW) is precisely the assertion that the occupied-nonneighbor charge compensates any **negative degree covariance**, at the exact coefficient in (26). This is a nonlocal scalar comparison over all partial embeddings. It neither routes mass through bounded-local intermediate states nor assumes a stationary root marginal.

### A proved consequence: the weighted recurrence for stars, without criticality

If `T=K_(1,k)` and p is its center, then `U=K_(1,k-1)` and

\[
 h_v=\frac{(d_G(v))_{k-1}}{d_G(v)^{k-1}},\qquad M_p=0.       \tag{28}
\]

Set h=0 when the degree is too small. This h is nondecreasing as a function of degree: above the threshold each factor `1-j/d` is nondecreasing, and below it the value is zero. Every summand in (27) is nonnegative. Therefore

\[
 \boxed{2mZ(K_{1,k},G)\ge
       [2m-(k-1)n]Z(K_{1,k-1},G)}                           \tag{29}
\]

for every finite host with m>0, not just critical hosts. This is a proof of the quantitative recurrence for stars; it is not a proof for arbitrary trees.

### Why two natural shortcuts do not close (26)

#### Nonnegative degree covariance is false in critical hosts

In `G_2=K_2 join independent_5`, take `T=P_5`, delete an end leaf, and root `U=P_4` at the new endpoint. Exact values are

\[
 h_A=5/18\quad\text{at each of the two degree-6 vertices},
 \qquad h_B=4/9\quad\text{at each degree-2 vertex},
\]

\[
 Z(U)=70/9,\quad Z(T)=5/3,\quad M_p=20/9,
\]

and

\[
 n\sum d h-2m\sum h=-20/3<0.                              \tag{30}
\]

The nonneighbor term is essential; it makes the total (26) positive.

This is not an isolated small phenomenon. For the full-subdivision targets in the established critical split partition formula (`DegreeCorrectedMeasureFindings.md`, Sections 2 and 3), put

\[
 D=r(r+1),\qquad
 A_r=\frac{r!\,(r^2+1)_r}{D^{r-1}r^{r-1}}.
\]

Root the original tree with ell deleted at its former neighbor. The bad-orientation factor C is given by `C_v=product_w(1/(r+1)+C_w)` over children, with `C_v=1` at a leaf. In particular C>=1. The established pattern bijection gives

\[
 Z(U)=A_r(1+C),\quad \sum_v h_v=A_r(1/D+C/r),\quad C\ge1.
\]

Using `n=r^2+r+1` and `2m=r(2r^2+r+1)`, the covariance bracket divided by `A_r` is exactly

\[
 -r^2(C-1)-r+2-\frac2{r+1}<0\qquad(r\ge2).                \tag{31}
\]

This applies at every leaf, including for subcubic nonspider subdivisions. A mere Chebyshev claim about the conditioned root law cannot establish general CW.

#### The direct total-variation domination is also false

The supplied coarea inequalities imply

\[
 \sum_v(d_G(v)-c)h_v+
       \sum_{uv\in E(G)}|h_u-h_v|
 \ge\epsilon\max_v h_v.
\]

Together with (25), a sufficient route would be

\[
 M_p\ge\sum_{uv\in E(G)}|h_u-h_v|.                        \tag{32}
\]

But (32) fails even for a star in a critical host satisfying the literal specification. Take `G=K_4` minus one edge, `k=3`, `U=K_(1,2)` rooted at its center. The degrees are `3,3,2,2`, so h takes values `2/3,2/3,1/2,1/2`. Then

\[
 M_p=0,\qquad \sum_{uv\in E(G)}|h_u-h_v|=2/3.
\]

Here `n=4`, `m=5`, `epsilon=2`, `Z(U)=6`, and `Z(T)=4/3`; CW itself holds, with gap `4/3`. The total-variation bound was too strong, not the recurrence.

### What remains in this route

For a critical host the desired inequality is

\[
 2mM_p+(k-1)n^2\operatorname{Cov}(d,h)\ge0.                \tag{33}
\]

I have not proved (33) for arbitrary trees, nor found a critical-host violation of it. The already proved split-host comparison controls it in that family. The extra tests here are exact audits of (25)–(27), not a proof of (33).

If CW were proved globally, smaller-k ES would make `Z(U,G)>0` and CW would imply `Z(T,G)>0`. The missing comparison is therefore sufficient for the full induction, but is **not being assumed**.

---

## 7. Why the new theorems do not yet compose into a complete ES proof

The progress is in two genuinely global choices: rematching an entire star forest while moving roots, and retaining independent prescribed roots through arbitrary forest reembeddings. Neither argument is restricted to moving a bounded number of tree labels. Their proofs are not invalidated by the known local reconfiguration barriers.

The unresolved interface is nevertheless substantial:

* In Theorem 2, arbitrary forest roots need either independence or the explicit external-degree condition (13). Criticality does not automatically select such roots for all the required branches.
* Theorem 3 handles arbitrary different lists and joint Hall defects, but its components must be root-centered stars. Applying it to deeper branches would silently replace tree constraints by leaf slots.
* Both forest mechanisms still need an edge budget for the **whole forest**. A critical host's minimum degree is generally about k/2, not the edge count of the residual forest obtained by deleting a low-degree target vertex. This is the existing exact degree-budget obstruction, not a matter of rounding.
* The canonical Hall block is closed under rematching **for one fixed core**. Section 5 shows why combining blocks from different core embeddings is not automatically an incidence obstruction. A T-free cross-core exchange theorem is still needed.
* Saturation bounds the number of completion edges exactly and eliminates normalization slack at the maximum-degree boundary. It does not guarantee the common-list and original/virtual-edge compatibility needed to lift the specified tree.
* In the weighted route, (26) is an exact identity, and (29) is a theorem. The general inequality (33) is still unproved. No scalar cut reformulation is substituted for that shape-dependent step.

I also tested the stronger idea that arbitrary nontrivial rooted forests might satisfy a disjoint-reservoir theorem like Theorem 3, with a reservoir of size `|T_i|` for component i. A separate exact exploratory probe found no failure in 992,532 two-component small-host/reservoir tests. **I did not prove that stronger theorem, and do not use it.** Even its truth would not by itself supply the missing critical-host forest edge budget.

Thus the report contains proved progress toward nonlocal exchange and Hall-defect packing, but **not a closed global ES argument**. It would be incorrect to formalize `erdos_548` using any of the missing selection statements as though they had been established.

---

## 8. Verification and files

Run:

```text
python3 Submission/GlobalESFreshAttemptChecks.py
```

The reproducible exact audit, recorded in `GlobalESFreshAttemptChecks.log`, passed:

* **17,092** prescribed-independent-root embeddings on all relevant graph-atlas hosts through seven vertices, using 31 rooted-forest profiles and an independent embedding backtracker;
* **255,467** exhaustive disjoint-reservoir star packings, plus **1,115** additional different-list packings and **1,200** weighted-Hall/allocation equivalences;
* **2,519** strictly potential-decreasing root exchanges in **2,518** instances requiring an exchange, including the explicit `6 -> 3 -> 2` example;
* a star-packing example where the root candidates have degree e but all noncandidate vertices have degree one;
* the adjacent-root, isolated-independent-root, and weighted-Hall-with-isolate counterexamples;
* **1,291** deficiency-one Hall systems, checking intersection/union closure, the canonical minimum, alternating reachability, and the exact set of possible missing-leaf parents;
* **47,424** proper/full subset-type calculations for the critical split family, and **181** deficient core embeddings with independently checked full-tree repairs;
* six exact nonresistant-union audits for the canonical Hall blocks;
* **742** exact critical-host covariance identities, of which **429** have negative covariance; the root messages and occupied-nonneighbor mass were computed directly from occupied-set polynomials, independently of the full-tree partition sum;
* **3,000** exact degree-sequence audits of the star Chebyshev inequality, the two displayed failed scalar shortcuts, and the root-selection nonmatroid example;
* **666,596** exact saturation-surplus/parity identities.

The checks are safeguards for the proofs and formulas, **not finite evidence asserted to prove unrestricted ES**. The exploratory general-reservoir probe and the larger prior CW searches are not used as premises.

Files added for this attempt:

* `Submission/GlobalESFreshAttempt.md`
* `Submission/GlobalESFreshAttemptChecks.py`
* `Submission/GlobalESFreshAttemptChecks.log`

All shared Lean-file hashes agree with the pre-attempt audit. `Spec.lean` retains SHA-256

```text
674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103
```

**Final outcome: genuine universal packing and charging progress, but the complete exact Erdős–Sós proof remains unresolved in this attempt.**
