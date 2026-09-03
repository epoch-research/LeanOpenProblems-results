# Weighted root-list Hall is sufficient for nontrivial forests

## Outcome and scope

**The proposed theorem is true.** This report gives a complete mathematical proof, including arbitrary rooted shapes and mixtures of root-centered stars and nonstars. It also proves the arbitrary-different-lists version with every list of size at least the whole forest order, **including isolated components**, and the resulting cost-free connected-core extension theorem.

The main new ingredient is stronger than the requested result:

> **Rooted-star dominance.** In a host of minimum degree at least `e = sum_i e_i`, if stars with `e_i` leaves can be packed at specified distinct centers `x_i`, then arbitrary nontrivial `e_i`-edge trees, with their specified roots at those same centers, can be packed there.

A protected-center version of the star Hall exchange proves this by induction on the **total edge count**. The number of components can increase in the induction. This avoids the list-survival obstruction in a direct clique-reservoir induction: convert the lists to a star certificate first, and subsequently preserve the original root images while allowing complete leaf rematchings.

The proof is not an inference from the previous 992,532 tests, and does not assume independent root images. It does not use Erdős–Sós, a smaller-case version of Erdős–Sós, CL, or the unmarked forest theorem as a premise. It gives an alternative proof of the relevant common-list and independent-prescribed-root results.

**Unrestricted Erdős–Sós remains unproved here.** The adaptive-core consequences below have explicit hypotheses. Criticality alone does not force the coarse connected-core degree budget used in one of these consequences; Section 9 gives an exact literal-bound critical example demonstrating that limitation.

This is a mathematical proof with an independently audited constructive implementation, **not a new Lean formalization**. No `WeightedListForest.lean` with unfinished obligations has been created. `Submission/Spec.lean` and every pre-existing shared Lean file are unchanged.

---

## 1. Statement and notation

Graphs are simple and undirected. We write the proof for finite hosts; the finite-forest results also hold in arbitrary hosts, as explained at the end of Section 4. All density applications and computational audits concern finite graphs. An embedding means an injective homomorphism, not an induced embedding. Trees and their vertices may be regarded as labelled, so all root prescriptions below refer to the specified target vertices.

Let

\[
 F=\bigsqcup_{i\in I}T_i,\qquad
 r_i\in V(T_i),\qquad
 a_i=e(T_i)\ge1,
\]

and put

\[
 e=\sum_{i\in I}a_i,\qquad
 m=\sum_{i\in I}(a_i+1)=e+|I|.
\]

Give root `r_i` an arbitrary list `L_i subset V(H)`.

### Theorem WH — weighted root-list Hall

If `delta(H) >= e` and

\[
 \left|\bigcup_{i\in Q}L_i\right|
 \ge\sum_{i\in Q}(a_i+1)
 \qquad\text{for every }Q\subseteq I,                 \tag{1}
\]

then F embeds in H with the image of `r_i` in `L_i` for every i.

The empty family is allowed and is immediate. The hypothesis `a_i >= 1` is essential for this particular degree threshold and list condition; see Section 5.

Weighted Hall is equivalent to the existence of pairwise disjoint reservoirs

\[
 A_i\subseteq L_i,\qquad |A_i|=a_i+1.                 \tag{2}
\]

Indeed, apply ordinary Hall to `a_i+1` labelled copies of list i. For a subset of these labelled slots, let Q be the set of list indices represented. Its number of slots is at most the right side of (1), and its neighborhood is the union on the left side. Conversely, reservoirs (2) immediately imply (1).

This equivalence concerns **reservoir allocation**, not necessity of (1) for a particular rooted forest embedding. Condition (1) is a sufficient embedding condition and need not be necessary.

---

## 2. The protected-center star lemma

This is the exchange lemma needed to make the induction work with mixed component shapes.

### Lemma 1 — frozen centers and flexible reservoirs

There are two disjoint sets of indices, J and I.

* For `j in J`, a center `x_j` is prescribed and a positive leaf demand `a_j >= 1` is given. There is already a star packing at these centers: sets `B_j subset N_H(x_j)` with `|B_j|=a_j`, such that all the sets `{x_j} union B_j` are pairwise disjoint.
* For `i in I`, the center is flexible, its leaf demand is `b_i >= 0`, and it has a reservoir `A_i` of size `b_i+1`. The reservoirs are pairwise disjoint and avoid **every vertex of the initial prescribed-center star packing**, including its leaves.

Put

\[
 E=\sum_{j\in J}a_j+\sum_{i\in I}b_i,
 \qquad q=|\{i\in I:b_i=0\}|.
\]

Suppose every prescribed center and every member of every flexible reservoir has degree at least `E+q` in H.

Then all these stars can be packed simultaneously, keeping each prescribed center at `x_j` and choosing flexible center i in `A_i`.

**Only the prescribed centers are fixed. Their old leaf sets need not be preserved.** Flexible zero-demand stars are allowed in this lemma, with the indicated q-unit degree allowance.

### Proof

Choose one flexible center `x_i in A_i` for each i. All centers are distinct. Let R be their set, including the prescribed centers. Among these finitely many choices minimize

\[
 \Phi(R)=e_H(R).
\]

Try to match all leaf slots into `V(H)-R`. If this fails, Hall gives subsets `J' subset J` and `K subset I`, with nonzero total demand, such that

\[
 Y=\bigcup_{t\in J'\cup K}(N_H(x_t)\setminus R),
 \qquad
 |Y|\le a(J')+b(K)-1,                                \tag{3}
\]

where `a(J')=sum_{j in J'} a_j` and similarly for b. To obtain this form from an arbitrary deficient set of labelled leaf slots, include all slots belonging to every represented center; their neighborhoods do not change.

For every `j in J'`, the original set `B_j` is still outside R: it avoids prescribed centers and **all** flexible reservoirs. It is contained in Y. These original leaf sets supply `a(J')` distinct vertices of Y outside every flexible reservoir.

Consequently K is nonempty. Moreover, with

\[
 A_K=\bigcup_{i\in K}A_i,
\]

we have

\[
 |Y\cap A_K|\le |Y|-a(J')\le b(K)-1.
\]

The set `A_K` has `b(K)+|K|` vertices and contains exactly |K| members of R. Hence there is

\[
 z\in A_K\setminus(R\cup Y).                          \tag{4}
\]

Let `i in K` be its unique reservoir index. By (4), z is adjacent to none of the current centers indexed by `J' union K`.

Write `t=|J|+|I|` and `Q=J' union K`, interpreting the index union as disjoint. For the old flexible center `x_i`, (3) and its degree bound give

\[
 \begin{aligned}
 d_{H[R]}(x_i)
 &\ge E+q-|Y|\\
 &\ge E+q-a(J')-b(K)+1\\
 &=a(J\setminus J')+b(I\setminus K)+q+1\\
 &\ge t-|Q|+1.                                      \tag{5}
 \end{aligned}
\]

The last inequality uses positivity of every prescribed demand and of every nonzero flexible demand; the q units cover all zero-demand flexible centers outside Q.

Replace `x_i` by z. The new center is in its own reservoir and distinct from the others. It has at most `t-|Q|` neighbors among the other centers, whereas the old one has at least `t-|Q|+1` by (5). Edges among unchanged centers are unaffected. Therefore this replacement strictly decreases `Phi`, contradicting minimality.

The leaf matching must exist. Use its matched vertices for the leaves. This proves the lemma. **QED.**

### Constructive form

One need not find a global minimum initially. Start with any reservoir representatives. Whenever a leaf matching fails, extract its Hall witness and perform the replacement just proved. The nonnegative integer potential decreases, so at most `binom(t,2)` replacements are possible before matching succeeds.

For `J=empty` and all `b_i>=1`, this is precisely the different-list star mechanism of `GlobalESFreshAttempt.md` Section 4. The additional invariant here is that the **initial frozen leaf packing remains a Hall certificate disjoint from every flexible reservoir**, even while new leaf matchings are tried.

---

## 3. Rooted-star dominance

### Theorem 2 — replace stars by arbitrary rooted trees

Let `T_i` be nontrivial rooted trees with `a_i` edges, and let `e=sum_i a_i`. Suppose `delta(H)>=e`. Let the roots have distinct prescribed images `x_i`. Assume there are sets

\[
 B_i\subseteq N_H(x_i)\setminus R,
 \qquad |B_i|=a_i,
 \qquad R=\{x_i:i\in I\},                             \tag{6}
\]

with the B_i pairwise disjoint.

Then F embeds in H with `r_i -> x_i` for every i.

Thus the external-neighborhood Hall condition

\[
 \left|\bigcup_{i\in Q}(N_H(x_i)\setminus R)\right|
 \ge\sum_{i\in Q}a_i\quad(Q\subseteq I)                \tag{7}
\]

is sufficient for every rooted forest with these component orders. Ordinary Hall converts (7) to (6).

### Proof by strong induction on e

If every component is a root-centered star, (6) is already the desired packing. The empty forest is also immediate.

Otherwise choose a component T that is **not** a root-centered star. Denote its root by r, its prescribed image by x, its edge count by a, and its leaf reservoir from (6) by B. Write

\[
 d=d_T(r).
\]

Delete r from T. Its d components are rooted at the distinct neighbors of r. Let these rooted branches be `C_1,...,C_d`, and let q of them be singletons. Equivalently, q is the number of leaf neighbors of r in T.

Since T is not a root-centered star, r has at least one neighbor that is not a leaf. Therefore

\[
 d\ge q+1.                                           \tag{8}
\]

Also

\[
 \sum_{\ell=1}^{d}|C_\ell|=a,
 \qquad
 \sum_{\ell=1}^{d}e(C_\ell)=a-d.                      \tag{9}
\]

Partition B arbitrarily into disjoint sets

\[
 A_\ell\subseteq B,
 \qquad |A_\ell|=|C_\ell|=e(C_\ell)+1.                \tag{10}
\]

Work temporarily in `H'=H-x`.

* The other original component centers are **frozen**, with their original star leaf sets from (6).
* Branch `C_ell` has a **flexible** center in `A_ell` and star leaf demand `e(C_ell)`.
* The old frozen stars avoid the whole of B, hence all reservoirs (10).
* Exactly q flexible demands are zero.
* The sum of the new star leaf demands is
  \[
  E=(e-a)+(a-d)=e-d<e.
  \]

The degree budget required by Lemma 1 holds:

\[
 \delta(H')\ge e-1
             \ge(e-d)+q
             =E+q,                                   \tag{11}
\]

using (8). Apply that lemma. It gives a new star packing, preserving every other original root image and placing the root of each branch in its own `A_ell subset B`.

Now remove from `H'` the q center images of the singleton branches. Call the resulting host `H''`. The new star packing on the nontrivial components avoids those vertices, since all of its leaves are matched outside the entire new center set. Moreover,

\[
 \delta(H'')\ge e-1-q\ge e-d=E.                       \tag{12}
\]

The nontrivial forest consisting of the other original components and the nontrivial branches has exactly E edges. It comes with the star certificate just constructed. The induction hypothesis therefore replaces these stars by those rooted trees, **preserving every one of their new centers**.

Restore the singleton branch images and put `r -> x`. Every branch root is still in its reservoir `A_ell subset B subset N_H(x)`, so every edge formerly incident with r is present. All images are distinct: the recursive embedding was in `H''`, which excluded x and the singleton images. The other original roots were frozen in Lemma 1 and preserved by induction.

This is the required rooted embedding of the original forest. **QED.**

### The two invariants that close the argument

1. **The outer recursion decreases total edges, not components.** Replacing T by its branches can increase the component count. The strict decrease is `e -> e-d`.
2. **Original root lists need not survive vertex deletion.** They are used only to obtain the first star certificate. Thereafter original roots are fixed. The new branch reservoirs are carved from the old star leaves, so they are clean with respect to every frozen star. Frozen leaves may be completely rematched.

The q isolated branches are not being ignored or treated by an invalid prescribed-isolate theorem. Lemma 1 explicitly pays q units, and (8) proves that deleting a nonstar root releases enough budget to pay them. This is the step that handles arbitrary mixtures of stars and nonstars without an extra permanent star cost.

As a useful check, independence is sufficient for (7): if R is independent, every nonempty union on the left has size at least e. Theorem 2 thus recovers the independent-prescribed-root theorem without invoking its clique argument. Independence is **not** assumed in Theorem 2.

---

## 4. Proof of weighted Hall, and an algorithm

Allocate disjoint reservoirs (2) by ordinary Hall. Apply Lemma 1 with no frozen centers, flexible demands `b_i=a_i`, and `q=0`. Its degree threshold is exactly e. It produces centers

\[
 x_i\in A_i\subseteq L_i
\]

and a star certificate (6). Apply Theorem 2, preserving those centers. The resulting F-copy respects all original root lists. This proves Theorem WH. **QED.**

In particular, a root transversal minimizing `e_H(R)` among the choices `x_i in A_i` always supports the star certificate and hence the whole rooted forest. Such a transversal need not be independent.

The proof is constructive:

1. one matching allocates the original reservoirs;
2. Hall-defect exchanges obtain the first star certificate;
3. each nonstar-root substitution uses another protected-center Hall exchange;
4. recursion ends in actual root-centered stars.

There are at most e substitutions, and each invokes at most `binom(m,2)+1` leaf-matching attempts. Thus this is a polynomial matching-based construction, not a backtracking tree-embedding oracle or a naive greedy extension of fixed branch images.

The clique-reservoir approach suggested by the earlier work is therefore not needed in the final proof. The root-set potential is combined instead with a star-certificate substitution induction; this removes precisely the list-survival difficulty that blocked direct CL induction.

**Arbitrary-host variant.** Theorem WH, Lemma 1, Theorem 2, and the large-list corollary also hold for an infinite host when the degree bound means that each relevant vertex has at least the specified finite number of neighbors. Hall with a finite left side and possibly infinite right side supplies the finite reservoirs and the needed finite matchings. If a leaf matching fails, its Hall witness Y has size smaller than a finite demand, so Y is finite. All failed-matching degree counts can then be made in the finite set `R union Y`. The root-choice space and its potential are finite, and deleting finitely many vertices loses at most that many neighbors. Thus the same induction applies. No finite induced subgraph of the infinite host with the same minimum degree is assumed.

---

## 5. Different large lists, isolates, and qualifications

### Corollary 3 — arbitrary lists of size at least the forest order

Let F be **any** finite forest, with one root per component, including isolated components. Put `m=v(F)` and `e=e(F)`. If `delta(H)>=e` and every root list has size at least m, then F embeds respecting those lists.

**Proof.** First consider the nontrivial components. Their lists satisfy weighted Hall: for a nonempty subfamily the union contains any one of its lists, so has size at least m, at least the sum of the orders in that subfamily. Apply Theorem WH to this nontrivial forest. Then place isolated components one at a time at unused vertices of their own lists. At every such placement fewer than m vertices are occupied. **QED.**

This proves the arbitrary-different-lists strengthening of CL at the same minimum degree, with no star-count penalty.

### Weighted Hall with isolated components: a sufficient and sharp extra cost

If there are q isolated components, weighted Hall for **all** component orders is sufficient under

\[
 \delta(H)\ge e(F)+q.                                 \tag{13}
\]

Allocate all component reservoirs. Reserve the singleton reservoirs of the isolated components, delete their q vertices, and apply Theorem WH to the remaining forest. Its reservoirs survive and its host has minimum degree at least e(F).

The q-unit allowance in this general statement cannot be uniformly decreased. For any `q>=1`, take `H=K_(q+2)` minus the edge 01. Take F to be one edge and q isolated vertices. Give the edge root list `{0,1}` and give the isolated roots the distinct singleton lists `{2},...,{q+1}`. The lists are already disjoint reservoirs of the required sizes, and

\[
 e(F)=1,\qquad \delta(H)=q=e(F)+q-1.
\]

But the isolated roots occupy all neighbors of both possible edge-root images. No rooted embedding exists. The case q=1 is the earlier `P_3` obstruction.

### Other boundary distinctions

* The uniform common-list size m cannot in general be decreased to `m-1`: for any nontrivial forest with at least two components, use `H=2K_(m-1)` and put every list in the first clique. Then `delta(H)=m-2>=e(F)`, but all m target vertices would have to fit in that clique.
* The candidate-only degree hypothesis from the **star** theorem does not extend to general rooted trees. In three disjoint copies of `P_3`, let L be the three middle vertices. They all have degree `2=e(P_3)` and `|L|=3`, but no `P_3` rooted at an endpoint can start at a member of L. Theorem WH uses the minimum degree of the whole host.
* The star condition (7) is sufficient, not necessary for a particular shape. In two `K_5`s on `0,...,4` and `5,...,9` joined by edge 45, prescribe two endpoint-rooted `P_3`s at 0 and 1. The external root-neighborhood union is `{2,3,4}`, so the two 2-leaf stars cannot be packed. Nevertheless the paths `0-4-5` and `1-2-3` are disjoint rooted copies.
* There is only **one mark per component**. Nothing here asserts the multi-mark theorem refuted in `ForestInterfaceFindings.md`.

---

## 6. Paper application: cost-free connected-core extension

Let T be a k-edge tree and let C be a nonempty, proper, connected vertex set in T. Write

\[
 h=|C|,\quad F=T-C,\quad b=c(F)=e_T(C,V(T)\setminus C).
\]

The equality defining b holds because each component of F has exactly one edge to C. If there were two, the connected subtree on C and the path inside that component would give a cycle.

Consequently

\[
 m=v(F)=k+1-h,
 \qquad e_F=e(F)=k+1-h-b.                             \tag{14}
\]

For a component `T_i` of F, write its unique attachment edge as `u_i r_i`, with `u_i in C`. The root of that component is `r_i`.

Let `psi:T[C] -> G` be any injective homomorphism, and put

\[
 S=\psi(C),\quad H=G-S,\quad
 L_i=N_G(\psi(u_i))\setminus S.                       \tag{15}
\]

### Exact interface corollary

The embedding psi extends to T if:

* `delta(H)>=e_F`, and every list (15) has size at least m; or
* F has no isolated components, `delta(H)>=e_F`, and the lists (15) satisfy weighted Hall with the component-order demands.

This follows directly from Corollary 3 or Theorem WH, respectively. It is stronger than the numerical degree consequence below, since actual degree losses and actual list unions can be used.

### Corollary 4 — boundary-high core extension

Suppose

\[
 \delta(G)\ge k+1-b,                                  \tag{16}
\]

and every boundary vertex of C, meaning every `u in C` with a neighbor outside C, is mapped by psi to a host vertex of degree at least k. Then psi extends to an embedding of all T.

**Proof.** Deleting S loses at most h neighbors at each remaining host vertex, so

\[
 \delta(H)\ge\delta(G)-h\ge k+1-b-h=e_F.
\]

For each list (15), its defining high vertex belongs to S and is not adjacent to itself. Therefore it loses at most `h-1` neighbors when S is removed:

\[
 |L_i|\ge k-(h-1)=k+1-h=m.                            \tag{17}
\]

Corollary 3 embeds F respecting these arbitrary different lists, including any isolated components. Restore psi and all unique attachment edges. **QED.**

The degree condition has **no additional apex-count or bad-star cost**. The h-unit deletion loss cancels the h term in (14). The list bound correctly uses `h-1`, not h. Host chords inside S are allowed; no estimate replaces actual occupied host adjacency by target-core adjacency.

Only boundary vertices of C need high images. Interior core vertices may have low images. The core and its embedding may be chosen adaptively from the host. High images need not be independent, and the core embedding itself is preserved by the extension.

Connectedness of C is important. For a disconnected deleted target set, a surviving component may have several attachment edges and hence several marks; this theorem does not solve that interface.

---

## 7. Precise host-adaptive consequences of critical density

Assume `k>=1`. Suppose

\[
 e(G)=\frac{k-1}{2}|G|+\eta,\qquad \eta>0,
\]

and every proper induced subgraph is `(k-1)/2`-sparse. Put `a=(k-1)/2`. For every nonempty X,

\[
 I_G(X)=e(G)-e(G-X)\ge a|X|+\eta.
\]

In particular,

\[
 \delta(G)\ge\lceil a+\eta\rceil\ge\lceil k/2\rceil,
 \qquad
 X_k(G):=\{v:d_G(v)\ge k\}\ne\varnothing.             \tag{18}
\]

The second assertion follows from the average degree being greater than `k-1`.

### Adaptive core criterion

Define `beta_T(G)` to be the maximum boundary-edge count b over nonempty proper connected target cores C having an embedding into G with every boundary vertex mapped into `X_k(G)`. This maximization allows **both C and its embedding to depend on G**. By (18), singleton cores are available, so `beta_T(G)>=Delta(T)`.

Corollary 4 proves

\[
 \boxed{\delta(G)+\beta_T(G)\ge k+1
        \quad\Longrightarrow\quad T\subseteq G.}      \tag{19}
\]

Thus, in a critical T-free host, every such core would have to satisfy

\[
 b\le k-\delta(G),
 \qquad\beta_T(G)\le k-\delta(G).                     \tag{20}
\]

Using only the universal lower bound in (18), it suffices to have an adaptive core with

\[
 b\ge\lfloor k/2\rfloor+1.                           \tag{21}
\]

This is a proved criterion, **not a proof that such a core always exists**.

### Two adjacent adaptive apices

If `st in E(G)` and both s and t have degree at least k, then for any target edge uv,

\[
 \boxed{\delta(G)+d_T(u)+d_T(v)\ge k+3}               \tag{22}
\]

suffices to embed T with `u -> s, v -> t`.

Take `C={u,v}`. Its boundary count is `d_T(u)+d_T(v)-2`, and apply Corollary 4. In a critical host, the readily checkable sufficient condition is

\[
 d_T(u)+d_T(v)\ge\lfloor k/2\rfloor+3.                \tag{23}
\]

Here the target edge and the high host edge may both be chosen adaptively. Existence of a high host edge is **not** inferred from criticality.

### High endpoints connected through low interior vertices

More generally, let a path in T have endpoints u,v and all its interior vertices of target degree two. If G has a simple path of the same length with high endpoints, then (22) again suffices to extend a path-to-path embedding to all T.

Indeed, this path core has boundary count `d_T(u)+d_T(v)-2`, independent of its length. Only its endpoints can be boundary vertices. Thus high host apices may be joined through low host vertices; high-high adjacency is not required in this variant. Existence of the required pair of paths remains an explicit hypothesis.

### An explicit numerical star-core profile

For a nonnegative integer q, let

\[
 B_q(T)=\max_{u,\ J\subseteq N_T(u),\ |J|=q}
 \left(d_T(u)+\sum_{v\in J}d_T(v)-2q\right),          \tag{24}
\]

omitting q if no such J exists. If `G[X_k(G)]` has a star with q leaves and

\[
 \delta(G)+B_q(T)\ge k+1,
\]

then T embeds. Map the corresponding target star core into that high-host star, then apply Corollary 4. If this core is already all of T, its embedding itself is the conclusion. Maximizing over

\[
 0\le q\le\min\{\Delta(T),\Delta(G[X_k(G)])\}
\]

gives a host-adaptive sufficient criterion. The q=0 case is the usual one-apex maximum-degree consequence; q=1 is (22). These statements are direct consequences of the proved forest theorem and (18), with no unproved core-selection step.

---

## 8. A fully critical, genuinely different-list two-apex application

Here is an explicit literal-bound critical example illustrating the extension beyond the common-list interface and the full-host one-apex budget.

### Host

Start with a six-vertex clique

\[
 K=\{s,t,c_1,c_2,c_3,c_4\}
\]

and a cycle `y_0 y_1 ... y_15 y_0`. Add all K-to-cycle edges, then delete:

* `s y_j` for `0<=j<=7`;
* `t y_j` for `8<=j<=15`.

There are no other vertices or edges. Then

\[
 n=22,\quad e(G)=15+16+96-16=111=5n+1,
\]

and the degrees are

\[
 d(s)=d(t)=13,\quad d(c_i)=21,\quad d(y_j)=7.          \tag{25}
\]

This is the literal density threshold for `k=11`, with surplus one.

**All proper induced sets are 5-sparse.** Let such a set select x clique vertices and a cycle-vertex set Y of size y. Write `ell=e(C_16[Y])` and let D count the deleted cross edges whose endpoints were both selected. Its surplus over five times its order is

\[
 {x\choose2}-5x+(x-5)y+\ell-D.                       \tag{26}
\]

* If `x<=4`, use `ell<=y` and `D>=0` to bound (26) by
  `binom(x,2)-5x+(x-4)y<=0`.
* If `x=5`, at most eight cycle vertices have their deleted cross edge directed to the omitted clique vertex. Hence `D>=y-8`, so `ell-D<=8` and (26) is at most `10-25+8=-7`.
* If `x=6`, then `D=y`, and (26) equals `ell-15`. For a proper vertex subset of a 16-cycle, `ell<=14`. Thus (26) is negative. For the whole graph `ell=16`, giving surplus one as asserted.

This proves full induced criticality, not just a minimum-degree condition.

### Target and extension

Let T have adjacent hubs u,v. At each hub attach two pendant leaves and one path of length three. Thus

\[
 k=11,\qquad d_T(u)=d_T(v)=4,\qquad\Delta(T)=4.
\]

Map the two-vertex core `{u,v}` to `{s,t}`. Its boundary count is b=6. Since

\[
 \delta(G)=7\ge 11+1-6=6,
\]

Corollary 4 completes the copy. The remaining forest consists of **two endpoint-rooted `P_3`s and four isolated components**. Its order is 10 and its edge count is 4.

The two attachment lists are genuinely different:

\[
 L_s=\{c_1,c_2,c_3,c_4,y_8,\ldots,y_{15}\},
\]
\[
 L_t=\{c_1,c_2,c_3,c_4,y_0,\ldots,y_7\}.
\]

Each has size 12, whereas their intersection has size only four, below the forest order ten. Applying common-list CL to that intersection would not justify this extension.

An explicit copy sends the long u-leg to `y_8-y_9-y_10`, its two short leaves to `y_11,y_12`, the long v-leg to `y_0-y_1-y_2`, and its two short leaves to `y_3,y_4`, with the hubs at s,t.

For every high vertex z in this host, `delta(G-z)=6`. The full-host one-apex CL condition at any target vertex would require at least `k-Delta(T)=7`, so it does not apply. This is only a comparison of these specified full-host certificates, not an assertion that no other older theorem or subgraph argument could embed this particular T.

---

## 9. Why the global Erdős–Sós step is still separate

The forest generalization is now proved. What does **not** follow is that every critical host and every target admit a boundary-high core satisfying the coarse budget (16).

Here is a rigorous limitation of that automatic-selection claim, even at the literal density threshold. For `r>=2`, set

\[
 k=2r+1,\qquad b_0=r(r+1)+1,\qquad
 G=K_{r+1,b_0}.
\]

Then

\[
 e(G)=(r+1)b_0=r|G|+1,
 \qquad\delta(G)=r+1.                                \tag{27}
\]

Every proper induced subset is r-sparse: if its two part counts are x,y and `x<=r`, then `xy<=r(x+y)`; if `x=r+1`, properness gives `y<=b_0-1=r(r+1)`, so

\[
 xy-r(x+y)=y-r(r+1)\le0.
\]

Take T to be the `k`-edge path. Every proper connected target core is an interval and has at most two boundary edges. Thus (16) would require

\[
 \delta(G)\ge k+1-b\ge2r>r+1,
\]

which is impossible. This excludes **every** core from that particular numerical certificate, before any host embedding or high-boundary issue is considered. Yet T certainly embeds in G, using `r+1` vertices in each bipartition class.

This is not an Erdős–Sós counterexample. It also does **not** refute the stronger exact interface from Section 6: actual deletion losses can be smaller than h, so the exact residual-degree test can succeed when the coarse budget fails. It shows why (19)–(21) alone cannot be asserted to exhaust all critical hosts and targets.

For a general tree, every component outside a connected core contains a target leaf, so its boundary count is at most the number of target leaves. Thin or heavily subdivided targets therefore retain the familiar residual-edge-budget difficulty at critical minimum degree near k/2. No global proof selecting suitable exact interfaces, or combining this result with other terminal mechanisms to exhaust all targets and hosts, is claimed here.

---

## 10. Verification and artifacts

The mathematical proofs are Sections 2–4. The code is a safeguard for the Hall inequalities, recursive invariants, and applications, not a substitute for those proofs.

Files:

* `Submission/WeightedListForestFindings.md` — this report;
* `Submission/WeightedListForestChecks.py` — matching-based constructive implementation and independent audits;
* `Submission/WeightedListForestChecks.log` — completed reproducible audit output.

Run from `/workspace/leanproject`:

```sh
python3 Submission/WeightedListForestChecks.py --random 3000
```

The construction uses no tree-embedding backtracker. `protected_star_packing` implements Lemma 1, checking every Hall-defect inequality and every strict potential decrease. `replace_stars` implements the induction in Theorem 2 and checks both degree budgets (11)–(12), root preservation, all target edges, and global injectivity at every return. Independent backtracking is used only in the audit layer.

The full audit covers:

* **317,614** constructive disjoint-reservoir instances on graph-atlas hosts through seven vertices, with the 31 two-/three-component rooted-forest profiles used by the audit;
* **96,032** prescribed-center star-dominance instances, also independently checked by fixed-root backtracking;
* **3,000** additional arbitrary-list instances on deeper, larger rooted forests and repaired clique/independent blow-up hosts;
* **750** arbitrary-large-list cases including isolated components;
* **500** connected-core extension instances with their degree and attachment-list hypotheses checked;
* **4,194,303** proper vertex-set calculations for the 22-vertex critical two-apex example;
* the critical bipartite family in Section 9 and the sharp boundary counterexamples in Section 5.

The final log records **4,278** strictly decreasing root exchanges, including **399** with frozen centers, and **125,412** nonstar-root substitutions. It also records changed frozen leaf sets and isolated-branch substitutions. An explicit recursive example has one frozen center, two isolated child branches, and potential `6 -> 3`; its edge budget decreases `5 -> 2` while exactly three host vertices are deleted. Thus the key new mixed case is exercised directly, not merely inferred from star-only tests.

All pre-existing shared Lean hashes match the pre-task snapshot. In particular `Submission/Spec.lean` retains SHA-256:

```text
674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103
```

**Final mathematical outcome:** weighted root-list Hall for arbitrary nontrivial forests is proved; arbitrary lists of size at least the forest order work at the same minimum degree even with isolates; the connected-core/adaptive-apex extension has no additional star or apex cost. The unrestricted global Erdős–Sós selection/degree-budget step remains separate and unresolved.
