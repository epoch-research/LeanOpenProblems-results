# High leaf-parents in incidence-critical hosts: proved exclusions and the remaining gap

## Status

**The general question is not settled here.** I obtained neither a counterexample in the requested critical class nor a proof for all its nonbipartite, core-free members. In particular, I do **not** claim the conditional strengthening follows from merely knowing that the target tree embeds.

There are, however, rigorous positive results that eliminate whole proposed sources of counterexamples:

1. **Every bipartite incidence-critical host has the high-leaf-parent property.** This is not restricted to complete bipartite graphs. A stronger smaller-color-class rooted statement is proved below.
2. **A nonempty `(k-1)`-core gives the property for every choice of the deleted leaf**, not just unrooted universality.
3. **Every complete multipartite graph of average degree greater than `k-1` has the property.** Criticality is unnecessary for this result.
4. **Every critical host of the form `K_a ∨ (a disjoint union of cliques)` has the property.** Thus complete split graphs and these clique-wing/cone models are not counterexamples.
5. The already-proved exact-apex theorem gives the property whenever a leaf-parent has degree at least `floor(k/2)+1`; in particular it covers every tree with maximum degree above `k/2`.

These are mathematical proofs, not deductions from positive numerical tests. The surviving general case is specified in Section 8. No Lean file or specification was edited; no new Lean formalization is claimed.

All graphs are finite and simple, trees have `k>=1` edges, and embeddings are non-induced injective homomorphisms.

## 1. The two embedding formulations and their exact logical relation

Write

\[
 r=(k-1)/2,\qquad e(G)=r|G|+\eta,\quad \eta\in\{1/2,1\},
\]

and require `e(G[S])<=r|S|` for every proper induced vertex set `S`. Let

\[
 H=\{v:d_G(v)\ge k\},\qquad P(T)=\{p:p\text{ is adjacent to a leaf of }T\}.
\]

For **any** host graph, the following two statements are equivalent:

* There are a leaf `ell`, its parent `p`, and an embedding `f:T-ell -> G` with `f(p) in H`.
* There is an embedding `F:T -> G` with `F(P(T)) intersect H` nonempty.

Indeed, `T-ell` occupies `k` vertices. At most `k-1` of them are neighbors of `f(p)`, so degree at least `k` supplies a fresh neighbor for `ell`. The converse is restriction of a full copy.

Consequently, if `E(G,T)` means ordinary containment and `P(G,T)` denotes either equivalent high-parent condition, the proposed universal conclusion is precisely

\[
 \bigl[\forall G,T\text{ critical}:E(G,T)\bigr]
 \quad\textbf{and}\quad
 \bigl[\forall G,T\text{ critical}:E(G,T)\Rightarrow P(G,T)\bigr].
\]

The first bracket is the critical-host form of ES. The second is the conditional strengthening in the question. To demonstrate an obstructed strengthening, one really must exhibit an already-embedded tree with **every** leaf-parent excluded from **every** high host vertex. None of the existing maximum-root examples does this.

### Basic critical-host facts

Such a host is connected, has `n>=k+1`, and has a high vertex. Otherwise a component would be a proper positive witness, simplicity would prohibit positive density, or the degree sum would be at most `(k-1)n`, respectively. Also

\[
 d_G(v)\ge r+\eta,\qquad \delta(G)\ge\lceil k/2\rceil.
\]

The exact high/low budget is

\[
 \boxed{\sum_{v\in H}(d_G(v)-k+1)
       -\sum_{v\notin H}(k-1-d_G(v))=2\eta.}       \tag{1}
\]

This identity is useful below, but by itself is not a theorem about allowable tree roles.

## 2. Bipartite critical hosts: a full positive theorem

**Theorem.** Let `G` be bipartite and incidence-critical for `k`. Let `T` have color classes `A,B`, with `alpha=|A|<=beta=|B|` and `alpha+beta=k+1`. There is a high vertex `s` such that **every prescribed vertex `u in A`** can be mapped to `s` in a full `T`-copy. The vertex `s` and the construction may depend on `G` and the color-class sizes; `s` is not prescribed to be a maximum-degree host vertex.

### Proof: asymmetric peeling with a high vertex retained

Choose the host bipartition `X,Y` with `|X|<=|Y|`. For an induced vertex set `C`, put

\[
 q(C)=e_G(C)-(\beta-1)|C\cap X|-(\alpha-1)|C\cap Y|.
\]

Initially

\[
 q(V(G))=\eta+\frac{\beta-\alpha}{2}(|Y|-|X|)>0.       \tag{2}
\]

Repeatedly delete an `X`-vertex of current degree at most `beta-1`, or a `Y`-vertex of current degree at most `alpha-1`. Each deletion does not decrease `q`. The process therefore stops at a nonempty induced set `C` with `q(C)>0` and

\[
 d_{G[C]}(x)\ge\beta\ (x\in C\cap X),\qquad
 d_{G[C]}(y)\ge\alpha\ (y\in C\cap Y).               \tag{3}
\]

Write `x=|C intersect X|`, `y=|C intersect Y|`. **Crucially, `x<=y`.** If `x>y`, then

\[
 (\beta-1)x+(\alpha-1)y
 =r(x+y)+\frac{\beta-\alpha}{2}(x-y)\ge r(x+y).
\]

Together with `q(C)>0`, this makes `C` a positive induced witness. It cannot be proper by criticality, and it cannot be all of `G` because the original host sides were chosen with `|X|<=|Y|`. This proves `x<=y`, including the balanced-color case.

Now

\[
 e_G(C)>(\beta-1)x+(\alpha-1)y
        =(k-1)x+(\alpha-1)(y-x)\ge(k-1)x.             \tag{4}
\]

Since every edge of `G[C]` has exactly one endpoint in `C intersect X`, some `s in C intersect X` has `d_{G[C]}(s)>=k`. In particular `s` is high in the original host. Notice that (4) actually gives high degree **inside the retained core**.

Start a colored greedy embedding of `T` at `u -> s`, using (3). When adding a `B`-vertex, at most `beta-1` positions in `C intersect Y` have been used, whereas its parent's degree into that side is at least `beta`. The symmetric assertion uses `alpha` for an `A`-vertex. Thus the whole rooted tree embeds. QED.

### Why this gives a leaf-parent

Every smaller tree color class contains a leaf-parent. If `A` contained none, there would be no leaf in `B`, so

\[
 k=\sum_{v\in B}d_T(v)\ge2\beta\ge\alpha+\beta=k+1,
\]

a contradiction. Choose `u in A intersect P(T)` in the theorem.

**Implications.** This rules out *all* bipartite critical constructions, including noncomplete ones, as counterexamples to either version of the question. It also explains why the old critical wing construction cannot refute joint selection: the high vertex supplied on the correct colored side can be an `A_i` vertex, not the distinguished maximum-degree apex.

Criticality was used for a specific purpose: it prevents a positive asymmetric core from having its side sizes reversed. Ordinary unrooted bipartite universality alone would not justify the high-root conclusion.

## 3. Nonempty `(k-1)`-core: every leaf works

**Theorem.** If a critical `G` has a nonempty `(k-1)`-core `Q`, then for every leaf `ell` of every `k`-edge tree, `T-ell` embeds with its parent at a high host vertex.

First, `Q` contains an ambient high vertex. If it did not, every vertex of `Q` would have both internal and ambient degree exactly `k-1`, and there would be no edge from `Q` to its complement. Connectedness forces `Q=G`, contradicting the strict degree-sum surplus.

Choose such an `s in Q`. For any specified leaf `ell` and parent `p`, the rooted tree `T-ell` has `k-1` edges. Minimum degree `k-1` in `Q` lets it be embedded greedily with `p -> s`. Its image occupies only `k` vertices, so ambient degree at least `k` extends it to `T`.

This argument also handles a `K_k` core with a boundary edge: its inside boundary endpoint is high. There is no need to settle a separate high-parent problem after applying the old core terminal.

## 4. A parent-retaining independent selection lemma

This supplies the flexible tree choice used in the next two host classes.

**Lemma.** Let `A` be a smaller color class of a `k`-edge tree, let `p in A` be any nonleaf, and let `1<=h<|A|`. There is an independent set `U subset A`, containing `p`, such that

\[
 |U|=h,\qquad \sum_{u\in U}d_T(u)\ge2h.              \tag{5}
\]

If `A` has at least `h` nonleaves, choose `h` of them including `p`. Otherwise include all its `j<h` nonleaves and fill with leaves. In the latter case the selected degree sum is

\[
 k-(|A|-h)=k-|A|+h\ge |A|-1+h\ge2h,
\]

because `k>=2|A|-1` and `|A|>=h+1`. Independence is automatic.

Thus the existing two-for-one complete-interface argument can retain **any nonleaf in the smaller color class**, not just a maximum-degree vertex of that class. In particular, it can retain a leaf-parent.

We use the already-proved forest theorem (a consequence of CL with the entire host as allowed set):

> If `|J|>=|F|` and `delta(J)>=e(F)`, then every forest `F` embeds in `J`.

No unrestricted ES statement is being assumed here.

## 5. Complete multipartite hosts: positive density is enough

**Theorem.** Every complete multipartite graph with `2e(G)>(k-1)n` has a `T`-copy with a high leaf-parent, for every `k`-edge tree `T`.

The case `k=1` is immediate. Let `k>=2`, put `t=n-k>=1`, and let the part sizes be `c_i`. A vertex in part `i` is high exactly when `c_i<=t`. Let `H` be the union of all such parts and `h=|H|>0`.

Let `A,B` be the tree colors, `alpha<=beta`, and choose `p in A intersect P(T)`.

**Case 1: `h>=alpha`.** Add entire high parts until their total size first reaches `alpha`. Their union `X` satisfies

\[
 \alpha\le |X|\le\alpha+t-1=n-\beta.
\]

The complementary union of parts has at least `beta` vertices, and all edges across this partition are present. Put `A` into `X` and `B` into its complement. In particular `p` maps to a high vertex.

**Case 2: `h<alpha`.** Every low part has size at most `t+h`. To prove this, the total high surplus over degree `k-1` is

\[
 \sum_{c_i\le t}c_i(t+1-c_i)\le ht.
\]

A low part of size `b>=t+h+1` would alone contribute deficit

\[
 b(b-t-1)\ge bh>ht,
\]

contradicting the strict positive degree sum. Therefore, for `L=V(G)-H`,

\[
 \delta(G[L])\ge(n-h)-(t+h)=k-2h.                  \tag{6}
\]

Choose `U` by (5), with `p in U`. The forest `F=T-U` has

\[
 e(F)=k-\sum_{u\in U}d_T(u)\le k-2h,
 \qquad |F|=k+1-h\le n-h=|L|.
\]

Embed `F` in `G[L]` by the forest theorem. Map `U` injectively onto `H`. Every edge from `U` to `F` is supplied by the complete interface between the union of high parts and the union of low parts; there are no tree edges inside `U`. This is a full embedding with `p` high. QED.

The deficit budget is genuinely used here; the argument does not assume that every high-root prescription is possible in arbitrary critical graphs.

## 6. Clique-join / split / clique-wing models

**Theorem.** Suppose a critical host has the form

\[
 G=K_a\vee\bigl(K_{b_1}\mathbin{\dot\cup}\cdots\mathbin{\dot\cup}K_{b_q}\bigr),
 \qquad a,q\ge1,\quad b_i\ge1.
\]

Then every nonleaf in the smaller color class of `T` can be mapped to **any prescribed vertex of the `K_a`**, in a full `T`-copy. These apex vertices are all high.

Let `S` be the `a`-clique. Deleting an entire outside clique is a proper induced-set test, so for each `i`,

\[
 a b_i+\binom{b_i}{2}>r b_i.
\]

Consequently

\[
 b_i>k-2a,\qquad\delta(G-S)=\min_i(b_i-1)\ge k-2a. \tag{7}
\]

If the smaller tree color class has size at most `a`, put it in `S`; put the other class in arbitrary remaining positions. All necessary edges are present, including edges to unused positions of the apex clique.

Otherwise choose `U` of size `a` by (5), including the desired nonleaf. Embed `T-U` in `G-S` using (7) and the forest theorem, then map `U` into `S` with the prescribed root image. The order inequality is `|G-S|>=k+1-a=|T-U|`.

This includes complete split graphs (`b_i=1`) and joins of a clique with larger clique components. It does **not** claim a result for every nonuniform split graph whose cross edges are incomplete.

## 7. Exact-apex coverage and the exact low-parent alternative

### A further proved exclusion

Let `d=max{d_T(p):p in P(T)}`. If

\[
 d\ge\lfloor k/2\rfloor+1,
\]

then for any high `s`,

\[
 \delta(G-s)\ge\lceil k/2\rceil-1\ge k-d.
\]

The existing exact-apex theorem embeds a corresponding leaf-parent at `s`.

Every vertex of tree degree greater than `k/2` is a leaf-parent: if all its neighbors were nonleaves, each branch would use at least two edges, giving `k>=2d_T(v)`. Thus a counterexample must also have `Delta(T)<=floor(k/2)`.

### The weakest pointwise extension disjunction, with no density loss

For a particular embedding `f:T-ell -> G`, set `s=f(p)` and let

\[
 M=|\{v\in f(V(T-\ell))\setminus\{s\}:sv\notin E(G)\}|.
\]

There are exactly `k-1` other occupied positions. Therefore the number of fresh neighbors is exactly

\[
 |N_G(s)\setminus f(V(T-\ell))|
   =M-\bigl(k-1-d_G(s)\bigr).                      \tag{8}
\]

Hence this partial copy extends **if and only if**

\[
 \boxed{d_G(s)\ge k
 \quad\text{or}\quad
 \bigl(d_G(s)\le k-1\ \text{and}\ M\ge k-d_G(s)\bigr).} \tag{9}
\]

The low-parent arm asks for one more occupied nonneighbor than the parent's deficit below `k-1`. It is sharp: equality `M=k-1-d_G(s)` gives zero fresh neighbors. There is no averaging constant or extra edge-density slack in (8)--(9).

Existence of a leaf-deleted copy satisfying this disjunction is **exactly ordinary containment**, not a further rooted strengthening: restrict any full copy for one direction, and extend by (8) for the other. Thus, if a high-parent obstruction is eventually found, (9) is the minimal pointwise relaxation of the final extension certificate. One must permit a low parent with actual unused-neighbor slack, rather than insisting on a high parent.

**Important limitation:** (9) is an exact certificate, not a proved selection/induction theorem for all critical hosts. Nothing here proves that an inductively supplied partial copy satisfies either arm. To retain the exact ES density in a successful disjunctive induction, the unresolved task is to select or reembed a partial copy satisfying (9) under the original critical hypotheses. Raising the density threshold, dropping full criticality to `W_k`, or declaring the low-parent alternative automatic would not solve that task.

## 8. What remains, and what the search does not establish

Any counterexample to the proposed conclusion must simultaneously be:

* a **nonbipartite**, normalized incidence-critical host;
* **`(k-2)`-degenerate**, because its `(k-1)`-core is empty;
* paired with a tree of **maximum degree at most `floor(k/2)`**;
* outside the complete multipartite and critical clique-join classes proved above;
* such that every embedding avoids `H` at every leaf-parent, even though at least one ordinary embedding exists if the aim is to refute the conditional version.

These necessary exclusions are **not** a proof that no counterexample exists.

Exploratory exact checks found no counterexample. In particular, structured nonuniform split generation tested 6,955 normalized critical **instances** (not asserted pairwise nonisomorphic) and 218,516 host/tree pairs not already certified by the scalar exact-apex test. The generated targets were all trees with leaf-parent degrees at most three for `6<=k<=11`, and selected subdivided-spider, double-hub, and three-hub families for `12<=k<=14`. Rooted nonleaf-subtree backtracking followed by exact leaf-slot matching was used. Criticality of a split instance was checked over every subset of its clique, maximizing independently over independent-set vertices, not inferred from minimum degree. This was a finite search, not a theorem about nonuniform split graphs.

The exploratory scripts/logs are in `/tmp/high_leaf_parent/`. Earlier critical 6-cycle blow-up exploration is now superseded by the proof for **all bipartite critical hosts**. The old maximum-root wing and the uniform leaf-count recurrence counterexamples remain non-counterexamples to the present property.

### Independent constructive audit

Run

```
python3 Submission/HighLeafParentChecks.py
```

The checker implements the proved constructions rather than using a general ES oracle. It checks the independent selection lemma, asymmetric high-core peeling and rooted colored copies, arbitrary-leaf extensions from a `(k-1)`-core, the complete multipartite two-case construction, critical clique-join constructions, and the exact identity (8). Its forest routine is the existing constructive CL implementation. Every produced full copy is checked for injectivity and every tree edge is checked in the original host.

It also checks the old `k=19` critical-wing example explicitly: the unique degree-four tree vertex is sent to an appropriate high `A_i` vertex, **not** to the forbidden maximum-degree apex.

Results are recorded in `Submission/HighLeafParentChecks.log`: **all checks pass**, including 17,739 explicitly verified full embeddings, 9,135 parent-containing independent selections, 1,246 prescribed smaller-color roots at high vertices, 637 arbitrary-leaf core extensions, and 3,968 exact leaf-extension identities. The 25 asymmetric cores include genuine peeling (20 vertex deletions). These audits support the proofs; they do not settle the residual case above.

`Spec.lean` remains unchanged, SHA-256:

```
674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103
```

**Bottom line:** the flexible high-leaf-parent route survives the tested constructions and is proved for several substantial host classes, especially every bipartite critical host. Whether it is always true, or is obstructed even conditional on ordinary containment in a nonbipartite core-free critical host, remains unresolved in this investigation.
