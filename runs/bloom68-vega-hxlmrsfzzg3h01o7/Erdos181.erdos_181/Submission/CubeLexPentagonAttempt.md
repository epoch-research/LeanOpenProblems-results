# Iterated lexicographic pentagon colouring: candidate ruled out

## Outcome — complete for this family

**No.** Let `D_t` be the largest dimension of an ordinary injective monochromatic cube in the stated colouring of `[5]^t`, where `t >= 1` and `N = 5^t`. In fact, **each colour separately** contains the cube of dimension

\[
 d_t=1+\left\lfloor(t-1)\log_2 5\right\rfloor.
\]

Consequently

\[
 \boxed{\quad
 1+\lfloor(t-1)\log_2 5\rfloor
 \ \le D_t\le\lfloor t\log_2 5\rfloor,
 \qquad
 0\le\log_2N-D_t<\log_2 5<2.322.
 \quad}                                                     \tag{1}
\]

Thus the proposed gap cannot tend to infinity. More directly, for every `d >= 1`,

\[
 \boxed{\qquad
 5^t\ge\frac52\,2^d
 \quad\Longrightarrow\quad
 \text{both colours contain an ordinary injective }Q_d.
 \qquad}                                                    \tag{2}
\]

Any cube-avoiding sequence from this family therefore has `N/2^d < 5/2`. This is a theorem about this family, **not** an upper bound of `(5/2)2^d` for the general Ramsey number.

The decisive fact is already stated abstractly in `CubeHomCapacityLowerAttempt.md`, Sections 1.2–1.3: a strict homomorphism lifts through arbitrary interiors, and fixed top-level branching cannot amplify the avoiding ratio. Flattening this family into an exponentially large template does not remove its five equal first-digit classes.

---

## 1. The first digit settles every required edge

Use digits `0,1,2,3,4` modulo five, and put

\[
 V_i=\{i\}\times[5]^{t-1},\qquad |V_i|=s=5^{t-1}.
\]

Every edge between `V_0` and `V_1` is red. Every edge between `V_0` and `V_2` is blue. Therefore the red graph and the blue graph each contain a **noninduced** `K_(s,s)`. Edges within its two vertex classes may have either colour and are irrelevant.

The cube `Q_d` has a bipartition

\[
 E_d=\{x\in\{0,1\}^d:|x|\equiv0\pmod2\},\qquad
 O_d=\{x\in\{0,1\}^d:|x|\equiv1\pmod2\},
\]

with `|E_d| = |O_d| = 2^(d-1)`. Both classes are independent. If `2^(d-1) <= s`, inject `E_d` into `V_0` and `O_d` into `V_1`. Every cube edge crosses this complete red pair. Replacing `V_1` by `V_2` gives a blue embedding. These are ordinary injections; no preservation of nonedges is asserted or needed.

Taking `d = 1 + floor(log_2 s)` proves the lower bound in (1). The upper bound is simply the vertex-count condition `2^D_t <= N`. For the stated gap, writing `a = log_2 5` gives

\[
 t a-D_t
 \le a-1+\{(t-1)a\}<a.
\]

In particular, `D_t >= floor(log_2 N)-2`. The guaranteed cube has more than `N/5` vertices and at most `2N/5` vertices. The threshold in (2) is precisely `2^(d-1) <= 5^(t-1)`.

The two colour graphs are isomorphic: multiplying every digit by two modulo five preserves the first differing position and exchanges differences `±1` with `±2`. This is not needed to transfer the lower bound, since both embeddings were given directly.

### A completely explicit injection

For `x = (x_1,...,x_d)`, define

\[
 p(x)=\sum_{i=1}^d x_i\pmod2,\qquad
 r(x)=\sum_{i=2}^d x_i2^{i-2}.
\]

Let `b_(t-1)(r)` be the length-`t-1` base-five expansion of `r`, padded with leading zeros. For `2^(d-1) <= 5^(t-1)`, it exists for every `r(x)`. Then

\[
 F_R(x)=\bigl(p(x),b_{t-1}(r(x))\bigr),\qquad
 F_B(x)=\bigl(2p(x),b_{t-1}(r(x))\bigr).                     \tag{3}
\]

The pair `(p(x),r(x))` determines `x`: `r` recovers `x_2,...,x_d`, and their parity together with `p` recovers `x_1`. Thus both maps are injective. Every cube edge flips `p`, so its images differ at their **first** digit, by `±1` in `F_R` and `±2` in `F_B`. The remaining digits need not preserve any graph relation.

For `t=d=1`, the tail in (3) is the empty word. No limiting argument, approximate balancing, or hypothesis about typical embeddings occurs here.

---

## 2. Why the proposed recursive obstructions do not apply

1. **A large flattened template is not the operative template.** At the root there are still five children, each of size `N/5`. A single root edge is already sufficient. The polynomial-template barrier and the fixed-template connected-fractional-matching limit are not needed.

2. **The top-level map is strict.** It is the parity map to the edge `0–1` (red) or `0–2` (blue). No cube edge has both endpoints in one top-level fibre. Consequently the nonuniform recursive interiors can be replaced by completely arbitrary graphs, or arbitrary internal two-colourings, without harming this embedding.

3. **The recursive fibres are not smaller cubes.** They are independent parity classes, not full coordinate subcubes when `d >= 2`. At every subsequent level their arbitrary subsets remain independent. Once the first digit is assigned, all deeper digits serve only as injective addresses. Requiring a cube-like, affine, product, or Lipschitz structure of these deeper address maps would impose constraints that an ordinary embedding does not have.

4. **The integer lift causes no obstruction.** For the red top-level map, the integer-valued lift is just `p(x) in {0,1}`. It changes by `±1` on every edge and has zero sum around every oriented square. In blue-cycle coordinates the identical statement holds. The square-lifting observation is consistent with this construction.

5. **A bad product/Hamming-weight map cannot exclude this injection.** Equation (3) is a legal injection of the entire cube. It does not try to distribute edges recursively among coordinate groups. An all-map claim forcing `D_t < d_t` is therefore false, irrespective of the fibre behaviour of another restricted class of maps.

An all-nonlinear-embeddings upper obstruction is unnecessary for a negative answer to the candidate: one verified embedding in dimension `log_2 N - O(1)` already precludes the proposed divergence.

---

## 3. General recursive partition and separator principles

These elementary principles make precise which recursive constraints are real. They concern ordinary, not induced, embeddings.

### 3.1 Exact partition criterion for a graph substitution

Let

\[
 G=T[G_1,\ldots,G_m]
\]

be a graph substitution: the `G_i` have disjoint vertex sets, and between `G_i` and `G_j` all edges are present if `ij` is an edge of `T`, and none are present otherwise. The graphs `G_i` may have unrelated structures and sizes.

**Lemma.** A finite graph `F` embeds injectively as an ordinary subgraph of `G` if and only if there is a partition

\[
 V(F)=X_1\mathbin{\dot\cup}\cdots\mathbin{\dot\cup}X_m
\]

(empty parts allowed) satisfying:

* if an `F`-edge has endpoints in different parts `X_i,X_j`, then `ij` is a `T`-edge;
* for each `i`, the source graph `F[X_i]` has an ordinary injective embedding into `G_i`.

**Proof.** An embedding supplies the partition by taking preimages of the host classes; its restrictions satisfy the second condition. Conversely, take the union of the embeddings of `F[X_i]`. Their images lie in disjoint host classes, so the union is injective. Edges within a part are preserved by its embedding, and edges between parts are preserved by the complete joins. There is no constraint arising from a source nonedge. QED.

Iterating this equivalence down a substitution tree is an **exact** recursive criterion for arbitrary embeddings. Crucially, the sources at descendant nodes are arbitrary induced subgraphs `F[X]`, not necessarily cubes. An independent source part is a terminal case: it needs only enough host vertices, irrespective of how much decomposition remains below it.

### 3.2 Separator-to-complete-join corollary

Fix a vertex `a` of `T`, and a source set `S subseteq V(F)`. Let `C_1,...,C_k` be the connected components of `F-S`. Suppose:

* `F[S]` embeds into `G_a`;
* each component `C_j` is assigned to a child `G_(i_j)` with `i_j != a` and `a i_j in E(T)`;
* the assigned components have embeddings into their children whose images are pairwise disjoint when they use the same child.

Then `F` embeds into `G`.

**Proof.** Use the proposed embeddings. Edges inside `S` or inside a component are already preserved. Edges from `S` to a component use its complete join to `G_a`. There are no source edges between distinct components. Apply the partition criterion. QED.

If `S` is independent, its first requirement is merely `|S| <= |G_a|`. If every component of `F-S` is a single vertex, their packing requirements likewise reduce to cardinalities. For `F=Q_d`, take `S=E_d`: the components of `F-S` are exactly the singletons in `O_d`, and assign all of them to one child adjacent to `a`. This is the construction in Section 1. It uses a separator of half the vertices, rather than a small separator; here that costs only a constant fraction of the host and is sufficient.

### 3.3 Quantitative complete-pair consequence

For a colour `c` in an arbitrary coloured substitution with top-level template `T`, define

\[
 B_c=\max_{ij\in E(T_c)}\min\{|G_i|,|G_j|\}.
\]

Set `B_c=0` if the colour has no template edge. When `B_c >= 1`, the maximum colour-`c` cube dimension satisfies

\[
 D_c\ge1+\lfloor\log_2 B_c\rfloor.                         \tag{4}
\]

More generally, any bipartite graph with parts of sizes at most `|G_i|` and `|G_j|` embeds across a colour-`c` template edge `ij`. This follows by injecting the two independent parts; internal colours do not enter.

In a uniform `m`-child substitution, an edge in a given colour yields a `Q_d` in that colour whenever `N >= (m/2)2^d`. Keeping these equal top-level classes, a fixed branching factor cannot create an unbounded avoiding ratio, regardless of recursion depth or internal nonuniformity. This is not a claim about arbitrarily unbalanced top-level class sizes. For the present family, `m=5` and both colours have root edges.

---

## 4. Exact structural checks and scope

`check_cube_lex_pentagon.py` deterministically constructs the two maps (3) for `t=1,...,8` at the guaranteed dimensions `d_t`. It checks, with integer arithmetic:

* the dimension and capacity inequalities (without floating-point logarithms);
* that all image words have length `t` and digits in `[5]`;
* injectivity on all `2^d_t` source vertices;
* the colour of **every** cube edge, using the stated first-differing-digit rule;
* the elementary digit permutation exchanging the colours.

This checks explicit certificates, not a numerical search for embeddings or obstructions. Output is saved in `CubeLexPentagonVerification.txt`. The proof for all `t,d` is Section 1, not an extrapolation from these checks.

**Complete:** the candidate is ruled out; the gap is uniformly below `log_2 5`; both colours satisfy (2); the recursive partition and separator lemmas are proved.

**Not claimed:** an exact formula for `D_t`, an induced cube embedding, or a solution of the general linear-order cube Ramsey problem. No unresolved assertion is needed for the conclusion about this family. `Submission/Spec.lean` is not modified.
