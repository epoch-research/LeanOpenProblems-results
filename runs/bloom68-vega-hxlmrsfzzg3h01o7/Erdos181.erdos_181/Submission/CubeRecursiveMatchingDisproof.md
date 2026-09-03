# Recursive perfect matchings do not imply a uniform linear Ramsey bound

## Outcome

The proposed broader theorem is **false**, even when every recursive split has two **identical** halves and the joining matching is perfect.

More precisely, there are connected graphs `H_k`, with `h_k = 2^{d_k}` vertices and degree `d_k`, formed recursively from two identical halves by adding a perfect matching, such that

\[
\chi(H_k)\ge k,\qquad
R(H_k)\ge (k-1)(h_k-1)+1,\qquad
\frac{R(H_k)}{h_k}\ge \frac{k}{2}.
\]

Thus their Ramsey ratios are unbounded. The construction and proof below are finite and unconditional. They do not postulate a recurrence for Ramsey numbers. The essential argument amortizes **proper-coloring counts** under actual matching choices, with a proved loss at every step.

This does **not** prove or disprove `R(Q_d) = O(2^d)`. The counterexample family eventually has unbounded chromatic number, whereas every cube is bipartite. Restricting the matching class to bipartite graphs evades this counterexample; a uniform Ramsey theorem for that restriction is not established here.

`Submission/Spec.lean` is unchanged. Its SHA-256 remains
`9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`.

## 1. The precise graph class

Let `T_0 = {K_1}`. If `G` belongs to `T_d` and `p` is any permutation of `V(G)`, put `D(G,p)` in `T_{d+1}`. Its vertex set is

\[
\{0,1\}\times V(G),
\]

its two layers are copies of **the same** graph `G`, and its only cross-edges are

\[
(0,x)(1,p(x))\quad(x\in V(G)).
\]

Allowing nonidentical halves or nonperfect matchings only enlarges the class, so a disproof for this definition also disproves those versions.

Every `G in T_d` is connected, has `2^d` vertices, and is `d`-regular. These facts follow immediately by induction. It is also triangle-free: a triangle crossing a recursive cut would use two matching edges incident with the same vertex, which is impossible.

There is a useful genuinely hereditary restriction: **every induced subgraph with at least two vertices has a nontrivial matching cut**. Descend the decomposition tree until its vertex set first meets both children. All edges across that split belong to the relevant matching. In particular, every such induced subgraph has edge-isoperimetric constant at most 1: on the smaller side `A` of that cut, `e(A,A^c) <= |A|`.

Consequently the counterexamples below do retain the hereditary obstruction to edge expansion proportional to a large degree. That obstruction is not enough for a uniform Ramsey bound.

A balanced perfect-matching bisection is not, by itself, a sublinear **vertex** separator. Covering all edges of that matching needs half the vertices. Small cube vertex separators use additional coordinate geometry.

## 2. A finite matching-amplification lemma

**Lemma.** Let `H` be a graph on `h >= 2` vertices, with `chi(H) >= k >= 2`. There is a graph obtained from `H` by repeated identical-half perfect-matching doublings that has chromatic number at least `k+1`. It suffices to use

\[
t=2kh(h-1)
\]

doublings.

This holds regardless of whether `H` itself belongs to the recursive class.

### 2.1 Every base copy uses every color

Start with `F_0=H`. After `j` doublings, `F_j` contains a fixed partition into `m=2^j` copies of `H`, each labelled by `Z/hZ`. Write `P_j` for the number of proper colorings of `F_j` with the labelled palette `[k]`.

The restriction of any such coloring to any base copy of `H` uses **every** color. Otherwise that copy would be `(k-1)`-colorable. If `P_j=0`, the desired conclusion has already been obtained; the following counting inequalities still apply.

### 2.2 A restricted set of actual perfect matchings

Between two identical copies of `F_j`, only consider the following matchings. For each of the `m` base blocks, independently choose a shift `s_b in Z/hZ`, and join

\[
(0,b,x)\quad\text{to}\quad(1,b,x+s_b).
\]

There are exactly `h^m` choices. Each is a perfect matching between the two entire copies of `F_j`, so all are allowed by the recursive construction. In particular, the argument does not need the full set of `(hm)!` perfect matchings.

Fix an ordered pair `(f,g)` of proper `[k]`-colorings of `F_j`. In each block choose an `x` colored 1 by `f` and a `y` colored 1 by `g`. The shift `s_b=y-x` creates a monochromatic edge in this proper-coloring problem. Thus at most `h-1` shifts in that block are compatible with `(f,g)`. Across the `m` blocks, at most `(h-1)^m` shift vectors are compatible.

Every proper coloring of a doubled graph is uniquely an ordered pair of proper colorings of its halves, compatible with the selected matching. Double-counting pairs consisting of a shift vector and a compatible coloring therefore gives

\[
\sum_{s\in(\mathbb Z/h\mathbb Z)^m} P\bigl(D(F_j,p_s)\bigr)
\le P_j^2(h-1)^m.
\]

Choose a shift vector with at most the average number of colorings. Set the resulting doubled graph to be `F_{j+1}`. With

\[
a=\frac{h-1}{h}\in(0,1),
\]

we have established, rather than assumed,

\[
\boxed{P_{j+1}\le P_j^2 a^{2^j}.} \tag{1}
\]

A lexicographically first minimizing shift vector makes every step a deterministic, finite-search construction.

### 2.3 The loss accumulates until no coloring remains

Iteration of (1), for `j>=1`, yields

\[
P_j\le P_0^{2^j}a^{j2^{j-1}}
     =\bigl(P_0^2a^j\bigr)^{2^{j-1}}
\le\bigl(k^{2h}a^j\bigr)^{2^{j-1}}. \tag{2}
\]

The exponent identity is exact: squaring the bound at step `j` and multiplying by `a^{2^j}` changes `j 2^{j-1}` to `(j+1)2^j`.

Bernoulli's inequality gives

\[
\left(\frac h{h-1}\right)^{h-1}
=\left(1+\frac1{h-1}\right)^{h-1}\ge2,
\quad\text{so}\quad a^{h-1}\le\frac12.
\]

For `t=2kh(h-1)`, since `2^k>k`,

\[
k^{2h}a^t
\le k^{2h}2^{-2kh}
=\left(\frac{k}{2^k}\right)^{2h}<1.
\]

Equation (2) implies `P_t<1`. Since `P_t` is a nonnegative integer, it is zero. Hence `chi(F_t)>=k+1`. This proves the lemma.

Equivalently, while `P_j>0`, (1) subtracts the positive constant `-log(a)/(2h)` from the normalized entropy `log(P_j)/|V(F_j)|` at each step. The finite proof above does not require logarithms or asymptotics.

## 3. An explicit infinite counterexample scheme

Let `H_2=K_2`, with `d_2=1`. Given `H_k in T_{d_k}`, apply the lemma with base `H_k` and palette size `k`, always choosing a minimizing cyclic-shift matching. Continue for the specified number of steps and call the result `H_{k+1}`. Thus one may take

\[
h_k=2^{d_k},\qquad
d_{k+1}=d_k+2k h_k(h_k-1).
\]

Induction proves `H_k in T_{d_k}` and `chi(H_k)>=k`. This is an explicit finite algorithm for each member, though the displayed size bounds are deliberately very inefficient. If no `k`-coloring existed at the beginning of a stage, all subsequent graphs still contain the previous one, so the construction and conclusion remain valid.

### The Ramsey countercolorings

For each `k`, color the complete graph on

\[
N_k=(k-1)(h_k-1)
\]

vertices as follows: partition its vertices into `k-1` blocks of size `h_k-1`, make all edges within a block red, and all edges between blocks blue.

* A red copy of the connected graph `H_k` would have to lie in one red component, of size `h_k-1`. Injectivity forbids this.
* A blue copy would give a proper `(k-1)`-coloring of `H_k` by its block indices, contradicting `chi(H_k)>=k`.

These are ordinary noninduced copies; no induced-containment assumption is used. Therefore

\[
R(H_k)\ge N_k+1,
\qquad
\frac{R(H_k)}{h_k}\ge k-1-\frac{k-2}{h_k}\ge\frac k2.
\]

The last inequality uses `h_k>=2`. This proves the failure of a single Ramsey constant for the recursive-matching class.

## 4. A small concrete witness

For a list `p` of length `n`, use the convention that doubling the graph on `0,...,n-1` adds the edges `x -- (n+p[x])` and duplicates all old edges into the second half.

Starting with one vertex, use these five permutations:

```
p1 = [0]
p2 = [0, 1]
p3 = [0, 1, 3, 2]
p4 = [2, 3, 4, 5, 6, 7, 0, 1]
p5 = [0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 8, 9]
```

The resulting graph `J` is a connected, triangle-free, 5-regular graph on 32 vertices, in `T_5`, with `chi(J)=4`.

The dimension-3 graph has 48 proper labelled 3-colorings. The dimension-4 graph has 72. The dimension-5 graph has none. The last two matchings are precisely the restricted blockwise cyclic shifts from the proof, with base size 8: shift `(2)` and then shifts `(0,2)`.

An explicit proper 4-coloring, in vertex order, is

```
[0, 1, 1, 2, 1, 0, 0, 2,
 1, 0, 2, 3, 2, 1, 0, 3,
 1, 3, 2, 0, 0, 2, 2, 1,
 1, 0, 0, 2, 0, 1, 1, 3]
```

Consequently `R(J)>=94`: the red union of three 31-cliques, with all cross-edges blue, is a countercoloring on 93 vertices. This single example is only an illustration; unbounded ratios follow from the infinite construction, not from this finite computation.

## 5. What cube coordinate consistency supplies

### 5.1 Bipartiteness is already an essential missing invariant

If `G` is connected and bipartite with bipartition map `b:V(G)->Z/2Z`, then `D(G,p)` is bipartite if and only if

\[
b(p(x))-b(x)
\]

is constant in `x`. Indeed, any bipartition on either connected layer is `b` up to a global flip; the matching edges must all be compatible with one choice of relative flip. Arbitrary permutations need not satisfy this condition.

Preserving this invariant blocks the unbounded-chromatic construction. It does not prove a uniform Ramsey bound for bipartite twisted cubes. In particular, parity-compatible matchings still need not assemble the two given cubes into a cube, as the 16-vertex example in `CubeRecursionFindings.md`, section 2, already shows.

### 5.2 Exact cube structure is a commuting-coordinate condition

A perfect-matching direction defines a fixed-point-free involution `tau_i` on vertices. For `Q_d`, the coordinate flips satisfy

\[
\tau_i^2=1,\qquad \tau_i\tau_j=\tau_j\tau_i.
\]

The latter equality says that the two label-preserving paths around each coordinate square have the same endpoint. A recursive matching cut does not impose it.

**Characterization.** Suppose a connected graph on `2^d` vertices has its edges given by `d` involutions `tau_1,...,tau_d`, and these involutions commute pairwise. Then it is `Q_d`, with those directions as coordinates.

Proof. Fix a vertex `v`. Send a subset `S` of `[d]` to `(product_{i in S} tau_i)(v)`. Commutation and involutivity reduce any walk to such a product, so connectedness makes this map surjective. Its domain and codomain both have size `2^d`; hence it is bijective. Toggling `i` applies `tau_i`, so the bijection preserves and reflects the given edges. This proves the characterization.

The relevant assertion is the **existence of a globally consistent direction labelling**, not that every arbitrary 1-factorization of an unlabelled cube must commute.

For two labelled `Q_m` layers glued by `p`, consistency means, after a single coherent relabelling of the directions in the right layer,

\[
p(x\mathbin\oplus e_i)=p(x)\mathbin\oplus e_{\sigma(i)}
\quad\text{for every }x,i,
\]

where one permutation `sigma` works for all vertices. Equivalently, `p` is a cube automorphism. Merely mapping the two bipartition classes consistently is weaker.

Thus an embedding invariant must retain **simultaneous transport of all coordinate labels and their square relations**, not just plentiful copies in each half and a matching between their vertex sets. This repairs the structural identification of the target as a cube; it is not a proved constant-loss embedding procedure in arbitrary two-colorings.

## 6. Scope of the progress

Proved here:

1. A finite matching-amplification lemma forcing unbounded chromatic number in the identical-half recursive class.
2. An infinite family of explicit-algorithm Ramsey countercolorings with unbounded normalized Ramsey numbers for that class.
3. Compatibility of this obstruction with triangle-freeness and the hereditary matching-cut / edge-expansion restriction.
4. The precise bipartition and commuting-coordinate invariants that arbitrary matching forgets.

Not proved here:

* A counterexample to `R(Q_d)=O(2^d)`.
* A uniform linear Ramsey theorem or counterexample for the **bipartite** recursive-matching subclass.
* A list-universality or supersaturation invariant that supplies cube-coordinate consistency with a bounded total loss.
* A new sufficient recurrence for the actual cube Ramsey numbers.

The infinite-family proof above is a paper proof. Any accompanying finite computation or Lean result is an additional check of its stated finite/reduction claims, not a claim to have Lean-formalized the entire family proof.

## 7. Verification artifacts

- `CubeRecursiveMatchingVerification.lean` compiles with
  `lake env lean Submission/CubeRecursiveMatchingVerification.lean`.
- `check_recursive_matching_disproof.py` checks the recursive construction, exact coloring counts, the double count for **every** pair of colorings and **every** allowed cyclic matching in the two displayed amplification steps, and the explicit 4-coloring. Run
  `python3 Submission/check_recursive_matching_disproof.py --milp` to also use an independent integer-programming check.
- `RecursiveMatchingExample32.json` records all five permutations, all 80 edges, and the 4-coloring.
- `CubeRecursiveMatchingVerification.txt` records the checks and the Lean axiom audit.

The Lean declarations include:

* `multipartite_countercoloring`: for every finite connected graph not colorable with `k` colors, an explicit countercoloring on `Fin k × Fin (|V|-1)` has neither a red nor a blue noninduced copy.
* `example_not_colorable_three` and `example_chromatic_number`: the recursively defined 32-vertex graph has chromatic number exactly 4. The generated proof has 94 case splits, with each forced-color and contradiction step checked by the kernel.
* `example_connected` and `example_degree`: connectedness and degree 5 for that graph.
* `example_countercoloring_93`: the specific noninduced Ramsey countercoloring on `Fin 3 × Fin 31`.
* `example_permutations_valid` and `example_permutation_sizes`: the listed operations use permutations of exactly the required sizes.

The file has no new axioms, proof placeholders, or `native_decide`, and imports neither Spec nor the earlier investigation. The audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. The amplification lemma and the infinite family, as well as the commuting-coordinate characterization, remain rigorous paper proofs rather than newly Lean-formalized theorems.

For the finite double count, the eight coloring counts at the first step are
`[432,120,72,120,432,120,72,120]`. At the second step, the 64 choices have total coloring count 4992, and 32 choices have zero colorings. Independent exhaustive search and the HiGHS integer-programming solver agree that the chosen 32-vertex graph has no proper 3-coloring; the Lean proof does not trust either solver.

