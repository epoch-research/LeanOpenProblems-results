# Exact positive cases retained after refuting the general conjecture

Write the color-class sizes as `m≤m+δ`.

### Endpoint `c=m`

Whenever admissible, `δ≥1`. Take a singleton core in the larger class. This is the endpoint construction already suggested in the question.

### Next endpoint `c=m−1`: always exact

Let `A` be a class of size `m`. Since

\[
 \sum_{a\in A}d(a)=n-1=2m+\delta-1,
\]

some `a∈A` has degree at most `δ+1`. Otherwise the sum is at least `m(δ+2)`, larger by `δ(m−1)+1`.

Take

\[
 R=\{a\}\cup N(a),\quad U=A\setminus\{a\},\quad W=B\setminus N(a).
\]

The core is a connected star, `U` is independent, and all neighbors of `W` lie in `U`. Moreover,

\[
 |U|=m-1,\qquad |W|\ge(m+\delta)-(\delta+1)=m-1.
\]

This includes the balanced case: choose a leaf and its neighbor as the core.

### `c=1,2`: always exact when admissible

For `c=1`, connectivity and a proper core force the existing nonempty odd set to have size one.

For `c=2`, the class-size assumption excludes stars. Let `H` be the tree induced by the nonleaves. If `|H|≥3`, choose two leaves `s,t` of `H`. They are nonadjacent. Delete each together with all its leaf neighbors; set `U={s,t}`. The surviving core is connected and nonempty, and at least two leaves belong to `W`.

If `|H|=2`, the tree is a double star. One center has at least two leaf neighbors, since `n≥5`. Delete that center and its leaves, and delete one leaf at the other center. The two odd vertices are the deleted center and the latter leaf; at least two even vertices remain outside. Retain the other center and its remaining leaves as the core.

### At most three leaves: exact for every admissible `c`

Here `E(T)≤1`, so

\[
 2c\le2|U|+1,\quad |U|\le c
\]

forces `|U|=c`. This result is fully formalized as `exists_exact_of_leaves_le_three`; the path specialization is also formalized separately.

### A leafless smaller class: an exact rooted theorem

Suppose every vertex of the smaller class `A` has degree at least two. For any `c<m`, put `j=m−c`. Choose `X⊆A` of size `j` such that `X∪N(X)` is connected. It can also contain any prescribed root: grow a connected `j`-set in the half-square on `A`, starting at that root if it is in `A`, otherwise at one of its neighbors.

All degrees in `A` are at least two, and

\[
 \sum_{a\in A}(d(a)-2)=\delta-1.
\]

Since `T[X∪N(X)]` is a tree,

\[
 |N(X)|=1+\sum_{x\in X}(d(x)-1)
        =j+1+\sum_{x\in X}(d(x)-2)\le j+\delta.
\]

Therefore `R=X∪N(X)`, `U=A\X`, and `W=B\N(X)` give exactly `c` odd vertices and at least `c` even vertices. This proves the full exact statement for trees whose leaves all lie in one color class, including the rooted interior version for this family.

These last constructive arguments are paper proofs, checked by explicit certificates; they are not being represented as Lean theorems in the new file.

