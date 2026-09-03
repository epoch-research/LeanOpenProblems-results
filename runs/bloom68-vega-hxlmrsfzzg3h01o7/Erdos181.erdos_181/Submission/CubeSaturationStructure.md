# Saturation, structural templates, and the remaining global cube-Ramsey gap

## Outcome and scope

**This investigation does not prove or disprove `R(Q_d)=O(2^d)`.** It does not supply an absolute Ramsey constant.

There is a positive structural embedding theorem below: colorings close to an arbitrary **bounded homogeneous template**, not just a partition coloring, contain an ordinary monochromatic cube with a dimension-uniform size multiplier. Its proof uses a connected fractional matching, a closed walk, the distribution of Hamming weight modulo the walk length, and a final injective greedy embedding. The fractional matching is not rounded to a cube without a capacity argument.

There are also two limitations on using saturation as the missing structural argument:

* For every `d>=3`, an explicit coloring on `3*2^(d-1)-2` vertices is red-`Q_d`-saturated and has neither a red nor a blue cube, but its minimum maximum-incident edit distance from **any partition coloring, in either color orientation**, is exactly `2^(d-1)-1`. Deleting `d-1` exceptional vertices fixes this example.
* At arbitrarily large fixed host multipliers, one-sided `Q_d`-saturation alone does not force a useful partition or bounded-template structure, even after deleting `O(2^d)` vertices. A probabilistic construction proves this assertion. Its complement is **not asserted cube-free**, so it is not a Ramsey counterexample and does not refute a structural theorem using both colors.

The missing step remains a genuinely simultaneous, global theorem: obtain usable structure or an embedding from both-color cube-freeness and all the globally compatible failure certificates. Neither saturation nor the exact Hall/matroid reduction currently gives that implication.

Throughout, `d>=1`, `h=2^d`, and `m=h/2`. Copies are ordinary injective graph homomorphisms. Additional host edges are harmless. No Lean files or statements in `Spec.lean` were changed or used as premises.

## 1. What saturation legitimately provides

Assume a red-blue coloring has neither color containing `Q_d`. Recolor a blue edge red whenever doing so leaves the red graph cube-free. This cannot create a blue cube, because it only deletes blue edges. Termination gives a red-`Q_d`-saturated graph while retaining blue cube-freeness.

It does **not** follow that blue is saturated too. Subsequent blue saturation can undo red saturation.

### A small obstruction to simultaneous-saturation normalization

There is no coloring of `K_4` in which both colors are `C_4`-saturated, although there are colorings with both colors `C_4`-free. Indeed, a `C_4`-saturated graph on four vertices must have at least four edges. With at most two edges, adding one cannot create `C_4`; with three edges, the only possible saturated candidate is `P_4`, and adding its distance-two chord does not create `C_4`. Thus both saturated colors would require at least eight edges in `K_4`.

This example rules out the unqualified normalization. It does not settle whether some additional, separately proved extremality assumption would yield simultaneous saturation in a particular dimension or at a particular host size.

### Private cube witnesses

For a red-saturated, red-cube-free graph and each blue edge `uv`, adding `uv` gives a red cube that necessarily uses `uv`. Deleting that edge from the copy gives a red `Q_d-e` with endpoints `u,v`.

For `d>=2`, every such witness contains:

1. two disjoint red `Q_(d-1)` copies;
2. the `m-1` remaining edges of the coordinate matching between those copies, with their actual cube labels retained;
3. `d-1` internally vertex-disjoint red paths of length three from `u` to `v`, one for each square through the missing cube edge;
4. a red perfect matching of size `m`, by choosing a coordinate other than the missing edge's coordinate.

In particular, for `N>=h`, a red-saturated graph has minimum red degree at least `d-1`. These are local rooted witnesses, not a coherent packing or an interchangeable collection of labelled halves.

### What full edge-count optimization adds

One may instead maximize the number of red edges over **all** countercolorings on the given host. This gives red saturation and also the following exact trade condition. If `F` is a set of blue edges, `D` a set of red edges, and `|F|>|D|`, then

```
R'=(R\D) union F,       B'=(B\F) union D
```

cannot both be cube-free. Thus, if the red cubes created by adding `F` can all be destroyed by deleting `D`, then `B'` has a blue cube, necessarily using an edge of `D`.

No bounded trade size is assumed. This condition is stronger than inclusion-maximality of red. The examples below must not be represented as refutations of a theorem that genuinely uses this full optimization together with a sufficiently large host multiplier.

## 2. A saturated two-color counterexample to unrestricted per-vertex partition stability

For `d>=3`, use disjoint sets

```
|T|=d-1,       |A|=h-d,       |B|=m-1.
```

Make precisely the edges between `A` and `B` blue. All other edges are red. Equivalently, the red graph is

```
K_(d-1) join (K_(h-d) disjoint_union K_(m-1)).                 (1)
```

The total order is `N=3m-2`.

### Neither color contains a cube

The blue graph is `K_(h-d,m-1)` together with isolated vertices. It has a vertex cover of size `m-1`, whereas a cube has a matching of size `m`. Thus it has no blue cube.

The cube is `d`-vertex-connected. One elementary proof that deleting at most `d-1` vertices preserves connectivity is induction on its two coordinate halves. If each half loses at most `d-2` vertices, the surviving halves are connected by induction and a coordinate matching edge survives. If all `d-1` deletions lie in one half, every surviving vertex of that half has its matching neighbor in the intact half.

Removing `T` from (1) separates `A` from `B`. Hence a red cube cannot meet both `A` and `B`: removing its at-most-`d-1` preimages of `T` would disconnect it. A cube contained in `A union T` is impossible because this set has `h-1` vertices. A cube contained in `B union T` is impossible because its order is `m+d-2<h`.

### Red saturation is exact

Every missing red edge is `uv` with `u in A` and `v in B`. After adding it, embed the all-zero cube vertex at `v`, one of its neighbors at `u`, and its other `d-1` neighbors bijectively at `T`. Map all remaining cube vertices bijectively into `A\{u}`. Every required edge not incident to the root lies in the red clique `A union T`. This proves saturation for every missing edge.

### Exact partition-edit lower bound

For a coloring `c`, let `dist_infty(c,P)` be the maximum, over vertices, of the number of incident edges on which `c` differs from partition coloring `P`. Allow either color to be the within-part color. For (1),

```
min_P dist_infty(c,P) = m-1.                                  (2)
```

Write `a=h-d`, `b=m-1`, and `t=d-1`. We have `a>=b+2` and `t<=b` for `d>=3`.

First suppose the proposed partition coloring is red within parts and blue between parts, and has error degree `D<b`. A universal-red vertex `u in T` must belong to a part `P` with `N-|P|<=D`. Thus `P` contains both an `A` vertex and a `B` vertex. If its counts are `a',b',t'`, the incident error counts at an `A` vertex and a `B` vertex in `P` are respectively

```
(a-a')+(t-t')+b',       (b-b')+(t-t')+a'.
```

Their sum is `a+b+2(t-t')>=2b`, contradicting `D<b`.

Now suppose the proposed partition coloring is blue within parts and red between parts. If no part mixes `A` and `B`, every `B` vertex has at least `a>=b` errors. If a part does mix them, the error counts at an `A` vertex and a `B` vertex in that part sum to

```
a+b-2+2t' >= 2b.
```

Again `D>=b`.

Finally, the red-within partition `{A union T, B}` has maximum error degree exactly `b`: only the red edges `T x B` are wrong, and `t<=b`. This proves (2).

Deleting `T` leaves an exact partition coloring. Thus a small exceptional vertex set can matter much more than a small maximum incident error budget.

**Scope warning.** This family has ratio `N/h=3/2-2/h`. It disproves an unrestricted stability assertion from red saturation plus simultaneous cube-freeness. It does **not** disprove a statement additionally assuming `N>=C h` for a sufficiently large absolute `C`, and it is not asserted to maximize red edge count over all countercolorings or to have order `R(Q_d)-1`.

## 3. Saturation alone cannot supply structure at large fixed multipliers

Here is an obstruction on the scale actually relevant to the question.

### One-sided saturation obstruction

Fix constants `a,b>=0` and

```
C > a + 3/2 + 3b.
```

For all sufficiently large `d`, there is a `Q_d`-saturated graph `G` on `N=ceil(C h)` vertices such that, after deleting **any** at-most-`a h` vertices, its red-blue coloring is not within `b h/d` incident edits per vertex of any partition coloring in either orientation.

The assertion involves only red saturation and red cube-freeness. No blue cube-freeness is claimed.

**Proof.** Fix `0<p<1/4`, for example `p=1/8`. Let `G_0` be the random graph `G(N,p)`. The expected number of labelled injective red cube embeddings is at most

```
N^h p^(dh/2) = [N p^(d/2)]^h
              <= [(C+o(1)) (2 sqrt(p))^d]^h -> 0.              (3)
```

For every fixed positive `eta`, standard Chernoff bounds and a union bound over at most `3^N` disjoint pairs of vertex sets also show, with probability tending to one:

* every set of size at least `eta N` spans at least `(p/2) binom(|S|,2)` edges;
* every two disjoint sets of sizes at least `eta N` have at least `(p/2)|S||T|` cross edges.

The tail probability for each applicable set or pair is `exp(-Omega_eta(N^2))`, which dominates the `exp(O(N))` number of choices. Only finitely many fixed thresholds, depending on `a,b,C`, are needed below. Choose a cube-free `G_0` having these lower-density properties, and extend it to a maximal cube-free supergraph `G`. Then `G` is saturated and retains all the lower-density properties.

Let `U` be a proposed remaining vertex set, `n=|U|>=(C-a)h`, and suppose its partition error degree is an integer `D<=b h/d`.

* **Red within parts.** Each part has fewer than `h+dD` vertices, since a graph with at most `D` wrong incident edges inside such a part greedily contains a red cube once its size is at least `h+dD`. Thus the largest part has size at most `(1+b)h`, bounded away from `n`. By grouping parts there are two unions of parts, both of size at least a fixed positive multiple of `h`. (Add parts until a fixed small linear threshold is first reached, or take a single part already above it.) Every red edge between these unions is an error. Their number is at most `nD/2=o(h^2)`, contradicting the retained lower-density property of `G_0`.
* **Red between parts.** Put `r=m+dD`. Since `n>=3r-1`, if every part has size at most `n-r`, the partition subset-sum lemma produces two unions, each of size at least `r`. Greedy parity embedding across them gives a red cube. Thus there must instead be a part of size greater than `n-r`, again a fixed positive multiple of `h`. Every red edge inside that part is an error, so there are at most `|P|D/2=o(h^2)` such edges. This contradicts the lower-density property of `G_0[P]`.

Both orientations are impossible. The argument is uniform over the deleted set because the random lower-density properties hold for all applicable subsets. QED.

### Bounded templates are not forced by one-sided saturation either

Fix also an integer `t`. The same construction, now assuming just `C>a+1+b`, cannot become a coloring with at most `t` homogeneous template classes and incident error degree at most `b h/d` after deleting at most `a h` vertices.

To see this, discard template classes smaller than `delta h`, where `delta>0` is small enough that `t delta < C-a-1-b`. The retained union has more than `(1+b)h` vertices. A template-blue loop on a retained class, or a template-blue pair of retained classes, contradicts the positive red lower density of `G_0` and the `o(h)` error-degree budget. Hence the template is all red on the retained union. That union has blue maximum degree at most `D` and order greater than `h+dD`, so greedily contains a red cube, a contradiction.

These constructions do not refute a majority-density-qualified statement, a statement about global edge-count maximizers among two-color countercolorings, or a statement retaining blue cube-freeness. They demonstrate exactly why one-sided saturation is not by itself a structural reduction.

## 4. A positive robust bounded-template embedding theorem

A **homogeneous template** on `t` labels assigns red or blue to every unordered pair of labels, including a loop at each label. A vertex partition `V_1,...,V_t` realizes the template if edges between two different classes have the pair's color, and edges within a class have its loop's color. These are arbitrary finite templates, not necessarily partition colorings.

### Theorem

Let `0<epsilon<=1`, `t>=1`, and `D>=0` be an integer. Suppose that after deleting `E` vertices, a coloring of `K_N` differs in at most `D` incident edges per remaining vertex from a homogeneous template on at most `t` classes. Define

```
L_* = ceil(132 t^2 / epsilon^2).
```

If

```
N-E-t dD >= (3/2+epsilon) h,                                   (4)
d >= (L_*^2/2) log(16 t L_*/epsilon^2),                         (5)
```

then the coloring contains a monochromatic `Q_d`.

In particular, for each fixed `t,epsilon`, exact homogeneous templates have the asymptotic threshold `(3/2+epsilon)h`, uniformly over all class sizes and all template colorings. The sufficient dimension bound in (5) is

```
O(t^4 epsilon^(-4) log(2t/epsilon)).
```

For fixed `epsilon`, this permits an unbounded number of classes up to a sufficiently small constant times `(d/log d)^(1/4)`, provided `t dD=O(h)`. For fixed `t`, a linear bound alone would follow just by pigeonholing a large homogeneous class; the content here is the uniform `3/2+epsilon` threshold and the allowance for growing template complexity. The coefficient `3/2` is asymptotically necessary even for simple partition templates, by the usual coloring on `3m-2` vertices.

### 4.1 Connected fractional matching lemma, including loops and weights

Give the vertices of a red-blue looped complete template positive capacities `a_i`, with total `W`. A fractional matching is a nonnegative edge weighting `x_e`, where a non-loop edge consumes `x_e` at each endpoint and a loop consumes `2x_e` at its vertex. Its covered mass is `2 sum_e x_e`.

**Lemma.** Some monochromatic connected component has a fractional matching of covered mass at least `2W/3`.

**Proof.** One color's ordinary graph, ignoring loops, is connected on all template vertices: if one is disconnected, the other connects all its components. Call a connected color red. The one-vertex case has the same interpretation.

If its maximum fractional matching already covers at least `2W/3`, stop. Otherwise fractional matching/vertex-cover linear programming duality gives a fractional red vertex cover of weighted cost less than `W/3`. There is one taking values in `{0,1/2,1}`. For completeness, truncate an optimal cover to `[0,1]`, choose `s` uniformly in `(0,1/2)`, and round a value `y` to `0` if `y<s`, to `1` if `y>1-s`, and to `1/2` otherwise. An edge whose endpoint rounds to zero has its other endpoint round to one; a red loop never rounds to zero. Expected cost is unchanged, so some half-integral rounding costs no more.

Let `I,J,K` be the zero, half, and one sets, and denote their total capacities by `A,B,F`. Then

```
F+B/2 < W/3,
A+B = W-F > 2W/3,
A > W/3.
```

All loops on `I`, all pairs within `I`, and all pairs from `I` to `J` are blue. Their blue component has a fractional matching covering

```
min(2A,A+B) > 2W/3.
```

Explicitly, match capacities between `I` and `J`; if `A>=B`, use blue loops to cover leftover capacity in `I`. This proves the lemma. QED.

### 4.2 Make room for errors and small classes

For a class of size `n_i`, use effective capacity

```
a_i=max(n_i-dD,0)/h.
```

By (4), their sum is at least `3/2+epsilon`. Discard zero capacities and those less than `epsilon/(2t)`. The lost effective mass is less than `epsilon/2`. The retained template therefore has total capacity at least `3/2+epsilon/2`.

Apply the lemma and take a maximum fractional matching in the resulting monochromatic connected component. Write its covered mass as `M`; then

```
M >= 1+epsilon/3.
```

Choose an extreme optimal matching. It has at most `t` positive edge variables: otherwise its positive columns in the vertex-incidence matrix are linearly dependent and a small perturbation in both directions contradicts extremality.

Normalize its edge weights by `q_e=x_e/M`. Then `sum q_e=1/2`. Let `p_i` be their incident normalized load, counting a loop twice, so `sum p_i=1` and `p_i<=a_i/M`. Every vertex in the chosen component has the uniform capacity margin

```
a_i-p_i >= epsilon^2/(8t) =: eta.                              (6)
```

This includes vertices used only to connect the positive matching support. Indeed, all retained capacities are at least `epsilon/(2t)`, and `1-1/M>=epsilon/(3+epsilon)>=epsilon/4`.

### 4.3 A capacity-controlled closed walk

Set

```
T_0=ceil(16t/eta)=ceil(128t^2/epsilon^2).
```

For each positive edge `e`, put `2 floor(T_0 q_e)` copies of it in a multigraph. Add two copies of every edge of a spanning tree of the chosen monochromatic component. This gives a connected Eulerian multigraph, hence a closed walk

```
v_0,v_1,...,v_(L-1),v_L=v_0
```

using only edges and loops of that color. In the one-vertex case the positive matching loop supplies the walk.

Let `c_i` be the number of positions labelled `i`. Its value is half the multigraph degree, with the usual degree-two convention for a loop. There are at most `t` positive matching edges. Rounding and adding the doubled tree give

```
|L-T_0|<=2t,
|c_i-T_0 p_i|<=2t,
L<=L_*,
|c_i/L-p_i|<=8t/T_0<=eta/2.                                  (7)
```

For the second inequality, flooring loses at most `t+1<=2t` at a vertex, counting a loop twice, and the tree adds at most `t-1`. The ratio inequality follows using `L>=T_0-2t>=T_0/2`.

Thus the walk's occurrence proportions are at most `a_i-eta/2`. This step preserves capacities; it does not simply declare a fractional matching integral.

### 4.4 Use cube geometry without identifying host vertices

For `K` distributed as `Bin(d,1/2)`, Fourier inversion on `Z/LZ` gives

```
|Pr(K = j mod L)-1/L|
 <= cos(pi/L)^d
 <= exp(-2d/L^2).                                              (8)
```

For the last inequality, use `cos(pi/L)=1-2 sin^2(pi/(2L))<=1-2/L^2`. Here `L>=2`.

Map a cube vertex `x` provisionally to the template label

```
v_(|x| mod L),
```

where `|x|` is its Hamming weight. Adjacent cube vertices have weights differing by one, so every required template pair or loop has the chosen color.

By (7)-(8), the fraction of cube vertices provisionally assigned label `i` is at most

```
p_i+eta/2+L exp(-2d/L^2) <= a_i.                               (9)
```

Condition (5) ensures `L exp(-2d/L^2)<=eta/2`, since the expression is increasing as a function of `L>0` and `eta=epsilon^2/(8t)`.

If `k_i` cube vertices receive label `i`, (9) says exactly

```
k_i+dD <= n_i.                                                (10)
```

The provisional label map is intentionally many-to-one. It is **not** the final graph copy.

### 4.5 Restore full injectivity and actual edge colors

Embed the cube vertices one at a time, always in their provisionally assigned host class. A step in class `i` excludes at most `k_i-1` previously used vertices there. Each of at most `d` already embedded neighbors forbids at most `D` additional vertices of this class, because its expected template edge has the chosen color. Thus at most `k_i-1+dD` candidates are excluded. Equation (10) leaves a candidate.

All host images are distinct and every required cube edge has the chosen actual color. This completes the theorem for standard, noninduced graph copies. QED.

## 5. What still has to be proved to settle the question

The structural theorem is conditional on finding the structure. It does not assert that an arbitrary countercoloring, even after saturation, admits such a template.

For example, the following **unproved** normal-form statement would suffice:

> There are absolute constants `a,b>=0`, `t>=1`, and `C_0`, such that every two-color cube-free coloring on `N>=C_0 h` can, after any required full global optimization, be reduced by deleting at most `a h` vertices to a coloring within `b h/d` incident errors per vertex of a homogeneous template on at most `t` classes.

Take `epsilon=1/2`. Together with the theorem this statement would rule out all sufficiently large-dimensional countercolorings once

```
N/h > max(C_0, a+2+tb).
```

The finitely many smaller dimensions could be absorbed into a larger absolute constant using ordinary finite Ramsey existence. A more flexible sufficient statement would allow `t=t(d)` satisfying (5), with error degree at most `b h/(t d)` and at most `a h` deleted vertices; then a multiplier greater than `a+2+b` suffices. Alternatively, an exceptional-set version of the user's partition lemma would suffice with multiplier greater than `a+3/2+3b` and no bound on the number of parts. None of these proposed normal forms is asserted as an established invariant.

Neither normal form is proved here. Section 3 shows that any proof must actually use the simultaneous blue obstruction, not merely maximal red cube-freeness. Section 2 shows that an exceptional set or a genuinely large-host hypothesis cannot simply be dropped from a per-vertex partition assertion.

The existing `CubeGlobalHallReduction.md` remains relevant and valid at this point:

* Every even-side rematching is represented by the two-matroid common-base condition.
* Any odd subset may be unfrozen, including the whole odd side.
* A genuine countercoloring supplies failure certificates for every such assignment, in both colors and for every host cut.

What is missing is an implication from this **simultaneous family** of coupled certificates to a successful common basis or a structural normal form. Individual private saturation witnesses do not make the flats consistent, do not make witnesses from different roots disjoint, and do not yield boundedly many template types. A large packing of labelled smaller cubes likewise does not provide the required compatible cross-coordinate edges. Nothing above restricts reconfiguration to a bounded number of odd vertices.

Thus the unresolved step is combinatorial, not a formalization issue. No claim that the linear Ramsey conjecture follows from saturation, source isoperimetry, packing, or the already-established matroid reduction is justified by the present argument.

## Verification

The accompanying `check_cube_saturation_structure.py` checks the explicit saturation witnesses, small ordinary cube-containment cases, exact partition distances, connected fractional matching inequality on small weighted looped templates, the closed-walk rounding identities, the binomial residue bound, and the final greedy embedding with actual incident color errors.

The full run passed, with output in `CubeSaturationStructureVerification.txt`:

* 261 explicit added-edge cube embeddings, plus ordinary noncontainment checks for the core construction in dimensions 2 and 3;
* exact partition-distance minimization over all 15 partitions for the four-vertex case and all 115,975 partitions for the ten-vertex case;
* 42,189 cube vertex-deletion connectivity cases, and all 64 colorings of `K_4`;
* 2,980 weighted looped templates, comparing primal linear programs with exhaustive half-integral dual covers;
* 247 exact rational closed-walk rounding checks and 62 full theorem-scale capacity estimates;
* 4,992 binomial dimension/modulus pairs and 240 actual injective greedy embeddings with incident color errors.

`Submission/Spec.lean` retains SHA-256 `9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`.

These finite checks supplement the proofs. They do not verify the unproved normal-form statement or establish any new absolute Ramsey constant.
