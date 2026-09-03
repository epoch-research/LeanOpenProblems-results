# Direct cube-Ramsey progress: a low-waste two-color cut decomposition

## Status and the positive result

**This does not prove `R(Q_d) <= C 2^d`.** No absolute Ramsey constant for arbitrary colorings is claimed. The new result here is an **unconditional decomposition theorem for every two-coloring**, with an actual injective cube as one outcome. It is not a theorem restricted to a spectral class.

Dimension zero is trivial: `Q_0` is a single vertex and `R(Q_0)=1`. For the new module put `h=2^d`, `m=h/2`, `D=floor(h/(16d))`, and `s=ceil(sqrt(d))`, with `d>=1`. Every red-blue coloring on `N>=5h/2` vertices has one of the following outcomes:

1. an ordinary monochromatic copy of `Q_d`; or
2. a partition
   
   `V = U disjoint_union P_R disjoint_union P_B disjoint_union W`
   
   with `|P_R|,|P_B| <= m-1`, such that:
   * each vertex of `P_R` has at most `D` **blue** neighbors in `U`, and each vertex of `P_B` has at most `D` **red** neighbors in `U`;
   * `U` satisfies the two-color, vertex-resilient cut condition (6) below with `alpha=1/(16s)`;
   * with `s=ceil(sqrt(d))`,
     
     \[
     |W|\le\frac{|P_R|+|P_B|}{16s-1}
          \le\frac{h-2}{16s-1}
          \le\frac{h}{15\sqrt d}.                         \tag{1}
     \]

The at-most-`h-2` vertices in the two pools are **retained resources**, not discarded vertices: their individual adjacency guarantees to the entire surviving core remain valid. Only `W` is waste. There is no bound on the number of cuts or on the number of neighborhood types.

A stronger constant-expansion version uses `alpha=1/8` instead of `1/(16s)` and has `|W| <= (h-2)/7`. The small-waste version has a proved, summable `O(1/sqrt(d))` normalized discard cost along dimension-halving chains. This is a cost of a genuine combinatorial operation, not a postulated Ramsey recurrence.

There is also a total-error cut-chain embedding certificate, Theorem 2, which permits uneven errors and arbitrarily many cuts. These results cover cuts with small separators, cuts with bounded wrong-color degrees, and cuts with small **total** wrong-color edge count. All constants and the conversion to a full cube are proved below.

**Remaining gap:** the robust core can persist. Neither its expansion nor the two stored pools are proved sufficient to complete a cube. Section 8 gives large-spectrum examples satisfying the core condition, so this branch has not covertly been reduced to the spectral benchmark. No compatible dimension-reduction or lifting operation for these cores is claimed.

All copies below are injective, noninduced graph copies. No statement in `Spec.lean`, including either of its opposed placeholders, is used as a premise. The specification is unchanged.

---

## 1. One-sided completion: an elementary ingredient, not the new extraction step

Let `c` be a color and write `bar(c)` for the other color.

### Lemma 1

Let `A,B` be disjoint host sets. If

\[
 |A|\ge m,\qquad |B|\ge m+dD,\qquad
 \deg_{\bar c}(v,B)\le D\quad(v\in A),                    \tag{2}
\]

where `D` is a nonnegative integer, there is a color-`c` copy of `Q_d` in `A union B`.

**Proof.** Map the even parity class of `Q_d`, of size `m`, injectively into any `m` vertices of `A`. For an odd cube vertex, its `d` already assigned neighbors exclude at most `dD` vertices of `B`. Thus it has at least `|B|-dD>=m` available color-`c` neighbors before injectivity exclusions. Assign the odd vertices successively. At any step at most `m-1` vertices of `B` have already been used, so an unused candidate remains.

The two pools are disjoint; all `h` images are distinct; every required edge joins the two parity classes and has color `c`. No matching between independently labeled smaller cubes is being used. All square relations are preserved because the map is defined on the vertices of the actual cube. QED.

No hypothesis on wrong-color degrees **from `B` into `A`** is needed. Those degrees may be as large as `|A|`. Internal edges of either pool are irrelevant.

This standard greedy ingredient alone does not locate `A,B` in an arbitrary coloring. The contribution below is an amortized extraction, retaining its unused resources and accounting for every discarded vertex.

## 2. A cut-chain certificate with a total error budget

A cut chain consists of nested host sets

\[
 U_0=V,\quad U_i=U_{i-1}\setminus(A_i\cup Z_i),\quad 1\le i\le t,
\]

where `A_i,Z_i` are disjoint subsets of `U_(i-1)` and `A_i` is nonempty. Assign a desired color `c_i` to each `A_i`. Put

\[
 E_i=e_{\bar c_i}(A_i,U_i),\qquad
 b_i=\max\left\{0,\ |A_i|-\left\lfloor\frac{E_i}{D+1}\right\rfloor\right\}.
\]

Here `e_c(A,B)` counts unordered color-`c` edges across disjoint sets once.

### Theorem 2 — total-error certificate

If `|U_t|>=m+dD` and, for some color `c`,

\[
 \sum_{i:c_i=c} b_i\ge m,                                  \tag{3}
\]

then the coloring contains a color-`c` copy of `Q_d`. In particular, the following scalar condition suffices for a copy in one of the two colors:

\[
 |U_t|\ge m+dD,\qquad
 \sum_i |A_i|-\frac{\sum_i E_i}{D+1}>h-2.                   \tag{4}
\]

Equivalently, the second condition is

\[
 N-|U_t|-\left(\sum_i|Z_i|+\frac{\sum_i E_i}{D+1}\right)>h-2.
\]

**Proof.** At most `floor(E_i/(D+1))` vertices of `A_i` have more than `D` wrong-color neighbors in `U_i`. Keep the others, calling them `G_i`. They satisfy `|G_i|>=b_i`. Since `U_t subset U_i`, every vertex of `G_i` still has at most `D` wrong-color neighbors in `U_t`.

The sets `G_i` are pairwise disjoint. Condition (3) therefore gives the two pools in Lemma 1. For (4), their total size is an integer greater than `h-2=2m-2`, so at least one color has at least `m` retained vertices. QED.

**Why the error budget is amortized.** The `Z_i` are disjoint. Moreover, an edge counted in `E_i` has one endpoint in `A_i` and the other in the then-future set `U_i`; it cannot be counted at any later cut. Thus each charged vertex or edge is charged at most once. There is no multiplication by the chain length, a logarithmic number of scales, or the number of classes.

The `E_i` need not be individually small. This is a sufficient **aggregate** certificate. It does not assert that every coloring supplies such a chain.

## 3. Low-waste cuts and the precise terminal condition

For a current host `U`, a nonempty `A subset U` with `|A|<=|U|/2`, an outside set `Z subset U\A`, and a color `c`, define

\[
 H_{c,D}^{U}(A,Z)
 =\bigl|\{a\in A:\deg_c(a,U\setminus(A\cup Z))\ge D+1\}\bigr|. \tag{5}
\]

Call `U` **`(alpha,D)`-cut-resilient in both colors** if

\[
 \boxed{\quad H_{c,D}^{U}(A,Z)+|Z|>\alpha|A|\quad}          \tag{6}
\]

for every such `A`, every `Z subset U\A`, and both colors `c`. Here `0<=alpha<1`. Only `|Z|<=alpha|A|` can give a nontrivial test.

Failure of (6) has a literal deletion interpretation. Put

\[
 P=\{a\in A:\deg_c(a,U\setminus(A\cup Z))\ge D+1\}.
\]

Delete `P` and `Z`, and retain `G=A\P` in the **opposite-color** pool. Each vertex of `G` has at most `D` color-`c` neighbors in the future core. The true waste is

\[
 w=|P|+|Z|\le\alpha|A|.                                    \tag{7}
\]

The whole removed block is `A union Z`, but `G` is not waste.

### Theorem 3 — unconditional two-color extraction

Let `d>=1`, `D>=0` be integers, `0<=alpha<1`, and `M=m+dD`. Suppose

\[
 \boxed{\quad N\ge\frac{h-2+2M}{1-\alpha}.\quad}           \tag{8}
\]

Every two-coloring on `N` vertices has either a monochromatic `Q_d`, or a partition

\[
 V=U\ \dot\cup\ P_R\ \dot\cup\ P_B\ \dot\cup\ W
\]

with all of the following properties:

\[
\begin{aligned}
 &|P_R|,|P_B|\le m-1,\\
 &\deg_B(v,U)\le D &&(v\in P_R),\\
 &\deg_R(v,U)\le D &&(v\in P_B),\\
 &|W|\le\frac{\alpha}{1-\alpha}(|P_R|+|P_B|),\\
 &|U|\ge N-\frac{|P_R|+|P_B|}{1-\alpha}
          \ge N-\frac{h-2}{1-\alpha}
          \ge\frac{2M}{1-\alpha},                         \tag{9}
\end{aligned}
\]

and `U` satisfies (6).

**Proof.** Start with `U=V` and empty pools and waste. Maintain that every stored pool vertex has at most `D` wrong-color neighbors in the current `U`.

If (6) fails, select `A,Z,c` witnessing failure, and let `P,G` be as in (7). Replace `U` by

\[
 U'=U\setminus(A\cup Z),
\]

put `G` into `P_(bar c)`, and put `P union Z` into `W`. Since old cores are nested, all previously stored adjacency guarantees survive.

Write `a=|A|`, `p=|P|`, `z=|Z|`, `g=a-p`, and `w=p+z`. From `p+z<=alpha a`,

\[
 g\ge(1-\alpha)a+z>0,\qquad
 w\le\frac{\alpha}{1-\alpha}g,\qquad
 a+z=g+w\le\frac g{1-\alpha}.                              \tag{10}
\]

Thus there is a real gain at every step, and summing (10) proves the waste and core-size inequalities in (9) whenever neither pool has reached `m`.

Before a step, the two pool sizes then total at most `h-2`. By (8),

\[
 |U|\ge\frac{2M}{1-\alpha}.
\]

Also `z<=alpha a` and `a<=|U|/2`, so the future core is large enough:

\[
 |U'|=|U|-a-z\ge |U|-(1+\alpha)a
                    \ge\frac{1-\alpha}{2}|U|\ge M.        \tag{11}
\]

If the new pool has at least `m` vertices, apply Lemma 1 to it and `U'`, obtaining an actual cube. Otherwise (9) is restored for the next step. Every step removes at least one vertex from `U`, so the process terminates. If it has not produced a cube, it terminates because no failure of (6) remains. Its final pools and waste give the asserted partition. QED.

This is a finite exhaustive-search procedure if necessary; no polynomial-time claim is made. It is valid for **every** initial coloring and every choice among admissible cuts. The bound is independent of the number of steps.

## 4. Explicit dimension-uniform corollaries

Fix

\[
 D=\left\lfloor\frac h{16d}\right\rfloor,\qquad M=m+dD.
\]

Then

\[
 dD\le h/16,\quad M\le9h/16,\quad D+1>h/(16d).             \tag{12}
\]

### Constant-expansion version

Set `alpha=1/8`. Condition (8) follows already from

\[
 N\ge (17h-16)/7,
\]

and hence from the convenient integer threshold `N>=5h/2`. The conclusion has

\[
 |W|\le(h-2)/7,\qquad |U|\ge N-8(h-2)/7.                   \tag{13}
\]

The core satisfies (6) with the fixed constant `1/8`, independently of `d`.

### Small-waste version

Set

\[
 s=\lceil\sqrt d\rceil,\qquad \alpha_d=1/(16s).
\]

Condition (8) follows from `N>=(34h-32)/15`, because `alpha_d<=1/16`; in particular `N>=5h/2` suffices for every dimension. Now

\[
 |W|\le\frac{|P_R|+|P_B|}{16s-1}
       \le\frac{h-2}{16s-1}
       \le\frac h{15s}\le\frac h{15\sqrt d},              \tag{14}
\]

and

\[
 |U|\ge N-(h-2)-\frac h{15\sqrt d}.                        \tag{15}
\]

There is no asymptotic cutoff or hidden small-dimensional constant. In dimensions with `D=0` the same proof uses exact one-sided monochromatic adjacency.

### Proved summability, and what it does not say

Let `d_0>d_1>...>d_r>=1` be a dimension-halving chain, `d_(j+1)=floor(d_j/2)`, stopped before zero. If the small-waste operation is applied at these dimensions, its waste bounds satisfy

\[
 \sum_{j=0}^r \frac{|W_j|}{2^{d_j}}
 \le\frac1{15}\sum_{j=0}^r d_j^{-1/2}
 \le\frac{2+\sqrt2}{15}<0.228.                             \tag{16}
\]

Indeed, `d_j>=2^(r-j) d_r>=2^(r-j)`, and the resulting geometric series sums to `1/(1-1/sqrt(2))=2+sqrt(2)`. Equivalently,

\[
 \sum_j 2^{d_0-d_j}|W_j|<0.228\,2^{d_0}.
\]

This bounds **discard costs**. It does not identify the different cores, turn the stored pools into compatible cube fibers, or prove a recurrence for `R(Q_d)`. In particular, the principal `P_R,P_B` masses cannot be silently discarded and called part of the summable error. They are retained with the explicit guarantees in (9).

## 5. What the robust core guarantees

The following are direct consequences of (6), not extra hypotheses. Here `U` is a core furnished by Theorem 3, so in particular `|U|>=2`; the estimates involving `h/d` use the choice of `D` in (12).

1. **Minimum degrees.** Taking `A={v}`, `Z=empty` shows
   
   \[
   \delta_R(U),\delta_B(U)\ge D+1>h/(16d).                 \tag{17}
   \]

2. **Many boundary-rich vertices, even after deletions.** If `0<|A|<=|U|/2` and `|Z|<=alpha|A|/2`, then more than `alpha|A|/2` vertices of `A` each have at least `D+1` color-`c` neighbors in `U\(A union Z)`, in either color. In particular,
   
   \[
   e_c(A,U\setminus(A\cup Z))>
                 \frac{\alpha(D+1)}2|A|.                 \tag{18}
   \]
   With `alpha=1/8`, the right-hand side exceeds `h|A|/(256d)` and the allowed deletion size is `|A|/16`.

3. **Vertex expansion.** For each color,
   
   \[
   |N_c(A)\setminus A|>\alpha|A|
       \quad(0<|A|\le |U|/2).                             \tag{19}
   \]
   Otherwise set `Z=N_c(A)\A` in (6), making `H=0`.

4. **Stability under a later exceptional deletion.** For `F subset U`, `A subset U\F`, and `0<|A|<=|U|/2`, more than `alpha|A|-|F|` vertices of `A` have at least `D+1` color-`c` neighbors in `(U\F)\A`. This is (6) with `Z=F`. If `alpha>0`, the conclusion of item 2 in particular survives for `|A|>=2|F|/alpha`.

Neither these properties nor mere minimum degree are asserted to imply a cube at linear scale.

## 6. How average cuts and separators are actually extracted

For disjoint `A,B`, the number of vertices of `A` having more than `D` color-`c` neighbors in `B` is at most `e_c(A,B)/(D+1)`. Therefore the condition

\[
 |Z|+\frac{e_c(A,U\setminus(A\cup Z))}{D+1}
                                      \le\alpha|A|        \tag{20}
\]

is a sufficient, verifiable failure of (6). It allows a trade between exceptional vertices and edge errors.

Three useful cases are:

* a separator `Z` of size at most `alpha|A|` killing all color-`c` edges across the cut;
* an average cut bound `e_c(A,U\A)<=alpha(D+1)|A|`, without a maximum-degree assumption;
* a **zero-waste** cut in which every vertex of `A` has at most `D` color-`c` neighbors in `U\A`. This last case works even when (20) fails: take `P=Z=empty` directly.

There is also an exact capped-neighborhood formula. Define

\[
 \Phi_{c,D}^{U}(A)=
   \sum_{v\in U\setminus A}\min\left\{1,\frac{\deg_c(v,A)}{D+1}\right\}.
\]

Then

\[
 \Phi_{c,D}^{U}(A)
 =\min_{Z\subseteq U\setminus A}
   \left(|Z|+\frac{e_c(A,U\setminus(A\cup Z))}{D+1}\right). \tag{21}
\]

**Proof.** Each outside vertex contributes independently: paying one puts it into `Z`; retaining it costs its incident color-`c` degree divided by `D+1`. Minimize each summand. QED.

Thus `Phi<=alpha|A|` always supplies an admissible low-waste cut. Every terminal core satisfies `Phi>alpha|A|`. The full condition (6) is stronger, since it also detects bounded-degree cuts of zero waste.

### A complete positive theorem for cut-reducible colorings

Under (8), suppose every induced host of order at least

\[
 N-(h-2)/(1-\alpha)
\]

has a cut violating (6). Then the coloring contains a monochromatic `Q_d`.

**Proof.** The core alternative of Theorem 3 would be an induced host in this size range with no such cut. QED.

It suffices to supply such cuts **along the actual surviving chain**; cuts for every induced host need not be constructed. Likewise, a supplied chain satisfying (3) or (4) certifies a full cube immediately. This is a genuine dimension-uniform positive class, with arbitrary depth and arbitrary internal colorings of the peeled blocks. It does not assume a bounded homogeneous template or a complete blow-up. The theorem's hypothesis is not asserted for arbitrary colorings.

### Two concrete applications, without a bound on template complexity

**Exact hierarchical colorings.** Suppose a binary tree recursively partitions the vertices down to singletons, and the edges across the two children of each node are all one color; the color may vary from node to node. Then `N>=2h-2` forces a monochromatic `Q_d`.

To see this, take `alpha=D=0` in Theorem 3 and always peel the smaller child of the current node, using the opposite color as the wrong color. These are zero-waste admissible cuts. If no cube has appeared, the current node still has at least `N-(h-2)>=h>=2` vertices, so another cut exists. A terminal core is impossible. This is a complete positive result for this hierarchical class, not an assertion that arbitrary colorings have such a tree. The tree may have `N` leaves and linear depth.

**Hereditary small balanced separators, with colors allowed to change.** Suppose every induced host `T` of size at least `N-8(h-2)/7` has a vertex set `S`, `|S|<=|T|/32`, such that in at least one color every component of `T\S` has size at most `|T|/2`. Then `N>=5h/2` forces a monochromatic `Q_d`.

Here is the full conversion, so a separator is not silently identified with a useful cut. There is a union `A` of components of `T\S` with `|T|/4<=|A|<=|T|/2`: take one component in this size range if it exists; otherwise add components, each smaller than `|T|/4`, until their union first reaches `|T|/4`. There is enough mass because `|T\S|>=31|T|/32`. Set `Z=S`. There are no edges of the selected color from `A` to `T\(A union Z)`, and `|Z|<=|T|/32<=|A|/8`. Thus this is an admissible cut for `alpha=1/8,D=0`. Theorem 3 applies since `(2h-2)/(1-1/8)<5h/2`, and its possible terminal core lies in the size range where a further separator is promised. This proves the claim.

The latter application allows arbitrary graphs inside the components and genuine exceptional vertices at each cut. Approximate versions are supplied by (20) and the more permissive degree-cut condition (6); the errors are not required to vanish. These are applications of the proved extraction, not proposed structural properties of all countercolorings.

## 7. Why this does not repeat the failed gluing, Hall, or template arguments

* No two smaller cubes are glued by an arbitrary perfect matching. The only final map is the explicitly injective parity construction in Lemma 1.
* A failure to extend one chosen injection is never interpreted as a blue cube. A stored vertex carries a proved wrong-degree guarantee to the **whole future core**.
* No homomorphism count, nearly injective map, or repair of a missing vertex is substituted for a full embedding.
* There is no assertion that random colorings contain large complete blow-ups. In a typical random coloring the cut process can stop immediately.
* A long sequence of tiny cuts is allowed. Pool sizes, waste, and later adjacency guarantees are summed exactly; no error is charged once per level.
* Errors need not be bounded at every vertex in both directions. Many stored vertices can have their wrong-color edges concentrated on the same core vertex. The reverse error degree can therefore be linear in the pool size, even though each stored vertex has only `D` errors.
* The old bounded-template theorem has a template-complexity/dimension condition. The present cut-chain and core statements have none. Their limitation is instead the explicit surviving-core branch.

The new extraction theorem uses a general bipartite completion ingredient, but does not import any maximum-degree Ramsey theorem with uncontrolled constants. The only appearance of `d` in the completion capacity is the displayed `dD`, bounded by `h/16` in (12).

## 8. The core branch is real, including at large spectral norm

Here is a quantitative scope check. It is not a Ramsey counterexample.

Let `N=3h`, `d>=10`, and let distinct host edges be independent, with each red-edge probability in `[1/4,3/4]`. Set `alpha=1/8` and use `D` from (12). Put

\[
 q_N=2N^{9/8}\exp(-49N/4096).
\]

With probability at least `1-8q_N`, the **entire** host satisfies (6). In particular it also satisfies (6) for the smaller `alpha_d`.

**Proof.** If (6) fails, there are `A,P,Z,c`, with `a=|A|<=N/2`, `p+z<=a/8`, such that all `g=a-p>=7a/8` vertices in `G=A\P` have at most `D` color-`c` neighbors in `B=V\(A union Z)`. We have `b=|B|>=7N/16` and

\[
 D\le N/(48d)\le b/8.
\]

The `gb` edge indicators are independent, each having color-`c` probability at least `1/4`. Their mean is at least `gb/4`. A multiplicative Chernoff bound, or domination by `Bin(gb,1/4)`, gives

\[
 \Pr[e_c(G,B)\le Dg]\le \exp(-gb/32)
                        \le\exp(-49aN/4096).
\]

For fixed `a`, overcount the choices by `N^a` for `A`, `2^a` for `P`, and `(a+1)N^(a/8)` for `Z`. Include both colors and sum over `a>=1`:

\[
 \Pr[\text{some failure}]\le
 2\sum_{a\ge1}(a+1)q_N^a
 =\frac{2q_N(2-q_N)}{(1-q_N)^2}\le8q_N.                    \tag{22}
\]

For `N>=2048`, `q_N<1/4`; it is decreasing there. Our `N>=3072` is safely in this range. QED.

For a large-spectrum example, split the host into two equal sets, take red probability `3/4` within sets and `1/4` between them, and let `s_v=+1,-1` be the balanced sign vector. Write `A_R` for red adjacency and `B_0=A_R-(J-I)/2`. For each unordered pair,

\[
 X_{uv}=s_us_v(A_R(u,v)-1/2)
\]

has range length one and mean `1/4`. Hoeffding's inequality gives

\[
 \Pr\left[s^TB_0s<N(N-1)/8\right]
                   \le\exp(-N(N-1)/64).                   \tag{23}
\]

Consequently `||B_0|| >= (N-1)/8` outside this exceptional event. If `p` is the **actual** red density, then

\[
 \frac{s^T(A_R-p(J-I))s}{N}
 =\frac{s^TB_0s}{N}+p-1/2
 \ge (N-5)/8\ge N/16                                    \tag{24}
\]

for `N>=10`. Combining (22)-(24) proves the existence of hosts satisfying the terminal cut condition with actual-density-centered spectral norm at least `N/16`.

These models also need not have a monochromatic `K_(m,m)`: its probability is at most

\[
 2\,3^N(3/4)^{m^2},\qquad m=N/6,                          \tag{25}
\]

by a union bound over disjoint two-sided choices. For completeness, `q_2048<10^(-6)` and `q_N` decreases for `N>=2048`. The logarithm of (25) is at most `1+2N-N^2/144`, using `log(4/3)>=1/4`; this upper bound is decreasing and less than `-1000` there. The bound in (23) is also less than `exp(-1000)`. Thus throughout the stated range the sum of (22), (23), and (25) is less than one. Large-spectrum, cut-resilient examples without either complete balanced biclique consequently exist simultaneously. They are **not asserted cube-free**. Their purpose is to show exactly why neither a universal complete-blow-up assertion nor automatic elimination of the robust-core branch is permissible.

## 9. What remains, and the precise level of completion

Established:

* Theorems 2 and 3 apply to actual, arbitrary red-blue complete hosts.
* Both successful outcomes are full injective cubes, not almost-cubes or homomorphisms.
* The general extraction threshold is (8); the convenient uniform threshold is `N>=5*2^d/2`.
* At most `2^d/(15sqrt(d))` vertices are genuinely discarded in the small-waste version. Up to `2^d-2` further vertices remain in two explicitly controlled pools.
* These discard costs are summable under dimension halving, as in (16).
* A cut-reducible coloring has a complete constant-multiplier cube theorem, irrespective of its cut depth or internal block complexity.

Not established:

* that (6), even together with the two pools, forces a monochromatic cube;
* a dimension-saving construction on a robust core that preserves all cube-coordinate compatibility and the pools' usable capacities;
* a recurrence for the actual normalized Ramsey numbers;
* a proof or disproof of `Erdos181.erdos_181`.

The missing step is now an explicit simultaneous two-color **robust-core** problem, with quantified reservoirs and a small exceptional set. This is a new direct positive module in this work, not a claim of literature priority and not a disguised complete proof.

## 10. Verification and specification audit

The mathematical proofs are above; finite checks supplement rather than replace them. The companion script is

```sh
python3 -u Submission/check_cube_direct_ramsey.py
```

All checks passed; the full output is `CubeDirectRamseyVerification.txt`. In particular:

* all 32,768 colorings of `K_6` were processed in the `d=2,alpha=D=0` specialization: 6,224 supplied a constructed `C_4`, and 26,544 ended at independently checked two-color connected cores;
* 768 further full extractions with nonzero degree or waste parameters gave 643 cube certificates and 125 cores; 347,024 terminal cut tests were checked independently;
* 3,840 cut-cost minima, 21,504 outside-deletion tests, and 12,096 admissible-cut accounting instances checked (10), (20), and (21);
* noisy chains included 99 discarded bad-row vertices and 99 separator vertices, as well as a 127-step zero-waste chain; aggregate error certificates and 24 hierarchical-coloring applications also succeeded;
* the general embedding checker audited 1,469 labeled cube certificates, 18,823 required edges, and 26,759 coordinate squares, including full `Q_10` embeddings;
* 15,680 separator/component packing cases, 4,000 exact uniform-threshold checks through dimension 2,000, and 1,000 dimension-halving budgets passed.

The tests do not certify or assume the unproved robust-core embedding implication. Terminal cores are legitimate outcomes even in hosts that may already contain a cube. The finite checks are separate from the all-dimensional proofs above.

Selected previous reports consulted: `CubeRecursionFindings.md`, `CubeRecursiveMatchingDisproof.md`, `CubeDensityInvestigation.md`, `CubeGlobalHallReduction.md`, `CubeSaturationStructure.md`, `CubeEndpointConflictInvestigation.md`, and the scope/results portions of the signed, finite-population, and spectral investigations. None supplies the missing implication above.

`Submission/Spec.lean` retains SHA-256

`9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`.

No Lean specification, definitions, axioms, or theorem statements were changed. These new results are rigorous paper proofs, not newly Lean-formalized theorems.
