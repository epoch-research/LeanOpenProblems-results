# Independent attack C: coherent grids in algebraic and intersection colorings

## Status — partial results, not a settlement

I have **not proved or disproved**
\[
\exists C>0\ \forall d\geq 0:\quad R(Q_d)\leq C2^d.
\]
No improved upper bound for arbitrary two-colorings is established here, and
no superlinear Ramsey lower bound is established.

What is proved below is that several genuinely unbounded structural families
cannot give a superlinear lower bound. The embeddings are ordinary **injective**
graph embeddings, not induced embeddings, homomorphisms, or embeddings of an
arbitrary-matching recursive substitute for the cube.

Here and throughout, the displayed color rule specifies red, and all other
edges are blue. The rules apply only to pairs of distinct vertices.

| Vertex set, of cardinality `N` | Red rule | Proven conclusion |
|---|---|---|
| All `a` by `b` matrices over a finite field of order `q >= 3` | `rank(X-Y) <= s` | A monochromatic cube with more than `N/4` vertices, for every rank threshold `s` |
| All `k`-subspaces of `F_q^r` | `dim(U intersect V) >= t` | A monochromatic cube with more than `N/8` vertices, for every `q,r,k,t` in the ranges below |
| All permutations in `S_r`, `r >= 20` | At least `t` agreements | A monochromatic cube with more than `N/4` vertices, for every `0 <= t <= r` |
| All `k`-subsets of `[r]`, `2 <= k <= r` | Nonempty intersection | A red cube with more than `N/(4e)` vertices |

The set-intersection example is not explained by a linear-sized monochromatic
complete bipartite graph. When `r=k^2` and `k -> infinity`, **neither color has
a complete bipartite graph with both sides a fixed positive fraction of `N`**.
A proof, including the needed spectral calculation, is in Section 6.

The common positive mechanism is a *coherent Cartesian grid*: coordinate changes
are compatible on every square, so no arbitrary matching is mistaken for a cube
coordinate. In some threshold regimes, a complementary-color greedy embedding
replaces the grid. Section 7 proves that these two certificates are **not** an
exhaustive dichotomy for arbitrary colorings.

No claim of priority is made for these auxiliary results. No Lean proof of them
is claimed. The mathematical proofs are given here, without using either
`sorry` declaration in `Submission/Spec.lean`; that file was not changed.

## 1. Conventions and a coherent-coordinate embedding lemma

Write `Q_d` for the graph on `{0,1}^d` whose edges change exactly one coordinate;
`Q_0` has one vertex. A copy in a graph is an injective map taking every cube
edge to an edge of that graph. Extra edges are irrelevant. All logarithms below
are base 2 unless written `ln`. The number `e` is the base of the natural
logarithm.

**Lemma 1 (two-coordinate grid).** Let `G` be a finite simple graph. Suppose
`X,Y` are nonempty finite sets and there is an injection
\[
\Phi:X\times Y\longrightarrow V(G)
\]
with both properties:

* for every `x` and every distinct `y,y'`, the pair
  `Phi(x,y), Phi(x,y')` is an edge of `G`;
* for every `y` and every distinct `x,x'`, the pair
  `Phi(x,y), Phi(x',y)` is an edge of `G`.

Then `G` contains
\[
Q_{\lfloor\log |X|\rfloor+\lfloor\log |Y|\rfloor}.
\tag{1}
\]
In particular the order of this cube is greater than `|X||Y|/4`, and its
dimension is at least `floor(log(|X||Y|))-1`.

**Proof.** Set `u=floor(log |X|)` and `v=floor(log |Y|)`. Choose injections
`alpha:{0,1}^u -> X` and `beta:{0,1}^v -> Y`. Map
\[
(a,b)\longmapsto\Phi(\alpha(a),\beta(b)).
\]
The map is injective. An edge of `Q_{u+v}` changes exactly one of its two
blocks; the other block is unchanged. The corresponding clause of the
hypothesis gives the desired edge. Finally
\[
2^u>|X|/2,\qquad 2^v>|Y|/2,
\]
and `floor(A)+floor(B) >= floor(A+B)-1`. This proves everything. `□`

Equivalently, the hypothesis is the existence of a subgraph
`K_|X| square K_|Y|`, with `square` denoting the Cartesian graph product.
There is no requirement about pairs differing in both coordinates. In
particular the number of rows and columns can both grow without bound.

## 2. The complementary-color certificate

**Lemma 2 (greedy embedding).** Let `F` be a simple graph on `N` vertices and
suppose its complement has maximum degree at most `b`. Every graph `H` on `h`
vertices, of maximum degree at most `Delta`, embeds in `F` if
\[
h+\Delta b\leq N.
\tag{2}
\]

**Proof.** Embed the vertices of `H` in any order. At a given step there are at
most `h-1` used vertices. Each already embedded neighbor forbids at most `b`
additional vertices, namely its nonneighbors other than itself. There are at
most `Delta` such neighbors. Thus at most `h-1+Delta b <= N-1` vertices are
forbidden. Choose a remaining vertex. This maintains injectivity and every
required edge. `□`

For example, if `N>=2`, `D=floor(log N)-1 >= 0`, and
\[
b\log N\leq N/2,
\tag{3}
\]
then Lemma 2 embeds `Q_D`, since `2^D<=N/2` and `D<=log N`.
For `N=2,3` this assertion simply concerns `Q_0`.

## 3. Every matrix-rank threshold has a constant-ratio cube

**Theorem 3.** Let `q>=3` be a prime power, let `a,b>=1` be integers, and let
`0<=s<=min(a,b)` be an integer. On all `a` by `b` matrices over `F_q`, color
\[
XY\text{ red}\quad\Longleftrightarrow\quad
\operatorname{rank}(X-Y)\leq s.
\tag{4}
\]
Put `N=q^(ab)` and `D=floor(log N)-1`. There is a red or blue copy of `Q_D`.
In particular there is a monochromatic cube of order greater than `N/4`.

**Proof.** Transposition allows us to assume `a<=b`. Equivalently we may regard
the matrices as linear maps from `F_q^a` to `F_q^b`; transposition preserves
all ranks.

If `s=0`, every edge is blue, so the conclusion is immediate.

### 3.1. Large rank threshold: a spanning red grid

Suppose `2s>=a`. Decompose the domain as a direct sum of dimensions
`a_1=floor(a/2)` and `a_2=ceil(a/2)`. A map is determined independently by
its restrictions to these two summands. These restrictions give sets `X,Y`
of cardinalities `q^(a_1 b)` and `q^(a_2 b)`.

If two maps differ in only their first restriction, their difference has
rank at most `a_1<=s`; the corresponding assertion holds for the second
restriction. Thus the whole matrix space is a red grid of the kind in
Lemma 1, of order `N`. This gives a red cube of dimension at least `D`.
A zero-dimensional summand, when `a=1`, causes no difficulty: its set of maps
has cardinality one.

### 3.2. Small rank threshold: the blue graph is sufficiently complete

Now suppose `1<=s<a/2`; in particular `a>=3`. Let
\[
E=(a-s)(b-s).
\]
For any fixed matrix, its number of red neighbors is smaller than
\[
2Nq^{-E}.
\tag{5}
\]
Here is a complete counting proof. Every map of rank at most `s` vanishes on
some `(a-s)`-dimensional subspace of its domain. For a prescribed such subspace,
there are `q^(bs)` possible maps. The number of subspaces is
`{a brack a-s}_q={a brack s}_q`, by the usual subspace-counting formula, and
\[
{a\brack s}_q
=q^{s(a-s)}\prod_{i=1}^{s}
 \frac{1-q^{-(a-s+i)}}{1-q^{-i}}
<2q^{s(a-s)}.
\tag{6}
\]
Indeed,
\[
\prod_{i=1}^{s}(1-q^{-i})
\geq1-\sum_{i=1}^{s}q^{-i}
>1-\frac1{q-1}\geq\frac12,
\]
where the product inequality follows by induction. A union bound over the
possible kernels now gives (5), even before removing the zero difference.

We next verify the constants uniformly, not just asymptotically. Since
`a>=2s+1` and `b>=a`,
\[
\begin{aligned}
E&\geq(s+1)(b-s)\\
 &=2(b-1)+(s-1)(b-s-2)\geq2(b-1).
\end{aligned}
\tag{7}
\]
For every pair of integers `b,q>=3`,
\[
4b^2\log q\leq q^{2b-2}.
\tag{8}
\]
To check this elementary inequality, first use `log q<=q-1`, which follows
from `q<=2^(q-1)` by induction. For `b=3` it is enough to check
`36(q-1)<=q^4`. At `q=3` this is `72<=81`; for `q>=4` use
`q^4>=64q>36(q-1)`. Increasing `b` by one multiplies the right side by
`q^2`, while multiplying `b^2` by `((b+1)/b)^2 <= (4/3)^2 < q^2`.
This proves (8) for every `b>=3`.

Let `b_R` denote the maximum red degree, not the matrix parameter `b`.
Equations (5)--(8) imply
\[
\begin{aligned}
\frac{b_R\log N}{N}
&<2q^{-E}\,ab\log q\\
&\leq2q^{-2b+2}\,b^2\log q\leq\frac12.
\end{aligned}
\tag{9}
\]
Apply Lemma 2 to the blue graph and `Q_D`. This completes the proof. `□`

**Characteristic two.** The question already supplies the stronger fact
that every two-color binary Cayley coloring has a monochromatic spanning
cube. Thus if `q` is a power of two, the rank-threshold coloring in fact has
a spanning cube of order `N`, since its additive group is a binary vector
space. This is not claimed as a new result here. For completeness, if the
nonzero vectors of a binary vector space are partitioned into two colors,
one color spans the space: two proper linear subspaces cannot cover the
space. Choose a basis in that color. Its subset sums give a bijection from
a binary cube, and each cube edge has a basis vector as its difference.

The work in Sections 3.1--3.2 is needed in particular for odd characteristic;
it does not assert that arbitrary rank-layer colorings in odd characteristic
have the same property. The threshold hypothesis is essential to this proof.

## 4. Every Grassmannian intersection-dimension threshold

**Theorem 4.** Let `q>=2` be any prime power, let `r>=1`, `0<=k<=r`, and
`0<=t<=k` be integers. Let `Omega` be the set of all `k`-dimensional subspaces
of `F_q^r`, and set `N=|Omega|`. Color distinct `U,V` by
\[
UV\text{ red}\quad\Longleftrightarrow\quad
\dim(U\cap V)\geq t.
\tag{10}
\]
There is a monochromatic ordinary cube of order greater than `N/8`.
Consequently, for every `d>=0`, `N>=8*2^d` guarantees a monochromatic `Q_d`
in every coloring of the form (10), uniformly in all its parameters.

**Proof.** If `k=0` or `k=r`, then `N=1` and `Q_0` suffices. Otherwise fix a
direct-sum decomposition `F_q^r=E_0 direct-sum F_0`, with dimensions `k` and
`r-k`. Consider the set of graphs of all linear maps `f:E_0 -> F_0`.
It has cardinality
\[
M=q^{k(r-k)}.
\]
The graph construction is injective, and
\[
\dim(\operatorname{graph}(f)\cap\operatorname{graph}(g))
=k-\operatorname{rank}(f-g).
\tag{11}
\]
Indeed, the common vectors are exactly `(x,f(x))` with `(f-g)(x)=0`.
Thus (10) restricted to this set is the rank-threshold coloring with
threshold `k-t`. If that threshold is at least `min(k,r-k)`, all its edges
are red. Otherwise Theorem 3 applies when `q>=3`.

Counting ordered bases and dividing by the number of bases of a fixed
`k`-space gives
\[
N={r\brack k}_q
=M\prod_{i=1}^{k}
 \frac{1-q^{-(r-k+i)}}{1-q^{-i}}.
\tag{12}
\]
For `q>=3`, the product estimate used in (6) gives
\[
\frac MN
=\prod_{i=1}^{k}
 \frac{1-q^{-i}}{1-q^{-(r-k+i)}}>\frac12.
\tag{13}
\]
Theorem 3, or completeness in the all-red case, gives a cube of order greater
than `M/4 > N/8`.

For `q=2`, the binary Cayley observation following Theorem 3 gives a cube
using all `M` graph subspaces. To bound its relative size, for every `k>=1`,
\[
\prod_{i=1}^{k}(1-2^{-i})>\frac14.
\tag{14}
\]
For `k<=3` this is immediate. For `k>=4`, the first three factors have product
`21/64`, while the remaining factors have product at least
\[
1-\sum_{i=4}^{k}2^{-i}>1-\frac18=\frac78.
\]
Their product is greater than `147/512 > 1/4`. Equations (12) and (14) give
`M>N/4`, stronger than needed. All embeddings used are injective. `□`

This includes unbounded field sizes, dimensions, and thresholds, not just
nonzero intersection or a fixed finite blow-up template.

## 5. Every agreement threshold on the symmetric group

**Theorem 5.** Let `r>=20` and `0<=t<=r` be integers. On `S_r`, whose order
is `N=r!`, color
\[
\pi\sigma\text{ red}\quad\Longleftrightarrow\quad
|\{i\in[r]:\pi(i)=\sigma(i)\}|\geq t.
\tag{15}
\]
There is a monochromatic `Q_D`, where `D=floor(log N)-1`; hence there is
a monochromatic cube of order greater than `N/4`.

The restriction `r>=20` is an explicit sufficient range, not a conjectured
sharp boundary. Since only finitely many orders occur for `r<20`, it has
no effect on excluding a superlinear lower-bound sequence from this family.

**Proof.** If `t=0`, the red graph is complete.

### 5.1. At most a quarter of the positions required: a spanning red grid

Suppose `1<=t<=r/4`. Let `T` be a fixed `t`-element subset of `[r]`, and let
`H` be its pointwise stabilizer, of order `(r-t)!`. Let `P` be the set of all
injections `p:T -> [r]`, of cardinality `r!/(r-t)!`.

For each `p`, choose a permutation `tau_p` extending `p` whose support is
contained in `T union p(T)`. Such a choice always exists. Define `tau_p=p`
on `T`, choose any bijection
\[
p(T)\setminus T\longrightarrow T\setminus p(T),
\]
and fix every point outside `T union p(T)`. The specified images partition
`T union p(T)`, so this is a permutation.

Define
\[
\Phi:P\times H\longrightarrow S_r,\qquad
\Phi(p,h)=\tau_p\circ h.
\tag{16}
\]
This is a bijection. The restriction of `Phi(p,h)` to `T` is `p`; once `p`
is known, `h` is recovered by composition with `tau_p^(-1)`. Conversely for
any `g in S_r`, take `p=g|_T` and `h=tau_p^(-1)g`, which fixes `T` pointwise.

For fixed `p`, all permutations `Phi(p,h)` agree on `T`, so they form a
red clique. For fixed `h`, the permutations `Phi(p,h)` and `Phi(p',h)` agree
whenever
\[
h(i)\notin T\cup p(T)\cup p'(T).
\]
There are at least `r-3t>=t` such positions. Thus fixed `h` also gives a
red clique. Equation (16) is a spanning red grid, so Lemma 1 proves the claim.

### 5.2. More than a quarter required: blue greedy embedding

Now suppose `t>r/4`. For a fixed permutation, the number of other
permutations agreeing with it on at least `t` positions is at most
\[
\binom rt(r-t)!-1=\frac{N}{t!}-1.
\tag{17}
\]
To see this, count permutations satisfying equality on each prescribed
`t`-set of positions and take a union bound. The union includes the fixed
permutation; remove it afterwards. Thus the maximum red degree is at most
`N/t!-1`.

Here `t>=6`, because `r>=20` and `t>r/4`. For every integer `t>=6`,
\[
t!\geq8t^2.
\tag{18}
\]
At `t=6` this is `720>=288`; the inductive step follows from
`t^2>=t+1`, since
`(t+1)t! >= 8(t+1)t^2 >= 8(t+1)^2`.
Also `4t<=2^t` for `t>=4`, by induction, so `log(4t)<=t`.
Consequently
\[
2\log N=2\log(r!)\leq2r\log r
<8t\log(4t)\leq8t^2\leq t!.
\tag{19}
\]
Equations (17)--(19) imply that the blue graph satisfies (3).
Lemma 2 embeds the required `Q_D`. `□`

This is a nonabelian, growing-template family. The proof uses a transversal
with controlled support, not a binary color basis and not the chromatic
number of any recursive substitute for a cube. It does not handle arbitrary
colorings by conjugacy class, nor parity-of-agreement colorings.

## 6. Set intersections: large cubes without linear homogeneous pairs

### 6.1. A red cube on a constant fraction of every uniform layer

**Theorem 6.** Let `2<=k<=r` be integers, let
`Omega=binom([r],k)`, and put `N=binom(r,k)`. Color two distinct members
red if they intersect and blue if they are disjoint. Then the red graph
contains a cube with more than `N/(4e)` vertices.

**Proof.** Choose a random subset `T` of `[r]` by including each point
independently with probability `1/k`. For every fixed `A in Omega`,
\[
\Pr(|A\cap T|=1)=(1-1/k)^{k-1}\geq e^{-1}.
\tag{20}
\]
For the inequality, write the reciprocal as
`(1+1/(k-1))^(k-1) <= e`, using `ln(1+x)<=x`.
Thus some deterministic `T` has at least `N/e` members of `Omega` meeting
it in exactly one point. This is a counting/averaging proof, not a numerical
search. Fix such a `T`.

Those members are precisely
\[
\Phi(x,B)=\{x\}\cup B,
\quad x\in T,\quad
B\in\binom{[r]\setminus T}{k-1}.
\tag{21}
\]
The map is injective, and its domain has cardinality at least `N/e`.
Both factors are nonempty. For fixed `x`, all sets contain `x`. For fixed
`B`, all sets contain the nonempty set `B`, since `k>=2`. Hence (21) is a
red grid. Apply Lemma 1. `□`

The choice of `T` can also be made explicit, without any search: take the first
`floor((r+1)/k)` ground-set elements. Indeed, for
`1<=u<r-k+1`, the consecutive values `F(u)=u binom(r-u,k-1)` satisfy
\[
\frac{F(u+1)}{F(u)}
=\frac{(u+1)(r-u-k+1)}{u(r-u)}\geq1
\quad\Longleftrightarrow\quad
u\leq\frac{r+1}{k}-1.
\]
Thus `floor((r+1)/k)` is a maximizing size (with a possible tie). Since the
averaging argument already proves the maximum is at least `N/e`, this fixed
choice has the required bound.

For `k=1`, the blue graph is complete and contains a cube of order greater
than `N/2`. The `k=0` layer has one vertex.

### 6.2. Neither color need have a linear-sized complete bipartite graph

A *homogeneous pair* here means two disjoint, nonempty vertex families
`A,B subset Omega` such that all their cross edges have one color.

**Theorem 7.** In Theorem 6, specialize to `r=k^2`, `k>=2`. Every homogeneous
pair satisfies
\[
\min(|A|,|B|)\leq\frac{N}{k-1}.
\tag{22}
\]
Thus for every fixed `delta>0`, when `k>1+1/delta` there is no homogeneous
pair with both sides of size at least `delta N`. Nevertheless Theorem 6
still gives a red cube of order greater than `N/(4e)`.

**Proof.** We give the needed calculation for all `r>=2k`. Let `K` be the
adjacency operator of the blue disjointness graph on `Omega`. It is symmetric
and regular of degree
\[
D_0=\binom{r-k}{k}.
\]
On the space perpendicular to constants its operator norm is at most
\[
\lambda=D_0\frac{k}{r-k}.
\tag{23}
\]
Here is a derivation, so that no unproved spectral assertion about Kneser
graphs is required. For each `S subset [r]` of size at most `k`, put
`f_S(U)=1_{S subset U}`. Let `U_j` be the span of these functions with
`|S|=j`. The spaces are nested: for `|S|=j-1`,
\[
\sum_{x\notin S} f_{S\cup\{x\}}=(k-j+1)f_S.
\tag{24}
\]
Also `U_0` consists of constants, and `U_k` is the entire space, since
`f_S` with `|S|=k` is the indicator of a single vertex.

For `|S|=j`, direct counting gives
\[
\begin{aligned}
(Kf_S)(U)
&=\binom{r-k-j}{k-j}\,1_{U\cap S=\varnothing}\\
&=\binom{r-k-j}{k-j}
  \sum_{J\subseteq S}(-1)^{|J|}f_J(U).
\end{aligned}
\tag{25}
\]
Consequently `K` preserves every `U_j` and, for `1<=j<=k`, acts on the quotient
`U_j/U_(j-1)` by the scalar
\[
\theta_j=(-1)^j\binom{r-k-j}{k-j}.
\tag{26}
\]
Because `K` is symmetric, the orthogonal spaces
`W_j=U_j intersect U_(j-1)^perp` are invariant. Equation (25) implies that
`K` acts on `W_j` by exactly `theta_j`: subtracting that scalar produces
a vector in both `W_j` and `U_(j-1)`, hence zero. Together these orthogonal
spaces and `U_0` span the whole space.

For `1<=j<k`, consecutive absolute values in (26) have ratio
\[
\frac{k-j}{r-k-j}\leq1.
\]
The largest possible nonconstant absolute value is therefore
`binom(r-k-1,k-1)=D_0 k/(r-k)`. This proves (23), including any cases in
which an orthogonal space has dimension zero.

Set `p=D_0/N`. For arbitrary vertex families `A,B`, subtract their constant
indicator components and apply (23) and Cauchy--Schwarz. This gives
\[
\left|e_K(A,B)-p|A||B|\right|
\leq\lambda\sqrt{|A||B|},
\tag{27}
\]
where `e_K(A,B)` counts ordered pairs `(a,b) in A times B` that are disjoint
as subsets of `[r]`.

Now let `r=k^2`. Then `k/(r-k)=1/(k-1)` and
\[
p=\prod_{i=0}^{k-1}\left(1-\frac{k}{r-i}\right)
\leq(1-1/k)^k\leq e^{-1}<\frac12.
\tag{28}
\]
For a red homogeneous pair, `e_K(A,B)=0`, so (27) yields
\[
\sqrt{|A||B|}\leq\lambda/p=\frac{N}{k-1}.
\]
For a blue homogeneous pair, `e_K(A,B)=|A||B|`, so (27)--(28) yield
\[
\sqrt{|A||B|}\leq\frac{\lambda}{1-p}
=\frac{p}{1-p}\frac{N}{k-1}<\frac{N}{k-1}.
\]
Since the smaller side is at most the geometric mean, (22) follows. `□`

Thus a search confined to linear homogeneous pairs would miss this positive
family entirely. The grid's large cube is assembled coherently from many
smaller cliques; no pair of its rows has to be joined completely.

## 7. What this does — and does not — imply for the global conjecture

### 7.1. Exact scope of the lower-bound exclusions

For each family above, the constant is uniform in the parameters explicitly
quantified in its theorem. Thus no sequence of those colorings with
`N_j / 2^(d_j) -> infinity` can avoid monochromatic `Q_(d_j)` indefinitely.
The fixed finite exceptions in Theorem 5 cannot affect such a sequence:
a coloring avoiding `Q_d` has `d>=1`, whereas those exceptions have bounded
`N`.

The exclusions do **not** include:

* arbitrary two-colorings of complete graphs;
* arbitrary colorings of rank layers over odd fields;
* arbitrary conjugacy-class colorings of symmetric groups;
* arbitrary intersection-size colorings of uniform set layers;
* arbitrary dense restrictions or arbitrary perturbations of the vertex/edge
  families in the theorems.

For example, Theorem 6 proves only the nonempty-intersection threshold on a
uniform set layer; it is not a theorem about all intersection thresholds there.
Theorem 4, in contrast, does cover all dimension thresholds on full
Grassmannians, because its large graph chart preserves the rank rule exactly.

### 7.2. The two certificates are not a universal dichotomy

It would be incorrect to infer that every large coloring either has a
linear-order monochromatic grid or has a linear-order almost-complete color
subgraph to which Lemma 2 applies. The following makes this failure precise.

**Proposition 8.** Fix `0<eta<1`. For every sufficiently large integer `N`,
there is a red/blue coloring of `K_N` with both properties:

1. Every monochromatic two-coordinate grid in Lemma 1 has order less than
   `ceil(3 log N)^2`, hence less than `eta N`.
2. For every vertex set `W` of size at least `eta N`, each color has edge
   density between `1/3` and `2/3` in `W`. In particular neither color on
   such a `W` has complementary maximum degree at most
   `|W|/(2 log |W|)`.

These colorings are **not asserted to be cube-free**.

**Proof.** Color the edges independently, each color with probability `1/2`.
Let `h=ceil(3 log N)`. The probability of a monochromatic `K_h` is at most
\[
2\binom{N}{h}2^{-\binom{h}{2}}\leq2N^h2^{-h(h-1)/2}=o(1).
\tag{29}
\]
A monochromatic `K_a square K_b` has cliques of sizes `a` and `b`. If there
is no monochromatic `K_h`, then both `a,b<h`, so `ab<h^2`.

For a fixed `W` of size `w`, its red edge count is binomial with
`m=binom(w,2)` trials and parameter `1/2`. Its probability of lying outside
`[m/3,2m/3]` is at most `2 exp(-m/18)`. For completeness, this follows by
applying the exponential Markov inequality to
\[
\mathbb E e^{u(X-m/2)}=\cosh(u/2)^m\leq e^{mu^2/8}
\]
with `u=2/3`, and also to `-X`. A union bound over at most `2^N` vertex
sets gives failure probability at most
\[
2^{N+1}\exp\bigl(-\eta N(\eta N-1)/36\bigr)=o(1).
\tag{30}
\]
Both desired events therefore occur simultaneously for all sufficiently
large `N`.

Under the density conclusion, either complementary color has average degree
at least `(w-1)/3`; its maximum degree is at least this large. For all
sufficiently large `w`, this exceeds `w/(2 log w)`, proving the final
assertion. `□`

Thus the positive mechanism found here is a sufficient certificate for
specific structured hosts, not a universal embedding principle.

### 7.3. A precise remaining branch

For a fixed `eta>0`, either of the following certificates would give a
monochromatic cube of order greater than `eta N/4`:

* a monochromatic grid of order at least `eta N`, by Lemma 1;
* a set `W`, `|W|>=eta N`, on which one color has complementary maximum
  degree at most `|W|/(2 log |W|)`, by Lemma 2.

To turn this approach into a global proof one would still have to control
colorings possessing **neither** certificate, or use a different embedding
argument altogether. Proposition 8 shows that this remaining branch really
exists. No theorem embedding a constant-ratio cube in every member of that
branch is proved here. Failure of the tested algebraic lower-bound families
is not evidence sufficient to remove this logical gap.

## 8. References, integrity, and verification scope

The following corpus items were checked for context, not used as unproved
steps in the structural arguments:

* Jacob Fox and Benny Sudakov, *Density theorems for bipartite graphs and
  related Ramsey-type results*, `/corpus/src/0707.4159/0707.4159.tex`.
  Its cube corollary states `R(Q_d) <= d 2^(2d+5)` for positive `d`.
  This is a verified bound available in the corpus, not a claim about the
  best current bound.
* Gonzalo Fiz Pontiveros, Simon Griffiths, Robert Morris, David Saxton, and
  Jozef Skokan, *The Ramsey number of the clique and the hypercube*,
  `/corpus/src/1306.0461/1306.0461.tex`. It proves
  `r(K_s,Q_d)=(s-1)(2^d-1)+1` for every fixed `s` and every
  `d>=d_0(s)`. This is an off-diagonal theorem with a parameter-dependent
  threshold, not a solution of the diagonal question.

Verification in this report is mathematical: injectivity, all required
edge conditions, both threshold cases, the counting bounds, and the uniform
constant inequalities are proved explicitly. The operator bound in Section 6
is derived rather than assumed. Proposition 8 is an analytic probabilistic
existence proof, not a search over small colorings. No numerical experiment
is a premise of any theorem. The results have not been formalized in Lean.

`Submission/Spec.lean` was left unchanged. Its SHA-256 before and after this
investigation is

```
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```

Neither the conjectural theorem nor the purported disproof declaration in
that file is invoked. The global Ramsey conjecture remains unresolved by
this investigation.
