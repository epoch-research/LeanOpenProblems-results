# Buffered third-colour reuse and a hereditary frustration witness

Write `tau(G)` for the minimum number of edges whose deletion makes a finite simple graph `G` bipartite. Distances below are ordinary graph distances, with distance infinity between different components. For an edge set `F`, write `V(F)` for its endpoints. Subgraphs in the statements are actual subgraphs, not minors, suppressed graphs, or graphs with added edges.

## Main theorem

**Every finite graph `G` with `chi(G) >= 4` has a subgraph `H` such that**

\[
 t=\tau(H)\ge2,\qquad |V(H)|\le (t+1)^{16t}.                 \tag{1}
\]

The proof below is a mathematical proof, not a Lean formalization. Its key invariant is a *localized independent odd-cycle transversal*, not an arbitrary three-colouring of the defect core. An independent buffer and the inductive transversal are far apart, so both use the same third colour.

The size bound in (1) is exponential in `t log t`, **not polynomial in `t`**. In particular, it is consistent with the expanding projective-annulus counterexamples to every power-law witness. It does not assert an order bound for chromatic-critical or frustration-critical graphs.

### A sufficiently slow divergent function

Set

\[
 B(t)=(t+1)^{16t}\quad(t\ge1),\qquad
 f_*(n)=\min\{t\ge1:n\le B(t)\}-1.                          \tag{2}
\]

This is a nondecreasing divergent integer function, of order `log n / log log n`. By (1), if every finite subgraph `H` of a graph `G` satisfies

\[
 \tau(H)\le f_*(|V(H)|),
\]

then `G` is three-colourable. For infinite graphs this follows from the finite result by the usual compactness theorem for three-colourings.

One explicit, substantially slower, choice is

\[
 f_0(n)=\max\{0,\lfloor\log_2\log_2(n+4)\rfloor-6\}.        \tag{3}
\]

An unshifted logarithm-logarithm with an initial zero interval also works:

\[
 f_1(n)=
 \begin{cases}
 0,&n\le2^{960},\\
 \lfloor\log_2\log_2(n+4)\rfloor,&n>2^{960}.
 \end{cases}                                               \tag{4}
\]

The estimates establishing these explicit choices appear in Section 6.

## 1. Short-cycle parity and the sparse certificate

For `L >= 3`, a short-parity support is an edge set `S` satisfying

\[
 |S\cap E(C)|\equiv |E(C)|\pmod2
 \quad\text{for every cycle }C\text{ of length at most }L.
                                                               \tag{5}
\]

Short **even** cycles are included. Let `a_L(G)` be the minimum size of such a support.

If `p:V(G)->F_2` is any two-colouring, its monochromatic edges `F` satisfy the same equation on **every** cycle, since

\[
 1_F(uv)=1+p(u)+p(v).
\]

Thus `a_L(G) <= tau(G) <= |F|`.

**Sparse-certificate lemma.** If `a_L(G) >= k >= 1`, there is `H subseteq G` with

\[
 \tau(H)\ge k,\qquad |V(H)|\le L+L^2+\cdots+L^k\le2L^k.     \tag{6}
\]

**Proof.** Build a search tree starting with `D=empty`. At a node with `|D|<k`, choose a cycle `C_D` of length at most `L` on which `D` has the wrong parity, and branch to `D union {e}` for each edge `e in E(C_D) minus D`. Stop at depth `k`. A node with no possible child is allowed. Let `H` be the union of the selected cycles. There are at most `1+L+...+L^(k-1)` selected cycles.

If a cut of `H` has bad-edge set `A` with `|A|<k`, follow the tree while maintaining `D subseteq A`. Since `A` has the correct parity on `C_D` and `D` does not, some edge of `A` lies in `E(C_D) minus D`. Thus one can follow another branch until `k` distinct bad edges have been selected, a contradiction. This proves (6). Every edge counted is an original edge of `G`.

## 2. A minimum short support stays near an old cut

**Support-locality lemma.** Let `F` be the monochromatic-edge set of a two-colouring of `G`. Let `S` be a minimum-cardinality support for (5), and put `s=|S|`. Then

\[
 V(S)\subseteq N_{sL}^G(V(F)).                              \tag{7}
\]

The assertion is vacuous for `S=empty`.

**Proof.** Form an auxiliary graph whose vertices are the edges of `F union S`; two distinct such edges are adjacent if they lie on a common cycle of length at most `L`.

Every component meeting `S` must meet `F`. Otherwise, let `A` be the edge set forming a component with no edge of `F`. It is a nonempty subset of `S`. Any short cycle meeting `A` has all its edges from `F union S` in this one component. In particular it contains no edge of `F`, so it is even. Equation (5) then says that it meets `A` evenly. Consequently deleting `A` from `S` preserves every equation (5), contradicting minimality of `S`.

For any edge of `S`, take a shortest path in this auxiliary graph to an edge of `F`, stopping at the first edge of `F`. Before the final vertex all its vertices are distinct edges of `S minus F`, so its length is at most `s`. Consecutive edges lie on a cycle of length at most `L`. Their endpoints are at distance at most `L` in `G` (in fact at most `floor(L/2)`). Concatenating these short routes proves (7).

This lemma bounds distance, not the number of vertices in a neighbourhood. Degrees can be arbitrarily large.

## 3. Buffered parity surgery

The following strengthens the interpolation in `Erdos74Amplification.md` by reserving an arbitrary-width empty buffer around all defect terminals.

**Buffered-surgery lemma.** Let `p_0:V(G)->F_2` have monochromatic-edge set `F`, with `|F|=t`. Let `S` satisfy (5), with `|S|=s <= t`. Let `r >= 0` be an integer, and suppose

\[
 L\ge8t(r+2).                                              \tag{8}
\]

Put `W=V(F union S)`. There is an independent set `Z` in `G` such that:

1. `G-Z` has a two-colouring whose monochromatic-edge set is **exactly `S`**;
2. every vertex of `Z` is at distance at least `r+2` from `W` in `G`;
3. every vertex of `Z` is at distance at most `r+3` from `W` in `G`.

In particular no endpoint of `S` is removed.

**Proof.** Put `D=2r+4` and `P=G-(F union S)`. The colouring `p_0` is proper on `P`. On the terminal set `W`, construct a labelled auxiliary multigraph:

* retain every edge `uv in F union S`, with label `1+1_S(uv)` in `F_2`;
* for every pair of distinct terminals at `P`-distance at most `D`, choose a shortest such path and add an auxiliary edge labelled by its length modulo two.

A simple auxiliary cycle, including a two-edge cycle from parallel edges, traces a closed walk in `G` of length at most

\[
 D|W|\le D\,2(t+s)\le4tD=8t(r+2)\le L.
\]

Its label sum is zero. Indeed the labels sum `1+1_S` along the traced walk; decompose that walk into simple cycles and doubled edges, and use (5). Thus the auxiliary labels integrate to a map `q:W->F_2`.

For special edges,

\[
 q(u)+q(v)=1+1_S(uv).
\]

For terminals at `P`-distance at most `D`,

\[
 q(u)+p_0(u)=q(v)+p_0(v).
\]

Therefore the terminal sets

\[
 X=\{w\in W:q(w)\ne p_0(w)\},\qquad Y=W\setminus X
\]

have `d_P(X,Y)>D`.

For a vertex `v`, let `d=d_P(v,X)`. Colour `P` with colours `0,1,2` using the following table. The two entries are for `p_0(v)=0,1`, respectively:

| `d` | colour pair |
|---|---|
| `0 <= d <= r+1` | `(1,0)` |
| `d = r+2` | `(1,2)` |
| `d = r+3` | `(0,2)` |
| `d >= r+4`, or infinity | `(0,1)` |

This is proper on `P`: on every edge the `p_0` bit changes and the distance changes by at most one, and the table gives distinct colours for every such pair. It agrees with `q` on all terminals. Terminals in `X` have distance zero, and terminals in `Y` have distance at least `2r+5`.

Let `Z` be the vertices with colour `2`. They are at distances `r+2` or `r+3` from `X`. Also

\[
 d_P(Z,Y)\ge (2r+5)-(r+3)=r+2.
\]

Thus `d_P(Z,W)>=r+2` and `Z subseteq N_(r+3)^P(W)`.

The same lower distance bound holds in `G`: a path from outside `W` to its first vertex of `W` uses no edge of `F union S`, since both endpoints of every such edge lie in `W`. Hence its initial segment is a path in `P`.

The set `Z` is independent in `P`, and no edge of `F union S` is incident with `Z`, so it is independent in `G`. After deleting `Z`, the displayed colouring uses only `0,1`. Every edge of `P` is proper, every edge of `F minus S` is proper by the terminal labels, and every edge of `S` is monochromatic by those labels. This proves all three assertions.

## 4. The invariant that removes the extra colour

Assume that `G` contains no witness of type (1); explicitly, every subgraph `H` with `tau(H)>=2` satisfies

\[
 |V(H)|>(\tau(H)+1)^{16\tau(H)}.                           \tag{9}
\]

We prove the following stronger property by induction on `t`:

> For every two-colouring of `G` with bad-edge set `F` of size `t`, there is an independent set `I` such that `G-I` is bipartite and
>
> \[
> I\subseteq N_{t^8}^G(V(F)).                              \tag{10}
> \]
>
> For `t=0`, take `I=empty` and interpret the containment in the evident way.

The assertion is made simultaneously for all finite graphs satisfying (9), so it can be applied to induced subgraphs.

### Base cases

For `t=0`, the graph is bipartite. For `t=1`, choose one endpoint of the single edge of `F`. Deleting it removes all bad edges, and a singleton is independent; its distance from `V(F)` is zero.

### Inductive step

Let `t>=2`, and set

\[
 m=\lfloor\sqrt t\rfloor<t,\qquad r=m^8,\qquad
 L=8t(r+2),\qquad k=m+1.                                   \tag{11}
\]

First we claim `a_L(G)<=m`. Otherwise (6) gives a subgraph `H` with, writing `q=tau(H)`,

\[
 q\ge k\ge2,\qquad |V(H)|\le2L^k.
\]

Since `q>=m+1>sqrt(t)`, we have `t<q^2`. Also `m>=1`, so

\[
 L=8t(m^8+2)\le24t m^8\le24t^5\le24q^{10}.
\]

Using `k<=q`, `24<=(q+1)^5`, and `2<=(q+1)^q`, we obtain

\[
 |V(H)|\le2(24q^{10})^q\le(q+1)^{16q},                    \tag{12}
\]

contrary to (9). This proves the claim.

Choose a minimum short support `S`, with `s=|S|<=m`. Apply the buffered-surgery lemma with buffer parameter `r=m^8`. It gives an independent set `Z`, at distance at least `r+2` from `V(F union S)`, and a two-colouring of `G'=G-Z` with bad-edge set exactly `S`.

The hereditary condition (9) holds for `G'`. The inductive assertion applied to `G'` and this cut gives an independent set `I'` such that `G'-I'` is bipartite and

\[
 I'\subseteq N_{s^8}^{G'}(V(S))\subseteq N_r^{G}(V(S)).     \tag{13}
\]

For `s=0`, take `I'=empty`. Since `d_G(Z,V(S))>=r+2`, equations (13) and the triangle inequality show that there is **no edge between `Z` and `I'`**. Therefore

\[
 I=Z\cup I'
\]

is independent in `G`. Also `G-I=G'-I'` is bipartite. This is the precise reuse of the third colour; no chromatic-number preservation under deletion of `Z` is assumed.

It remains to check the radius invariant. By (7), `V(S) subseteq N_(sL)^G(V(F))`. The surgery lemma puts `Z` within distance `r+3` of `V(F union S)`, while (13) puts `I'` within distance `r` of `V(S)`. Consequently

\[
 I\subseteq N_{sL+r+3}^G(V(F))
   \subseteq N_{mL+r+3}^G(V(F)).                           \tag{14}
\]

For `t=2,3`, the last radius is respectively `52,76`, both at most `t^8`. For `t>=4`, using `r=m^8>=1` and `tm>=2`,

\[
\begin{aligned}
 mL+r+3
 &=8tm(r+2)+r+3\\
 &\le24tmr+4r\\
 &\le26tmr
  =26t m^9
 \le26t^{11/2}
 \le t^8,
\end{aligned}                                             \tag{15}
\]

where the last inequality follows from `t^(5/2)>=4^(5/2)=32>=26`.

This proves (10) and completes the induction.

## 5. Deduction of the main theorem

Any finite graph has a two-colouring with finitely many bad edges. If it satisfies (9), the invariant supplies an independent set `I` whose deletion leaves a bipartite graph. Two-colour `G-I` and give every vertex of `I` a third colour. Hence `chi(G)<=3`.

Contraposition proves (1), with `tau(H)>=2`. The independent sets used at different stages may be very large; only their separation and their distance from the successive supports are controlled. No bound on neighbourhood sizes, graph degree, or critical graph order has entered the proof.

## 6. Verification of the explicit divergent profiles

For (2), `B(t)` is increasing and unbounded, so `f_*` is well-defined, nondecreasing, and divergent. A witness with `n<=B(t)` has `f_*(n)<=t-1`, contradicting `tau(H)<=f_*(n)`.

For (3), it suffices by monotonicity to prove `f_0(B(t))<=t-1`. Since `B(t)>=4` and `log_2(t+1)<=t`,

\[
 \log_2(B(t)+4)
 \le1+16t\log_2(t+1)
 \le17t^2.
\]

The elementary inequality `t^2<=2^(t+1)` holds for every positive integer `t`: check `t=1,2,3`, and use `((t+1)/t)^2<2` for `t>=3`. Therefore

\[
 \log_2(B(t)+4)\le17t^2\le34\,2^t<2^{t+6}.
\]

It follows that `floor(log_2 log_2(B(t)+4))<=t+5`, and hence `f_0(B(t))<=t-1`.

For (4), if `t<=15`, then `B(t)<=B(15)=16^240=2^960`, where `f_1` vanishes. If `t>=16`, then

\[
 \log_2(B(t)+4)\le17t^2<2^t.
\]

The strict inequality holds at `t=16` and persists thereafter, because `2^t/t^2` is increasing for integers `t>=3`. Consequently `floor(log_2 log_2(B(t)+4))<=t-1`. This proves that (4) also excludes every witness in (1).

Three colours cannot be replaced by two for any divergent profile: choose an odd cycle so long that the profile is at least one at its order. Every proper subgraph of that cycle is bipartite.

## 7. Why the earlier obstructions do not invalidate this induction

* **The bare `+1` cannot just be removed.** For example, in `M(K_3)` the base triangle is the endpoint graph of a minimum three-edge cut support, but the whole graph is four-chromatic. The present argument instead uses the stronger *localized independent-transversal invariant* (10) under the hereditary no-witness hypothesis.
* **No compatible sequence of minimum cuts is assumed.** Different stages can have entirely different terminal phases. The interpolation removes an independent layer between those phases; only separation from the next correction is retained.
* **No critical-order bound is assumed.** The radius `t^8` can enclose arbitrarily many vertices. The vertex bound on the witness comes exclusively from the sparse certificate (6).
* **The descent does not preserve chromatic number.** That is unnecessary. If the smaller graph has no small witness, the induction gives a *localized* third-colour class, which can coexist with the old buffer. An arbitrary three-colouring would not suffice.
* **All hereditary transfers are to actual induced subgraphs.** The next graph is `G-Z`; a witness extracted at any later stage is still an actual subgraph of the original graph.

## Verification record

The companion script `check_Erdos74BufferedColoring.py` checks the explicit interpolation, exact residual cut support, support locality, separated reuse of colour three, and the integer size/radius estimates. These checks are independent consistency tests, not replacements for the mathematical proofs above. Their saved output is in `Erdos74BufferedColoringChecks.txt`.

All checks passed:

* 7,986 possible adjacent-layer/bit configurations, with buffer widths from 0 through 32;
* 31,368 minimum-support/cut/scale locality instances, with the support minima obtained by exhaustive original-edge enumeration;
* 2,883 homogeneous support-component pruning instances;
* 2,400 arbitrary-support surgery tests, checking every conclusion in all 1,267 cases with balanced auxiliary labels;
* six long odd cycles, where the support is not a full cut support and the buffer width ranges up to 128;
* a 72,390-vertex graph with two genuine surgeries `4 -> 2 -> 0`, verifying that the two nonempty buffers together are independent and give an explicit proper three-colouring;
* a connected four-chromatic graph, with a first surgery `4 -> 2` followed by extraction of an actual four-vertex subgraph of frustration two;
* the radius/scale inequalities for every integer `2 <= t <= 100000`, and the witness/profile inequalities for `1 <= q < 500`.

Reproduce with

    cd /workspace/leanproject
    python3 Submission/check_Erdos74BufferedColoring.py

No claim of a literature priority check or of a completed Lean formalization is made.
