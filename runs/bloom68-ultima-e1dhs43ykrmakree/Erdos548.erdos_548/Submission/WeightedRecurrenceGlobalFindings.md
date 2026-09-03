# Weighted global recurrence: unresolved, with a bounded-block transport obstruction

## Outcome and scope

**Neither the proposed recurrence nor unrestricted Erdős–Sós is proved here.
No counterexample to the proposed recurrence is obtained.** In particular, the
counterexamples below are to a class of **proof mechanisms**, not to (CW).
This distinction is essential: the weighted recurrence holds, with a constant
escape probability, in the very hosts used for the transport obstruction.

The new rigorous results are:

1. **Bounded-block transport can require super-polynomial weighted
   congestion in actual critical hosts, simultaneously at every leaf of
   subcubic targets.** Thus a
   switching proof cannot simply route blocked mass by changing a bounded
   number of images at a time and charge every intermediate state at most
   `2e(G)` times its degree-corrected weight. This fails even though enough
   extendible mass exists globally. One-vertex Gibbs resampling is actually
   reducible into blocked and extendible classes in these examples.
2. The same examples give a super-polynomial conductance obstruction for
   **every bounded-block Markov chain** having the proposed injective Gibbs
   measure as its stationary law, reversible or not. Stationarity of that
   law does not supply a rapid reembedding procedure.
3. An exact **critical-host composition lemma** permits selected hub degrees
   to become arbitrarily large while retaining all proper induced-set
   inequalities and surplus exactly `epsilon=1`. It is a legitimate test
   family for a future nonlocal argument, not an assumed augmentation.
4. The scalar cut consequences of criticality and a correct free-attachment
   aggregate inequality are recorded below. Neither controls the prescribed
   leaf-parent, so neither closes the recurrence.

This is global negative information about local weighted transport, not
another positive terminal case of Erdős–Sós. A proof based on genuinely
nonlocal branch switching, a different congestion accounting, or an entirely
different global inequality remains possible. I did not obtain such a proof.

Only this note, `WeightedRecurrenceGlobalChecks.py`, and its log were added.
No Lean file or specification was changed.

---

## 1. The exact claim and the unfilled scalar-to-shape step

Write

\[
 a=(k-1)/2,\qquad 2m=(k-1)n+\epsilon,\qquad
 \epsilon\in\{1,2\},
\]

and assume

\[
 e_G(S)\le a|S|\qquad(S\subsetneq V(G)).                       \tag{1}
\]

For a nontrivial tree R, use the **host degrees** throughout:

\[
 w_R(f)=\prod_{u\in V(R)}d_G(f(u))^{1-d_R(u)},\qquad
 Z(R,G)=\sum_{f\in\operatorname{Emb}(R,G)}w_R(f).
\]

For k>=2, the desired assertion is, for every k-edge tree T and every leaf
ell with parent p, putting `U=T-ell`,

\[
 \boxed{2m\,Z(T,G)\ \ge\ \epsilon Z(U,G).}                    \tag{CW}
\]

For k>=2, the exact identity is

\[
 Z(T,G)=\sum_{f\in\operatorname{Emb}(U,G)}w_U(f)
 \frac{|N(f(p))\setminus f(V(U))|}{d_G(f(p))}.                \tag{2}
\]

The total unconditioned tree-walk mass is `2m`. Conditioning on injectivity
changes root marginals. No stationary-root substitution is used here.

### 1.1 What exact criticality does give for scalar potentials

Let `I_G(X)` count edges incident with X, with internal edges counted once.
For every nonempty X, (1) gives

\[
 I_G(X)=m-e_G(V\setminus X)\ge a|X|+\epsilon/2.               \tag{3}
\]

For any nonnegative vertex potential x, integration over its level sets
therefore gives the exact cut-dual bounds

\[
 \sum_{uv\in E(G)}\max(x_u,x_v)
 \ge a\sum_v x_v+\frac\epsilon2\max_v x_v,                   \tag{4}
\]

\[
 \sum_{uv\in E(G)}\min(x_u,x_v)
 \le a\sum_v x_v+\frac\epsilon2\min_v x_v.                   \tag{5}
\]

Indeed, the left sides are respectively the integrals of incident-edge and
induced-edge counts of `{v:x_v>t}`. The full level set contributes the extra
surplus in (5); every nonempty level set contributes it in (4). Indicator
potentials recover (1) and (3), so these are exact reformulations of the
scalar cut information, not extra embedding information.

The missing implication is a **shape-dependent** comparison between these
cut functionals and the expectation in (2). Replacing x by a rooted embedding
marginal does not establish that comparison. An occupied chord may contribute
to an incidence budget without being an available image for ell.

### 1.2 A valid aggregate which does not prescribe the parent

Let U be any k-vertex tree, and let `U+p` mean adding a new leaf at p. For an
embedding f with image S, write `b(S)=e_G(S,V(G)\S)`. Since `|S|=k<n`,

\[
 e_G(S)+b(S)\ge ak+\epsilon/2,\qquad e_G(S)\le\binom k2=ak.
\]

Thus `b(S)>=1`, using integrality. If `Delta=Delta(G)`, summing (2) over all
possible parents gives the correct inequality

\[
 \boxed{\sum_{p\in V(U)}Z(U+p,G)\ge \frac{Z(U,G)}\Delta
                                      \ge\frac{Z(U,G)}{n-1}.} \tag{6}
\]

The reason is simply
`sum_p fresh(f(p))/d(f(p)) >= b(S)/Delta` pointwise.

But the terms on the left are generally **different target trees**. This
cannot replace the fixed-parent inequality (CW). In particular, (6) is not
an induction establishing containment of the originally prescribed T.

---

## 2. An exact state-space description in critical split hosts

This section specializes the proved matching/partition identity in
`DegreeCorrectedMeasureFindings.md`. Its purpose here is to analyze **all
intermediate embedding states and all bounded-block moves**, not to claim a
new positive split-host theorem.

For an integer r>=1, let

\[
 G_r=K_r\vee\overline K_{b_r},\qquad b_r=r^2+1,\qquad
 D=r(r+1),\qquad q=\frac rD=\frac1{r+1}.
\]

Call the clique A and the independent class B. Set `k=2r`. Then

\[
 n=r^2+r+1,\qquad 2m=r(2r^2+r+1)=(2r-1)n+1.                 \tag{7}
\]

For a vertex set using x vertices of A and y of B, its doubled surplus is

\[
 x(x-2r)+(2x-2r+1)y.                                        \tag{8}
\]

This is nonpositive for `x<=r-1`. If `x=r` and the set is proper, it is
`y-r^2<=0`. Thus these are actual critical hosts, with **all** the required
proper induced-set inequalities and `epsilon=1`.

### 2.1 Target, perfect matching, and ancestor-closed patterns

Let R be a rooted tree on r vertices, with root h. Add a new leaf ell at h
to form H. Subdivide every edge of H once, obtaining T, and put `U=T-ell`.
The deleted leaf's parent p is the subdivision vertex on `ell-h`.

For every original vertex v in R, denote by `m_v` the subdivision vertex on
its parent edge; at the root `m_h=p`. The r edges `v m_v` form a perfect
matching of U. The remaining edges are `parent(v) m_v`, for `v!=h`.

In any U-embedding into G_r, the preimage of B is independent. It has at
least r vertices because A has capacity r, and at most r by the displayed
perfect matching. Hence it has **exactly r**, with exactly one endpoint of
each matching edge in B. All r vertices of A are occupied.

Define

\[
 W=\{v\in V(R): f(v)\in A\}.
\]

Then `f(m_v) in B` exactly when `v in W`. The edge
`parent(v) m_v` forbids `v in W, parent(v) notin W`. Consequently the
feasible patterns are precisely:

* `W=empty`; or
* a nonempty **ancestor-closed** subset W of the rooted tree R.

Conversely every such pattern is realizable, since every A--B edge and
every edge inside A exists. In a nonempty pattern the A--A tree edges are
exactly the edges of the boundary `partial_R W`. Write

\[
 j(W)=|E_R(W,V(R)\setminus W)|.
\]

The root h belongs to every nonempty W. Therefore

\[
 \boxed{\text{the embedding extends at p exactly when }W=\varnothing.} \tag{9}
\]

For nonempty W, p lies in B and all its r neighbors A are already occupied.
For W empty, p lies in A, and exactly `b_r-r` neighbors are fresh.

### 2.2 The exact weight of an entire pattern

Each pattern has `r!(b_r)_r` labelled embeddings. Since U has `2r-1` edges,
its degree exponents on A and B are respectively

\[
 r-1+j(W),\qquad r-1-j(W).
\]

Put

\[
 M_r=\frac{r!(b_r)_r}{D^{r-1}r^{r-1}},\qquad
 \alpha_r=\frac{b_r-r}{D}=\frac{r^2-r+1}{r(r+1)}.
\]

Then the total weight of the pattern W is exactly

\[
 \boxed{M_r q^{j(W)}.}                                      \tag{10}
\]

Both the extendible pattern `W=empty` and the completely blocked pattern
`W=V(R)` have weight `M_r`.

Let

\[
 C_R(q)=\sum_{\substack{W\ne\varnothing\\W\text{ ancestor-closed}}}
                  q^{j(W)}.
\]

Equations (2), (9), and (10) give

\[
 \boxed{Z(U,G_r)=M_r(1+C_R(q)),\qquad Z(T,G_r)=M_r\alpha_r.}   \tag{11}
\]

Given the boundary of a nonempty W, W is the root component after those
edges are deleted. Thus there is at most one such W per boundary edge set,
and

\[
 C_R(q)\le(1+q)^{r-1}<e.
\]

For r>=2, `alpha_r>=1/2`, so

\[
 \frac{Z(T,G_r)}{Z(U,G_r)}>\frac1{2(1+e)}>\frac18.            \tag{12}
\]

For r=1 the ratio is `1/4`, and (CW) is equality. These examples therefore
**satisfy (CW)**. What follows is not a recurrence counterexample.

As a small nonstationarity check, at r=2 and R a rooted two-vertex path,
`P(f(p) in A | injective U)=3/7`, whereas stationary degree mass on A is
`6/11`. The distinction persists despite the root-free definition of w.

---

## 3. What bounded-block reembedding means

Two U-embeddings are b-local neighbors if their images differ at at most b
vertices of U. There is no restriction on how their new images are chosen:
a move can be an arbitrary valid simultaneous reembedding of those vertices.
Thus this permits more than just a particular greedy or Gibbs update rule.

Because every matching pair has exactly one image in A, changing membership
of one original vertex in W also changes membership of its matching partner.
Consequently every b-local move projects to

\[
 |W\mathbin\triangle W'|\le j,\qquad j=\lfloor b/2\rfloor.    \tag{13}
\]

In particular, a **one-vertex update cannot change W at all**. A one-site
Gibbs/heat-bath chain has closed blocked classes of positive mass, and cannot
transport their mass to an extendible state by any number of updates.
Conditioning that chain on injectivity does not make it irreducible.

For the congestion statements, a weighted routing means a collection of
nonnegative-mass paths in this b-local graph, transporting the weight of a
specified source set to extendible U-states. An intermediate-state bound C
means that the total mass of paths visiting any state f is at most `C w_U(f)`.
Loops can be erased without worsening such a bound. No reversibility is
assumed for this routing definition.

If a separating set X has total weight `w(X)`, and the source weight is M,
then every such routing necessarily satisfies

\[
 \boxed{C\ge M/w(X).}                                       \tag{14}
\]

This is just a cut bound: every routed unit must visit X. It is a condition
on this kind of **intermediate-state accounting**, not a necessary condition
for an arbitrary direct injection or for the total-mass inequality (CW).

---

## 4. A simple exponential obstruction, with an explicit small parameter

Take R to be the `(r-1)`-leaf star rooted at its center h. Equivalently, H is
the r-leaf star, and T is its full subdivision.

A nonempty ancestor-closed W consists of h and a set of s of its `r-1`
children. Its boundary has size `r-1-s`. For two-image updates, (13) permits
one W-vertex to change. The only blocked pattern adjacent to the extendible
pattern W empty is therefore `W={h}`. Its total weight is

\[
 M_r q^{r-1}.
\]

The completely blocked pattern `W=V(R)` has weight `M_r`. Every two-image
routing of this one source pattern to extendible states must pass through
`W={h}`, so (14) gives

\[
 \boxed{C\ge q^{-(r-1)}=(r+1)^{r-1}.}                       \tag{15}
\]

For example, at r=5,

\[
 k=10,\quad n=31,\quad 2m=280,\qquad C\ge6^4=1296>280.
\]

Yet the actual recurrence margin is

\[
 \frac{2m\,Z(T,G_5)}{Z(U,G_5)}
   =\frac{254016}{3697}>68.
\]

There is abundant extendible mass. It is the **bounded-congestion local
route to that mass** that fails.

More generally, for b-image updates with `j=floor(b/2)>=1`, an incoming
blocked pattern at W empty must have `1<=|W|<=j`. Its total weight is at most

\[
 M_r S_{r,j},\qquad
 S_{r,j}=\sum_{s=0}^{j-1}\binom{r-1}{s}q^{r-1-s}             \tag{16}
\]

when `j<=r`. Thus `C>=1/S_{r,j}`. For fixed j,

\[
 S_{r,j}\le j r^{j-1}(r+1)^{-(r-j)},
\]

so the required congestion grows faster than any polynomial. Allowing an
arbitrary long sequence of bounded-size switches does not remove this cut
obstruction.

---

## 5. The obstruction also occurs for subcubic nonspiders

The preceding star is not needed for the main negative conclusion. Here is
a subcubic family, together with a proof that also allows nonmonotone moves.

**Theorem (scope made explicit).** For every fixed block size b>=2 and
fixed exponent d, there are arbitrarily large pairs `(T,G)`, with T subcubic
and G an actual critical host, such that **at every leaf** the weighted
escape ratio is greater than `1/8`, but transporting the indicated blocked
pattern to extendible states by b-local moves requires intermediate-state
congestion greater than `n^d`. Hence this statement does not contradict (CW).

Let R_h be the perfect rooted binary tree of height h, with

\[
 r=|R_h|=2^{h+1}-1.
\]

Construct H, T, U as in Section 2 by attaching ell at the root and subdividing.
For h>=2, T is a subcubic nonspider, with `2r` edges. Continue to use the
actual critical host G_r and its exact degree-corrected weights.

### 5.1 Exact boundary barrier for single-vertex pattern changes

Consider paths of ancestor-closed subsets of R_h, starting at `V(R_h)` and
ending at empty, in which each step adds or removes one vertex. They need
not be monotone. Let B_h be the least possible maximum boundary size along
such a path. Then

\[
 B_0=0,\qquad \boxed{B_h=h+1\quad(h\ge1).}                   \tag{17}
\]

**Upper bound.** Clear one child subtree, then the other, then the root.
While the second child is being cleared, the already empty first child
contributes one boundary edge. Starting with `B_1=2`, this gives
`B_h<=B_{h-1}+1=h+1` for h>=2.

**Lower bound, including backtracking.** Stop the path the first time the
whole set becomes empty. Until that last step the root is present. For a
child subtree Q, its contribution to the parent's boundary is:

* zero if Q is full;
* one if Q is empty;
* its internal boundary if Q is nonempty and proper, hence at least one.

Look at the **last** time each of the two child subtrees is full. For a
single-vertex path these last times are distinct: leaving the two full
child subtrees cannot happen in one step. After the later last-full time,
the other child is never full again and contributes at least one throughout.
The later child still has a full-to-empty path. By induction its internal
boundary reaches `B_{h-1}=h`, at a time when it is nonempty. The total boundary
therefore reaches at least `h+1`. The base h=1 follows because `{root}` has
boundary two before the first empty state. This proves (17).

### 5.2 Passing from bounded-block moves to a high-boundary cut

Let `j=floor(b/2)>=1`. Any two ancestor-closed sets differing at at most j
vertices can be connected by at most j single-vertex changes: first remove
vertices in decreasing depth, then add vertices in increasing depth.
Ancestor-closure is preserved. Each change alters the boundary by at most
two, since R_h is subcubic and the root has degree two.

Thus the intermediate boundary during this refinement is at most the larger
endpoint boundary plus `2(j-1)`. Put

\[
 \boxed{t=h+1-2(j-1)=h+3-2j,}                               \tag{18}
\]

and assume t>=1. A b-local embedding path from the completely blocked pattern
to the extendible pattern must visit an embedding whose pattern has boundary
at least t. Otherwise refining its projected steps would contradict (17).
For b=2 or b=3, `j=1`, so the sharp threshold is `t=h+1`.

### 5.3 Total weight of the separating states

Let X_t be all U-embeddings with `j(W)>=t`. There is at most one nonempty
ancestor-closed W per boundary edge set. By (10),

\[
 \frac{w(X_t)}{M_r}
 \le\sum_{s=t}^{r-1}\binom{r-1}{s}q^s
 \le\sum_{s=t}^{\infty}\frac1{s!}
 \le\frac2{t!}.                                             \tag{19}
\]

The second inequality uses `(r-1)q<1`; the last follows by bounding the
successive factorial ratios by a geometric series. These are positive
coefficient estimates, not a stationary-root or Jensen assertion.

The completely blocked pattern has weight `M_r`. Therefore every b-local
routing of its weight to extendible states, with the intermediate-state
accounting of Section 3, has

\[
 \boxed{C\ge t!/2.}                                         \tag{20}
\]

For every fixed b, `t=h-O_b(1)` while `r=2^{h+1}-1`. Hence `t!/2` grows
faster than any fixed power of r, n, or m. For example, the last half of the
factors of t! already give `(t/2)^(t/2)`, whose logarithm is
`Omega(h log h)`, whereas the logarithm of any such fixed power is `O(h)`.

There is no dependence on a chosen local switching rule: (13), the boundary
barrier, and the cut-weight bound apply to **all** b-local moves.

### 5.4 Choosing another leaf does not avoid the obstruction

The result is not confined to the specially attached leaf ell. Let ell' be
**any** leaf of H (equivalently, of T), and use `U'=T-ell'`. The matching
pattern description applies with `R'=H-ell'` rooted at the original
neighbor of ell' in H.

If ell' is the special added leaf, Section 5.1 applies directly. Otherwise
ell' lies in one of the two height-`h-1` binary subtrees below H's central
root. The other subtree Q is untouched. When R' is rooted at the neighbor
of ell', Q is a descendant subtree with exactly the usual binary rooting.

Intersecting an ancestor-closed full-to-empty pattern path in R' with Q
produces an ancestor-closed full-to-empty path in Q, with at most one
vertex changed per step. Every internal boundary edge of Q is also a
boundary edge of R'. For h>=2, (17) therefore gives a boundary barrier at
least `B_(h-1)=h`, for **every** choice of ell'. Refining block moves as
before yields the common threshold

\[
 \boxed{t_{\rm all}=h-2(j-1),\qquad
        C\ge t_{\rm all}!/2}                              \tag{21}
\]

whenever `t_all>=1`. The high-boundary weight estimate is unchanged because
it holds for any rooted R'. Thus the same subcubic T and the same critical
G_r give the super-polynomial obstruction simultaneously at every leaf.
Their actual weighted escape ratios still exceed `1/8` at every leaf by
(11)--(12).

### 5.5 An explicit subcubic parameter exceeding the proposed budget

For two-image moves, choose h=24. Then

\[
 r=33554431,\qquad k=67108862,\qquad
 n=1125899873288193,
\]

and

\[
 C\ge\frac{24!}{2}=310224200866619719680000
    >75557858096414956978174=2m                             \tag{22}
\]

**at every leaf**. At the specially attached leaf, the sharper bound is
`C>=25!/2=7755605021665492992000000`.

This is an exact, finite member of the proved family; neither the huge host
nor its embeddings need to be enumerated. It is again **not a counterexample
to (CW)**: (12) gives an escape ratio greater than `1/8` at every leaf.
The obstruction concerns the proposed polynomial local transport budget
despite that large escape mass.

### 5.6 Consequence for all stationary local Gibbs kernels

Let `mu(f)=w_U(f)/Z(U,G_r)`. In the projected pattern graph, remove the
patterns of boundary at least t. Let C be the union of the remaining pattern
components reachable from W empty, and take all embeddings with patterns
in C. By Section 5.2 the full blocked pattern is outside C. Consequently
both C and its complement have weight at least `M_r`.

Every actual b-local transition from outside C into C has its outside state
in X_t. For **any** Markov chain with stationary law mu and b-local
transitions, stationarity balances the total flow across the cut, giving

\[
 Q(C,C^c)=Q(C^c,C)\le\mu(X_t).
\]

Thus the cut conductance, using the smaller side, is at most

\[
 \boxed{\frac{Q(C,C^c)}{\min\{\mu(C),\mu(C^c)\}}\le\frac2{t!}.} \tag{23}
\]

The two sides are substantial: by (11), each has probability at least
`1/(1+e)>1/4`. This also proves a mixing obstruction without assuming a
particular transition rule. Start from mu conditioned on the smaller side
S of the cut. At every later time the law is at most `mu/mu(S)` pointwise,
by stationarity. A union bound shows that crossing the cut in L steps has
probability at most `L Q(S,S^c)/mu(S) <= 2L/t!`. For `L<=t!/16`, the law
therefore differs from mu by at least `1/2-1/8=3/8` on the event S. Thus
worst-case total-variation mixing to distance `1/4` requires `Omega(t!)`
steps. If the chain is reducible, the failure is stronger still.

This uses only stationarity, not detailed balance: the equal cut flows
follow by computing `mu(C)` before and after one step. Thus nonreversibility
with the same stationary law does not bypass the obstruction either. The
same reasoning uses `t_all` at the other leaves.

---

## 6. A new exact critical-host composition for nonlocal investigations

The degree energy in the original split host is unusually uniform within
each class. To investigate whether unequal hub degrees could break (CW),
I used the following construction. It establishes full criticality without
assuming that an arbitrary protected state can be augmented.

### Composition lemma

Let r>=2, `1<=h<r`, and `s=r-h`. Let F be an actual critical host for
parameter `2s`, with doubled surplus `epsilon_F in {1,2}`. Put

\[
 \gamma=\epsilon_F-1\in\{0,1\},\qquad
 C=K_r\vee\overline K_{r^2-\gamma}.
\]

Choose any h vertices A_0 of C's clique. Take C and F disjoint, and add every
edge between A_0 and F, with no other cross edges. Call the resulting graph G.
Then G is an actual critical host for `k=2r`, with

\[
 \boxed{2e(G)=(2r-1)|G|+1.}                                 \tag{24}
\]

**Proof.** The core C has doubled surplus `-gamma` at threshold `2r-1`.
Every nonempty proper core subset X has surplus at most `-gamma-1`.
To check the latter, a subset with x clique vertices and y independent
vertices has surplus

\[
 x(x-2r)+(2x-2r+1)y.
\]

If x=r and X is proper, this is at most `-gamma-1`. If `1<=x<=r-1`, it is
at most `-(2r-1)<=-3`; if x=0 and X is nonempty, it is again at most
`-(2r-1)`. These imply the assertion for both possible gamma.

The full surplus of G is

\[
 -\gamma+\epsilon_F=1,
\]

because the h added incidences per F vertex change its density threshold
from `2s-1` to `2r-1`.

For an arbitrary induced set `S=X union Y`, with `X subseteq C` and
`Y subseteq F`, set `x_0=|X intersect A_0|`. Its doubled surplus is exactly

\[
 \sigma_G(S)=\sigma_C(X)+\sigma_F(Y)-2(h-x_0)|Y|,             \tag{25}
\]

where each sigma uses its own indicated parameter. If Y is proper in F,
`sigma_F(Y)<=0`, and all terms on the right are nonpositive. If `Y=F` and
X is nonempty proper in C, the first two terms sum to at most
`-gamma-1+epsilon_F=0`. If X is empty and `Y=F`, the surplus is
`epsilon_F-2h|F|<=0`. The remaining case `X=C,Y=F` is the full graph.
This proves every proper-set inequality. QED.

### Arbitrarily unequal hub degrees, with a concrete lower-rank host

Let `F_L` be the prism `C_L square K_2`, L>=3, with one added cross-layer
nonedge, say between `a_0` and `b_1`. The prism is cubic and contains a
Hamiltonian cycle, so every nonempty proper vertex cut has at least two base edges.
For every proper S,

\[
 2e_{F_L}(S)
 =3|S|-|\delta_{\rm prism}(S)|
     +2\mathbf1_{\{a_0,b_1\}\subseteq S}
 \le3|S|.
\]

Also `2e(F_L)=3|F_L|+2`. Thus F_L is critical for parameter 4, with
`epsilon_F=2`.

In the composition lemma take `h=r-2`, for any r>=3. The outer graph has

\[
 n=r^2+r-1+2L,\qquad 2m=(2r-1)n+1.
\]

Its vertex degrees are:

* `n-1` at the selected r-2 clique vertices;
* `r^2+r-2` at the other two clique vertices;
* r at the `r^2-1` old independent vertices;
* r+1 at ordinary F_L vertices, and r+2 at the two added-edge endpoints.

In particular the ratio between the first two hub degrees is unbounded as
L grows, with **no loss of induced criticality**.

### Why this did not produce a recurrence counterexample

It is tempting to compare only embeddings supported in the old core: large
degrees at some clique vertices can favor putting them at U-leaves and
penalize putting them at internal vertices. That is not a valid comparison
of the full partition functions. The new F part also supports embeddings
of U and T, including embeddings split among several branches through A_0.
Their multiplicities can compensate the large-degree penalties.

I did not prove a bound on all those competing embeddings that reverses
(CW), nor a general lower bound that establishes it. The construction is
therefore a rigorous new test family, **not** a counterexample and not an
augmentation lemma. Ignoring the extra embeddings would give a spurious
negative result.

---

## 7. What a correct replacement would have to change

The obstruction in Sections 3--5 is not lack of total mass. Both the blocked
full pattern and the extendible pattern have weight `M_r`, and the full
escape ratio is bounded below by a constant. The obstruction is the
**small weight of every bounded-local bridge between them**.

Consequently:

* One-site resampling cannot be assumed to explore the injective Gibbs law.
  Its blocked components can be closed.
* Permitting all two-image switches connects the pattern space in these
  examples: a legal W-vertex change is realized by swapping the images of
  that vertex and its matching partner. Nevertheless it does not supply a
  polynomial intermediate-state congestion or mixing bound. Even subcubic
  targets require super-polynomial bounds of this kind, at every leaf.
* A global injection can still bypass the bottleneck. For example, an entire
  matched branch can be switched at once; charging only endpoints is very
  different from charging all intermediate embeddings by their Gibbs weight.
  The split-host partition proof effectively makes such a nonlocal comparison.
* Thus any switching replacement using this measure needs genuinely
  nonlocal branch changes, a rigorously different accounting of intermediate
  mass, or a direct global inequality that never routes through these rare
  intermediate states. Moves through noninjective maps, pruned subtrees,
  forests, or augmented-memory states are not covered by this obstruction,
  but would need their own proved progress and measure comparison. Merely
  declaring a local chain reversible, retaining exact incidence surplus,
  or preserving the current embedding does not do it.
* The scalar identities (4)--(5), matrix/forest totals that forget target
  shape, and the free-parent aggregate (6) still require a new theorem to
  recover the specified parent and the specified tree. No such theorem is
  asserted here.

**Remaining gap:** establish (CW) for arbitrary critical G, or find a genuine
critical-host violation after counting **all** embeddings. Even its weaker
positivity-only consequence is enough for the intended induction, but that
consequence was not established in this investigation. The original
Erdős–Sós task remains open here.

---

## 8. Verification and files

Run

    python3 Submission/WeightedRecurrenceGlobalChecks.py

The targeted exact-rational checks passed:

* 1,527 feasible matching-pattern checks, with independent checks of adjacency,
  degree exponents, class capacities, and the escape factor;
* 26 comparisons with a separate general tree independent-set DP, computing
  both U and T directly rather than assuming the pattern partition formula;
* three independent injective backtracking comparisons, including the exact
  weighted leaf identity;
* exact **nonmonotone** minimax-boundary computations at binary heights 0--3,
  giving respectively `0,2,3,4`, plus 14 minimax checks covering every leaf
  at heights 2 and 3, and separating-cut checks for two-image and four-image
  updates;
* the r=5 exponential congestion obstruction and the h=24 subcubic budget
  obstruction by exact arithmetic, without constructing the large example;
* 1,580 critical-split proper-subset types and 14,752 composition subset types
  across four small host constructions, plus direct induced-subset audits of
  the smallest composition and of three prism hosts;
* five rational scalar-potential checks and the free-attachment aggregate;
* unchanged specification hash before and after the checks.

These are audits of the displayed proofs and formulas, **not** a large finite
search offered in place of a global theorem. The general transport statements
are proved in Sections 3--5; the critical composition is proved in Section 6.
The code does not establish general (CW), and the positive split-host checks
are not represented as new evidence beyond that already proved case.

Files:

* `Submission/WeightedRecurrenceGlobalFindings.md`
* `Submission/WeightedRecurrenceGlobalChecks.py`
* `Submission/WeightedRecurrenceGlobalChecks.log`

`Spec.lean` retains SHA-256
`674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103`.
The results in this note are mathematical proofs, not Lean formalizations.
