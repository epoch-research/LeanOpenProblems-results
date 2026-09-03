# Global augmentation: exact open packets and the unresolved reachability step

## Status — no coarse constant bound proved

**I have not proved `c(G) <= 100 |V(G)|`, or any universal constant bound.**
There is no specification edit and no claimed resolution of Erdős–Gallai.
This investigation stops at the global augmentation/retirement implication
identified in Section 6. It does not replace that implication by a routing
assumption, critical fixed count, fractional rounding, or an all-long-cycles
statement.

The rigorous partial results are:

1. A counterexample minimal first in vertices and then in edges would have
   `q = 100n+1`, every proper even restriction would satisfy the desired
   bound on its own support, and **minimum degree at least 204**. The last
   statement uses the explicit one-saving smoothing in Section 3; the more
   immediate old-cycle deletion argument only gives 202.
2. Its globally minimum partition is a **minimally Hall-deficient system**
   for 100 vertex slots per vertex. From any unmatched cycle, ordinary
   Hungarian alternating reachability reaches **the whole graph**. It does
   not by itself produce a proper, retirable vertex cluster.
3. Deleting a vertex of degree `2k` has an exact global objective: minimize
   the number of mark-free cycles in a matching cap, and then add `k`.
   Optimization is over all cap partitions and all pairings. A cap cycle
   containing several marks is explicitly split into several real simple
   cycles; it is never counted as one lifted cycle.
4. A chain of `s` old cycles between two open paths can be absorbed with at
   most `B+mu` new residual cycles, with an exact formula for the two trails'
   repeated-vertex defect. Thus `B+mu<s` is a genuine augmentation. The
   chain length is unrestricted. This is an open-path counterpart of the
   ring exchange in `ResearchIncidence.md`, not a completeness theorem for
   all global exchanges.

The two sharp optima already in `ResearchIncidence.md` also check the exact
obstructions for open paths: one has `(B,mu)=(0,1)` and the other `(1,0)`
when attempting to absorb one cycle. No new obstruction family or random
search is introduced.

Only these files are created:

* `Submission/ResearchGlobalAugmentation.md`;
* `ResearchGlobalAugmentationCheck.py` at the project root.

These are paper-level reductions and finite exact checks, not a Lean proof.

---

## 1. What a genuine minimal counterexample supplies

All original graphs are finite, simple, undirected, and even. A cycle is
vertex-simple and has length at least three. A partition is an exact edge
partition. Let `c(F)` be its minimum cycle count, with `c(empty)=0`.
For an edge restriction, its support excludes isolated vertices.

For this section let `K>=1` be an integer; ultimately `K=100`. Suppose a
counterexample to `c(G)<=K|V(G)|` exists. Choose one minimizing first
`n=|V(G)|`, then the number of edges, and put `q=c(G)`. It has no isolated
vertices and is connected: deleting isolates, or adding the bounds on
smaller connected components, would contradict the choice.

### 1.1 Proper restrictions and the exact count

Every proper even edge restriction `W` satisfies

```
c(W) <= K |supp(W)|.                                      (1.1)
```

If its support is smaller, use vertex minimality; if its support is all
of `V(G)`, use edge minimality. For any simple cycle `C` in `G`,

```
q <= 1+c(G-E(C)) <= Kn+1.
```

Since `q>Kn` is integral, this proves

```
q = Kn+1,                 c(G-E(C)) = Kn                 (1.2)
```

for **every** simple cycle `C`. In particular every such residual still
has all `n` vertices in its support. Every single specified cycle extends
to a minimum partition of `G`.

This last fact does **not** say that other old cycles can be retained in
that extension. Nor does genuine `q`-criticality, which follows from
(1.1), imply fixed count here. No critical fixed-count assertion at
`q>=4` is used.

Let `D` be any globally minimum partition. For every subfamily `A` of `D`,

```
c(union A) = |A|.                                        (1.3)
```

Otherwise a cheaper partition of this exact edge union, completed with
`D\A`, would improve `D`. There is no bound on the size of `A` in (1.3).
Combining it with (1.1), every proper subfamily satisfies

```
|A| <= K |V(A)|.                                         (1.4)
```

For every nonempty vertex set `S`, let `t_D(S)` count old cycles meeting
`S`. The cycles avoiding `S` are minimum on their even edge union and
have support on at most `n-|S|` vertices. Hence

```
t_D(S) >= K|S|+1.                                        (1.5)
```

At a single vertex, `t_D({v})=d_G(v)/2`, so initially
`delta(G)>=2K+2`. Section 3 improves this to `2K+4`.
Also `|E(G)|>=3q` and simplicity imply

```
n >= 6K+2,               average degree > 6K.            (1.6)
```

For `K=100` these give `n>=602` and average degree greater than 600.
None of these statements assumes regularity or a lower bound on every
cycle's length beyond three.

### 1.2 The exact Hungarian closure is the entire graph

Give each vertex `K` distinct slots. A cycle may use any slot at a vertex
it contains. For any chosen `C0 in D`, all subfamilies of `D\{C0}` satisfy
Hall's inequality by (1.4). The finite marriage theorem, after replacing
each vertex by its `K` slots, therefore gives an assignment of the
`Kn` cycles other than `C0` to distinct slots. All slots are occupied.

Start alternating reachability at the unassigned cycle `C0`:

* a reached cycle reaches every vertex it contains;
* a reached vertex reaches all `K` cycles assigned to its slots.

Let `R` and `X` be the reached cycles and vertices after closure. Every
reached assigned cycle was reached from its owning vertex. Conversely all
cycles owned by reached vertices are reached. Thus

```
R = {C0} union {cycles assigned at vertices in X},
|R| = K|X|+1,               V(R)=X.                       (1.7)
```

If `R` were a proper subfamily, (1.7) would contradict (1.4). Therefore

```
R=D,                         X=V(G).                    (1.8)
```

This applies to every choice of the unmatched cycle and every saturating
assignment. Traversing an already matched cycle-to-owner incidence adds
no extra reachability, so the aggregate description agrees with ordinary
slot-level alternating reachability.

**Consequence for the proposed route.** Token rotations are available
throughout the system, but their closure is not a proper deficient cluster
that can be retired. An incidence `v in C` only certifies membership; it
does not specify compatible cut positions or vertex-simple routes through
several cycles. Upgrading (1.8) to such routes is a genuinely additional
claim.

---

## 2. The exact open-path and marked-cap objectives

Fix any vertex `v` of an even simple graph, and put

```
F=G-v,            T=N_G(v),            |T|=2k.
```

The odd vertices of `F` are exactly `T`.

### 2.1 Open paths are not closed trails

A `T`-perfect path–cycle partition of `F` consists of:

* exactly `k` nonempty vertex-simple paths;
* some vertex-simple cycles;
* exact edge coverage, with each member of `T` an endpoint exactly once
  and no other endpoints.

Different paths can intersect each other, and a terminal may occur
internally on another path. Requiring internally disjoint paths would be
an unjustified strengthening.

Opening all cycles of a partition of `G` through `v` gives such a
partition. Conversely, closing each of its paths with its two incident
edges at `v` gives a simple cycle. The two endpoints are distinct and the
path avoids `v`; even a one-edge path lifts to a triangle. All star edges
at `v` are used exactly once. Consequently

```
c(G) = k + minimum number of residual cycles
               in a T-perfect path–cycle partition of F.       (2.1)
```

For a globally minimum `D`, its opened partition is globally optimal for
this residual-cycle objective, with `q-k` residual cycles.

### 2.2 Matching caps, with every auxiliary two-cycle explicitly paid

Let `M` be any perfect matching on `T`. Form a **labelled multigraph**
`F+M` by adding one new marked edge for each matching pair. An existing
edge on a pair is retained, so that pair may have two parallel edges.
This auxiliary cap is even. Its cycles are vertex-simple, with two
parallel edges allowed as an auxiliary length-two cycle.

For a cap partition `P`, define

```
b(P) = number of cycles of P containing no marked edge,
u(F+M,M) = min_P b(P).                                    (2.2)
```

This is optimization over **all** cap partitions, not merely those
minimizing total auxiliary cycle count.

A cap cycle with `a>=1` marked edges becomes exactly `a` nonempty simple
paths when those edges are cut. Marked edges form a matching, so two of
them cannot be consecutive along that cycle; every intervening unmarked
path has at least one edge. Closing these paths at `v` gives exactly `a`
real simple cycles. An unmarked cap cycle already is an ordinary simple
cycle of `F`. An auxiliary two-cycle consists of one real and one marked
edge and becomes **one triangle**, included in the payment below.

The cap partition therefore gives exactly

```
k+b(P)                                                   (2.3)
```

real simple cycles partitioning `G`. In particular, a cap cycle with
several marks is not lifted as one cycle with repeated visits to `v`.

Conversely, a partition of `G` induces a matching by pairing the two
neighbors used on each cycle through `v`. After opening at `v`, cap each
path with its marked matching edge. Each such cap cycle has one mark,
and the other cycles are unmarked. Thus

```
c(G) = k + min_M u(F+M,M).                                (2.4)
```

All pairing and cyclic-order freedom is retained in (2.4). It is an exact
reformulation, not an inequality obtained by rounding a fractional cover.

---

## 3. Simple smoothing and a rigorous minimum-degree improvement

To apply induction on ordinary simple graphs, set

```
A = M \ E(F),       R = M intersect E(F),
H_M = (V(F), E(F) symmetric-difference M).
```

The graph `H_M` is simple and even: every terminal changes parity once.
Mark the edges of `A`. For any simple-cycle partition `P` of `H_M`, put

```
p=|P|,       h_M(P)=number of cycles in P meeting A.
```

Complete `P` to a partition of `F+M` by adding the parallel two-cycle on
each pair in `R`. Section 2 then gives an exact simple lift of size

```
p+k-h_M(P).                                              (3.1)
```

Equivalently, cut the marked edges of `P`, close the resulting paths at
`v`, and add the real triangle on each pair in `R`. The surcharge is
exactly

```
k-h_M(P)
  = |R| + sum_(C in P, E(C) meets A) (|E(C) intersect A|-1). (3.2)
```

Thus both deleted old matching edges and repeated marks on the same cap
cycle are paid. Knowing that many cap cycles exist does not imply they
meet many marks.

If induction supplies `p<=K(n-1)`, define its slack
`Delta=K(n-1)-p`. The sufficient lifting condition is precisely

```
h_M(P)+Delta >= k-K.                                    (3.3)
```

In a hypothetical minimal counterexample every such choice instead
satisfies `h_M(P)+Delta<=k-K-1`, by (1.2) and (3.1). A rotation argument
would have to improve the *net* quantity, including the cost of any
additional unmarked cap cycles it creates.

### 3.1 One saving is always possible when `d(v)>=4`

**Lemma.** If `d_G(v)=2k>=4`, there is an even simple graph `J` on
`V(G)\{v}` and an explicit lift of every partition of `J` to a partition
of `G` with at most `k-1` additional simple cycles. In particular,

```
c(G) <= c(J)+k-1.                                        (3.4)
```

**Proof.** If two neighbors `x,y` of `v` are nonadjacent, choose `M`
containing `xy` and use `J=H_M`. Every partition of `J` has at least one
cycle meeting the nonempty marked set `A`, so (3.1) saves at least one.

Otherwise `N_G(v)` is a clique. Choose four distinct neighbors
`a,x,y,b` and first remove the real simple five-cycle

```
C=(v,a,x,y,b).
```

In `G'=G-E(C)`, the vertex `v` has degree `2(k-1)`, and its remaining
neighbors include the now nonadjacent pair `x,y`. Smooth `v` in `G'`
using a matching containing `xy`. Equation (3.1) lifts a partition of
the resulting simple even `J` to `G'` at cost at most
`(k-1)-1=k-2`. Restore the single five-cycle `C`. The total cost is at
most `k-1`, as claimed. All graphs used for induction are simple; the
auxiliary marked parallel edges are only the bookkeeping of Section 2.
This construction also works when `k=2`. ∎

For degree two, the elementary smoothing bound is at most one additional
cycle. Consequently a vertex-minimal counterexample for integer `K>=1`
cannot have degree at most `2K+2`: for `2<=k<=K+1`, (3.4) costs at most
`K`, and the degree-two case costs at most `K` as well. Hence

```
delta(G) >= 2K+4,                 so delta(G)>=204 at K=100. (3.5)
```

This is an actual single-vertex lifting lemma. Its charge `k-1` is not
bounded by 100 when `k` is unbounded. It does not supply the needed
larger-cluster lemma.

---

## 4. An arbitrary open-chain exchange with exact collision cost

Work in a `T`-perfect path–cycle partition of `F`. Select two distinct
paths `P,Q`, `s>=1` distinct residual cycles `C_1,...,C_s`, and distinct
connectors `x_0,...,x_s` with

```
x_0 in P intersect C_1,
x_i in C_i intersect C_(i+1)       (1<=i<s),
x_s in C_s intersect Q.                                  (4.1)
```

No further intersection restriction is imposed. Connectors may lie on
additional selected pieces. In particular, the paths may intersect each
other many times, and a connector may be a path endpoint.

Orient `P` and cut it at `x_0` into tails `P_L,P_R`. Choose either
orientation of `Q` and cut it at `x_s` into `Q_L,Q_R`; write `tau` for
this orientation choice. A tail is allowed to have length zero. Cut
`C_i` at `x_(i-1),x_i` into its two oriented arcs `A_i^0,A_i^1`, both
running from `x_(i-1)` to `x_i`.

For bits `z_i`, let `S_0` concatenate the chosen arcs `A_i^(z_i)` and
let `S_1` concatenate their complements. Construct

```
T_0 = P_L + S_0 + Q_R,
T_1 = Q_L + reverse(S_1) + P_R.                           (4.2)
```

These are edge-disjoint open trails, not yet simple paths. Together they
use exactly the selected edges and retain the four distinct endpoints
of `P,Q`, with their pairing possibly changed.

### 4.1 The defect is an explicit signed constraint system

For each vertex let `t_w` be the number of selected pieces containing it,
counting the two paths and all `s` cycles. Put

```
B = sum_w (t_w-2)_+ .                                    (4.3)
```

At every connector both trails have a visit before considering any
extra incidences. At a nonconnector, each original occurrence is assigned
to one of the two trails. The path-tail labels are fixed after choosing
`tau`. A cycle occurrence on arc `a_i(w)` has trail label
`z_i XOR a_i(w)`.

Let `f(z,tau)` count nonconnectors with `t_w>=2` for which all their
occurrence labels agree, and let

```
mu = min_(z,tau) f(z,tau).                                (4.4)
```

A vertex is counted once by `f`, even if it has many occurrences. If
`D(T)=sum_w(visits_T(w)-1)_+`, then

```
D(T_0)+D(T_1) = B+f(z,tau).                              (4.5)
```

**Proof.** Total occurrences across both trails at `w` equal `t_w`.
This also holds at endpoints: the original and new four-endpoint
multisets are identical. If both trails use `w`, the excess is `t_w-2`;
if only one uses it, the excess is `t_w-1`. Connectors always occur in
both trails. For a nonconnector of multiplicity at least two, the second
case is exactly the failed not-all-equal constraint. Multiplicity one
contributes zero. Summing proves (4.5). ∎

When all `t_w<=2`, `B=0` and these constraints are XOR equations in the
arc bits and the tail-orientation bit, possibly pinned by path-tail
occurrences. Their consistency is an additional cyclic-order condition,
not a consequence of incidence reachability.

### 4.2 Converting the trails, and the actual count gain

Splitting an open trail at a repeated vertex produces one open trail
with the same endpoints and one closed trail. Splitting a closed trail
at a repeated vertex produces two closed trails. In either case the
summed repeat excess over the pieces decreases by at least one: it
decreases at the split vertex and at every other vertex shared by both
resulting pieces. For a closed trail, its displayed final repetition of
the starting vertex is not counted as an additional visit. Continue until
the open piece is a simple path and all closed pieces are simple cycles.

Starting with two open trails gives exactly two simple paths and at most
`D(T_0)+D(T_1)` simple cycles. No length-one or length-two closed piece
can occur: these trails use distinct edges in a loopless simple graph.
The paths' endpoints remain the original four distinct terminals.

Therefore (4.2) has an exact-edge replacement by two simple paths and
at most

```
B+mu                                                       (4.6)
```

residual simple cycles. Closing the paths at the deleted vertex `v`
creates exactly two real simple cycles, just as before. All unselected
paths and cycles stay unchanged. Hence

```
B+mu < s                                                  (4.7)
```

is a genuine reduction of the primary cycle count of `G`.
In every globally minimum opened partition, necessarily

```
B+mu >= s                                                 (4.8)
```

for every such chain. A clean chain with no additional selected-piece
intersections has `B=mu=0` and absorbs all its `s` cycles. The number of
selected cycles is not bounded.

The computation of `B+mu` is a **sufficient** replacement bound. A large
value does not prove that the packet has no better decomposition using
more cuts or more paths.

---

## 5. Existing sharp optima still obstruct a naive path closure

These are the two supplied examples from `ResearchIncidence.md`,
Sections 3.1–3.2, reused only to check the proposed operation.

In its 13-vertex, 19-edge optimum, delete the junction `w_0`. The two
long old cycles become paths, and the triangle `(a_0,b_2,z)` remains.
Use contacts `a_0,b_2`. The paths still share `w_1,w_2,w_3`. One path
puts all three on one side of its cut, whereas the other separates
`w_1,w_2` from `w_3`. Either tail pairing therefore violates at least one
constraint, and exactly one violation can be attained:

```
s=1,                   B=0,                   mu=1.
```

This is the cyclic-order obstruction, not a shortage of incidences.
The original minimum count is three, so removing its sole residual
cycle after opening two paths really would be impossible.

In the existing 10-vertex branching example, open the two cycles through
connector `x_0` and try to absorb the remaining cycle using contacts
`x_2,x_1`. The central degree-six vertex lies on all three selected
pieces. Here

```
s=1,                   B=1,                   mu=0.
```

Two simple paths alone cannot cover its six selected incident edges.

Both examples have small cycle count and low-degree vertices. They do
**not** refute an augmentation theorem under `q>100n` and the minimal
counterexample hypotheses. They do rule out simply turning a token
return or an open incidence chain into a simple-path absorption without
checking the defects.

---

## 6. Exact unresolved step — stopping here

For the hypothetical counterexample and a minimum-degree vertex of
degree `2k`, the exact numerical obligation is

```
min_M min_(P a partition of (G-v)+M) b(P) <= 100n-k.       (6.1)
```

Equation (2.4) shows that (6.1) is **exactly the desired bound in
one-vertex form**, not a separate proved theorem. A simple inductive cap
starts with `b_0=p-h_M(P)`. To reach (6.1), a global augmentation must
remove at least

```
max(0, b_0-(100n-k))                                     (6.2)
```

unmarked cycles **net of all new unmarked cycles it creates**. It may
change the matching, reopen the auxiliary two-cycles, change arbitrarily
many old cycles, and use more than two paths. Freezing the removed-pair
triangles is not imposed as a necessary restriction.

The unproved structural implication in the attempted proof is:

> Starting from the minimally Hall-deficient global optimum of Section 1,
> use token reachability together with arbitrary count-preserving
> reoptimization to realize a net-saving simple-path/cycle augmentation;
> or, if compatible routes cannot be realized, extract a vertex set with
> an actual simple-graph lifting certificate whose charge is at most
> `100` times the number of vertices permanently retired.

More specifically, the missing inference is from a token-alternating
return to simultaneous arc choices with **fewer collision-created cycles
than absorbed old cycles**, or to that paid retirement certificate.
Membership reachability (1.8) does not control `B`, does not imply the
signed constraints in (4.4) are consistent, and does not bound the total
cost of resolving incompatible returns after further switches. Taking
all globally minimum partitions into account does not, by itself, prove
that one of them has a successful chain. No completeness assertion for
two-path chains is made; multi-path augmentation may be essential.

For retirement, one would have to produce an even **simple** smaller
graph and prove the lift for its permitted partition, with that
partition's cost also controlled. If actual stages satisfied

```
c(G_i) <= c(G_(i+1)) + 100|S_i|,
```

where `S_i` are disjoint sets of permanently removed original vertices,
then the charges would telescope once. But **no extraction/lifting lemma
providing these stages in the stalled case is proved here**. Reaching a
cluster in an incidence graph, measuring its rank, or naming a collection
of open trails does not give this inequality. In particular the
context-uniform rank-only absorption failure already in
`ResearchGlobalAbsorption.md` cannot be bypassed by asserting global
routing for the exterior.

Thus all established necessary conditions remain compatible with the
hypothetical value `q=100n+1`. The proof stops at this implication. There
is no asserted constant 100, no other asserted universal constant, and
no further unrelated family exploration.

---

## 7. Targeted verification and preservation

Run from the project root:

```sh
PYTHONHASHSEED=0 python3 -B ResearchGlobalAugmentationCheck.py
```

The checker uses only the Python standard library and exact integer
arithmetic. It writes no files. Its cycle enumeration retains edge
identities in marked multigraph caps; every reported original-graph
partition is independently checked for vertex simplicity, length at
least three, disjoint edges, and exact edge coverage.

The completed checks are:

* **43 vertex deletions and all 97 neighbor pairings** in six fixed
  graphs: the triangle, six-cycle, `K5`, the octahedron, and the two
  existing sharp incidence examples. Complete cycle enumeration and
  exact-cover dynamic programming verify the count and mark-free
  objectives. The minimum counts are respectively `1,1,2,2,3,3`, with
  `1,1,37,63,53,28` simple cycles enumerated in the original graphs.
* **334 exact simple lifts** check both auxiliary objectives, the simple
  toggle-cap formula (3.1), and the inverse induced pairing from an
  actual minimum partition. For every deleted vertex, the independently
  optimized values satisfy (2.4).
* **21 one-saving smoothings**, including all five clique-neighborhood
  cases of `K5` using the preparatory five-cycle, verify the construction
  of (3.4) edge by edge.
* **252 clean-chain assignments** for `1<=s<=6` check that all selected
  cycles are absorbed into two real simple cycles after closing at `v`.
  These are direct unit tests of the operation, not minimum-partition
  counterexample candidates.
* **21 open chains and all 84 bit/tail assignments** obtained from the
  two existing three-cycle optima check the exact defect identity,
  endpoint preservation, the split-cycle upper bound, and the necessary
  inequality (4.8). The two specific sharp defects in Section 5 are
  independently recovered.

The final status line is

```
ALL TARGETED EXACT CHECKS PASSED; UNIVERSAL BOUND NOT PROVED
```

The checker protects all **245 pre-existing non-cache project files
outside `.lake`** by the initial combined path/content fingerprint,
excluding only the two allowed new paths:

```
5ca3ea88e16ceacd703d119434fcf7631334002e43806e5964f4cc58ed00ec62
```

The unchanged specification SHA-256 is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

No pre-existing file, specification, or bytecode cache was written.
Finite checks validate the stated identities and constructions only;
they are not evidence of a completed augmentation lemma for all graphs.
