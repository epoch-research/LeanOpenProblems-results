# The low-degree completion: a critical-host root obstruction and an exact CL budget

**Status: unrestricted Erdős–Sós remains unproved.** This investigation does
not replace the target by a restricted theorem. It identifies two precise
obstacles to a recursive CL completion. In particular, the fixed-maximum-root
obstruction persists under **full incidence density**, even in an actual
incidence-minimal circuit, with a unique maximum-degree host vertex and a
unique maximum-degree tree vertex of degree **four**.

No Lean file was changed. CL remains the mathematical theorem proved in
`CommonMarkedForestCL.md`; no Lean formalization of it is claimed here.
All containments below are non-induced.

## 1. Incidence-minimal hosts with a unique maximum-degree vertex

Fix an integer `r >= 2`, and set `k=2r+1`. Take `r+1` disjoint pairs of
independent sets

    |A_i|=r+1,       |B_i|=r^2,       1 <= i <= r+1.

Join each `A_i` completely to `B_i`. Add a vertex s adjacent to all `A_i`
and to no `B_i`. There are no other edges. Thus `G-s` is a disjoint union
of `r+1` copies of `K_(r+1,r^2)`.

The order and edge count are

    n=(r+1)(r^2+r+1)+1,
    m=(r+1)^2(r^2+1)=rn+1.

The degrees are

    d(s)=(r+1)^2,
    d(a)=r^2+1   for a in A_i,
    d(b)=r+1     for b in B_i.

Consequently s is the **unique maximum-degree vertex**, and `d(s)>=k`.

### Every proper induced subgraph is r-sparse

For a subset Q, write `x_i=|Q intersect A_i|` and
`y_i=|Q intersect B_i|`.

If `s notin Q`, the contribution of wing i to `e(Q)-r|Q|` is

    (x_i-r)y_i-rx_i.

It is nonpositive when `x_i<=r`. When `x_i=r+1`, it is
`y_i-r(r+1)<=-r`. Thus `e(Q)<=r|Q|`.

If `s in Q`, then

    e(Q)-r|Q| = -r + sum_i [(x_i-r)y_i-(r-1)x_i].       (1)

Each summand is at most one. It equals one only when the entire wing is
included: `x_i=r+1, y_i=r^2`. Indeed, `x_i<=r` gives a nonpositive summand,
and `x_i=r+1` gives `y_i-(r^2-1)`.

For a proper Q containing s, at least one wing is not full, so at most r
summands in (1) equal one; all the others are nonpositive. Hence again
`e(Q)<=r|Q|`. The whole graph has surplus exactly one.

Therefore G is an r-circuit and a minimum-cardinality positive induced
witness. For every nonempty X,

    I_G(X)=e(G)-e(G-X) >= r|X|+1.                       (2)

This is full `ID_(2r+1)`, not merely `W_(2r+1)`. Moreover
`m=(k-1)n/2+1`, so these hosts satisfy the **literal edge bound** in
`Spec.lean`, without a half-integral rounding caveat.

## 2. A bounded-degree tree whose unique maximum cannot map to s

For every `r>=9`, construct a tree R as follows.

* Take `r-4` vertices X, arranged in a path with every consecutive pair
  joined through a new Y vertex. There are `r-5` such Y vertices.
* Add seven further Y leaves: two at each end X vertex, and one at each
  of three distinct internal X vertices.

Thus R has bipartition sizes

    |X|=r-4,       |Y|=r+2,

and maximum degree three. Choose one of its Y leaves, ell. Add a new vertex
u adjacent to ell, and add three new leaves at u. Call the resulting tree T.

Then

    e(T)=2r+1=k,
    d_T(u)=4,
    d_T(v)<=3 for every v != u.

In particular u is the **unique maximum-degree vertex**, and
`Delta(T)=4<=floor(k/2)`. The two color-class sizes of T are `r-3` and `r+5`;
u belongs to the smaller class.

Suppose an embedding had `u -> s`. The connected component R of `T-u`
would have to lie entirely in one component `K_(r+1,r^2)` of `G-s`.
Because ell is adjacent to u, its image must belong to that wing's `A_i`.
Bipartiteness then forces **all `r+2` vertices of Y into `A_i`**, which has
only `r+1` vertices. This is impossible.

Thus:

> Even for incidence-minimal hosts, one cannot prescribe the unique
> maximum-degree tree vertex at the unique maximum-degree host vertex.
> The failure occurs for arbitrarily large k with tree maximum degree four.

### This is not an Erdős–Sós counterexample

T embeds entirely in any one wing: map its `(r-3)`-vertex color class into
`A_i`, and its `(r+5)`-vertex color class into `B_i`.

Also, s can be used by a suitable **degree-two** tree vertex in the larger
color class. Map that vertex to s and embed each of its branches in a separate
wing. The total opposite color class has only `r-3<=r+1` vertices, and each
same-color branch has fewer than `r^2` vertices.

At the smallest displayed parameter, `r=9`, this gives

    k=19,  n=911,  m=8200=9*911+1,
    d(s)=100,  d(A_i)=82,  d(B_i)=10,
    Delta(T)=4, with a unique degree-four vertex u.

Here `T-u` is a 19-vertex forest with 15 edges; its large component needs
11 positions in one 10-vertex `A_i`. The common allowed set `N(s)` has
100 vertices, but its distribution between host components matters. The
actual CL minimum-degree hypothesis fails: `delta(G-s)=10<15`.

This does **not** refute the weaker possibility that some degree-at-least-k
host vertex can accommodate the maximum-degree tree vertex: the vertices of
`A_i` do so in the displayed unrooted embedding. Nor does it refute choosing
u and s jointly from T and G.

## 3. Even a tree-only choice of a different root cannot be universally prescribed

There is a clean pair of critical hosts for the same 15-edge tree.

Let T consist of a central vertex z joined to three hubs, with four leaves
at each hub. Its color classes are

    P = the three hubs,
    Q = z and the twelve leaves.

In the preceding host with `r=7`, the unique maximum-degree vertex s has
degree 64; other degrees are 50 and 8. Its parameters are

    n=457,       m=3200=7*457+1.

No hub can map to s. Deleting a hub leaves a large connected component
containing z and eight leaves, all nine of which would need positions in
one 8-vertex `A_i`. Conversely every vertex in Q can map to s: for z use
one wing per branch, and for a leaf embed the remainder in one wing.
Therefore the set of permissible tree roles at s is **exactly Q**.

For the other host take `K_(8,57)`, and choose s in its 8-vertex part. This
host has `n=65`, `m=456=7*65+1`, and s is a maximum-degree vertex. Every
proper induced subset is 7-sparse: for `K_(x,y)`, use `x<=7`, or use
`x=8,y<=56` to get surplus `y-56<=0`. Hence this too is incidence-minimal.

In every copy of T, its 13-vertex class Q must map into the 57-vertex part.
The permissible roles at s are therefore **exactly P**. Each is realizable
by the obvious bipartite injection.

The two permissible-role sets are disjoint. So even after retaining full
incidence minimality, no rule selecting one root from T **without using
the host** can prescribe that root at a maximum-degree host vertex in all
instances. Host-dependent joint selection remains possible and unproved
in general.

## 4. Exact boundary bookkeeping for recursive CL

Let U be a nonempty proper subset of a k-edge tree T. Let
`F=T-U`, let `q=c(T[U])`, and let `b_C` be the number of edges from a
component C of F to U. Contract all components of `T[U]` and of F. The
result is a bipartite tree, so

    sum_C (b_C-1) = q-1.                                  (3)

This exactly measures the extra boundary requirements beyond one attachment
per remaining component. When U is disconnected, there are `q-1` such extra
boundary edges. They either create additional marked vertices or intersect
several neighborhood lists at the same marked vertex. CL does not resolve
either requirement merely from a lower bound on raw list sizes.

When U is connected, every `b_C=1`. Write `h=|U|` and `b=sum_C b_C`.
Then

    e(F)=k-h+1-b.                                         (4)

Suppose U has been embedded on a host set S of size h. Using **only** the
minimum-degree bound supplied by the incidence core, together with the trivial
nonnegativity of degree, gives

    delta(G-S) >= max(0, ceil(k/2)-h).

For this bound to certify the CL degree hypothesis for all of F, (4) gives
exactly

    e(F)=0   OR   b >= floor(k/2)+1.                       (5)

The edgeless alternative must not be omitted. For `e(F)>0`, the degree test
is equivalent to `k-h+1-b <= ceil(k/2)-h`, giving the second alternative.
For `e(F)=0`, minimum degree zero always suffices.

This is a degree-budget obstruction before the separate issue that the
components can have different allowed neighborhoods. It is not a claim
that the actual residual minimum degree can never be better.

For connected U, every component of `T-U` contains a distinct leaf of T,
so `b<=number_of_leaves(T)`. Thus, for trees with at most `floor(k/2)`
leaves, **the only residual forests passing this guaranteed degree test are
edgeless**. Since every remaining component has one attachment, every
remaining vertex is then a leaf of T. In other words, U already contains the
entire nonleaf core; the remaining interface is precisely the unused-neighbor
matching problem for the leaf slots. This includes arbitrarily long
subdivisions of nonspider bounded-degree trees, not just paths.

A successful recursive approach must therefore justify a globally extendible
core embedding, obtain additional actual host degree savings, solve the extra
boundary requirements (3) for a disconnected deletion, or take a different
route. Equation (2) does not itself select the shape-compatible boundary:
Section 2 shows its failure for a preselected single deleted tree vertex,
even in a circuit and even with a very large common allowed set.

## 5. Verification and remaining gap

Run

    python3 Submission/IncidenceCriticalRootChecks.py

It passes, checking:

* all wing-subset types for `r=2,...,60`: 3,498,464 exact types. By separability
  this certifies every proper subset of every displayed host, not a sample;
* the degree-four construction and its root-capacity obstruction for
  `r=9,...,100`;
* explicit unrooted and alternative-root injections in the `k=19` graph,
  checked edge by edge;
* an independent rational endpoint-weight certificate in that graph, with
  every vertex receiving load `8200/911>9`;
* both exact, disjoint permissible-role sets in Section 3, including explicit
  injections for every allowed role;
* identities (3)--(5) on 140,028 tree/deletion pairs through 10 vertices,
  including 21,905 connected deletions.

The CL constructive checker was rerun independently with 30,000 random
trials; it passed, including its 362,970 atlas instances and 79,782 exact-apex
instances. These are audits, not substitutes for the stated proofs.

`Spec.lean` retained SHA-256

    674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103.

**Remaining gap.** No shape-sensitive selection/reembedding theorem was
proved which turns full incidence density into a compatible forest interface
for arbitrary low-degree T. Replacing W by ID, prescribing maximum-degree
vertices, or simply iterating the one-mark CL degree calculation does not
supply that theorem. The unrestricted Erdős–Sós target has not been completed.
