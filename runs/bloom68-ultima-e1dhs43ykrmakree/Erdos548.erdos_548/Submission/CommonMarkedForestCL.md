# CL is true: a common-list marked forest theorem

**Outcome.** The claim CL is proved below, by a root-sensitive adaptation of
Goldberg–Magdon-Ismail's global reembedding proof. Consequently every nonempty
`W_k` graph contains every `k`-edge tree with
`Delta(T) >= floor(k/2)+1`. The same high-degree case of Erdős–Sós follows.
This does **not** settle unrestricted `W_k => all k-edge trees` or unrestricted
Erdős–Sós.

The proof below is mathematical. The finite-host statement is now also fully
formalized independently in `Submission/CommonMarkedForest.lean`; see
`Submission/CommonMarkedForestLean.md` for theorem interfaces and the axiom
audit. A constructive, non-backtracking implementation and independent finite
audits are in `Submission/CommonMarkedForestChecks.py`.

## 1. Statement and terminology

Graphs are simple and undirected. An embedding is an injective homomorphism;
it need not be induced. For a graph J, write `v(J)=|V(J)|` and `e(J)=|E(J)|`.
A root is just the specified marked vertex, not a prescribed host image.

**Theorem CL.** Let F be a finite forest with one specified root in each
component. Let H be a host graph such that every vertex of H has at least
`e(F)` neighbors. If `A subset V(H)` and `|A| >= v(F)`, then F has an embedding
in H that takes all its roots into A.

The argument works for arbitrary host graphs as well as finite ones: all
cliques, occupied sets, and modifications used in the proof are finite. If
desired, first replace A by a subset of exactly `v(F)` vertices. Below, degree
subtractions can equivalently be read as bounds on the number of neighbors
remaining after excluding a finite set.

Call a nontrivial rooted tree a **root-centered star** when its root is
adjacent to every other vertex. An edge is a root-centered star with either
choice of root. A star marked at a leaf, with at least two edges, is *not*
a root-centered star.

## 2. Two elementary extension facts

**Ordinary tree extension.** If a tree T has a edges, a connected subtree of T
has already been embedded in a graph of minimum degree at least a, and T is
not yet fully embedded, one can extend the embedding along any boundary edge.
Indeed, at most a vertices are currently embedded, so the image of the parent
has at most `a-1` occupied neighbors. Repetition embeds all of T. In particular,
the root of T can be sent to any chosen host vertex.

**Clique-plus-outside extension.** Let J have a clique K of order a, and put
`S=V(J)-K`. Suppose every vertex of S has degree at least a **in J**. Then for
any rooted a-edge tree T and any `s0 in S`, there is an embedding of T in J
sending its root to s0.

To prove this, start at s0 and grow a connected subtree. Until the embedding
is complete, it uses at most a vertices. If the parent's image is in S, its
degree at least a gives a fresh neighbor. If the parent's image is in K, the
partial embedding contains s0 outside K, so at most `a-1` vertices of K have
been used; an unused vertex of K is a fresh neighbor. This proves the fact.
Notice that no degree bound on the vertices of K is needed beyond K being a
clique. This fact is the key change to the last step of the unmarked proof.

## 3. Proof of CL

### Isolated vertices and induction

It suffices to prove the theorem when F has no isolated vertices. After
embedding the forest F' of its nontrivial components, place the isolated
vertices at distinct unused vertices of A: at most `v(F')` members of A have
been used, leaving at least `v(F)-v(F')` available. The empty forest is immediate.

For forests without isolated vertices, induct on the number p of components.
The case `p=1` is ordinary tree extension starting at any vertex of A.

Now assume `p>=2`, that CL holds for fewer components, and, for contradiction,
that the present instance has no embedding satisfying the root condition.
Write

    F = T_1 union ... union T_p,
    r_i = the root of T_i,
    a_i = e(T_i) >= 1,
    e = sum_i a_i,       m = v(F) = e+p.

If F has a root-centered-star component, choose one of them as T_1.
Otherwise choose any component as T_1. Set `a=a_1` and
`F_- = T_2 union ... union T_p`. There is **no** requirement that T_1 be a
largest component. None of the estimates below uses `a_i <= a`.

### A reserved clique meeting A

Every embedding of T_1 whose root image lies in A has a vertex outside its
image adjacent to its entire image. Otherwise, deleting that `(a+1)`-vertex
image would remove at most a neighbors from each remaining vertex. The
remaining host would have minimum degree at least `e-a`, and its remaining
allowed set would have size at least

    m-(a+1) = v(F_-).

Induction would embed F_- there with all its roots in the remaining allowed
set, a contradiction.

It follows that H contains a clique of order `a+2` meeting A. In detail,
start with a singleton `{z}`, where `z in A`. If a clique L containing z has
order `t<=a+1`, choose a connected subtree of T_1 of order t containing r_1,
map it bijectively onto L with `r_1 -> z`, and extend it to T_1 by ordinary
tree extension. The preceding paragraph supplies a vertex outside the image
adjacent to all of L, enlarging the clique while keeping z. Finitely many
steps give the asserted clique. We only need a subclique K of order a
containing z.

Choose a leaf `ell` of T_1 other than r_1; every nontrivial tree has such a
leaf. Embed `T_1-ell` bijectively into K, sending r_1 to z. Let x be the image
of the neighbor of ell. Consequently, for **every**

    w in N_H(x)-K,

this fixed embedding extends to a root-respecting copy of T_1 on `K union {w}`.
The vertex x need not be in A. This formulation avoids incorrectly assuming
that an arbitrary edge from an outside vertex to K suffices for a rooted copy.

Since `d_H(x)>=e` and K has a vertices, choose

    X subset N_H(x)-K,       |X|=e-a+1.

The host `H-K` has minimum degree at least `e-a` and

    |A-K| >= m-a = v(F_-)+1.

Induction therefore gives an embedding g of F_- into `H-K` respecting A.
Moreover, **every** such embedding must cover all of X: if some `w in X`
were unused, the fixed copy on `K union {w}` would complete F.

### The four classes and the counting inequality

Fix such an embedding g. Put

    B = g(V(F_-)),
    Y = B-X,
    S = V(H) - (K union B),
    J = H[K union S] = H-B.

Here

    |B| = e-a+p-1,
    |Y| = p-2,
    |K union B| = m-1.

Because `|A|>=m`, there is a vertex `s0 in A intersect S`.

Partition the components of F_- into four classes, with counts q_1,...,q_4:

1. all their image vertices lie in X;
2. at least two image vertices lie in X, and at least one lies in Y;
3. exactly one image vertex lies in X;
4. all their image vertices lie in Y.

Write a(T) for a component's number of edges. Class 2 consumes at least one
vertex of Y per tree, class 3 consumes a(T), and class 4 consumes `a(T)+1`.
Since `q_1+q_2+q_3+q_4=p-1`, the bound `|Y|=p-2` gives

    q_2 + sum_{class 3} a(T) + sum_{class 4} (a(T)+1)
      <= p-2 = q_1+q_2+q_3+q_4-1,

or equivalently

    q_1 >= 1 + sum_{class 3}(a(T)-1) + sum_{class 4}a(T).       (1)

In particular,

    q_1 >= 1+q_4.                                            (2)

If no component is a root-centered star, then all a(T) are at least 2, so

    q_1 >= 1+q_3+2q_4.                                       (3)

### Root-sensitive swaps

The basic forbidden operation is this: take `s in S` and a target vertex v
whose current image g(v) lies in X. If s is adjacent to the images of all
neighbors of v in its tree, replacing g(v) by s is still an injective
homomorphism. It respects the root condition provided either v is not that
tree's root or `s in A`. It would omit the vertex g(v) of X, contradicting
the preceding universal coverage of X. Hence no such legal swap is possible.

First take `s in S intersect A`. All roots may legally be moved to s.

* For a class-1 tree, s must miss at least two vertices of its image. If it
  misses exactly one, replace the preimage of that vertex by s. If it misses
  none, replace any vertex. The replacement is legal because the graph is
  simple: a vertex is not its own neighbor.
* For a class-2 or class-3 tree, s must miss at least one image vertex. If s
  is adjacent to the whole image, replace any vertex whose image lies in X.

It follows that s has at most `|B|-(2q_1+q_2+q_3)` neighbors in B. Thus

    d_J(s) >= e-|B|+2q_1+q_2+q_3
           = a+q_1-q_4
           >= a+1,                                          (4)

using (2).

If T_1 was chosen to be a root-centered star, (4) at s0 finishes the proof:
embed its root at s0 and its a leaves at distinct neighbors in J. This copy
is disjoint from B and has its root in A, contradicting the assumed failure.

We may therefore assume **no component of F is a root-centered star**.
For every `s in S`, whether or not s is in A, the following bounds hold:

* A class-1 tree still forces at least two missed image vertices. If the
  only missed vertex is not its root image, replace that nonroot vertex.
  If the only missed vertex is its root image, choose a nonroot target
  vertex v **not adjacent to the root**; such v exists precisely because the
  tree is not a root-centered star. All neighbors of v then have images
  adjacent to s, so replace v. If s misses nothing, replace any nonroot.
  All these swaps leave the root fixed.
* A class-2 tree forces at least one missed image vertex. It has at least
  two vertices mapped into X, hence at least one of them is not its root.
  If s were adjacent to the whole image, that nonroot could be replaced.

We make no claim for class 3 in this case; its unique X vertex might be its
root. Consequently, using (3), every `s in S` satisfies

    d_J(s) >= e-|B|+2q_1+q_2
           = a+q_1-q_3-q_4
           >= a+1+q_4
           >= a+1.                                          (5)

Apply the clique-plus-outside extension fact to J, its a-clique K, and
`s0 in A intersect S`. It embeds T_1 into J with root s0. Together with g,
this is the forbidden marked embedding of F. The contradiction proves CL.
QED.

## 4. Why this is a valid adaptation rather than prescribed-root greediness

The source is Goldberg–Magdon-Ismail,
`/corpus/src/1011.3882/theorem.tex`. The clique reservoir, set X, four classes,
and inequality (1) are adapted from its unmarked proof. The new ingredients
needed for the common marked set are:

* choose T_1 to be a root-centered star if one is present;
* produce the reserved clique through a vertex of A;
* reserve a *specific* leaf-deleted rooted copy, not an arbitrary outside
  edge to the clique;
* use an unused member of A, available because the reservoir plus the other
  components occupy only `v(F)-1` vertices;
* distinguish swaps into A from swaps preserving the component's root;
* retain K in the free host J for the final embedding.

In particular, the proof never claims arbitrary prescribed roots can be
preserved. It also never claims unused vertices have large degree in H[S];
the degree estimates are in `H[K union S]`. Ignoring either distinction would
leave a genuine gap.

The common set is essential to the swaps into A: the same s0 is legal for
**every** component root. The result says nothing about differing root lists
or multiple marks in one component, for which the prior counterexamples
remain applicable.

## 5. Consequences

### Exact one-vertex tree extension

Let T be a k-edge tree, let `u in V(T)` have degree d, and let `s in V(G)`.
If

    d_G(s) >= k,       delta(G-s) >= k-d,

then T embeds in G with `u -> s`.

Indeed, `F=T-u` has k vertices and `k-d` edges. Each component contains exactly
one former neighbor of u; mark it. Use CL in `H=G-s` with the common set
`A=N_G(s)`, whose size is at least k. Adjoining `u -> s` completes the tree.
This includes isolated components of F. No triangle-free hypothesis is needed.

### High-degree trees in W_k graphs

For a finite nonempty graph G, define W_k by

    for every nonempty X subset V(G), there is v in X with
        2 d_G(v) - d_{G[X]}(v) >= k.

Singleton X gives `delta(G)>=ceil(k/2)`, and `X=V(G)` gives some vertex s
with `d_G(s)>=k`. For any k-edge tree T and any vertex u with

    d_T(u) >= floor(k/2)+1,

we have

    k-d_T(u) <= ceil(k/2)-1 <= delta(G-s).

The exact extension result therefore embeds T with u at s. In fact **any**
vertex s of degree at least k can serve as its image. Thus the promised
high-degree case holds for every W_k graph, without triangle-freeness.
Only these two local degree consequences of W_k are used in this case.

### High-degree Erdős–Sós

Suppose G is finite and

    e(G) > (k-1)|V(G)|/2.

Choose a nonempty vertex set U of minimum cardinality subject to the same
strict inequality for `G[U]`, and put `Q=G[U]`. For each nonempty
`X subset V(Q)`, minimality gives

    I_Q(X) = e(Q)-e(Q-X) > (k-1)|X|/2,

where I_Q(X) is the number of edges with at least one endpoint in X. Since

    sum_{v in X} (2d_Q(v)-d_{Q[X]}(v)) = 2 I_Q(X),

some integer summand is at least k. Thus Q satisfies W_k, and the preceding
corollary embeds every k-edge tree with maximum degree at least
`floor(k/2)+1` in Q and hence in G. This proves exactly the advertised
high-degree case, not the unrestricted Erdős–Sós conjecture.

## 6. Sharpness of the common-set size

The requirement `|A|>=v(F)` cannot uniformly be reduced by one, even when H
has the required minimum degree. Take two disjoint triangles as H, take
`F=2K_2` with one marked endpoint per edge, and let A be the three vertices
of one triangle. Then `delta(H)=2=e(F)` and `|A|=3=v(F)-1`. Both components
would have to be embedded inside that triangle, needing four distinct
vertices, which is impossible.

More generally, for any forest with p>=2 components and m>=2 vertices,
`H=2K_{m-1}` and A equal to one clique give
`delta(H)=m-2>=m-p=e(F)`, but no marked embedding: every component's image
must stay in the component containing its root, so all m vertices would have
to fit in A. Thus CL's list-size bound is sharp for each such forest.

## 7. Verification and artifacts

The code `Submission/CommonMarkedForestChecks.py` realizes the induction as
an algorithm. When constructing a clique, a trial rooted T_1 copy with no
outside universal neighbor immediately permits induction on its complement.
Otherwise its outside universal neighbor enlarges the clique. After the
recursive placement of F_-, an unused X vertex or a legal one-vertex switch
finishes immediately. If neither occurs, the proved degree bounds guarantee
the final star or clique-plus-outside greedy embedding. This algorithm does
not call a marked-embedding search oracle.

Command:

    python3 Submission/CommonMarkedForestChecks.py --random 30000

Results:

* 1,839,848 local-switch configurations passed: all nonisomorphic rooted trees
  of orders 2 through 10, all possible adjacencies from an external vertex,
  and both allowed/not-allowed statuses of that vertex.
* 149,268 clique-plus-outside greedy-extension cases passed on atlas hosts.
* 362,970 CL instances passed constructively: the same entire atlas domain
  as the prior search, including marked isolated components.
* 79,782 instances of the exact prescribed-apex tree corollary passed on atlas
  hosts; this uses its local hypotheses, not a triangle-free restriction.
* 26,785 additional CL instances from 30,000 random clique/independent-set
  blow-up trials passed constructively.
* All recursive degree/list hypotheses and all returned marked embeddings
  were checked. Both final branches were exercised, as were root-moving
  switches, nonroot switches, and switches to vertices outside A.
* Independently rerunning `/tmp/forest_interface/search_marked.py` also
  returned `ATLAS PASS 362970`.

The complete constructive run took approximately 27 seconds. Logs are in
`/tmp/forest_interface/common_marked_constructive.log` and
`/tmp/forest_interface/common_marked_backtracking_audit.log`. These finite
checks audit the proof and its implementation; the general theorem is
established by Sections 2–3, not inferred from the tests.

`Submission/Spec.lean` was not modified and retained SHA-256

    674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103

The finite-host theorem CL is now independently proved in
`Submission/CommonMarkedForest.lean`, including empty forests and isolated
marked components. Its main theorem is `CommonMarkedForest.CL`; its transitive
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. The file
imports only Mathlib and does not import or modify `Submission.Spec`.
`Submission/CommonMarkedForestLean.md` describes the formal interfaces and the
sum-ready equivalent of the four-class count used in Lean. The infinite-host
variant and the Section 5 consequences remain mathematical results here, not
additional Lean theorems.
