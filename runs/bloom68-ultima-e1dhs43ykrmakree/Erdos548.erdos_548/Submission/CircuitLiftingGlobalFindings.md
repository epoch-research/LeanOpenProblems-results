# Circuit lifting: a valid split-off, exact elimination, and the remaining global gap

**Status: partial structural progress, not an Erdős–Sós proof.** There is a valid oriented inverse operation that produces a **unique smaller circuit**, an exact accounting of the virtual edges and the original surplus, and a dense terminal that selects a fresh copy rather than lifting an arbitrary one. There is also an associative, non-graphical density-elimination invariant. **No theorem was obtained that makes the adaptive tree/forest interface positive in every residual circuit.** In particular, the density invariant closes density elimination, not the tree-embedding induction.

The principal findings are:

1. A quota orientation permits matching split-off at every vertex of degree `r+t`, `1 <= t <= r`. It always gives a unique smaller **multigraph** circuit. A specified Hall condition makes the output simple; a separate reachability condition makes it spanning. Neither condition may be omitted.
2. If the extracted circuit uses `q` virtual edges, its original-host support has exact r-slack `q-1`, and its complement has exact incidence surplus `q`. In the original orientation, all `q` outgoing surplus arcs from that support go to the **unused deleted vertex**.
3. A matching completion and ordinary smaller-tree induction do not form a closed branch-reduction calculus. If the added edges are the only certified root connectors, deleting a target vertex of degree `s >= 3` leaves a marked forest. Reconnecting it into one tree needs a nonmatching completion or additional certified original edges between root images.
4. **An original `(k+1)`-vertex block with at least `r(k+1)` edges is terminal for every nonstar k-edge tree.** Thus a minimum-order extracted circuit using just one virtual edge is already terminal in the original graph. Ambient maximum degree handles stars.
5. Exact elimination of a degree-`r+t` vertex produces the boundary charge `(|S intersect N(v)|-r)_+`, not `t` ordinary edges. For `r >= 2` this charge cannot be represented by any nonnegative weighted graph on the retained vertices. It has an associative extension to arbitrary eliminated sets.

The three requested prior reports were read first. Their edge protection, failed support steering, and occupied-chord obstruction are not reproved here. The supplied common-list forest theorem (CL), parity-cut reduction, core terminal, and matching-defect boundary terminal are retained, not challenged. All new arguments below are finite graph arguments; no Lean formalization is claimed. No Spec/shared Lean file was edited.

## 1. Conventions and the exact admissibility test

Fix `k=2r+1`, `r >= 1`. An r-circuit is a simple graph G satisfying

    e(G) = r|V(G)|+1,
    e_G(S) <= r|S| for every proper S subset V(G).

We use the already established consequences: G is connected, `delta(G) >= r+1`, `Delta(G) >= k`, and `|G| >= k+1`. A quota orientation with outdegree r except `r+1` at any chosen root exists and is root-reachable.

The nonempty `(k-1)`-core and `K_k`-minus-matching boundary blocks are already terminal. Consequently a residual host is `(2r-1)`-degenerate and has a vertex of degree in `[r+1,2r-1]`. It can also have other vertices of degree `2r`, at which the operation below is available. For `r=1` there is no core-free residual host.

Choose a vertex v with

    A = N_G(v),   d(v)=r+t,   1 <= t <= r,
    U = V(G)-{v},   H=G-v,
    sigma(S) = r|S|-e_H(S),   S subseteq U.

Then

    sigma(U)=t-1,
    sigma(S) >= max(0, |A intersect S|-r)   for S proper in U.       (1)

The first formula is the total edge count. The two inequalities in (1) are exactly sparsity of S and of `S union {v}` in G.

For any set F of t distinct **nonedges** of H with both endpoints in A, put `G_F=H+F`. Then

    G_F is a spanning r-circuit
      iff |F intersect binom(S,2)| <= sigma(S) for every S proper in U.  (2)

This follows directly from the edge count `e(G_F)=r|U|+1` and its proper-set inequalities. Thus merely adding the right number of edges is not an admissibility proof. If (2) fails, one can extract a smaller circuit from the resulting dense graph, but it need not contain all old edges or all completion edges.

### A genuine forward operation

The forward matching pinch does preserve circuits, for the entire range, not just degree `2r`.

Let C be an r-circuit, let M be a matching of t existing edges, and let B be `r-t` additional vertices disjoint from its endpoints. Delete M, add a new vertex v, and join v to `V(M) union B`. The resulting graph is an r-circuit and `d(v)=r+t`.

**Proof.** The edge count increases by r. A proper old set S remains sparse after deleting M. For a set `S union {v}` with S proper in `V(C)`, its surplus is

    [e_C(S)-r|S|] + |S intersect (V(M) union B)| - e_M(S) - r.

Here

    |S intersect V(M)|-e_M(S)
      = number of matching edges meeting S <= t,

and `|S intersect B| <= r-t`. The surplus is therefore nonpositive. The only other proper set is all old vertices; its surplus is `1-t <= 0`. QED.

This proves circuit preservation, **not preservation of a given tree copy or of tree-freeness**.

## 2. Oriented matching split-off: an unconditional smaller-circuit extraction

### Theorem 1 — quota-preserving split

Choose a root `z != v` and a quota orientation D of G. Put

    I = {x : x -> v in D},    O = {y : v -> y in D}.

Then `|I|=t`, `|O|=r`, and `I,O` partition A. Choose any injection `pi:I -> O`.

Delete v and its incident edges. For each `x in I`, add the arc `x -> pi(x)`, counting it as a new edge even if the underlying pair was already an edge. Call the resulting oriented multigraph D', its underlying multigraph G', and its set of added edges M.

Then:

* M is a matching of t new edges; no added edge is a loop.
* G' has `r|U|+1` edges, with outdegree r except `r+1` at z.
* If C is the vertex set reachable from z in D', `G'[C]` is the **unique r-matroid circuit** in G'.
* G' is itself a spanning r-circuit exactly when z reaches all of U.

**Proof.** The incoming and outgoing neighbor sets are disjoint, and pi is injective. Replacing `x -> v` by `x -> pi(x)` preserves the outdegree of x; deleting the other arcs only removes arcs with tail v. Thus all retained quotas are unchanged, and the edge count decreases by r.

No arc leaves C, so `e_G'(C)=r|C|+1`. A proper subset of C avoiding z has at most r times its order in internal edges. A proper subset containing z has an outgoing arc, by reachability from z inside C, and has the same bound. This proves the circuit inequalities.

Any positive vertex set in G' must contain z and have no outgoing arc, by the quota formula. It must therefore contain C. The quotas bound every induced surplus by one. Any matroid circuit with support S consequently uses all edges of `G'[S]`, and contains the already dependent `G'[C]`; edge-minimality makes it exactly `G'[C]`. The final assertion follows by the same reachability argument. QED.

### Simplicity is a Hall problem, not automatic

For this chosen orientation, form the bipartite graph between I and O whose allowed pairs are **nonedges of H**. The split is simple if and only if pi can be chosen as a matching saturating I, equivalently

    |N_nonedge(X) intersect O| >= |X|    for all X subseteq I.       (3)

A failure has a concrete structural certificate: some nonempty `X subseteq I` is complete in H to

    Y = O - N_nonedge(X),    |Y| >= r-|X|+1.

Changing the orientation or root can change this Hall problem. No theorem was proved that one of those choices always clears all its defects. Passing to a multigraph and applying the simple-graph Erdős–Sós induction is invalid.

### The degree-`r+1` case has a canonical, orientation-free description

When `t=1`, H is r-tight on all of U. Its r-tight vertex sets are closed under union and intersection: sigma is nonnegative and submodular on all subsets, so the two uncrossed deficits of any two tight sets must both be zero.

For any missing pair `xy` in A, let

    C_xy = intersection of all r-tight sets of H containing x and y.

The family contains U. Then `H+xy` has a unique circuit, exactly `(H+xy)[C_xy]`. Indeed, its positive vertex sets are precisely the tight H-sets containing the pair. Their intersection is tight and has no smaller positive subset. This is valid for **every** available missing pair; an extra orientation-existence hypothesis is unnecessary at `t=1`.

In any orientation of H with outdegree exactly r at every vertex, tight sets are exactly the sets with no outgoing arc. Thus

    C_xy = Reach_H(x) union Reach_H(y).

It is all of U exactly when the pair meets every source strongly connected component of that orientation. Original criticality forces A to meet every source component (orient every edge at v outward and use the original root-reachability theorem). If there are exactly two source components, choosing one A-vertex in each always gives a nonedge and a spanning simple completion. With three or more sources, no pair can be spanning, though cross-source pairs still give smaller simple circuits.

For a fixed pair, changing the surplus root cannot change this canonical circuit support. The remaining choices are genuinely the pair, the tree embedding, and its interface—not a hidden root prescription.

### Spanning is a genuinely additional requirement

Every r-circuit is connected. If `c(H)>t+1`, no addition of t ordinary edges can give a spanning circuit: t edges cannot connect all components. Circuit criticality only gives the previously proved bound `c(H)<=r+1`, which is weaker when `t<r`.

For example, attach v by one edge to each of `r+1` disjoint `K_(2r+1)` blocks. This is an r-circuit, `d(v)=r+1`, and one completion edge cannot make the deletion spanning when `r>=2`. These hosts are already clique-boundary terminals; this observation is not a proposed residual obstruction. It distinguishes a valid circuit **extraction** from a false spanning-reduction assertion.

## 3. Where the surplus goes: a fresh-vertex identity

Continue with Theorem 1, and let

    q = number of added matching edges internal to C,
    a = |A intersect C|,
    X = V(G)-C.                     // X includes v

Count original edges, without the added matching. Then

    1 <= q <= t,
    e_G(C) = r|C|+1-q,
    r|C|-e_G(C) = q-1,
    I_G(X) = r|X|+q.                                           (4)

Indeed, `G'[C]` is induced in G' and has `r|C|+1` edges. Removing its q added edges leaves exactly `G[C]`. Original sparsity on C forces `q>=1`, and subtraction from `e(G)=rn+1` gives the incidence identity.

There is a stronger oriented interpretation:

    all original arcs from C to V(G)-C go to v,
    their number is exactly q.                                (5)

An original arc from C to another retained vertex outside C would still be in D', contradicting closure of C. Each original `x -> v` with x in C has its new arc `x -> pi(x)` internal to C; these are exactly the q internal matching edges. Hence (5).

Unlike the red-boundary identity in the prior report, this boundary really reaches a vertex **not occupied by any embedding lying in C**. But it still does not resolve the missing/virtual edges of such an embedding.

If `C` is proper in U, sparsity of `C union {v}` additionally gives

    2q <= a <= r+q-1,
    |A-C| >= t-q+1.                                            (6)

The lower bound uses that M is a matching. The upper bound follows from

    e_G(C union {v}) = r|C|+1-q+a <= r(|C|+1).

In particular, a proper extracted circuit uses at most `r-1` added edges and misses at least one original neighbor of v. If it uses r added edges, it must be spanning. These are exact constraints, not an attachment or root-steering theorem.

### A compatible branch-and-leaves lifting rule

Let u be a target vertex of degree s and let L consist of h leaf neighbors of u. Put `R=T-({u} union L)`. Suppose R has an injective **original-edge** embedding in `G[C]` sending every vertex of `N_T(u)-L` into `A intersect C`. If `h<=|A-C|`, it extends to T: put u at v and put the h leaves at distinct vertices of `A-C`.

The forest has

    |R|=k-h,    e(R)=k-s,    c(R)=s-h.

All added images lie outside C, so the edge and injectivity checks are immediate. For a proper extracted C, (6) guarantees the host leaf budget for every `h<=t-q+1`. The target must actually have those h sibling leaves, and the marked original-edge embedding of R is still required. In the pendant-two-edge case `s=2, h=1`, R is a `(k-2)`-edge tree, so the target size aligns with rank `r-1`; **its marked attachment is not supplied by unrooted rank induction**. This is a valid quantitative lift, not a claim that the interface can always be realized.

## 4. Exact density elimination is hypergraphic and associative

An ordinary edge completion is a choice subject to (2). There is also an exact elimination that makes no choice.

### Theorem 2 — the one-vertex boundary charge

Define on subsets of U

    rho_v(S) = max(0, |A intersect S|-r).

Then G is an r-circuit if and only if its deletion satisfies the total count above and

    e_H(S)+rho_v(S) <= r|S|     for every proper S subset U,
    e_H(U)+rho_v(U) = r|U|+1.                                  (7)

The equivalence is precisely (1), including the proper sets with and without v. The inequality for the proper original set U itself is supplied by `t>=1`.

The charge also has the uniform-allocation interpretation

    rho_v(S) = min { |J intersect S| : J subseteq A, |J|=t }.

Among the d incident edges, at most r can be paid for at v. If S contains more than r of their other endpoints, at least the displayed excess must be paid on S. For `t=1`, rho is the indicator that **all r+1 neighbors** are present, not the indicator that a chosen pair is present.

For `r>=2`, rho cannot equal the induced-edge-count function of any nonnegative weighted graph, even allowing parallel edges and loops. It vanishes on every singleton and every pair, so all such edge weights would have to vanish; but `rho_v(A)=t>0`. Thus an exact ordinary-graph inverse is not available merely by rewriting the incidence slots. Actual slack in (2) must pay for the replacement.

### Theorem 3 — associative elimination of an arbitrary set

Let

    f(S)=e_G(S)-r|S|.

For an eliminated set Z with nonempty complement U, define

    f^Z(S) = max_{Y subseteq Z} f(S union Y),    S subseteq U.     (8)

Equivalently,

    f^Z(S) = e_G(S)-r|S| + rho_Z(S),
    rho_Z(S) = max_{Y subseteq Z}
                 [e_G(Y)+e_G(S,Y)-r|Y|].                        (9)

Then:

* `rho_Z` is nonnegative, integer-valued, monotone and supermodular, with `rho_Z(empty)=0`.
* `f^Z` is integer-valued and supermodular; `f^Z(empty)=0`, `f^Z(U)=1`, and `f^Z(S)<=0` for every proper S in U.
* Eliminating disjoint sets is associative:

      (f^Z)^W = f^(Z union W),

  as long as the same retained ground set is used on both sides.

**Proof.** The edge-count function is supermodular; subtracting r times cardinality does not change that. For two retained sets choose maximizing eliminated subsets `Y1,Y2`; supermodularity applied to their unions gives the inequality for `f^Z`, using `Y1 union Y2` and `Y1 intersect Y2` as competitors. The same proof applies to the function inside (9), which consists of internal-Y and cross S-Y edge indicators minus a modular term. Monotonicity of rho follows from nonnegative cross-edge contributions; choosing empty Y proves nonnegativity.

Every `S union Y` is proper in V(G) when S is proper in U, so all its surpluses are nonpositive. For empty S the empty choice gives zero. At U the choice Y=Z gives one, and every other choice gives at most zero. Associativity is the equality of two finite maxima over disjoint eliminated subsets. QED.

This is a genuinely closed **density** invariant. It is not a closed Erdős–Sós invariant: after eliminating all but one vertex, the effective count at that vertex is `r+1`, although a simple one-vertex graph cannot embed the target. The lost vertices and their tree roles must still be represented. Replacing this effective object by an ordinary simple circuit, or silently lowering the target parameter, is not justified.

## 5. The exact arbitrary-tree interface

Let T be the fixed k-edge tree. For a target vertex u of degree s, `T-u` has k vertices, `k-s` edges, and s components, with one distinguished root in each component: the former neighbor of u.

Define `Sigma_u(H,A)` to be the set of **injective embeddings of the whole forest** `T-u` in H that send all these roots into A. Roots have no prescribed individual host images. The exact one-step identity is

    Emb(T,G) = Emb(T,H) disjoint-union
                union_{u in V(T)} {u -> v} * Sigma_u(H,A).       (10)

The unions distinguish the target vertex mapped to v. This is a bijection of embedding sets, or an equality of their cardinalities. In particular,

    T is contained in G
      iff T is contained in H or some Sigma_u(H,A) is nonempty.  (11)

This is the appropriate adaptive interface: all choices of u, including leaves and branch vertices, remain available. It is not a claim that an arbitrary u can be prescribed at v.

### Tree smoothing with virtual-edge flags

Choose a forest Q on the s distinguished roots, with h edges, and form

    R = (T-u) + Q.

Because the roots initially lie in different components, R is a forest with

    |R|=k,    e(R)=k-s+h,    c(R)=s-h.                          (12)

An embedding of R in a completed graph `H+F` lifts to T by putting u at v provided:

1. every edge of `T-u` is realized by an original H-edge;
2. every Q-edge is realized by an added F-edge;
3. every distinguished root, including a root isolated in Q, lands in A.

Conditions 1 and 3 are precisely what is needed to put u at v while retaining the other images. Condition 2 is the additional flag requesting that the completion supply the smoothing edges. It is not necessary for an arbitrary lift: a Q-edge could also be an original edge between two root images. An unmarked smaller-tree induction supplies neither the common-list condition nor the required original/virtual edge-use information.

When all Q-edges are required to be virtual, and F is the matching produced by Theorem 1, injectivity forces Q to be a matching. Hence

    h <= floor(s/2),    c(R) >= ceil(s/2).                      (13)

Consequences for this virtual-edge smoothing rule:

* `s=1`: the reduced object is a tree, but its leaf-parent needs the common-list condition `phi(parent) in A` and the forest edges must avoid virtual edges.
* `s=2`: suppression can give a smaller tree with its distinguished replacement edge mapped to an added edge, and all other edges original. A replacement edge already in H also works if both root images are separately certified to lie in A.
* `s>=3`: **a matching completion cannot reconnect all s components using only virtual edges**. With only those connectors, at least `ceil(s/2)` components remain.

Mixed original/virtual connectors are not excluded. But if Q is a tree on the s roots, at most `floor(s/2)` of its `s-1` edges can be virtual. At least `ceil(s/2)-1` connectors must therefore be certified original H-edges between root images, in addition to the common-list requirement. Alternatively one needs a nonmatching completion governed by (2).

Thus the easy circuit-preserving matching operation and a scalar smaller-tree induction do not automatically align for arbitrary branching. Allowing forests or mixed connectors is mathematically natural, but their root and edge-use data must survive every subsequent reduction.

### What a single completed copy actually permits

For an embedding phi of the full T into `H+F`, a one-vertex replacement `phi(x) -> v`, keeping all other images, is valid exactly when

* every used artificial edge is incident with x in the target, and
* `phi(N_T(x))` is contained in A.

If no artificial edge is used, the copy already lies in G. For a matching F, a one-vertex replacement can repair at most one used artificial edge. If exactly one is used and it is a leaf edge of the target, moving that leaf to v always works. In a T-free original graph, therefore, every one-artificial-edge copy in a completion must use an internal target edge, and **both endpoints must have another tree neighbor mapped outside A**. This is a necessary saturation condition, not a complete obstruction to arbitrary reembedding.

Expanding all used virtual edges through v merely gives a subdivision/immersion with a shared internal vertex. It is not automatically a copy of the same tree. The supplied seven-edge local example already explains why exact branch distances cannot be ignored; no further local counterexample is needed.

### Why the available CL and parity lemmas do not close this state

For the entire forest `T-u`, CL would require

    |A| >= |T-u| = k.

But the deleted low vertex has `|A|=d<=2r=k-1`. Thus the **direct** CL application fails its list-size hypothesis for every choice of u, even before its degree hypothesis is considered. A partial forest with fewer vertices may satisfy CL, but the omitted branches then require an additional justified interface.

The host split keeps r fixed. A connected one-vertex smoothing has `k-1` edges, not the standard rank-`r-1` target size `k-2`. Fixed-r induction also gives unmarked smaller trees by padding them to k edges, but does not give their flags. A genuine decrease of r must therefore specify a compatible target/forest reduction; it is not implicit in the split or in the density profile.

After more than one host vertex is eliminated, a surviving target vertex can have several eliminated neighbors. For an actual injective, adjacency-preserving placement psi of the eliminated target vertices, its remaining list is

    intersection_{u in N_T(x), u eliminated} N_G(psi(u))
       intersect retained host vertices.                       (14)

There can also be several marked vertices in one surviving component. Hence one common list with one mark per component is not automatically closed under iteration. The prior interface warnings apply here too. The proved parity kernel supplies target decompositions when a host cut funds them; neither (4) nor (8) supplies that host-cut hypothesis.

## 6. A dense terminal from exact slack and global copy selection

The following elementary averaging argument is useful here because it selects among **all** copies. It does not try to repair a fixed one.

### Theorem 4 — half an edge per vertex of complement is enough for nonstars

Let J have N vertices, `N>=4`, and at most `N/2` missing edges. Then J contains every nonstar tree on N vertices. If it has strictly fewer than `N/2` missing edges, it contains every N-vertex tree, including the star.

**Proof.** Let S be an N-vertex tree and choose a uniformly random bijection of its vertices to J. If b counts tree edges sent to missing host pairs and m is the number of missing pairs, then

    E[b] = (N-1)m / binom(N,2) = 2m/N <= 1.                    (15)

If the inequality is strict, some bijection has b=0.

At equality, N is even and `m=N/2>=2`. Choose two distinct missing edges. If they meet, S has a pair of adjacent edges that can be sent to them. If they are disjoint and S is nonstar, S has two disjoint edges (it contains a four-vertex path). In either case some bijection has at least two bad edges. If every bijection had at least one, the average would consequently exceed one. Therefore a zero-bad-edge bijection exists. QED.

The exclusion of stars at equality is necessary: `K_N` minus a perfect matching has no spanning star.

### Circuit consequences

For `N=k+1=2r+2`:

1. Every r-circuit of order N is terminal for **all** k-edge trees: its complement has exactly `r=N/2-1` edges.
2. In any critical ambient G, an original N-vertex set S with

       e_G(S) >= rN

   is terminal for every nonstar k-edge tree, by Theorem 4. Stars use the ambient vertex of degree at least k. Proper critical sets can only attain equality here.
3. In the oriented split of Theorem 1, if the output is simple and

       |C|=k+1,    q=1,

   then (4) gives `e_G(C)=r(k+1)`. Therefore **G is already terminal for every target**, without any tree-lifting induction hypothesis. A completed copy using the new edge can simply be discarded; averaging gives an original-edge nonstar copy.
4. Every nonempty proper r-tight set in a genuinely T-free critical host would consequently have at least `k+2` vertices. Smaller tight sets have order at least k by simplicity; order k is a clique-boundary terminal, and order `k+1` is handled above.

This is an exact-slack success case of the proposed strategy. It does not extend by an unproved averaging assertion to larger supports or more virtual edges. Indeed, for an extracted simple circuit of order N using q virtual edges, the basic averaging condition for a k-edge target is

    rN(N-2r-2) <= (2r+1)(1-q).

With `N>=2r+2` and `q>=1`, it holds precisely at `N=2r+2, q=1`. Thus the elementary count identifies a boundary terminal, not the general recursion step.

## 7. Even the graph operation needs an additional terminal alternative

Core-freeness and exclusion of matching-defect boundary blocks alone do not guarantee a simple inverse completion. There is an all-r structural illustration, already terminal for a different elementary reason.

For `r>=3`, take

    G = K_(r+1) join I_b,    b=r(r+1)/2+1.                     (16)

It is an r-circuit. If an induced set uses x clique vertices and y independent vertices, its surplus is

    binom(x,2)-rx+(x-r)y.

This is nonpositive for `x<=r`; for `x=r+1` it is `y-r(r+1)/2`, nonpositive on every proper set. The full surplus is one.

The independent vertices have degree `r+1`, and every clique vertex has degree `|G|-1>2r`. Thus **every** vertex in the proposed degree range has a complete neighborhood: no simple added edge among its neighbors exists, regardless of orientations or copy selection.

This host has empty `2r`-core. Every k-set contains at least r independent vertices; such a vertex has induced degree at most `r+1<k-2`, so there is no k-vertex matching-defect boundary block either.

Nevertheless it contains every k-edge tree: a tree on `2r+2` vertices has an independent set of size at least `r+1`; put `r+1` of those vertices into the independent side, and all remaining vertices into the clique. More generally, any `K_a join I_b` with `a>=r+1` and `a+b>=2r+2` is terminal by the same choice of a sufficiently large independent subset.

The point is not a new finite counterexample search. It is that a global induction must prove **simple admissible split OR an appropriate terminal**, rather than assume that the two already-known terminal tests force a split.

## 8. The precise unclosed global step

The preceding results separate three tasks that must not be conflated:

* **Density:** the profile (8) closes exactly and preserves the unit surplus.
* **Simple circuit extraction:** Theorem 1 closes when its nonedge Hall matching exists, but can lose support; a general existence-or-terminal theorem for this choice was not proved.
* **Tree reconstruction:** the exact state is the disjunction (10), or its multi-vertex version with lists (14), together with virtual-edge flags. No positivity invariant for that state was proved.

One explicit way to state the remaining saturation problem is as follows. For `H=G-v`, let `E_A` be all missing pairs within A. For each injection of T into `H+K_A`, record its **demand set** B of edges that are not in H. In a T-free H every such B is nonempty, and

    T embeds in H+F  iff  some recorded demand set B is contained in F.  (17)

Admissible completions are constrained by the slack inequalities (2), or by the oriented construction and (3). A joint global theorem must use T-freeness and these inequalities to show that saturation of every available completion forces either a nonempty adaptive forest interface `Sigma_u(H,A)` or an actual original-host terminal. Merely covering all completions by demand sets in (17) does not prove either conclusion. For matching completions the demand sets are matchings, and the one-edge demands obey the outside-A obstruction in Section 5; these are genuine restrictions, but they do not yet force a progress step.

Equivalently, a sufficient minimal-counterexample lemma would say:

> If an r-circuit G is T-free and is not terminal, then some low vertex has a **simple** quota-compatible split whose unique smaller circuit is still T-free.

Fixed-r induction on host order would immediately contradict that conclusion. The report does **not** prove this safe-split-or-terminal lemma. Proving it would require a joint completion/reembedding argument, not just circuit matching, surplus transport, or an unmarked smaller-tree induction.

The strongest completed contribution here is therefore the valid host split with its fresh-vertex surplus identity, the exact branch/forest transfer calculus, and the one-virtual-edge minimum-support terminal. The associative elimination profile records exactly what a more general recursion must retain, but is not being presented as the missing embedding theorem.

## 9. Verification

The mathematical proofs above do not depend on a numerical search. Run

    python3 Submission/CircuitLiftingGlobalChecks.py

from the project root. The checker passed; output is saved in `CircuitLiftingGlobalChecks.log`. It uses deterministic endpoint-slot augmentations and direct induced-set counts. The audit includes all 48 atlas r-circuits for `r=1,2`, plus four fixed rank-three operation inputs, one of them core-free.

Selected results:

* 8,002 forward matching pinches; 2,840 oriented inverse splits, including 504 simple outputs; all quota, circuit, reachability, and surplus identities checked.
* 1,346 nonedge-Hall equivalences, 187 full proper-set admissibility equivalences, 77 canonical one-edge tight hulls, and 12 two-source spanning completions.
* 6,013 elimination profiles; 4,181,824 supermodularity pairs and 828,752 associative-elimination values.
* 942 independently counted adaptive embedding identities; 8,137 matching/forest interfaces and 3,407 branch-and-sibling-leaf interfaces.
* 62 exact averaging histograms, and 138 one-virtual-edge minimum-support terminal certificates. A separate algebra-only audit checked the rearranged averaging threshold in 146,450 parameter cases.
* The auxiliary join terminal was checked by 371,963 induced-set type inequalities and 680 explicitly constructed tree copies, in addition to its all-r proof.

These are checks of the stated theorems and identities, not a search for new cut examples, and not numerical evidence asserted to close the global lifting gap.

`Submission/Spec.lean` remains at SHA-256

    674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103.

No Spec/shared Lean file was modified.
