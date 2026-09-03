# Graphic circuits: global exchange closure and sharper boundary exclusions

## Status and scope

**No complete proof of GC_r, the connected-density assertion U_(2r+1), or Erdős–Sós was obtained. No counterexample to any of them was obtained.** This report proves structural and embedding lemmas, and gives an explicit restricted residual assertion which is still unproved. In particular, a spanning-tree exchange is not being called a tree-copy augmentation.

The starting point is `GraphicCircuitReduction.md`, not the earlier pseudoforest-circuit model. Throughout, r >= 2, k = 2r+1, and a **graphic r-circuit** C is a finite simple graph satisfying

    e(C) = r(n-1)+1,
    e_C(S) <= r(|S|-1)  for every nonempty proper S subset V(C).    (GC)

The target T has k edges and maximum degree at most r. The residual order is n >= 2r+3. Write

    sigma_C(S) = r(|S|-1) - e_C(S)                                (1)

for nonempty proper sets S. Singletons have slack zero. A set of slack zero is **tight**.

The main additions, relative to the reports read, are:

* An elementary **global exchange theorem**: from any decomposition of C-f into r spanning trees, the omitted edge can be moved to ANY other edge by a sequence of valid one-tree fundamental-cycle exchanges. The proof verifies the exchanges in the changing trees, not just reachability in a frozen exchange graph.
* The exact identity `sum_i (c_i(S)-1) = sigma_C(S) + 1_{f inside S}`, where c_i(S) counts components of the i-th spanning tree restricted to S. It completely characterizes common tree-path-convex proper sets.
* A sharper odd boundary lemma. A (2r+1)-vertex block with at most **2r-d** missing edges, together with ANY edge from a specified block vertex to the outside, contains T if T has an end of its internal tree of degree d. The earlier bound was r-1 missing edges.
* A multi-boundary version charges all attachment lists to distinct missing host edges. In particular it yields an additional sharp exclusion on **every 2r-set** whenever the two smallest internal-end degrees sum to at most `2r-Delta(T)`.
* Consequently, if C is T-free and beta(T) is the minimum degree of an end of T's internal tree, then EVERY (2r+1)-set S satisfies

      sigma_C(S) >= r-beta(T)+1.                                (2)

  Also C has no K_(2r), and every nontrivial proper tight set has at least 2r+2 vertices.
* Exact tight-contraction, separator, and degree-(r+1) neighborhood-hull statements. These make some of the remaining interfaces explicit without asserting they can be lifted through a target copy.

“New” means new to the reports examined, not a claim of literature priority. The exchange results are elementary graphic-matroid arguments and may also be viewed as specializations of matroid-union exchange theory.

No existing file was edited. In particular, `Spec.lean` and all other Lean files were left unchanged. No new Lean theorem, axiom, or formalization is claimed.

## 1. The exact global exchange theorem

Fix f in E(C) and a partition

    E(C) - {f} = B_1 disjoint-union ... disjoint-union B_r,

where every B_i is a spanning tree. Existence follows from the Nash-Williams forest-decomposition theorem as explained in the reduction report. The arguments below work for **every** such partition.

### 1.1 Every edge is reachable in the frozen exchange graph

Make a directed graph D whose vertices are the edges of C. For e=uv not in B_i, put an arc e -> h whenever h lies on the unique u-v path in B_i. Its label is i. There are no arcs into f.

**Theorem 1.** Every g in E(C) is reachable from f in D.

**Proof.** Let R be the set of edges reachable from f. It contains f and is closed under outgoing arcs. For every e=uv in R and every i, u and v are connected in B_i intersect R: if e belongs to B_i, use e; otherwise use its B_i-path, all of whose edges are in R by closure.

Let S_1,...,S_c be the vertex sets of the components of (V(C),R), including isolated vertices. The preceding observation implies that B_i intersect R induces a connected graph on each S_j. It is a forest, so it has exactly |S_j|-1 edges there. Therefore

    |R| = 1 + sum_i |B_i intersect R| = r(n-c)+1.                (3)

If c >= 2, every S_j is proper and (GC) gives

    |R| <= sum_j e_C(S_j) <= r(n-c),

a contradiction. If c=1, (3) gives |R|=r(n-1)+1=|E(C)|. Thus R=E(C). QED.

This uses all proper-set inequalities, not just minimum degree or edge connectivity.

### 1.2 A shortest frozen path gives VALID exchanges in the changing trees

Reachability alone is not enough: earlier exchanges change later fundamental paths. The following argument addresses that issue.

Choose a shortest directed path

    e_0=f, e_1, ..., e_s=g

in D. For j>=1, let i_j be the original color of e_j. By definition, e_j lies on the original B_(i_j)-path between the endpoints of e_(j-1). Shortestness implies

    there is no arc e_a -> e_b when b >= a+2.                    (4)

Starting with omitted edge e_0, at step j insert the current omitted edge e_(j-1) into the current tree of color i_j, and remove e_j.

**Theorem 2.** Every step is a valid fundamental-cycle exchange. Thus all intermediate states partition C minus the current omitted edge into r spanning trees, and the final omitted edge is g.

**Proof.** Induct on j. In the ORIGINAL tree B_(i_j), deleting e_j defines a cut (U,V-U). The incoming edge e_(j-1) crosses this cut. Any edge inserted earlier into color i_j has the form e_(h-1) for h<j. If such an edge crossed this cut, its original B_(i_j)-path would contain e_j, giving the forbidden shortcut e_(h-1) -> e_j in (4).

Therefore none of the earlier inserted edges of this color crosses the cut. Of its original tree edges, only e_j crosses, and e_j has not yet been removed because the shortest path has distinct vertices. Consequently the CURRENT tree of color i_j still has e_j as its unique edge across this cut. Adding e_(j-1) creates a cycle containing e_j. Removing e_j restores a spanning tree.

The inserted edge was the unique omitted edge, so no color conflict is introduced. The new omitted edge is e_j, completing the induction. QED.

The assertion here is about recoloring existing host edges. It does NOT move target vertices, preserve a chosen target core, or turn a noninjective map into an embedding.

## 2. Common convexity and the exact component-excess identity

For a nonempty S, let c_i(S) be the number of components of B_i[S], counting its isolated vertices. Put epsilon_f(S)=1 if both endpoints of f are in S and 0 otherwise. Since B_i[S] is a forest,

    e_C(S) = sum_i (|S|-c_i(S)) + epsilon_f(S).

Thus for every nonempty proper S,

    sum_i (c_i(S)-1) = sigma_C(S) + epsilon_f(S).                (5)

Call S **common convex** if the B_i-path between every pair of vertices of S stays in S, for every i. For a tree this is equivalent to B_i[S] being connected. Equation (5) gives the complete characterization:

> A nonempty proper S is common convex if and only if S is tight and f is not an internal edge of S.

In particular:

* No proper common-convex set contains both endpoints of f. Starting with these two endpoints and repeatedly adding any missing colored tree-path vertices eventually generates ALL of V(C).
* If S is tight and f is outside E_C(S), all r restrictions B_i[S] are spanning trees of S.
* If S is tight and f is inside E_C(S), exactly one restriction has two components and every other restriction is connected.

The last assertion counts **component excess**, not a number of available target augmentations.

### 2.1 An elementary fundamental-circuit extraction algorithm

The same hull operation does not require an initially critical graph. Let H be the union of r edge-disjoint spanning trees B_i, and let xy be a nonedge. Starting with {x,y}, close under all B_i-paths, and call the final vertex set U. Then

    (H+xy)[U]

is the unique graphic r-circuit in H+xy.

Indeed B_i[U] is a tree for every i, so the induced edge count is r(|U|-1)+1. A proper subset W of U could violate r-forest sparsity only if it contains x,y and every B_i[W] is connected. Such a W would be common convex containing x,y, contradicting minimality of U. For uniqueness, any circuit in H+xy must use xy, since H is a union of r forests. Its support W has equality in each forest bound, so is common convex and contains U; a circuit cannot properly contain the circuit already found on U. QED.

This is an algorithmic atom extraction and a useful exact interpretation of pair completion. It is not an embedding lift.

## 3. A sharper odd boundary terminal

Let I(T) be the subtree induced by the nonleaves of T. It is connected and has at least two vertices, because T is not a star. Choose an end p of I(T), let u be its unique nonleaf neighbor, and write

    d = d_T(p),             2 <= d <= r.

All other d-1 neighbors of p are leaves.

**Theorem 3 (odd boundary with exact d-budget).** Let J have 2r+1 vertices and q<=2r-d missing edges. Suppose the ambient graph also contains an edge xy with x in J and y outside J. Then it contains T.

There is no arbitrary prescribed-root assertion for T minus an arbitrary leaf.

**Proof.** Remove p and its d-1 leaf neighbors from T. The remaining tree R has

    m = 2r+2-d >= r+2,

vertices, and maximum degree at most r<=m-2. In particular R is not a star. Let B be the nonneighbors of x in J, and t=|B|. Since

    d_J(x) = 2r-t >= 2r-q >= d,

reserve any d-2 neighbors of x as a set D. Define

    K = J - ({x} union D).

Then |K|=m, B is contained in K, and the complement Q of K has at most q-t edges. On the m target positions R and the m host positions K, forbid only the assignments u -> b for b in B. The forbidden-assignment graph L has exactly t edges. Hence

    e(R)+e(Q)+e(L) <= (m-1)+(q-t)+t
                    = m-1+q <= 2m-3,                         (6)

because q<=2r-d=m-2. Also

    Delta(R) <= m-2,  Delta(Q) <= m-2,  Delta(L) <= m-1.

The proved finite list edge-sum packing theorem of Győri–Kostochka–McConvey–Yager therefore gives a bijection R -> K avoiding Q and L. Its seven exceptional unordered graph pairs are excluded because R is connected of order at least four. In particular, u is mapped to a neighbor of x.

Put p at x, one of its leaves at y, and its other d-2 leaves at D. This is an injective T-copy. QED.

The only list cost is t, and deleting x removed exactly t missing edges before the reserve vertices were deleted. No rooted packing theorem is being presumed.

Define

    beta(T) = min { d_T(p) : p is an end of I(T) }.

Thus 2<=beta(T)<=r. Applying Theorem 3 with d=beta(T) permits q<=2r-beta(T), in particular q<=r for EVERY target in the odd range. This is at least one missing edge more than the original report's uniform r-1 terminal.

### 3.1 Several pendant stars share the same defect budget

Here the saving is not obtained by adding several copies of the one-root estimate. The lists can instead all be charged to distinct missing host edges.

Choose t distinct ends p_1,...,p_t of I(T), put d_i=d_T(p_i), and let D=sum_i d_i and Delta=Delta(T). Assume

    D+Delta <= 2r.                                           (MB1)

**Theorem 3A (multi-boundary terminal).** Let J have `2r+2-t` vertices and at most `2r-D` missing edges. If the ambient graph contains a matching

    x_i y_i  (1<=i<=t),     x_i in J, y_i outside J,

then it contains T.

**Proof.** The internal tree has at least three vertices: if it had just two, T would have at most 2r-1 edges because both internal degrees are at most r. Its distinct ends are therefore nonadjacent, and their pendant stars are disjoint. Remove p_i and its d_i-1 leaf neighbors for all i. The remainder R is connected and has

    m=2r+2-D >= Delta+2

vertices. Hence it is a nonstar tree of maximum degree at most m-2. Let u_i be the attachment vertex of the i-th removed star; several u_i are allowed to coincide.

Write q for the number of missing edges of J and X={x_1,...,x_t}. The minimum degree of J is at least

    (2r+1-t)-q >= D+1-t.

For each i, greedily reserve d_i-2 neighbors of x_i, avoiding X and all earlier reserves. This is possible: excluding X costs at most t-1 neighbors, and even after all other reserves the number still available is at least

    D+1-t -(t-1) - sum_(j!=i)(d_j-2) = d_i.

The needed number is only d_i-2. Let K be J minus X and all reserves. Its order is m.

Forbid the assignment u_i -> b whenever b in K is a nonneighbor of x_i. Let L be the UNION of these forbidden pairs; if attachment vertices coincide, repeated pairs are counted only once. Every edge of complement K and every proposed list prohibition can be charged to a missing edge of J: respectively a missing edge inside K, or a missing edge x_i b. All the latter host edges are distinct as (i,b) varies, and none lies inside K. It follows that

    e(complement K)+e(L) <= q <= 2r-D = m-2.                  (MB2)

Thus `e(R)+e(complement K)+e(L)<=2m-3`, with all maximum-degree bounds of the finite list-packing theorem satisfied. R is connected of order at least four, so the exceptional pairs cannot occur. Pack R into K avoiding L. Restore each p_i at x_i, one of its leaves at y_i, and its other leaves at the reserve for x_i. The disjoint sets and the prescribed matching give an injective T-copy. QED.

For t=1 the degree condition is automatic: d_1+Delta<=2r. For t=2 it need not hold for every target; it is retained explicitly below. No t-edge matching is inferred from 2-connectivity when t>2.

## 4. A K_(2r) terminal and full-critical slack consequences

**Theorem 4.** A 2-connected graph of order at least 2r+2 containing K_(2r) contains every nonstar tree of order 2r+2.

**Proof.** Let S be the clique. The bipartite graph of edges between S and its complement has a matching of size two. Otherwise all its edges share one endpoint: a pairwise-intersecting family of edges in a bipartite graph is a star. Its center would be a cutvertex of the ambient graph. If the center is outside S, use the fact that at least two vertices are outside S; if it is inside S, use S minus that center. Both contradict 2-connectivity.

Write the matching as x_1 y_1, x_2 y_2, with x_i in S. A nonstar tree has two leaves with distinct parents; for example choose a leaf at each of two different ends of its internal subtree. Delete these leaves. Map the remaining 2r-vertex tree bijectively to S, sending their two parents to x_1,x_2. Restore the leaves at y_1,y_2. QED.

Now suppose, only for deriving necessary conditions, that C satisfies (GC), n>=2r+3, and T is absent.

1. **C contains no K_(2r).** The reduction already proves C is 2-connected, so Theorem 4 applies.
2. **Every (2r+1)-set S has sigma_C(S)>=r-beta(T)+1.** Its number of missing edges is exactly

       binom(2r+1,2)-e_C(S) = r+sigma_C(S).

   A connected ambient C supplies an edge from S to its complement. If sigma_C(S)<=r-beta(T), Theorem 3 embeds T, a contradiction.
3. **Every nontrivial proper tight set has at least 2r+2 vertices.** Simplicity excludes tight orders 2,...,2r-1. Order 2r is a clique and is excluded by (1). Order 2r+1 is excluded by (2).
4. **For every choice of f and every spanning-tree decomposition of C-f, every (2r+1)-set S satisfies**

       sum_i(c_i(S)-1) >= r-beta(T)+1+epsilon_f(S).              (7)

   This follows from (5), not from an assumed near-copy. In particular no such S is common convex in all r colors.
5. If X has n-(2r+1) vertices and I_C(X) counts its incident edges once, then the complementary form of the same obstruction is

       I_C(X) >= r|X| + r-beta(T)+2.                           (8)

   Indeed I_C(X)=r|X|+1+sigma_C(V-X).

6. **There is a stronger 2r-set bound when two end stars fit the budget.** Define

       beta_2(T) = min {d_T(p)+d_T(q): p,q distinct ends of I(T)}.

   If `beta_2(T)+Delta(T)<=2r`, then EVERY 2r-set S satisfies

       sigma_C(S) >= 2r-beta_2(T)+1.                           (17)

   Indeed C is 2-connected and at least two vertices lie outside S, so its boundary has a matching of size two by the matching argument in Theorem 4; that argument does not require S to be a clique. The number of missing edges of C[S] equals sigma_C(S), since `binom(2r,2)=r(2r-1)`. Theorem 3A with t=2 proves (17). Equivalently, for every decomposition of C-f,

       sum_i(c_i(S)-1) >= 2r-beta_2(T)+1+epsilon_f(S)

   on such 2r-sets. This is a component-excess bound, not a claim of equally many independent augmentations.

These statements use full induced-set criticality and an actual shape-dependent embedding terminal. They are stronger than a minimum-degree statement and apply to every set of the indicated order, not just supports of selected rooted copies.

## 5. Tight contractions, minimum cuts, and separators

### 5.1 Contraction retains a graphic circuit, but generally NOT simplicity

Let S be any nonempty proper tight set. Contract it to a vertex, discard its internal edges, and retain all parallel edges to the outside. The resulting multigraph Q has

    |Q|=n-|S|+1,     e(Q)=r(|Q|-1)+1.

If a proper vertex set W of Q avoids the contracted vertex, its sparsity follows directly from that in C. If it contains that vertex, lift it to W* in C; then

    e_Q(W) = e_C(W*)-e_C(S)
           <= r(|W*|-1)-r(|S|-1) = r(|W|-1).

Thus Q is a graphic r-circuit in the multigraph sense. The same proof works for simultaneous contraction of any partition into at least two nonempty tight sets.

The connectedness and no-cutvertex proofs in the reduction use only edge counts, so apply to Q with parallel edges as well. In particular **C-S is connected**. When Q has two vertices this last conclusion just says that the remaining single vertex is connected.

If at least two vertices are outside S, then for each z outside S,

    d_C(z,S) <= r,                                           (9)

by applying sparsity to the proper set S union {z}. With only one outside vertex the bound is r+1 instead, so that exception must not be dropped.

Contraction may create parallel edges. Consequently it is not a reduction to a smaller SIMPLE instance of GC_r, and it does not by itself lift a target embedding.

### 5.2 Exact cut accounting

For every nonempty proper S, with complement R,

    e_C(S,R) = r+1 + sigma_C(S)+sigma_C(R).                    (10)

Thus a cut has exactly r+1 edges if and only if both shores are tight. In a T-free circuit both shores of a nontrivial such cut have at least 2r+2 vertices. Therefore:

> If 2r+3 <= n < 4r+4 and C is T-free, every cut of size r+1 isolates a single vertex.

This is not a claim that every circuit has a cut of size r+1.

### 5.3 Exact vertex-separator accounting

Let X be a vertex separator, and let D_1,...,D_c, c>=2, be the components of C-X. Each X union D_i is proper. Counting every X-edge c times gives

    sum_i sigma_C(X union D_i) = (c-1)sigma_C(X)-1.            (11)

In particular a tight set cannot be a vertex separator, giving another proof of C-S connected for tight S.

If sigma_C(X)=1, the right side is c-2. Since all summands are nonnegative integers, at least two of the sets X union D_i are tight. In a T-free circuit they each have order at least 2r+2, so

    n >= 4r+4-|X|.                                          (12)

Equations (10)-(12) are exact consequences, not assumed interface-packing results.

## 6. The exact degree-(r+1) interface

Suppose d_C(v)=r+1. Set H=C-v and A=N_C(v). Then H is r-forest-sparse and

    e(H)=r(|H|-1),

so it is a union of r edge-disjoint spanning trees.

**Theorem 5.** The full criticality at the deleted vertex is equivalent to

    |A|=r+1, and no proper H-tight set contains all of A.      (13)

More precisely, for any simple union H of r spanning trees and any (r+1)-set A, adding v adjacent precisely to A gives a graphic r-circuit if and only if (13) holds.

**Proof.** For a nonempty proper S subset V(H), sparsity on S union {v} is exactly

    |A intersect S| <= r+sigma_H(S).                          (14)

If |A intersect S|<=r this is automatic. The only other case is A subset S, when it requires sigma_H(S)>=1. Sets not containing v, and the singleton {v}, satisfy sparsity directly. The full edge count is r(|H|)+1. This proves both directions. QED.

The H-tight sets containing a fixed nonempty set are closed under intersection. Indeed, for intersecting tight sets P,Q, the slack uncrossing identity is

    0 = sigma_H(P union Q)+sigma_H(P intersect Q)
        + e_H(P-Q,Q-P),

and every term is nonnegative. Hence their union and intersection are tight, and there are no edges between their exclusive parts.

Let hull_H(B) be the intersection of all H-tight sets containing a nonempty B. It exists because H itself is tight. Then (13) says exactly

    hull_H(A)=V(H).

For ANY anchor a in A one has the more explicit covering identity

    V(H) = union_{b in A-{a}} hull_H({a,b}).                   (15)

The union is tight by repeated uncrossing, since all its terms contain a; it contains A and hence must be all of H.

For a nonedge xy of H, H+xy has its unique fundamental circuit on hull_H({x,y}), by Section 2.1. In a T-free original C, every such pair hull, including those for pairs in A, has order at least 2r+2, by Section 4.

There need not be a nonedge pair in A with hull equal to all of H. The covering identity does not assert that. Nor does a copy in H+xy automatically lift to C: it may use xy in an internal role requiring a fresh global reembedding.

## 7. The sharper residual class is still unbounded

The necessary conditions above are not already contradictory. Here is an explicit unbounded family of circuits satisfying the new small-set exclusions. These graphs are NOT asserted to be T-free.

Fix r>=2 and choose a prime n>r(2r+1). On Z/nZ take the union G_0 of the r Hamilton cycles with steps 1,...,r. They are Hamilton because n is prime, and edge-disjoint because r<n/2. Equivalently G_0 is the r-th power of the n-cycle. Delete any r-1 edges and call the graph C.

Then e(C)=rn-(r-1)=r(n-1)+1. On a proper nonempty S, each Hamilton cycle restricts to a forest, so

    e_C(S) <= r(|S|-1).

Thus C is a simple graphic r-circuit for arbitrarily large n. Deleting a matching gives minimum degree 2r-1 and maximum degree 2r. In particular the graphic-circuit reduction does NOT supply a vertex of degree k=2r+1.

For any S of size 2r+1, some cyclic gap between its successive vertices has length at least r+1, since n>r|S|. Cut the cyclic order at that gap. No edge of G_0[S] crosses the gap. In the resulting linear order, the j-th vertex has at most min(r,j-1) predecessors adjacent to it. Therefore

    e_C(S) <= r(2r+1)-r(r+1)/2,
    sigma_C(S) >= r(r-1)/2 >= r-beta(T)+1.                    (16)

The same argument on 2r vertices excludes K_(2r): its last vertex cannot have 2r-1 preceding neighbors when at most r are available. For r>=3 the same estimate on 2r-sets gives slack at least `r(r-1)/2 >= 2r-3`. Since beta_2(T)>=4, this also satisfies (17) whenever its degree-budget condition holds. For r=2 that condition cannot hold. Consequently this family satisfies all the stated small-set exclusions for EVERY allowed target, at unbounded orders.

This verifies that the new terminal reduction does not inadvertently claim to make the problem finite. It is not numerical evidence for or against universality.

## 8. The still-unproved implication, stated precisely

For each fixed r and T define the following restricted statement:

> **RGC_(r,T), UNPROVED.** A circuit C satisfying (GC), of order n>=2r+3, contains T whenever all the following hold:
>
> 1. C contains no K_(2r).
> 2. Every (2r+1)-set S satisfies sigma_C(S)>=r-beta(T)+1.
> 3. If beta_2(T)+Delta(T)<=2r, every 2r-set S satisfies sigma_C(S)>=2r-beta_2(T)+1.

Theorems 3, 3A, and 4 prove that RGC_(r,T) would suffice for the original GC_r assertion for this target. Conversely GC_r would of course imply the restricted assertion. This is a further exact terminal reduction, not a proof of the residual statement.

The new exchange theorem settles the host-side reachability question completely: an omitted edge is not trapped in a proper subset of a graphic circuit, and its relocation can really be performed by valid spanning-tree exchanges. **What is not proved is a shape-compatible consequence for an injective T-copy.** Neither moving an omitted edge nor adding a colored path to a vertex hull preserves the adjacency roles, order, or injectivity requirements of a particular target tree. Arbitrary-root maps, fixed-core matching-pinch lifts, and star replacement at half the forest budget are not used to bridge that gap.

Likewise, a tight contraction has an exact quotient circuit but introduces parallel edges and loses attachment locations. Equation (13) specifies the exact neighborhood interface at degree r+1, but does not prove the required flexible rooted/list embedding in H. These are the remaining embedding implications, rather than unproved assertions hidden inside the exchange proof.

## 9. Dependencies, verification, and preservation

### Mathematical inputs

1. The graphic-circuit hypotheses and the connectivity conclusions proved in `GraphicCircuitReduction.md`.
2. The standard Nash-Williams forest-decomposition theorem, used to obtain r spanning trees after deleting an edge. The exchange and contraction proofs above are then elementary finite graph arguments.
3. The proved **finite edge-sum list-packing theorem** of Győri–Kostochka–McConvey–Yager, *A list version of graph packing*, arXiv:1501.02488, theorem `List B-E`, at `/corpus/src/1501.02488/b-e_2015_01_01arXiv.tex`, lines 124-126. The exceptional pairs are listed at lines 64-66. It is not a maximum-degree-product conjecture.
4. Elementary tree facts and the infinitude of primes for the illustrative unbounded family.

None of these embedding conclusions is claimed as an available Lean theorem. In particular, the list-packing theorem and the new statements here were not formalized or imported into Spec. No ES induction hypothesis, residual universality lemma, asymptotic announcement, or unavailable low-degree Lean result is assumed.

### Mechanical audit

`GraphicCircuitExchangeClosureChecks.py` implements exact checks of the constructions and formulas. It checks proper-set criticality by integer subset counts on its small circuit instances, validates every step of the shortest-path exchange algorithm, checks tight contractions and the degree-(r+1) hull condition, and constructs one- and multi-boundary embeddings with their exact attachment lists. It also checks the explicit unbounded-family construction at finitely many parameters. These computations audit the stated finite constructions; the universal proofs are the arguments above, not the tests.

The reproducible output is `GraphicCircuitExchangeClosureChecks.log`. The final run passed with:

* 54 graphic-circuit instances, including smaller terminal orders for the purely structural checks; 40,532 proper-subset inequalities checked exactly;
* 1,295 omitted-edge relocations, checking every destination edge of each initial decomposition, and 2,055 individually verified cycle exchanges;
* 81,064 component-identity subset checks, with 6,480 independent connected-component counts;
* 92 tight contractions, 74 degree-(r+1) interfaces, 3,780 cut identities, and 232 separator identities;
* 2,240 one-boundary embeddings and 1,156 multi-boundary embeddings, including 304 with coincident attachment vertices; 560 clique/two-boundary embeddings;
* nine instances of the unbounded cyclic family, for r=2,...,10, with 1,296 small-set checks.

The boundary checks cover all 560 nonisomorphic allowed target trees for r=2,...,5 against the specified construction patterns, not all hosts. No exhaustion of the residual graph class or universal tree-embedding result follows from these counts.

Reproduce with:

    cd /workspace/leanproject
    python3 Submission/GraphicCircuitExchangeClosureChecks.py

`Spec.lean` retains SHA-256

    674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103

and its two original placeholders. No unrestricted theorem has been filled in or submitted as proved.
