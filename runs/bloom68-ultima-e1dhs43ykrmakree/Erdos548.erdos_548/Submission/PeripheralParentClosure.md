# A shape-compatible high-parent closure at the peripheral degree boundary

## Status

**This does not prove unrestricted Erdős–Sós.** It proves the requested high-leaf-parent assertion for a non-equivalent, structurally specified class of low-maximum-degree targets. No Lean file has been edited, and no formal theorem or new axiom is claimed.

Here is the main result.

> **Peripheral boundary theorem.** Let `k>=4`, `r=floor(k/2)`, and let G be a finite simple graph with
>
> `I_G(X) > (k-1)|X|/2` for every nonempty vertex set X.
>
> Let T be a k-edge tree with `Delta(T)<=r`. Suppose the subtree induced by the nonleaves of T has an end u with `d_T(u)=r`. Then, for **every** h with `d_G(h)>=k`, there is a T-copy sending u to h.
>
> Consequently, deleting any one of the `r-1` leaves at u gives exactly the near-copy requested in the question, with its missing leaf's parent at h.

In particular the theorem applies to full a-critical hosts. Its incidence hypothesis is weaker than requiring all the proper-induced-set upper bounds as well. In fact the conclusion already follows from `W_k`: the singleton tests give the same minimum degree, and Lemmas 3 and 4 below have W versions. The conclusion is not being asserted for arbitrary prescribed roots, or even arbitrary leaf-parents.

The new closure is an actual occupation-and-rerouting argument for double brooms. Failed endpoint extensions force a closed regular set whose incident density contradicts the hypothesis. Non-broom targets in the stated class reduce, with a verified deletion budget, to a near-greedy rooted-tree lemma. This is not a matrix duality, a target-compression assumption, or a claim that arbitrary forest stars encode all copies.

“New” means additional to the Submission notes reviewed, not a claim of literature priority.

## 1. Definitions and the only embedding inputs

All copies are injective homomorphisms, not induced copies. `I_G(X)` counts edges having at least one endpoint in X, counting an internal edge once.

The following two previously proved tools are used, both at their **full forest edge budget**. Their proofs are in `WeightedListForestFindings.md`, Sections 2–3.

1. **Protected-star packing.** Some positive-demand stars are already packed at fixed centers. Other centers can be chosen in disjoint reservoirs of size one more than their positive leaf demand, disjoint from the entire initial fixed-star packing. If all relevant vertices have degree at least the sum e of the demands, the stars can be packed simultaneously, preserving the fixed centers. Old leaves need not be preserved.
2. **Rooted-star dominance.** In a host of minimum degree at least e, a packing of stars with positive leaf demands `a_i`, totaling e, at specified centers can be replaced by arbitrary rooted `a_i`-edge trees at those same centers.

Neither tool uses ES. No assertion of their validity at degree e/2 or e-1 is made. The usual common-list forest theorem at `delta>=e(F)` is also available; it follows from the same tools, with isolated components placed last.

For completeness, the protected-star argument used below can be checked directly. Choose one representative from each flexible reservoir, minimizing the number of host edges within the complete set D of centers. If the leaf slots cannot be matched outside D, Hall gives a deficient set Q of centers, whose external neighborhood Y has size at most the sum of their demands minus one. The old leaves of any fixed centers in Q still lie in Y and avoid all flexible reservoirs. Thus Q must include flexible centers K, and the union of their reservoirs contains a vertex z outside `D union Y`: those reservoirs have `sum_{i in K}(a_i+1)` positions, while their current centers and Y cover at most `|K|+sum_{i in K}a_i-1` of them. Replace the representative in z's reservoir by z. It has no neighbor among the centers in Q. The old representative has at least `e-|Y|`, hence at least one more than the number of centers outside Q, neighbors in D, because every demand outside Q is positive. This strictly decreases the chosen edge count, a contradiction. So the required leaf matching exists. The initial fixed leaves are used only as Hall certificates; they are not claimed to survive.

## 2. A boundary edge pays for one missing common-list position

> **Lemma 1.** Let F be a forest of nontrivial rooted components, with m vertices and e edges. Suppose `delta(H)>=e`, `|A|>=m-1`, and there is an edge xy with `x in A`, `y outside A`. Then F has an embedding with every component root in A.

**Proof.** Choose one component with a edges. At x choose an a-leaf star containing y as one of its leaves. This is possible since `d_H(x)>=e>=a`. Its `a+1` occupied vertices include y outside A, so it occupies at most a positions of A.

The remaining candidates in A therefore number at least

`(m-1)-a = sum_{other components C} |C|`.

Allocate disjoint component-order reservoirs there. They avoid both the fixed center x and all its initial leaves. Apply protected-star packing with this one frozen positive-demand star and the other positive demands. The total demand is e, exactly the available degree budget. Then apply rooted-star dominance, again at budget e. The roots remain in A. QED.

It is **not necessary to preserve y** in these two transformations. The initial outside leaf supplies the reservoir saving; the conclusion only concerns root locations. If `|A|=m-1`, any final m-vertex copy necessarily uses some vertex outside A, not necessarily y.

The no-isolated-components qualification is retained: this proof does not feed zero demands to the protected lemma without paying its extra cost. We will use Lemma 1 only when every branch is nontrivial.

The boundary condition is substantive. With `H=2K_(m-1)` and A equal to one clique, all marked components would have to fit in m-1 vertices. For at least two nontrivial components the host still has `delta(H)=m-2>=e(F)`.

Nor does this prove a uniform two-position discount. Take two K5's joined by one edge by, and let A consist of the four vertices of the first K5 other than b. For two center-rooted two-leaf stars, `m=6`, `e=4`, `delta(H)=4`, and `|A|=m-2`. Both centers and all their neighbors lie in the first K5, so the required six distinct vertices cannot be supplied. H is connected and A has boundary edges.

## 3. Near-greedy rooting works for every nonleaf of a nonstar

> **Lemma 2.** Let R be a nonstar tree with q edges and let w be any nonleaf of R. If J is connected, `|J|>=q+1`, and `delta(J)>=q-1`, then **every** z in J can be the image of w in an R-copy.

Here q>=3 automatically. The claim deliberately excludes a prescribed **leaf** role.

### Case A: w has a leaf neighbor

Choose a leaf ell adjacent to w. If `d_J(z)>=q`, greedily embed `R-ell`, which has q vertices, with w at z; the degree-q vertex z then has a fresh neighbor for ell.

Otherwise `d_J(z)=q-1`. The closed neighborhood `N_J[z]` has q vertices and is not all of connected J. Hence there is an edge bc with `b in N_J(z)` and `c outside N_J[z]`.

Since R is not a star, w also has a nonleaf neighbor v. Choose a neighbor t of v different from w. The path w-v-t survives in `R-ell`. Map it to z-b-c. Greedily extend this connected partial copy to all of `R-ell`, using minimum degree q-1.

The q occupied vertices include c, a nonneighbor of z. Thus at most q-2 occupied vertices are neighbors of z, although `d_J(z)=q-1`. A fresh neighbor completes ell.

### Case B: w has no leaf neighbor

All `d_R(w)>=2` components of `R-w` are nontrivial. This rooted forest has q vertices and

`e(R-w)=q-d_R(w)<=q-2`.

In `J-z` the minimum degree is at least q-2. If `d_J(z)>=q`, use the ordinary full common list `N_J(z)`.

If `d_J(z)=q-1`, the same connectivity argument supplies an edge from `A=N_J(z)` to its complement in `J-z`. Apply Lemma 1 with `m=q` and edge budget `q-d_R(w)<=q-2`. Restore w at z. QED.

### Why the qualifications are real

* A q-edge star cannot be centered in a `(q-1)`-regular host.
* A component of order q plainly cannot contain R.
* A prescribed leaf is different. For example, let J be the cone over a cycle of length at least four. It has minimum degree three. Let R have four edges, with edges `ell-a, a-b, b-c, b-d`. If ell is prescribed at the cone vertex, b would have to use three neighbors on the cycle, but each cycle vertex has only two such neighbors. This rooted copy does not exist, despite connectedness, sufficient order, and `delta(J)=q-1`.
* The degree cannot uniformly drop another unit: midpoint-rooted P5 at a high vertex in the two-vertex side of K2,8 is the familiar obstruction at `delta=q-2`.

## 4. The actual occupation closure: double brooms

A **double broom** here consists of a path of t edges between u and v, with d-1 additional leaves at u and s-1 additional leaves at v. We allow d or s to be two, but assume

`d>=2, s>=2, t>=2, k=d+s+t-2`.

Its designated end-hub u is a leaf-parent. Put

`b=k-d=t+s-2`.

> **Lemma 3 (rooted double-broom closure).** Suppose
>
> `delta(G)>=b`, `d_G(h)>=k`, and `I_G(X)>(k-1)|X|/2` for every nonempty X.
>
> Then the double broom has a copy with u at h.

In fact the last hypothesis can be replaced by `W_k`: every nonempty X contains a vertex with `2d_G(v)-d_{G[X]}(v)>=k`.

### 4.1 Failure gives an exact endpoint occupation identity

Assume no such rooted copy exists. Consider any t-edge path

`P = x_0 x_1 ... x_t`, with `x_0=h`, and put `z=x_t`.

If z has at least s-1 neighbors outside P, put the leaves at v there. The occupied vertices other than h then number

`t+(s-1)=b+1=k-d+1`.

Since h has degree at least k, it has at least d-1 still unused neighbors. These finish the leaves at u and give the forbidden rooted copy.

Consequently every such path satisfies

`|N_G(z) minus V(P)| <= s-2`.

Because the path contains exactly t other positions and `d_G(z)>=b=t+s-2`, this forces **both**

`d_G(z)=b`, and `z is adjacent to every other vertex of P`.       (1)

This is an exact equality statement, not an average over unspecified copies.

### 4.2 Rotations change all endpoint roles and force a clique on the occupation

For each `1<=i<t`, rotate P to

`h,x_1,...,x_(i-1),x_t,x_(t-1),...,x_i`.

The new joining edge exists by (1). This is a t-edge path starting at h and ending at x_i, on exactly the same occupied vertices. Apply (1) to it. Thus every vertex of `V(P)-{h}` has degree b and is adjacent to every other occupied vertex. In particular **G[V(P)] is a clique**.

Let B be the set of all endpoints of t-edge paths starting at h. It is nonempty: `delta(G)>=b>=t` permits a greedy t-edge path from h. Every vertex in B has degree b and is adjacent to h.

### 4.3 Occupation changes close B under all neighbors other than h

Take z in B and a witnessing path P. A neighbor y of z already in `V(P)-{h}` belongs to B by the rotations above.

If `y outside V(P)`, choose a `(t-1)`-edge path from h to z within the clique `G[V(P)]`, and append zy. This uses t+1 distinct vertices, starts at h, and ends at y. It is possible precisely because `t>=2`: the shorter path uses h, z and any t-2 other vertices of P. Hence y is in B too.

Therefore

`N_G(z) subset B union {h}` for every z in B.                     (2)

Together with (1), this gives

`d_{G[B]}(z)=b-1`, and `N_G(z) minus B = {h}` for every z in B.

So B is a nonempty union of entire components of `G-h`, and

`I_G(B) = e_G(B)+|B| = (b+1)|B|/2 <= (k-1)|B|/2`,

since `b+1=k-d+1<=k-1`. This contradicts the incidence hypothesis. Equivalently every vertex of B has W-potential `b+1<=k-1`. QED.

This closure does not merely explore leaf-parent positions of copies of `T-leaf`. B is built from bare-path occupations, all of whose non-h positions become endpoint roles; transitions may discard an occupied vertex and introduce a new one. The actual two end-star demands were paid before deriving (1). Thus the parent-support-only counterexample in the question is not being ignored or contradicted.

For t=1 this particular neighbor-closure argument is invalid; we have not used it there. Adjacent double stars are outside the low-maximum-degree range anyway.

## 5. The critical deletion bound

The following simple consequence of full incidence is used to prevent small-component trapping after fixing a bare stem.

> **Lemma 4.** If G has `I_G(X)>(k-1)|X|/2` for every nonempty X, and S has c vertices, then every component C of `G-S` has
>
> `|C| >= k-2c+1`.                                             (3)

**Proof.** Write `v=|C|`. There are no edges from C to `V(G)-(C union S)`, so simplicity gives

`I_G(C)=e_G(C)+e_G(C,S) <= binom(v,2)+cv`.

Strict incidence implies `v-1+2c>k-1`, or `v>k-2c`. QED.

The same bound follows under `W_k` alone. For every vertex v of a component C of `G-S`,

`2d_G(v)-d_{G[C]}(v) = d_{G[C]}(v)+2d_G(v,S) <= |C|-1+2|S|`.

Applying W to C makes the right side at least k, which is precisely (3).

For example every component of `G-h` has at least k-1 vertices. No minimum-degree hypothesis on those components beyond what actual vertex deletion supplies is being invented.

## 6. Proof of the peripheral boundary theorem

Put `r=floor(k/2)` and `b=k-r=ceil(k/2)`. The incidence hypothesis implies `delta(G)>=b`; fix any h of degree at least k.

The designated internal end u has r-1 leaf neighbors and exactly one nonleaf neighbor. Follow the unique stem away from u through degree-two vertices.

### Case 1: T is a double broom, including the one-hub/path-handle case

If there is no further branching vertex, use the last leaf-parent on the handle as the other end-hub, of degree s=2. Otherwise take the other end-hub, provided all branches there are single leaves.

In either situation T is a double broom as in Lemma 3, with d=r and `b=k-r`. Its hub distance t is at least two: distance one would give `k=r+s-1<=2r-1`, contrary to `k>=2r` and `Delta(T)<=r`.

All hypotheses of Lemma 3 hold, so u maps to h.

### Case 2: a nonstar remainder after the first further branch

Let the stem be

`u, v_1, ..., v_L, w`,

where the v_i have degree two, and w is the first further vertex of degree at least three. Delete u, its r-1 leaves, and the L vertices v_i. Let the remaining tree be R, rooted at w. It has

`E=e(R)=b-L`, and `d_R(w)=d_T(w)-1>=2`.

This case means R is not a star. Therefore `E>=3`, giving

`L<=b-3<=r-2`.                                                (4)

If R were a star, w would be its center and T would be the double broom of Case 1.

Choose any `(L+1)`-edge host path

`h=x_0,x_1,...,x_L,z`.

It can be grown greedily since `L+1<=b` and `delta(G)>=b`. Reserve its first L+1 vertices

`S={h,x_1,...,x_L}`

for `u,v_1,...,v_L`. In the component J of `G-S` containing z,

`delta(J)>=b-(L+1)=E-1`.

The deletion bound (3), followed by (4), gives

`|J| >= k-2(L+1)+1 = k-2L-1 >= E+1`,

because the difference in the last inequality is `r-L-2>=0`.

Apply Lemma 2 to R in J, with w at z. This retains the chosen host stem and is an actual injective R-copy. Restore the stem. Exactly the r-1 leaves at u remain unembedded.

The number of already occupied positions other than h is

`L+(E+1)=b+1=k-r+1`.

Thus h has at least `k-(b+1)=r-1` fresh neighbors, which receive those leaves. This completes T with its leaf-parent u at h. QED.

All budgets here concern actual deletions and actual component orders. In particular, Lemma 2 is invoked only at `delta(J)>=E-1`, where its rooted shape and order hypotheses have just been verified; an arbitrary E-edge forest is not being packed at degree E-1.

## 7. Nonuniform split critical hosts illustrating the scope

The theorem is not confined to complete bipartite graphs, complete multipartite graphs, or joins of a universal clique with clique components.

Here are infinite explicit full-critical families with minimum degree exactly `ceil(k/2)`. They also give a convenient nonrandom audit family.

### Even k=2r

Take a clique C of order r+1 and an independent set of order r^2. Every independent vertex is adjacent to all but one vertex of C. Distribute the omitted vertices among all r+1 possibilities, as evenly as possible.

This is an r-tree of order `n=r(r+1)+1`, with

`e=rn-r(r+1)/2=(r-1/2)n+1/2`.

Every induced s-vertex subgraph of an r-degenerate graph has at most `rs-r(r+1)/2` edges for `s>=r`, and at most `binom(s,2)` for smaller s. For every proper s<=n-1 these bounds are at most `(r-1/2)s`. Hence the full proper-set criticality assertion holds.

The half-unit surplus is intentional: these are critical witnesses allowed by the reduction, not hosts claimed to meet the literal surplus-one specification before reduction.

### Odd k=2r+1

Take C of order r+2 and an independent set of order `r(r+1)/2`, again with each independent vertex missing just one C-vertex, distributed as evenly as possible. This is an `(r+1)`-tree on

`n=(r+1)(r+2)/2+1`, with `e=rn+1`.

The same degeneracy bound proves every proper induced set is r-sparse. These hosts do meet the literal surplus-one threshold.

For r>=3, every clique vertex is high, every independent vertex has minimum degree `ceil(k/2)`, and each high vertex neighbors minimum-degree vertices. Thus for every high h,

`delta(G-h)=ceil(k/2)-1 < k-r`.

The scalar exact-apex forest test therefore fails for all high vertices when `Delta(T)=r`. Nevertheless the peripheral theorem supplies copies at all these high vertices for its entire target class. With every omitted type present, there is no universal vertex; the nonuniform independent neighborhoods also rule out the complete multipartite form. Degeneracy rules out a `(k-1)`-core.

This comparison is only to the stated scalar apex/core tests. It is not a claim that no other earlier sufficient criterion can certify individual examples.

## 8. Exact remaining gap

The result does **not** make every maximum-degree vertex peripheral. For example, the eight-edge tree

`u-a, u-b, u-l_1, u-l_2, a-a_1, a-a_2, b-c, c-d`

has maximum degree four, but the ends of its internal subtree have degrees three and two. The theorem above does not handle it. Nor does it handle general subcubic targets with large k, whose maximum degree is strictly below `floor(k/2)`.

There is no proved switch here turning such a target into the peripheral class while preserving a copy. When the large leaf-parent has several nonleaf neighbors, deleting it leaves several nontrivial marked components, not the single connected remainder used in Section 6. No simultaneous role change reducing that situation to this construction has been established. In particular:

* The rooted nonleaf theorem cannot be moved to the original half-degree budget for an arbitrary k-edge tree.
* Lemma 1 discounts the common-list size by one when a boundary edge is present; it does not halve the forest edge threshold.
* The double-broom equality (1) uses `delta(G)>=k-d`. When `d<floor(k/2)`, criticality's minimum-degree bound alone does not give this. The endpoint identities and resulting closure then need not follow.
* In the nonstar-stem argument, omitting `L<=d-2` would lose the required residual component-order inequality. Here that inequality was proved from the peripheral half-degree hypothesis and `E>=3`, not assumed.

Thus the general existential high-leaf-parent assertion, and unrestricted ES, remain unresolved. The contribution is a proved non-equivalent sufficient theorem with an actual shape-compatible occupation closure, not another equivalent formulation of the missing full theorem.

## 9. Verification and preservation

`PeripheralParentClosureChecks.py` constructs the new embeddings, reusing the audited protected-star/dominance algorithms at their correct budgets. It checks every produced injection and every target edge. Its double-broom routine implements the path rotations and neighbor switches; if it closes without a copy, it checks the regularity and incident-density certificate directly.

The audit uses explicit clique-bridge and complete-bipartite hosts for Lemma 2, and the certified nonuniform split families above for the peripheral theorem. Noncritical windmills deliberately exercise the negative/resistance branch. Unlabelled target enumeration is used to audit the constructions and their case split, not to search randomly for ES counterexamples or infer the theorem from finite tests. Exact integer arithmetic checks the displayed parity and deletion formulas as an additional audit of the analytic proof.

No existing file was edited. `Spec.lean` and every other Lean file retain their pre-attempt SHA-256 hashes; Spec's hash is

`674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103`.

The concrete audit totals are recorded in `PeripheralParentClosureChecks.log`. They include 100 admissible unlabelled targets, 678 high-parent copies on the explicit critical families, 3,472 rooted nonleaf copies, and 150 independently checked closed regular resistance sets in noncritical windmills. Additional relabelled critical examples force a genuine path rotation before augmentation; positive perturbed-windmill examples force an occupation-changing neighbor switch. No successful computation is claimed to prove the unrestricted conjecture.
