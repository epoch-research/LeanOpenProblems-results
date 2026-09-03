# Core-first absorption audit: new terminal blocks and the remaining gap

**Outcome.** The proposed core correction is valid. Every old regular-core example is terminal, not an uncovered instance. Three further terminal lemmas and exact finite coverage are established below. There are genuinely core-free, cut-free critical families, but none is a verified counterexample to the full certificate union. General extraction remains unresolved; unrestricted Erdős–Sós is not assumed.

Throughout, graphs are finite and simple and k>=3. The parity-kernel lemma in `/tmp/tree_odd_kernel_result.md` is proved and is not an open premise here. No specification, Lean file, or other agent's file was modified. All embeddings are non-induced injective homomorphisms.

## 1. The corrected core terminal

Write `a=(k-1)/2`. A normalized critical host satisfies

    e(G)=floor(a|G|)+1,    e(G[S])<=a|S| for every proper S.

It is connected, has more than k vertices, and has a vertex of degree at least k.

**Theorem.** A nonempty `(k-1)`-core in such a host is terminal for every k-edge tree.

For a nonstar T choose a diameter-end leaf ell and a path `ell-p-q-r`. A connected noncomplete graph Q of minimum degree at least k-1 contains an induced path `v-w-z`. If `|Q|>=k+1`, prescribe `p,q,r -> v,w,z` and greedily extend the connected partial copy to all of `T-ell`. This is valid with minimum degree k-1. Among the other k-1 occupied vertices, z is a nonneighbor of v. Thus at most k-2 neighbors of v are occupied, leaving a neighbor for ell. A complete Q is immediate.

Each component of the core has at least k vertices. A component of exactly k vertices is K_k and has an ambient boundary edge: place any leaf outside and the remaining tree in that clique. Stars use the ambient degree-at-least-k vertex. Consequently any genuinely residual critical host is **(k-2)-degenerate**.

### Exact core-first reclassification

Reusing `AbsorptionCutChecks.py`, with numeric vertex iteration order explicitly normalized, gives all **24,666** critical hosts with `4<=n<=9, 3<=k<n`:

The second column additionally applies the new matching-defect block theorem proved below.

| First certificate/test status | Core-first | Also matching-block-first |
|---|---:|---:|
| Core terminal | 827 | 827 |
| Matching-defect block terminal | — | 17,482 |
| Whole-host bipartite terminal | 27 | 0 |
| Absorbing cut | 9,209 | 2,682 |
| Large-cross terminal only | 1 | 1 |
| Cross-feasible but no budget | 2,638 | 594 |
| No cross-feasible cut | 11,964 | 3,080 |

The last two rows mean **failure of the cut tests only**, not uncovered by the other certificates.

The whole-host bipartite terminal is elementary for each target color pair `(alpha,beta)`. Orient the host sides so that `(beta-1)|X|+(alpha-1)|Y|<=a|G|`. Repeatedly delete X-vertices of degree at most beta-1 and Y-vertices of degree at most alpha-1. Positive weighted surplus survives, producing a nonempty asymmetric core. Greedy colored tree embedding then applies.

## 2. Additional terminal lemmas

### High-degree internal-tree lemma

Let `H={v:d_G(v)>=k}` and let I be the subtree induced by the nonleaves of T. **Any embedding of I into G[H] extends to T**: append all leaves greedily. Every parent has ambient degree at least k, and before each addition at most k-1 other vertices are occupied.

Each color class of I has at most floor(k/2) vertices: its members each have tree degree at least two, whereas the degree sum of a full tree color class is k. Therefore a `K_(floor(k/2),floor(k/2))` inside H is terminal for every T.

This disposes of the tempting matching-cone modification of the old rook hosts. It destroys the old core and preserves the no-cut obstruction, but its high K_(r,r) survives. The checker constructs all 680 target copies at r=3,4,5.

### Root-preserving near-clique lemma

Let J have N vertices and complement maximum degree d. Let P have at most N vertices and maximum degree Delta. If

    N > 2*Delta*d + t,

then **any injective, adjacency-preserving prescription on t vertices of P extends to a P-copy in J**.

Start with an injection extending the prescription. Choose a conflicting edge uv, with u not prescribed. Put x=phi(u). For a candidate position y, with occupant z if present, forbid y when either:

* y has a complement edge to an image of a neighbor of u;
* x has a complement edge to an image of a neighbor of z.

Each forbidden set has size at most Delta*d. The position x lies in both, so their union has size at most `2*Delta*d-1`. Additionally exclude phi(v) and all t prescribed images. The strict inequality leaves a candidate. Swap u with z, or move u to an unused position. If u and z are adjacent, their edge retains the same unordered image pair; it creates no new conflict. All other affected edges are covered by the two tests. Excluding phi(v) guarantees the chosen conflict disappears. Prescribed images remain fixed, so strictly improving swaps finish the proof.

**Boundary-block corollary.** A k-vertex block C, with complement maximum degree d and an ambient boundary edge, is terminal for a k-edge target T whenever

    k > 2*Delta(T)*d + 1.

Delete a leaf of T; prescribe its parent's image to the inside endpoint of the boundary edge; apply the lemma in C; then restore the outside leaf. Unlike the whole-target near-clique test, this works with only k block vertices. The strict inequality is intentional.

### Stronger matching-defect boundary-block theorem

**For k>=4, a k-vertex clique minus a matching, with an ambient boundary edge, contains every nonstar k-edge tree.** Stars again use an ambient degree-k vertex. Thus this is an unconditional terminal in a connected critical host, with no maximum-tree-degree restriction. Equivalently, **any k-set inducing minimum degree at least k-2 is terminal** there.

The elementary matching fact needed is: the complement of an odd-order forest has a near-perfect matching; the complement of an even-order forest has a perfect matching unless the forest is a spanning star.

Here is a proof. A maximum complement matching leaves at most two vertices uncovered, since three uncovered vertices would form a triangle in the forest. In the even nonperfect case let u,v be uncovered. For each matched pair, absence of a length-three augmenting path forces at least two forest edges to u,v. Together with uv this exhausts the forest's entire N-1 edge budget. Acyclicity forces each matched pair to have both these edges incident to the same one of u,v. If pairs of both types occur, a length-five augmenting path exists. Hence all pairs have the same center, and the forest is a spanning star.

Consequently a nonstar N-vertex tree S packs into K_N minus a matching with any prescribed root `p -> v`, provided N is even or `S-p` is not a spanning star. If v is matched in the host defect, use a complement matching covering p. In odd order a near-perfect matching exposing p can be changed to cover it by one edge replacement. If v is unmatched, use a matching in the complement of S-p. The stated forest fact supplies enough pairs in both parities. Assign these nonedge pairs to all host defect pairs, respecting p, and assign the remaining vertices arbitrarily.

Finally, every nonstar k-edge T, k>=4, has a leaf ell with parent p such that `S=T-ell` is nonstar and, when k is odd, `S-p` is not a spanning star. For diameter at least five, take an end leaf. For diameter three, take a leaf at the larger hub. For diameter four, use a depth-two parent with multiple leaf children if one exists; otherwise erase one two-edge branch. The sole exceptional shape for that last choice is P5, where k=4 is even. Apply the rooted packing with p at the inside boundary endpoint and put ell outside.

The checker constructs **25,550 complete target copies**, covering all nonstar targets, matching sizes, and boundary-vertex orbits for `4<=k<=12`. This gives a new exact residual restriction for k>=4: **every k-set must have a vertex of induced degree at most k-3**. This is a local restriction, not a claim of global (k-3)-degeneracy.

## 3. A genuinely (k-3)-degenerate no-cut family

For r>=4 put `k=2r+1`. Take a graph R on 2r-1 vertices with distinguished s,t of degree three and all other degrees four. An infinite explicit choice is the square of the cycle C_(2r-1), with the edge st removed. Add disjoint triples P,Q. Let D consist of R and cliques on `{s} union P` and `{t} union Q`; put `G=complement(D)`.

Then

    n=2r+5=k+4,    e(G)=rn+1,
    d(s)=d(t)=2r-2=k-3,
    d(R-{s,t})=2r=k-1,    d(P union Q)=2r+1=k.

**Full criticality.** Sets of size at most k are automatically r-sparse. Every other proper set omits j=1,2,3 vertices. For such a deleted set X,

    I_G(X) >= j(2r-2)-j(j-1)/2 >= rj+1.

Thus its complement is r-sparse. This is a full induced-subset proof, not merely a minimum-degree check.

**No cut.** H is exactly P union Q, inducing K_(3,3), and every high vertex has degree exactly k. Hence any eligible A is independent, so lies wholly in P or wholly in Q. Its own center s or t has no neighbor in A. No positive B-side minimum cross-degree is possible. Nevertheless H dominates G.

**Empty core.** Peel s,t. Some ordinary R-vertex is not adjacent in R to both centers and therefore loses a G-neighbor, so it peels at threshold k-1. All six high vertices now peel, followed by the remaining ordinary vertices.

For r>=6 the degeneracy is exactly k-3. At least `2r-9>=3` ordinary vertices are adjacent in R to neither center. Peel the centers, two such ordinary vertices, all six high vertices, then everything else. Every forward degree is at most k-3, and the initial minimum degree equals k-3. This also excludes every matching-defect k-block for r>=6.

**Other precise exclusions.** No subcubic one-apex CL certificate exists on any subgraph: a degree-k root must retain its opposite center, whose degree after root deletion is k-4, below the required k-3.

Every independent-class blow-up of a degree-at-most-two quotient is 3-colorable, hence has at most N^2/3 edges. If `N<=3r`, it cannot have density above rN. Since `n=2r+5<=3r` for r>=5, **no positive-density degree-two quotient completion exists on any subset** of this family. This excludes that compensated-completion route, not arbitrary pre-existing templates without its positive-density requirement.

### These graphs must still not be called uncovered

For every r>=11 the entire family is terminal: CL handles Delta(T)>=4, because `delta(G-s_root)>=k-4`. For subcubic T, remove the two centers. The remaining k+2 vertices have complement maximum degree at most four, and `k+2=2r+3>24`; the unrooted near-clique lemma applies.

There is a more informative small escape. For the explicit R stored as `EXAMPLE_R_EDGES` in the checker, r=7 gives

    k=15, n=19, e=134, degeneracy=12, maximum codegree=15.

Exact enumeration finds no `(8,8)`-colored core and excludes all 1,160 candidate uniform near-clique blocks. Nevertheless

    X={0,2,3,4,11,13,14,15},
    Y={1,5,6,8,10,16,17,18}

induces K_(8,8) minus the matching `(2,5),(4,10),(11,8)`. The asymmetric Hall bound `8>=3+3` embeds every balanced subcubic 15-edge tree with zero spare capacity. An explicit noncaterpillar, nonspider copy is constructed and checked. Thus this example demonstrates a necessary near-biclique escape, not failure of the full union.

## 4. A second core-free family: rooted near-cliques give full coverage

The following construction is useful precisely because its no-cut and low-degree CL obstructions persist, yet the new terminal lemmas prove universality.

For r>=5, k=2r+1, start with two disjoint K_k blocks. Perform a two-edge switch between them, preserving all degrees and making a connected 2r-regular Q. Add a path L with three vertices. Give its endpoints r neighbors each in Q and its middle vertex r-1 neighbors, all distinct across the three types. Split each type almost equally between the two blocks, using the exact rounding in `modular_host`. Choose the switch endpoints among ordinary (nonattachment) vertices.

Choose an r-edge matching consisting of one L-edge and r-1 Q-edges, all Q-edges lying within a single type or among ordinary vertices, avoiding the switch endpoints. Enough pairs exist: each block supplies at least r-2 disjoint within-group pairs after its two switch vertices are reserved. Replace the matching by a new vertex joined to its 2r endpoints.

The resulting G has

    n=4r+6,    e(G)=rn+1,    exact degeneracy=k-2.

Its high vertices are the three attachment types, all of degree k. An independent subset of a high block can meet only one type: the only missing within-block edges are matching edges within a type. Thus an eligible A meets at most two types over both blocks and misses a low path vertex. There is no cross-feasible cut. The all-subgraph CL test fails throughout `Delta(T)<=r`, since a high root forces a degree-(r+1) attachment whose remaining degree is r.

**Criticality mechanism.** More generally, attach a tree L with maximum degree at most r+1 to a connected 2r-regular Q, giving each ell exactly `r+1-d_L(ell)` Q-neighbors. For a proper subset J of L,

    e_L(J)+e(J,Q)-r|J|
      = components(L[J])-e_L(J,L-J) <= 0.

For all of L the surplus is one; any proper nonempty Q-subset subtracts at least one via its positive even cut. The empty Q-subset omits all `(r-1)|L|+2` attachment edges. Missing attachment edges only decrease the surplus. This proves full criticality. Replacing an r-edge matching by its cone preserves criticality: on a proper old set S, including the new vertex changes its surplus by

    number of matching edges meeting S - r <= 0.

The set of all old vertices, without the cone, loses r edges and is also sparse.

**Peeling.** The three low vertices peel at threshold 2r, then the cone vertex loses its two low endpoints and peels. A connected 2r-regular Q with a nonempty matching deleted has empty 2r-core. Conversely that deleted-matching Q has minimum degree 2r-1, proving exact degeneracy.

**Terminal dichotomy for every target.** Each original k-block is K_k minus a matching and has a boundary edge. If Delta(T)<=r-1, the rooted near-clique corollary applies. Otherwise T has at least r leaves, so its internal subtree has at most r+2 vertices. The larger high block has `3r/2` vertices for even r and `(3r+1)/2` for odd r: at least r+3 in either case, with minimum degree at least r+1. Embed the internal subtree there greedily and append all leaves. This proves universality for the whole displayed family, without ES. The stronger matching-defect theorem now gives another direct terminal for the same family.

The checker constructs **all 23,030 target trees at r=5,6,7**: 20,893 use the rooted near-clique and 2,137 the high-internal-tree lemma. No modular instance is reported as uncovered.

## 5. Exact order-10 coverage after the stronger terminal

For `n=10,k=7`, all **55,762** normalized critical hosts were classified against the six nonspider subcubic 8-vertex trees:

| Host-first test | Core-first | Also matching-block-first |
|---|---:|---:|
| Core terminal | 224 | 224 |
| Matching-defect block terminal | — | 13,693 |
| One-apex CL on any subgraph | 53,087 | 40,915 |
| Absorbing or large-cross cut | 1,531 | 594 |
| Remaining for tree-specific tests | 920 | 336 |

The new block theorem removes **584 of the former 920** residual hosts; all `584*6=3,504` resulting target copies were explicitly constructed. For the remaining `336*6=2,016` pairs:

| Tree color sizes | Colored core | Local degree-two quotient lift |
|---|---:|---:|
| (4,4) | 522 | 486 |
| (3,5) | 963 | 45 |

There is **no residual pair in this finite domain**. The only positive K_3-completion capacities on ten vertices are `(2,3,5),(2,4,4),(3,3,4)`. The checker enumerates capacitated tree colorings, verifies directional defects and the local `R_i+S_i` inequalities, and performs improving swaps. All **1,146** baseline lift certificates were realized, using **1,169** swaps; 531 of those lifts remain in the stronger first-certificate classification. Absorbing cuts are recursive certificates, not being mislabeled as direct terminal copies.

## 6. Verification, scope, and remaining work

Run:

    python3 Submission/CoreFreeAbsorptionChecks.py

The saved log is `Submission/CoreFreeAbsorptionChecks.log`. The complete run passes in about 75 seconds, including 108,682 checked injective copies (including intermediate leaf-deleted copies), 23,030 full modular target copies, 11,328 exact modular cut exclusions, and the finite classification tables above. An independent diameter-case leaf construction passed all 32,491 nonstar trees on 5–16 vertices; family arithmetic and matching-existence bounds passed through r=1000 (`/tmp/corefree_diameter_leaf_independent.log`).

A normalization pitfall was audited explicitly: the old bitmask helper assumes graph iteration order agrees with numeric labels. The new checker normalizes every graph before calling it and independently checks returned copies using adjacency sets. The old geng enumeration satisfies this ordering assumption. Exploratory negative results on nonnormalized graphs were rejected, not reported as coverage holes. Solver timeouts were never treated as absence certificates.

**What remains:** no general theorem produces an absorbing cut, a colored core, a suitable dense block, or a safely liftable quotient from every critical `(k-2)`-degenerate host. Nor is a host/target pair known here that defeats the entire available union. The results narrow the residual problem and establish exact conditional and finite coverage; they do not assert global extraction.
