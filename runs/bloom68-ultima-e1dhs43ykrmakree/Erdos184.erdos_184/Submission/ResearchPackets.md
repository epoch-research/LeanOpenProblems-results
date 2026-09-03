# Priced packets for the Erdős–Gallai cycle/edge problem

## Status and scope

This is a mathematical research record, not a proof of `erdos_184` and not a modification of the specification. **The full O(n) theorem is not proved here.** The useful advances are:

1. a harmonic segmentation lemma with a global matching proof;
2. exact, even-graph counterexamples to two tempting uses of the priced potential;
3. a **transport-coupled, piece-paid tail-exchange theorem**, with an explicit sufficient inequality and no constant-cycle-count assumption;
4. a strictly stronger **dense-core + globally sparse tails** certificate that still consumes whole paths and retains the original O(p) accounting;
5. a connected, cheap, locally short-path-faithful family in which, for the fixed original decomposition, the literal strict-F-descent / whole-union-dense / whole-path-sparse alternatives get stuck, although an additional, explicitly certified **integral routing packet** closes everything;
6. a clique-necklace lower bound: uncrossing t pairs forces at least t(L−1) new cycles, even if one is allowed to repartition the selected edges arbitrarily;
7. vertex- and harmonic-degree-share accounts for multi-core packets, including an explicit harmonic-budget repair of the necklace. The average degree-share certificate allows unbounded vertex overlap without assuming pointwise degree-normalized resilience.

The last section states what is still missing. In particular, no assertion below silently supplies the adaptive local-reservoir theorem that would finish the conjecture.

`Submission/Spec.lean` was only read. Its SHA-256 before this work was

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

### Conventions and imported results

Graphs are finite, simple, and undirected. Paths are nonempty simple paths, with distinct endpoints. A path's vertex set includes its endpoints. Cycles are simple cycles. All decompositions are edge partitions, not just covers.

We work in an even graph G on n vertices. Isolated vertices cause no difficulty. Every vertex on an edge consequently has degree at least 2. For reduction from an arbitrary graph, a spanning-forest parity subgraph with at most n edges (at most n−1 when n>0) can be removed to leave an even graph: in each spanning tree, take the unique edge subset with the prescribed even-cardinality set of odd-degree vertices as its odd boundary.

The following are imported, not reproved here:

* the Lovász path/cycle decomposition bound supplied in the question;
* the CFS dense theorem: for fixed η>0, a graph K with δ(K)≥η|V(K)| has a cycle/edge partition of cost at most D_η|V(K)|;
* the CFS hereditary power-sparsity theorem: for fixed γ and 0<ε<1, if e_S(X)≤γ|X|^(2−ε) for every vertex set X, then S has a cycle/edge partition of cost at most C_(γ,ε)|V(S)|.

An endpoint-multiplicity bound is stated whenever it is used. I do **not** infer that an endpoint≤2 refinement necessarily preserves the original n/2 bound or preserves all initial cycles without further justification. The unconditional calculations below keep these input assumptions separate.

---

## 1. Baseline accounting and the exact routing certificate

Let the retained initial cycles and the edge-disjoint paths P_1,…,P_p partition H, where E(G)=E(H) disjoint-union E(R). Initial cycles are never reopened merely to obtain an all-path decomposition.

Put

    a_i = 1 + sum_{v in V(P_i)} 1/d_G(v),
    θ = 1/64,
    λ_i = θ/(A a_i),

where A>0 is a fixed absolute constant. If t(v) is the number of original paths containing v, then t(v)≤d_H(v)≤d_G(v). Thus

    sum_i a_i = p + sum_v t(v)/d_G(v) ≤ p+n.                 (1.1)

This particular inequality does not need endpoint≤2. For internal path occurrences the stronger bound is

    sum_i sum_{v internal in P_i} 1/d_G(v) ≤ n/2,           (1.2)

because each such occurrence uses two distinct incident H-edges.

For distributions μ_i on simple R-paths Q_i between the endpoints of P_i, define

    p_ie = Pr[e in Q_i],       l_e = sum_i p_ie,
    I_i(Q_i) = |(V(Q_i) minus its endpoints) intersect V(P_i)|,
    J = sum_i λ_i E[I_i],
    F = (1/2) sum_e l_e² + J,
    M_i = sum_e p_ie l_e + λ_i E[I_i].

When every commodity has an R-route, for fixed original paths and fixed budgets, F is convex on a nonempty finite product of simplices. At an F-minimizer, every support route minimizes

    w_i(Q) = sum_{e in Q} l_e + λ_i I_i(Q),

and the minimum is M_i. This follows by differentiating in the direction of replacing μ_i by a point mass at Q. It is a statement about changing one routing distribution, **not** about changing the endpoints or the H-decomposition.

### 1.1 The LLL uses external collision price, not self price

Define

    C_i = sum_e p_ie (l_e − p_ie),
    Mhat_i = C_i + λ_i E[I_i].

Then Mhat_i≤M_i. The sharper sufficient certificate is

    C_i≤θ and E[I_i]≤A a_i for every i.                    (1.3)

In particular either M_i≤θ or Mhat_i≤θ for every i implies (1.3).

**Proof with explicit constants.** Independently sample all routes. For i<j let B_ij be their edge-collision event and q_ij its probability. A union bound gives

    q_ij ≤ sum_e p_ie p_je,
    sum_{j≠i} q_ij ≤ C_i ≤ 1/64.

Also let T_i be the event I_i>8A a_i. Markov gives Pr[T_i]≤1/8. Use the variable dependency graph, and assign

    x(B_ij)=4q_ij,         x(T_i)=1/4.

Zero-probability events may be discarded. For B_ij, the product over neighboring collision events is at least 1−8θ=7/8. The two possible neighboring unary factors contribute (3/4)². Consequently

    product_{neighbors of B_ij}(1−x) ≥ 63/128 > 1/4,

so the LLL inequality holds for B_ij. For T_i, the collision-neighbor product is at least 1−4θ=15/16, and

    x(T_i) product(1−x) ≥ 15/64 > 1/8.

The finite asymmetric LLL therefore gives edge-disjoint routes with I_i≤8A a_i simultaneously.

For each i, P_i union Q_i is connected and Eulerian. Its cycle-space dimension is I_i+1: the two paths have precisely I_i+2 common vertices. An edge-disjoint simple-cycle decomposition has at most that many cycles, since its cycle vectors are independent. Thus the cost for the routed original paths is at most

    p + 8A sum_i a_i ≤ p+8A(p+n).                          (1.4)

Any unused subgraph of R remains cheap if R was hereditary-power-sparse plus a fixed number of forests/O(n) individually paid edges. This proves the advertised implication from a valid routing certificate to O(n), without assuming a conditional-expectation version of the LLL.

### 1.2 Two elementary lower bounds that expose self-price overreach

If k original paths have endpoints on opposite sides of a cut S and m=|δ_R(S)|, then

    [M_i≤θ for all crossing i]  implies  k≤θ m.             (1.5)

Indeed, put a_e=sum_{i crossing} p_ie. Then sum_{e in cut} a_e≥k, and

    kθ ≥ sum_{i crossing} M_i
       ≥ sum_{e in cut} a_e l_e
       ≥ sum_{e in cut} a_e² ≥ k²/m.

This demands **64-fold cut slack**, not merely the necessary k≤m for edge-disjoint routing. At full utilization, deterministic edge-disjoint routes have C_i=0 but can have arbitrarily large M_i.

Similarly, with m_R=|E(R)|,

    sum_i M_i ≥ sum_e l_e²
              ≥ (sum_i E|E(Q_i)|)²/m_R
              ≥ (sum_i dist_R(s_i,t_i))²/m_R.             (1.6)

Thus low M is a strong sufficient device, not a necessary description of all successful closures. These distinctions matter for a descent theorem whose only stopping rule is M_i≤θ.

---

## 2. Iteration I: exact small blocked configurations

### 2.1 Five vertices: the convex optimum creates avoidable collisions

Take G=K_5 with vertices v,a,b,c,d. Let

    H: P_1=a-v-b,  P_2=c-v-d;
    R: the K_4 on a,b,c,d.

G is even. The two H-paths meet only at v, every endpoint occurs once, and I_1=I_2=0 for every possible R-route. There is therefore no regularizer issue.

At the F-minimum, for P_1 use

    a-b       with probability 2/3,
    a-c-b     with probability 1/6,
    a-d-b     with probability 1/6,

and symmetrically for P_2. The loads are 2/3 on ab,cd and 1/3 on the other four edges. Every positive-probability route has price 2/3; every unused three-edge route has price 4/3. Convexity/KKT proves optimality. Moreover the aggregate load vector is unique, by strict convexity in l. The shortest-route equations then force the displayed distribution, so this is not an artifact of choosing a bad minimizer.

Exactly,

    F=2/3,    M_1=M_2=2/3,    C_1=C_2=1/9 > θ.            (2.1)

All three endpoint pairings have the same optimal energy by K_4 symmetry. Thus no two-tail switch at v strictly decreases F. For a switch to another optimal pairing,

    sum l_e δ_e = −2/9,
    (1/2) sum δ_e² = 2/9,
    F'−F=0.                                               (2.2)

Nevertheless the deterministic direct routes ab and cd are edge-disjoint and have zero own intersections. Their energy is 1, **larger** than the fractional optimum 2/3, while their external collision prices are zero.

Consequences:

* replacing M by external price is a useful certificate correction, but merely testing external price at an F-minimizer is not a complete repair;
* an F-minimizer can prefer avoidable collisions to a perfectly good integral routing;
* a negative old-load linear price is not a discrete-exchange descent certificate.

Five vertices are the smallest possible size for this particular model of four distinct terminals and a single additional H-intersection vertex. This is not a claim of minimality among all conceivable obstructions.

### 2.2 Seven vertices: even the re-optimized switched energy is strictly larger

Keep the H-star paths a-v-b and c-v-d. Take R on a,b,c,d,u,w with edges

    ab, bc, cd, da, au, ub, cw, wd.

All degrees in G=H union R are even: v,a,b,c,d have degree 4 and u,w degree 2. Again I_i=0 for every route and every H-star pairing.

Think of ab as a parallel bundle consisting of a length-1 path and a length-2 path; likewise cd. Unit total load through either bundle has minimum sum of squared loads

    r = min_x [x²+2(1−x)²] = 2/3,

attained at x=2/3. The other two sides bc,da have length 1. The exact optimized energies are

| Endpoint pairing | Minimum F |
|---|---:|
| (a,b), (c,d) | 2/3 |
| (a,d), (b,c) | 1 |
| (a,c), (b,d) | 5/3 |

For the first pairing the two short bundles carry unit flow and bc,da carry zero. For the second pairing only bc,da carry unit flow. For the third, all four macro-sides carry unit total flow, with the two bundles split optimally. Checking shortest-route prices at these load vectors proves global optimality in each case; every simple terminal route chooses one of the two macro-arcs, so no routes have been omitted.

For the first-to-second switch,

    sum l_e δ_e = −4/3,
    (1/2) sum δ_e² = 5/3,
    F'−F = 1/3.                                          (2.3)

There are only two original paths, so a three-path exchange is unavailable. This is a strict finite-exchange barrier, not just a tie.

These tiny graphs are, of course, cheap and do not disprove the Erdős–Gallai statement. Their role is to invalidate specific algebraic shortcuts before using them in a large-graph argument.

---

## 3. Iteration II: a genuinely valid, piece-paid descent theorem

The following theorem is a positive replacement for “the linear price went down, so switch the tails.” Its hypotheses are concrete and can be checked on finite routing supports. The exact identity for any finite change, with δ=l'−l, is

    F'−F = sum_e l_e δ_e + (1/2)sum_e δ_e² + ΔJ.          (3.0)

The statements below control all three terms, including the recomputed intersection regularizer.

### 3.1 Transport-compatible route supports

Let P_1,P_2 have four distinct endpoints, with all their common vertices internal. Orient them s_i to t_i. Suppose they have k≥1 common vertices, and choose one common vertex w for an H-tail switch.

A pair of R-routes is called compatible if, with these orientations, it contains a common nonempty R-subpath C traversed in opposite directions. Suppose there is a coupling ν of μ_1 and μ_2 supported on compatible pairs. This coupling is used **only to construct new marginals**; it is not a claim that the final LLL sampling is correlated.

For finite supports this hypothesis is checkable by a transportation max-flow problem. Equivalently, for every set S of routes in the first support,

    μ_1(S) ≤ μ_2(N(S)),                                   (3.1)

where N(S) consists of compatible routes in the second support. This is the weighted Hall condition for a coupling supported on the compatibility graph.

Choose one compatible oppositely oriented subpath C for each coupled pair, and put

    r_e = Pr_ν[e in C].

For a selected C running from x to y in Q_1 and from y to x in Q_2, form

    W'_1 = Q_1[s_1,x] followed by Q_2[x,t_2],
    W'_2 = Q_2[s_2,y] followed by Q_1[y,t_1].

These walks use all old route segments except the two copies of C. Loop-erase each walk. Pointwise, their summed edge indicators are at most the old summed indicators minus twice the indicator of C. Consequently their new marginals satisfy

    δ_e = l'_e−l_e ≤ −2r_e ≤ 0.                            (3.2)

This coordinatewise monotonicity is the feature missing from the seven-vertex counterexample.

### 3.2 Exact energy gain

Write D_e=−δ_e. We have 2r_e≤D_e≤l_e. Since lD−D²/2 is increasing for 0≤D≤l,

    (1/2)sum_e(l_e²−l'_e²)
       = sum_e(l_e D_e−D_e²/2)
       ≥ 2 sum_e r_e(l_e−r_e) =: g.                       (3.3)

Let ΔJ be the actual change in the intersection regularizer, with the new budgets recomputed from the new simple H-paths. Then

    F'−F ≤ −g+ΔJ.                                        (3.4)

No denominator in J has been held fixed without justification.

### 3.3 Paying for the H-side cycles

Switch the H-tails at w, then loop-erase the resulting two H-trails and retain every extracted simple cycle. If c cycles are extracted, then

    c≤k−1.                                               (3.5)

Proof: the connected union of the original two H-paths has cycle rank k−1. The extracted edge-disjoint cycles have independent cycle vectors. The two new paths and all extracted cycles still partition exactly the same H-edges.

Also the sum of the two new path budgets is no larger than the old sum. Before loop erasure, the switched H-trails have the same vertex-occurrence multiset as the old paths; loop erasure only removes occurrences. This is a statement about the **sum** of the budgets, not about either denominator individually.

Let N count the retained initial cycles and the cycles created by tail exchanges, and price a newly retained cycle at a fixed β>0. Packet costs will be handled by separate bounded ledgers. For

    Φ=F+βN,

we obtain the concrete paid-descent criterion

    g > ΔJ+βc  ==>  Φ'<Φ.                                 (3.6)

Thus actual new pieces, rather than a fictional O(1) number of pieces, are paid for.

### 3.4 A usable bound on the regularizer change

Let U=V(P_1) union V(P_2), and define

    B = E_ν[ |V(Q_1) intersect U| + |V(Q_2) intersect U| − 4 ].

The four old and new endpoints are distinct and lie in U. Cutting out C and loop-erasing cannot increase the total number of route occurrences in U. The new own-intersection sum is therefore at most B. Since every new a_i≥1 and the old regularizer is nonnegative,

    ΔJ ≤ θB/A.                                           (3.7)

Combining (3.3), (3.6), and (3.7) gives a fully explicit sufficient condition:

    2 sum_e r_e(l_e−r_e) > θB/A + βc.                     (3.8)

This is not an equivalent restatement of routability: it specifies a finite coupling test, a concrete route construction, and an explicit quantitative improvement.

**Fixed-corridor corollary.** If every coupled pair uses the same opposite corridor of h edges, then r_e=1 there and g≥2h. With β=1, if

    B≤32Ah and c≤h,

then Φ'−Φ≤−h/2. In particular, a single H-meeting creates no cycles, and a common fixed R-edge gives a strict F-descent under the corresponding bounded-cross-intersection condition.

**Symmetric-bundle corollary.** Suppose b commodities all use a common bundle of f internally edge-disjoint corridors of length h, choosing each corridor with probability 1/f. Two of them can be coupled to choose the same corridor. With compatible orientations,

    g ≥ 2h(b−1)/f.                                       (3.9)

Equality holds if no other traffic uses the bundle and no additional edges are erased. This gives a concrete congestion-versus-cycle-cost comparison, rather than an infinitesimal exchange heuristic.

### 3.5 Three-tail version: cancel a cyclic chain of route segments

There is also a concrete three-path version. Suppose three edge-disjoint H-paths have six distinct endpoints and share an internal vertex w. Take a coupling of their three routing distributions such that, in every coupled outcome, Q_i contains an oriented segment C_i from x_i to x_(i+1), with indices modulo 3. The x_i are distinct. The three C_i need not be edge-disjoint; their edge multiplicities are counted honestly.

Delete C_i from Q_i, and concatenate the prefix of Q_i ending at x_i with the suffix of Q_(i−1) beginning at x_i. After loop erasure, the new route joins s_i to t_(i−1). Perform the corresponding cyclic H-tail permutation at w, loop-erase its three H-trails, and retain all c extracted cycles.

Let ρ_e be the expected total number of deleted C_i occurrences of e. Pointwise deletion and loop erasure give δ_e≤−ρ_e. Hence

    quadratic energy gain ≥ sum_e ρ_e(l_e−ρ_e/2).          (3.10)

With U the union of the three H-path vertex sets and

    B_3 = E[sum_i |V(Q_i) intersect U| − 6],

the same occurrence-counting argument gives ΔJ≤θB_3/A. Thus a sufficient paid-descent condition is

    sum_e ρ_e(l_e−ρ_e/2) > θB_3/A + βc.                   (3.11)

The total new path budget does not increase. The cycle count is at most the actual cycle rank of the connected H-union,

    c ≤ sum_i |V(P_i)| − |U| − 2,

not an assumed constant. If the three H-paths meet only at w, this rank is zero. A compatible triple coupling is a finite multi-marginal transportation feasibility problem; no unjustified pairwise Hall-to-triple implication is being used.

For a checked even example, take H-paths s_i-w-t_i for i modulo 3, and R-routes s_i-x_i-x_(i+1)-t_i. The R connector edges form a triangle. G has ten vertices, with degrees 6 at w, 2 at each terminal, and 4 at each x_i. The three-tail move replaces the routes by s_i-x_i-t_(i−1), deletes all three triangle edges from active routing, creates no H-cycles, and decreases F by exactly 3/2. This verifies the non-infinitesimal construction directly; it is not claimed to be a hard graph or an obstruction to other possible moves.

### 3.6 What these theorems do not prove

A positive independent collision probability does not imply the transportation condition (3.1). At the K_5 minimizer, for example, the direct route ab has mass 2/3 but is edge-disjoint from every route in the second commodity's support, so the compatible-neighborhood Hall condition fails. The seven-vertex example illustrates why a fallback for incompatible route pairs can introduce new loads and destroy descent.

Small old own-intersection costs do not bound B: a route can avoid its own H-path while visiting many vertices of the other H-path. Nor does a large number k of H-meetings imply that c is bounded. Those are precisely the cross-intersection and actual-piece terms retained in (3.8).

If an initial state has Φ=O(n), a sequence of such paid descents keeps the total retained cycle count O(n), because F≥0 and β is fixed. **An unconditional O(n) initial F and the existence of an applicable paid exchange are not proved here.**

---

## 4. Iteration III: harmonic segmentation without a large endpoint blow-up

This lemma can be applied once, before freezing the original paths used for packets and routing.

### Harmonic segmentation lemma

Given any edge-disjoint simple paths in an even G, one can subdivide them into simple paths so that:

1. fewer than 3 units of harmonic vertex mass lie on each new path, hence every new a_i<4;
2. at most n/2 cuts are made in total;
3. at most one cut is made at any graph vertex;
4. endpoint multiplicity increases by at most 2 at each vertex;
5. initial cycles are unchanged, and all edges retain their original multiplicity one.

Thus an input endpoint bound b becomes b+2, and p becomes at most p+n/2. If an input happens to satisfy both p+c≤n/2 and the desired endpoint bound, the resulting total path/cycle count is at most n. If only p≤n and c≤n/2 are available, the safe resulting bound is 2n, not n.

**Proof.** Give a vertex v weight w(v)=1/d_G(v)≤1/2. Along the internal vertices of each original path, greedily form consecutive full blocks of weight at least 1, stopping each block as soon as it reaches 1. Each full block has weight strictly below 3/2; the final residual block has weight below 1.

Build a bipartite graph between full blocks and graph vertices belonging to them. For any collection B of full blocks,

    |B| ≤ sum_{blocks in B} sum_{v in block} w(v)
        ≤ (1/2)|N(B)|,

because a graph vertex occurs internally in at most d_G(v)/2 original paths. Hall's condition holds, even with room for two distinct representatives per block. Choose just one distinct representative per block, and cut the corresponding path there.

The number of full blocks is at most the total internal harmonic mass, hence at most n/2 by (1.2). Representatives are distinct graph vertices, proving the endpoint bound.

A middle new piece lies in the suffix of one full block and the prefix of the next, so has mass below 3. The first piece has mass below 1/2+3/2=2. The last has mass below 3/2+1+1/2=3. With no full block the entire path has mass below 2. This proves all assertions.

The budget sum after subdivision still satisfies (1.1), because the new paths remain edge-disjoint. One need not estimate the duplicated cut-vertex weights separately.

**Caution.** Endpoint≤2 cannot in general be retained by pure subdivision of a fixed decomposition. A long path can have every internal vertex already serving as the endpoint of two other paths. Cutting there adds two endpoints. Rearranging other paths might repair this, but can create cycles, and is not part of this lemma.

This refinement makes the initial individual denominators uniformly controlled. It does not justify treating later tail-exchange denominators as unchanged, and it does not turn unweighted cross-intersection counts into O(1).

---

## 5. Iteration IV: local reservoirs — a proved construction and its limitation

### 5.1 A deterministic cheap edge-local reservoir

Fix an absolute integer f. Repeatedly, f times, take a greedy 3-spanner of the graph consisting of the not-yet-selected G-edges. Let the resulting edge-disjoint layers be S_1,…,S_f, and let R be their union.

Each S_j has girth at least 5: when an edge is added, its endpoints had no path of length at most 3 in the current layer. On any s-vertex subset of a C_4-free graph,

    sum_v binom(d(v),2) ≤ binom(s,2).

By Cauchy–Schwarz, if the subset spans m edges,

    2m²/s−m ≤ s(s−1)/2,
    m ≤ (s/4)(1+sqrt(4s−3)) ≤ s^(3/2).

Therefore the single reservoir satisfies

    e_R(X) ≤ f |X|^(3/2)                                 (5.1)

for every X, with fixed exponent and fixed constant. It is CFS-cheap.

For every final unused edge uv, each layer provides a u-v path of length at most 3, and the f paths are edge-disjoint because the layers are. Thus

    every H-edge has f edge-disjoint length≤3 replacements in R.    (5.2)

This is a genuine edge-local construction inside G; it cannot be replaced by an arbitrary remote reservoir. It is not, however, an independently sampled reservoir, nor does it give the uniform adaptive priced-routing assertion needed below.

### 5.2 Short local replacements alone do not control cuts

Let A,B be large disjoint vertex sets. Choose distinct centers a_1,…,a_f in A and b_1,…,b_f in B. Put in R:

* every edge from each a_j to A minus itself;
* every edge from each b_j to B minus itself;
* the f cross edges a_jb_j.

Take G to contain the complete graph on A union B. For every edge in G minus R there are f edge-disjoint R-paths of length at most 3. For example, a noncenter u in A and v in B use u-a_j-b_j-v. The same verification works when an endpoint is a center, shortening the appropriate route.

Yet |δ_R(A)|=f. Thus f+1 vertex-disjoint H-edge demands crossing A,B cannot all be routed edge-disjointly. Also R is O(f)-arboricity and therefore cheap. This example is about the insufficiency of the local-replacement property for a fixed demand family; it is not claimed to obstruct a carefully chosen complete H-decomposition.

Consequently, (5.2), even for a large fixed f, cannot substitute for a cut/traffic-faithful reservoir theorem. Conversely, cut slack alone does not control the distance lower bound (1.6).

A probabilistic proof must also be uniform for prices chosen **after** the reservoir is seen. Applying an independence or concentration statement for a fixed price assignment to the adaptive minimizer's loads is not justified.

---

## 6. Iteration V: whole-path packets need a more flexible certificate

### 6.1 The original dense-packet accounting is correct

If K is the union of q whole current original paths, then Δ(K)≤2q. Hence

    δ(K)≥η|V(K)|  ==>  |V(K)|≤2q/η.                       (6.1)

Removing disjoint sets of whole paths gives total packet order at most 2p/η, and therefore total dense-theorem cost at most 2D_ηp/η. This does not follow for arbitrary induced dense subgraphs without a path-accounting rule.

### 6.2 Stronger certificate: dense core plus globally sparse tails

A whole-path packet K need not itself have large minimum degree. It suffices to certify an edge subgraph C of K with

    δ(C)≥η|V(C)|,

and put **all** edges of K minus C into the one global sparse bucket B, provided the hereditary bound for the enlarged B is verified with the same fixed γ,ε.

This consumes every selected original path completely: no fragment of it remains in the active path family. Because Δ(C)≤2q, the same estimate holds:

    |V(C)|≤2q/η.                                         (6.2)

Over all such packets, dense-core cost is still at most 2D_ηp/η. The tail bucket is paid for once, at C_(γ,ε)n. Thus this is a strict strengthening of the original packet rule with **unchanged O(p) accounting**.

One may also put tails into a separately certified O(n)-edge/forest account. It is not enough that each packet's tails separately form a forest: the union of arbitrarily many forests need not remain cheap with a fixed constant. The global invariant must actually be checked.

### 6.3 A scalable fixed-decomposition obstruction, not just a tiny example

Here is an explicit family showing why both the potential and the whole-union density condition can be misleading at the same time.

Let q be a positive multiple of 4 and let f≥2 be a fixed even integer. On a core B of 2q vertices, partition K_(2q) into q Hamilton paths L_i with all 2q endpoints distinct. An explicit Walecki factorization, with vertices modulo 2q, is

    L_i = (i, i−1, i+1, i−2, i+2, …, i−(q−1), i+(q−1), i−q),
    0≤i<q.

Attach a private leaf s_i to the first vertex of L_i and a private leaf t_i to its last vertex. Let P_i=s_i+L_i+t_i, and let H be the union of these q paths.

Construct R as follows:

1. Add f new hubs, each adjacent in R to every core vertex.
2. Group the path indices into q/2 pairs. For each pair, put a K_4 in R on its four private leaves.
3. In each such K_4 choose one attachment leaf a, and join a to every hub.

All these R-edges are outside H. The graph G=H union R is even:

* core degree: 2q+f;
* ordinary leaf degree: 4;
* attachment leaf degree: 4+f;
* hub degree: 2q+q/2=5q/2, even since q is a multiple of 4.

There are n=4q+f vertices, p=q paths, endpoint multiplicity 1, and no initial cycles to discard. The reservoir is connected. Moreover

    e_R(X) ≤ (f+3/2)|X|,                                 (6.3)

because the hub edges contribute at most f|X| and the disjoint K_4 cells at most 3|X|/2. Every H-edge has R-distance at most 3: core edges use a hub; a leaf spoke uses leaf–attachment–hub–core, shortened if the leaf is the attachment.

Each terminal K_4 is attached to the rest of R only through its designated vertex a. A simple R-path with both endpoints in that cell cannot leave the cell and return through a. Therefore each original two-path cell has exactly the five-vertex routing calculation from Section 2:

    cell F=2/3, cell M_i=2/3, cell C_i=1/9,
    total F=q/3, all own-intersection costs zero.           (6.4)

In fact **no endpoint re-pairing at all**, not merely a two- or three-tail exchange, can lower F while preserving this endpoint multiset. To see this, consider one full cell's four terminals:

* if none is paired outside, its internal cost is at least 2/3;
* if exactly two are paired outside and one of them is a, the internal routing problem is again two disjoint terminal pairs, with cost at least 2/3;
* if exactly two go outside and neither is a, or if all four go outside, the other three cell vertices must each send a unit to a. The three edges incident to a carry total load at least 3, so internal quadratic energy is at least 3/2.

An odd number of outside-paired terminals is impossible. Transit through the cell by an outside-outside simple route is impossible. Summing the cell bounds gives F≥q/3, attained by the original local pairings; any outside traffic adds nonnegative energy. The intersection regularizer is nonnegative and was zero initially. Extracting H-cycles therefore cannot create an F-decrease by changing these pairings.

On the packet side, any nonempty union of r whole original paths contains all 2q core vertices and 2r private degree-1 leaves. Thus

    δ(K)=1,   |V(K)|=2q+2r.

For fixed η and sufficiently large q, **no** such whole union is an η-dense packet. A sparse bucket containing r whole original paths would satisfy, on the core B,

    r(2q−1) ≤ γ(2q)^(2−ε),
    r ≤ γ(2q)^(2−ε)/(2q−1) = O(q^(1−ε)).                  (6.5)

For large q this is less than q/2, so a globally fixed sparse bucket cannot even touch one path in every cell. Removing some whole paths does not cure the phenomenon in untouched cells: a cell with one remaining terminal pair has minimum internal energy 1/4; pairing its terminals outside cannot lower that bound. The factorized minima persist.

**Scope of this counterexample.** For this fixed original decomposition it blocks a literal strict-F-descent trilemma based only on cheapness, endpoint control, and even strong short-distance edge faithfulness. It is not presented as an output of an independently locally faithful sampler; that stronger condition has not been defined or established here. It does **not** refute global optimization over all decompositions and packets. In particular, neutral-F repartitions retaining additional H-cycles, or preprocessing that changes endpoints, can unlock other certificates. Low-H-degree preprocessing before freezing the paths would also change this example.

Most importantly, the example itself has an excellent O(n) solution. Two valid refinements find it immediately:

* **Core + sparse tails:** consume all q whole paths; apply the dense theorem to K_(2q), and put the 2q leaf spokes, which form a matching, into the global cheap bucket.
* **Integral routing packets:** in each pendant K_4, close each of its two original paths by its direct endpoint edge. These closing edges are distinct. Each closure is one simple cycle, and these choices do not affect other cells' possible routes.

Thus insisting on an F-decrease here is genuinely the wrong mechanism, not evidence of a difficult graph.

### 6.4 Explicit integral routing packets

The preceding repair generalizes as follows.

**Pendant-cell lemma.** Suppose a reservoir subgraph W meets the rest of R through at most one attachment vertex. All packet terminals lie in W, and every other commodity has both endpoints outside W minus the attachment. If the packet has certified edge-disjoint routes inside W, those routes may be reserved and the packet removed without restricting any remaining simple route: an outside-outside simple path cannot enter W minus the attachment and leave it again.

Two concrete certificates require no priced optimization:

* If the packet endpoint pairs are distinct R-edges, use those edges. Cost: one cycle per original path, zero own intersections.
* Suppose the endpoint multigraph has maximum degree b, and W contains 2b−1 distinct nonterminal hubs, each R-adjacent to every terminal. Greedily edge-color the endpoint multigraph with 2b−1 colors; an edge has at most 2b−2 previously colored incident edges. Route a color-c demand via hub c. Proper coloring makes these length-2 routes edge-disjoint. Every route has at most one own internal intersection, so the cost is at most two cycles per original path.

The nonterminal-hub condition matters: without it, routes with different hub colors can use the same edge with the roles of hub and terminal reversed.

These packets remove **whole** original paths and pay O(q), even when their H-union spans arbitrarily many vertices and has private leaves. They are a genuine extra outcome, not an assumed general routing theorem.

---

## 7. Iteration VI: necklace obstruction and a second accounting resource

The previous core-plus-tails rule still does not capture every obvious cheap configuration.

### 7.1 The necklace family

Take L disjoint blocks B_1,…,B_L, each a K_(2q). In every block use the Walecki Hamilton-path factorization L_(i,j), 0≤i<q. For each i, join the end of L_(i,j) to the start of L_(i,j+1), and concatenate to obtain a path P_i through all L blocks.

The q paths partition H. Each P_i is Hamilton on all n_0=2qL vertices. Every vertex is incident with at most one interblock connector, so the connector set is a matching.

For a nonempty whole packet of r paths,

    |V(K)|=2qL,   δ(K)=2r−1,
    δ(K)/|V(K)| < 1/L.                                   (7.1)

Thus no fixed-η whole-path dense packet exists once L>1/η. Yet H contains K_(2q) on every block and is not a fixed hereditary power-sparse bucket as q grows.

For an even completion, put in R the q edges joining each P_i's two global endpoints. These edges are not in H for L≥2. Every vertex of G=H union R has degree 2q. The direct R-closures already solve this completion, so again this is a packet/exchange obstruction, not a counterexample to the desired graph theorem. One can also reserve r of the q full Hamilton cycles instead: for the remaining q−r original paths, each prefix cut of R then has q+r edges. These formulas were checked separately.

### 7.2 An actual lower bound on the cycles created by uncrossing

Select h≤q original paths. Consider **any** repartition of their union into exactly h simple paths with the same 2h global endpoints, plus C simple cycles. Suppose s of the new paths still connect the first block to the last, and write

    t=(h−s)/2.

Thus t endpoint pairs have been uncrossed on each end. Then

    C ≥ t(L−1).                                          (7.2)

**Proof.** The selected union has h(2q−1) internal edges in each block. One simple path or cycle contains at most 2q internal edges in that block. Since h<2q, at least h different pieces must visit each block.

Each of the L−1 interblock cuts has exactly h selected edges. All s cross-endpoint paths must cross each cut at least once; every other piece that crosses it uses at least two cut edges. Hence at most

    s+(h−s)/2 = h−t

different pieces can cross any given boundary.

Every piece visits a consecutive interval of blocks. If N=h+C is the total number of pieces, counting piece/block incidences gives

    hL ≤ sum_j(number of pieces visiting B_j)
       = N + sum_{boundaries}(number of pieces crossing that boundary)
       ≤ h+C+(h−t)(L−1).

Rearranging yields (7.2).

In particular, a two-path uncrossing or a three-path exchange reducing the cross-pair count by two forces at least L−1 new cycles. This lower bound holds even for the best possible repartition, not just for a poorly chosen loop-erasure procedure. It cannot be dismissed by choosing a different switch vertex.

The lower bound is still compatible with O(n): uncrossing Θ(q) pairs costs Θ(qL)=Θ(n). What fails is a constant per-switch charge, or charging the entire necklace only to its q original-path tokens.

### 7.3 Vertex-accounted multi-core packets resolve the necklace

Allow a whole-path packet to have several **pairwise edge-disjoint** dense cores, with all noncore edges going into the **same globally certified** cheap bucket. Cores from different packets are edge-disjoint because the packets consume disjoint whole paths. There are two legitimate accounts for the core vertices:

* **Path account:** a core supported on q_j paths has order at most 2q_j/η; require total charged q_j≤C_p p. A path cannot be charged an unbounded number of times under this account.
* **Vertex account:** require every ambient vertex to belong to at most C_v vertex-accounted cores. Then their total order is at most C_v n.

With fixed constants, total dense-core cost is at most

    D_η(2C_p p/η + C_v n),                                (7.3)

plus the once-only cost of the global tail bucket. The two accounts may be mixed. They are explicit ledgers, not an assertion that arbitrary overlapping dense cores have O(n) total order.

For the necklace, consume the q whole paths in one packet, use its L disjoint K_(2q) blocks as vertex-accounted cores, and put the interblock matching in the cheap account. The core order is exactly n_0, and there are q(L−1)<n_0/2 connector edges. The cost is at most

    D_(1/2) n_0 + n_0/2.

This resolves the whole-path-density obstruction while paying for the actual linear-in-L complexity exposed by (7.2).

The unresolved issue is extending such a vertex ledger to overlapping or nested cores without spending the same vertices at unboundedly many scales. The following additional harmonic account gives a genuine extension, though not an unconditional extraction theorem.

### 7.4 New harmonic edge-share account for dense cores

Define the ambient degree share of an edge subgraph C by

    W_G(C) = sum_{v in V(C)} d_C(v)/d_G(v)
           = sum_{uv in E(C)} (1/d_G(u)+1/d_G(v)).         (7.4)

For any family of edge-disjoint cores C_j, irrespective of vertex overlap,

    sum_j W_G(C_j) ≤ n.                                  (7.5)

This is immediate by summing incident degrees at each vertex. Consequently, if every selected dense core satisfies the **average** share certificate

    W_G(C_j) ≥ α|V(C_j)|                                 (7.6)

for a fixed α>0, then

    sum_j |V(C_j)| ≤ n/α.                                (7.7)

Thus such cores have total dense-theorem cost at most D_η n/α, even with unbounded vertex overlap and even if a whole original path passes through arbitrarily many of them. Whole packets are still consumed, and all their noncore edges still need the one global cheap-tail certificate.

This account is directly related to the proposed path budgets, rather than being an unrelated vertex-count trick. For any original path P_i,

    W_G(P_i) = 2(a_i−1)−1/d_G(s_i)−1/d_G(t_i).

For an edge-disjoint collection of dense cores inside a q-path packet K,

    sum_j |V(C_j)| ≤ W_G(K)/α
                   ≤ (2/α)sum_{i in packet}(a_i−1),       (7.8)

provided (7.6) holds. Thus the harmonic budgets can pay for **dense pieces as well as own intersections**. Their edge form is additive and avoids repeated charging at a shared vertex.

This is **not** the false strong degree-normalized decomposition assumption. There is no assertion that every core or every graph admits (7.6), and no pointwise lower bound d_C(v)≥α d_G(v) is required. For example, take L edge-disjoint K_m's sharing one vertex, with m≥3 odd. G is even. At the common vertex the core/ambient degree ratio is 1/L, so every fixed pointwise domination fails as L grows. Nevertheless each core has

    W_G(C)=m−1+1/L ≥ (2/3)m,

and the harmonic account pays for all cores at O(n) cost.

A convenient sufficient test for (7.6) is that at least an a-fraction of core vertices have d_G(v)≤D|V(C)|. If δ(C)≥η|V(C)|, then W_G(C)≥(aη/D)|V(C)|. Only a constant fraction of vertices need pass the ambient-degree test.

There is also a precise failure certificate. If 0<α<1/2 and W_G(C)<αm, then more than half the vertices of C satisfy

    d_C(v)/d_G(v)<2α,
    d_(G minus E(C))(v) > ((1−2α)/(2α)) d_C(v).

For an η-dense core, the last quantity is at least

    ((1−2α)η/(2α))m.                                    (7.9)

So a core that fails this fixed-α harmonic account has a large supply of ambient edges **not belonging to that core** at many of its vertices. Those edges need not leave its vertex set, and need not lie in R: (7.9) is a proved degree-surplus statement, not a routing theorem. Turning that surplus into useful locally sampled reservoir traffic is a more concrete remaining target than simply asking for an arbitrary dense packet.

### 7.5 Harmonic segmentation also repairs the bare necklace constructively

In the even necklace completion, every ambient degree equals 2q. An original Hamilton path has a_i=1+L. The large harmonic budget exactly records the number of dense blocks traversed.

Cut P_i at the last vertex of its local Hamilton path in each block B_j with j<L. All q(L−1) cut vertices are distinct. The result has qL=n_0/2 paths, endpoint multiplicity at most 2, and individual budgets at most 2+1/(2q). Its first-block pieces are the local Hamilton paths; each subsequent piece consists of one incoming connector followed by a local Hamilton path.

For each block, collect its q pieces as one whole-path packet. Its dense core is K_(2q), and its tails are the incoming connectors. All tails together remain a matching. The core-plus-tails certificate now uses the original path account, with qL total path tokens and total core order 2qL. No repeated unbounded vertex charge is needed.

Alternatively, without any cuts, each block already has W_G(B_j)=2q−1≥|B_j|/2, so the harmonic edge-share account pays for the multi-core whole packet directly. These are two rigorous ways in which the proposed harmonic budgets resolve the necklace's apparent excess cycle cost.

By contrast, the inflated K_4-cell family in Section 6 already has a_i<5/2: its core contribution is 2q/(2q+f)<1 and each leaf contributes at most 1/4. Its internal harmonic mass is below 1, so the segmentation lemma makes no cuts there. That family really needs its core/tail or integral-pendant-packet repair; bounded budgets alone do not fix the potential.

---

## 8. What the iterations establish together

The following is a valid modular implication, with all its additional hypotheses visible.

Start from an O(n)-piece path/cycle decomposition, preserving initial cycles. Optionally apply the one-time harmonic segmentation. Freeze the resulting whole paths. Process only packets with one of the proved certificates:

1. dense whole union;
2. dense core plus globally certified sparse tails;
3. multi-core packet with bounded path/vertex/harmonic-share ledger expenditure;
4. explicitly routable isolated/pendant reservoir packet, with reserved edges harmless to remaining commodities.

For active paths, perform only exchanges satisfying a paid criterion such as (3.8) or (3.11), and retain every created cycle. Here F is the potential of the **active** routing variables, and N counts initial/tail-extracted cycles; packet pieces are charged to their separate O(n) ledgers. Deleting a nonrouting packet deletes nonnegative loads and regularizer terms, so cannot increase active F. Reserving an isolated/pendant routing packet also cannot increase the remaining active F, because no remaining simple route uses its reserved edges. Thus, if the starting paid potential is O(n), the expenditure on tail-created cycles stays O(n) even with these packet retirements interleaved. A direct packet closure may have higher energy if it were left among the active variables; retiring it, rather than insisting on such a replacement, is essential.

If the remaining routing distributions satisfy (1.3), the LLL and cycle-rank argument give the remaining O(n) partition. All unused reservoir and global-bucket edges are handled by their hereditary cheapness certificates.

The absolute-κ resilience decomposition supplied in the question may be used as a preliminary component ledger if it gives an edge partition, O(n) exceptions, and total component order at most 2n. Linear costs can then be summed over components, with another O(n) parity-forest deletion if necessary. Nothing here upgrades that input to the ruled-out strong degree-normalized resilience statement. Also, total component order alone is not a hereditary-union certificate: one must either keep the global bucket invariant or pay the known cheap theorem separately using the bounded total-order ledger.

This implication is not offered as the breakthrough itself. Its nontrivial content is in the independently proved segmentation, finite obstructions, transport descent, strengthened packet accounting, and necklace lower bound above.

### A useful cheap-bucket safety rule

A simple sufficient incremental rule is to keep the total number of bucket-path occurrences at each vertex bounded by an absolute b. Then the union of all those whole paths has maximum degree at most 2b and at most bn edges. Alternatively, bounded overlap of already power-sparse bucket pieces gives a fixed hereditary constant: if each vertex belongs to at most b such pieces and each has e(X)≤γ|X|^(2−ε), then the union satisfies e(X)≤γ(b|X|)^(2−ε).

Merely knowing that each piece or each path is individually sparse does not give either invariant. This is why the global bucket has been checked explicitly in every resolved example.

---

## 9. Verification performed

The mathematical proofs above do not depend on numerical optimization. Separate finite checks were nevertheless run to catch sign, parity, and counting errors:

* All simple terminal routes were enumerated for the five- and seven-vertex examples, and the resulting convex quadratic programs were solved independently. The outputs were:

```
K5 star-H example:
  all three pairings: F=2/3, M_i=2/3, C_i=1/9
  optimized switch: linear=-2/9, quadratic=2/9, difference=0

Seven-vertex example:
  pairings ab|cd, ad|bc, ac|bd: F=2/3, 1, 5/3
  first -> second: linear=-4/3, quadratic=5/3, difference=1/3
```

* Exact-rational two-route coupled cancellation was checked: the constructed new marginal loads decrease coordinatewise and the gain equals the bound in (3.3). The even ten-vertex three-tail example was also checked, with exact gain 3/2 and no new H-cycles.
* The connected inflated-cell construction was checked for q=4,8,12 and f=2,4,6, including evenness, edge partition, distance≤3 for every H-edge, whole-packet degrees, and the distinct direct closing edges.
* Three-layer greedy reservoirs were checked on 70 small graphs, including every vertex subset for the hereditary bound and every unused edge for its layerwise short replacements.
* The explicit Walecki paths were checked for q=1,…,14: they are Hamilton, edge-disjoint, cover K_(2q), and have pairwise distinct endpoints.
* For L=2,…,7 and all r<q in those tests, the even necklace completion, the path edge counts, the minimum degrees, the reservoir degrees 2r or 2r+1, and the prefix-cut size q+r were checked.
* The harmonic edge-share identities, the overlapping-clique windmill example, and the explicit endpoint≤2 necklace subdivision/core-tail packets were checked with exact rational arithmetic.
* The harmonic segmentation construction was tested using exact rational weights on 1,155 generated even graphs. Maximum bipartite matching selected 14,219 distinct cut representatives in total. Every resulting path had harmonic mass below 3, the number of cuts was at most n/2, and the total new budget satisfied p_new+n. These tests did not assume an endpoint≤2 input; the proved b→b+2 statement is separate.

The auxiliary exploratory scripts were in `/tmp`; the reproducible final check script is `Submission/ResearchPacketsCheck.py`. Running `python3 Submission/ResearchPacketsCheck.py` passed every check. It verifies the specification SHA-256 before and after the tests; the hash stayed equal to the value recorded at the start of this document.

---

## 10. Exact remaining gap

**No full Erdős–Gallai O(n) proof has been obtained.** The remaining statement is not a missing numerical constant or a missing LLL calculation.

What is needed is a **uniform structural extraction theorem for an endogenously chosen, locally faithful reservoir and decomposition**. After the proved packet reductions, it must convert genuine remaining collision/intersection pressure into at least one of:

* a transport-compatible two-/three-path exchange whose **actual** cycle count and cross-intersection change satisfy a paid inequality such as (3.8);
* a whole-path core/tail or multi-core packet whose path/vertex/harmonic-share ledger and global tail-bucket invariant can actually be verified;
* another explicit integral-routing packet whose reserved edges do not damage the remaining instance.

It must simultaneously justify an O(n) initial paid potential, or supply a different globally bounded account for the paid exchanges. It must remain valid for prices selected adaptively after seeing R. None of these conclusions follows from endpoint≤2, harmonic budgets, the existence of short R-replacements for H-edges, or F-optimality alone.

The most concrete unproved bridge is now identifiable: **turn external congestion into a compatible coupling with bounded paid H-complexity, or into globally chargeable dense cores.** The harmonic-share test gives an additional specific target: when it fails, (7.9) supplies many ambient edges not in the proposed core's edge set at more than half its vertices; no proof yet turns those edges into suitable adaptive R-routing or a globally sparse tail certificate. A shared R-edge in expectation supplies neither the weighted Hall condition (3.1) nor a bound on the cycles forced by an H-uncrossing; the necklace shows the latter can be arbitrarily large. The inflated pendant-cell family shows that sometimes the correct outcome is a certified integral closure that deliberately has higher F, not an energy descent.

A theorem that supplies this extraction with fixed constants, without an unbounded vertex-scale charge or a nonuniform sparse-bucket constant, would finish the stated strategy. That theorem remains unresolved.
