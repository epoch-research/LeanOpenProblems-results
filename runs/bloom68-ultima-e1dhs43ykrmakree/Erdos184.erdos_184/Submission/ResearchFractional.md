# Exact fractional cycle partitions: signed-dual rank bound

## Status
Paper-level auxiliary theorem, independently audited, **not an integral proof of Erdős 184** and not Lean-formalized. No priority claim. The external ingredients are the nonnegative weighted Bondy–Fan theorem and finite-dimensional LP duality. The specification remains unchanged.

For a finite simple even graph G, let r(G)=|V(G)|−κ(G), counting isolated components. Let c_f(G) minimize Σ_C x_C over nonnegative real coefficients on simple cycles, with Σ_{C∋e} x_C=1 for every edge. Then:

**Theorem: c_f(G) ≤ r(G).**

The missing step for the original task is a uniform additive O(n) passage from fractional to integral cycle partitions. A constant-factor passage is false; see the earlier Petersen-line-graph gadget research.

## 1. Nonnegative input
`/corpus/src/1911.07778/introduction.tex:47–52` states Bondy–Fan: a 2-edge-connected graph with nonnegative edge weights has a simple cycle of weight at least 2w(E)/(n−1). Only the finite-simple-graph specialization is used. Its original 1991 proof is not present locally; this is an accurately checked secondary quotation, not a Lean axiom.

Consequently, a bridgeless nonnegative weighted simple graph whose cycles have weight ≤1 has total weight ≤r/2, componentwise. For any simple graph J with edge weights in [0,1] and all cycle weights ≤1, delete its bridges B. The remaining graph K is bridgeless, r(K)=r(J)−|B|, and

    w(E(J)) ≤ |B| + r(K)/2 ≤ r(J).

Bridges must be treated separately; simply applying Bondy–Fan to the positive support is invalid.

## 2. Signed dual and negative-cycle deletion
The finite LP dual has unrestricted signed variables y_e and constraints y(C)≤1 for every simple cycle; its objective is y(E).

Given any such y on an even G, delete negative-total-weight cycles until none remains. Edge count strictly decreases, evenness is preserved, and total weight only increases. The resulting even spanning H satisfies

    y(E(G)) ≤ y(E(H)),   0≤y(C)≤1 for every cycle of H,   r(H)≤r(G).

Every even subgraph of H has nonnegative total weight, by an ordinary simple-cycle decomposition. This deletion is a DUAL analysis, not an integral algorithm which has to pay to reinsert the deleted cycles.

## 3. Short independently sufficient bound: 3r/2
The negative edges F of H form a forest. In any actual cycle partition of H, at most |F| cycles meet F (choose a distinct negative edge from each). Their total weight is at most their count. The union R of all other cycles is even and nonnegative, so Bondy–Fan gives y(E(R))≤r(R)/2. Hence

    y(E(G)) ≤ |F| + r(R)/2 ≤ 3r(G)/2.

This already proves a linear exact fractional bound, without the more delicate series-class argument below.

## 4. Series classes and the improved bound
In a bridgeless H, define e∼f if every simple cycle contains both or neither. For f≠e this is equivalent to f being a bridge of H−e: a bridge cut of H−e becomes the two-edge cut {e,f} in H; conversely a nonbridge f lies on a cycle avoiding e. Thus

    S_e = {e} ∪ Br(H−e)

are exactly the equivalence classes. Cycles use each class wholly or not at all.

For each e=uv, there exist two simple cycles C1,C2 (possibly equal) whose EDGE intersection is exactly S_e. In H−e all bridges separate u and v, so contracting the bridgeless components gives a bridge chain between them. In each chain component choose two edge-disjoint simple paths between its entry and exit, by edge-Menger; use empty paths when entry=exit. Concatenate these paths and the bridges, then add e. The resulting u-v paths are simple because chain components are disjoint; attached articulation blocks do not interfere. The cycles may share extra vertices, which is harmless.

Their symmetric difference is an EVEN edge-subgraph, not necessarily one cycle, and therefore has nonnegative total weight. Thus

    2y(S_e) = y(C1)+y(C2)−y(C1△C2) ≤ 2.

Choose one representative per series class, move the entire class weight onto it, and put zero on the other class edges. The weighting z preserves all cycle weights and total weight and satisfies z_e≤1. It need not be nonnegative. No contraction, suppression, or parallel edge is introduced.

Let J be the actual subgraph consisting of positive-z edges. Its edge weights are in (0,1], and its cycle inequalities are inherited from H. Section 1 gives

    y(E(G)) ≤ y(E(H)) = z(E(H)) ≤ z(E(J)) ≤ r(J) ≤ r(H) ≤ r(G).

Finite LP duality now proves c_f(G)≤r(G). The primal is feasible by the even-graph cycle decomposition, and its finite-dimensional feasible set is compact since each x_C≤1. Edgeless graphs have value zero.

## 5. Guardrails and exact examples
- On a triangle weights (M,−M,1) have the sole cycle weight 1. Its whole edge set is a single series class; realizing cycles must be allowed to coincide. Normalization leaves one positive bridge of weight 1, demonstrating the bridge term.
- Full nonnegative cycle-equivalent normalization is false. On K_(2r+1), assign spokes from one vertex v weight −1/(4r), all other edges 1/(2r). Cycles through v have weight (length−3)/(2r), all other cycles length/(2r); all lie in [0,1]. Every triangle through v is zero, so any nonnegative equivalent weighting would vanish on every edge, contradicting positive triangles avoiding v.
- Do NOT merely clip negative weights to zero on H: this can increase a cycle above 1. Delete nonpositive edges to form J instead.
- Simplicity is essential: two vertices joined by four parallel edges have exact fractional partition value 2 using 2-cycles, but rank 1. The weighted theorem is not being applied to such multigraphs.
- A bounded fractional VALUE does not bound the size of its support or give a finite edge-disjoint family. Nothing here fills either sorry in Spec.

## 6. Related stronger/simpler formulation
For an arbitrary finite simple graph, the exact fractional relaxation allowing both cycles and singleton edges also has value at most r(G): its signed dual already includes y_e≤1. Take the positive-edge subgraph directly and apply Section 1; neither negative-cycle deletion nor series normalization is needed. This still does not solve integral decomposition.

## Next research target
Seek a proved additive-rank rounding bound c(G)≤c_f(G)+C r(G), or a dual-fitting construction y(E)≥c(G)−C r(G), or a general binary/regular-matroid circuit partition theorem with this consequence. Check whether such a statement fails for general binary matroids before assuming graphic structure is irrelevant. Existing constant-factor, half-integral, bounded-local-exchange, and generic circuit-cone integer shortcuts have counterexamples.
