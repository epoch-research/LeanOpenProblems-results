# General interfaces: exact configurations, signed cap gluing, and a single collision ledger

## Status and scope

**The unrestricted Erdős–Gallai conjecture is not proved here.** In particular, this note does not establish a universal constant `C` with `c(G) <= c_f(G) + C r(G)`. The specification and all pre-existing research files are unchanged. These are paper-level auxiliary results, not Lean formalizations; no literature-priority claim is made.

The inputs read were `ResearchRounding.md` and `ResearchFractional.md`, including the exact series-parallel traffic theorem, signed-dual issues, exact two-edge splicing, and the Petersen-ring obstruction. The audited fractional theorem `c_f(G) <= r(G)` is used only as an input, not re-proved or strengthened by an integrality assumption.

The new results relative to those notes are:

1. An **exact arbitrary-vertex-separator state for one simple cycle**: endpoint matching, boundary vertices used internally, and connectivity. Its proof specifies precisely which path families are admissible.
2. A **global port-sewing theorem** with a repeated-original-vertex ledger. It works for arbitrary matched path interfaces, including flattened elimination constructions, and never calls a closed trail a simple cycle.
3. An **explicit signed dual gluing rule across arbitrary many-port capped regions**, valid for every simple cycle, not just selected cycles or fractional support.
4. An **exact variational reduction** of `c(G)` to capped-region partitions plus a computable connectivity/collision objective.
5. An unconditional **capped-region gap inequality**. For any nontrivial flat vertex partition of a connected even simple graph, with region order `n_i`, boundary size `b_i=2k_i`, and simple cap `H_i`,

   ```
   c(G)-c_f(G) <= sum_i [c(H_i)-c_f(H_i)]
                 + sum_i (n_i+1)(k_i-1).                         (A)
   ```

   This gives a genuine **linear closure theorem for uniformly bounded interfaces**, even with an arbitrary cyclic quotient and dense regions. There is just one final-region ledger, not a new O(n) charge at every recursion depth.
6. Two sharp graphic warnings: a fixed four-port sewing can require arbitrarily many simple cycles despite two-cycle partitions of both caps; and one bad degree-four transition can increase the constrained optimum from `2` to `k+1` in an Eulerian series-parallel graph.
7. A precise limitation: the crude boundary-volume ledger in (A) is **quadratic for every nontrivial partition of an odd complete graph**, although that graph has zero rounding gap. Thus universal cheap boundary volume is not a missing lemma one may simply conjecture.

The exact objective below retains more information than (A) and survives all these tests. Proving a uniform bound for that jointly chosen objective remains open.

---

## 0. Conventions

Graphs under discussion are finite, simple, undirected and even. A cycle has distinct vertices, length at least three, and is used as an edge set. Partitions are exact edge partitions. Write

```
c(G)   = minimum number of simple cycles in an edge partition,
c_f(G) = min sum_C x_C,  x_C >= 0,  sum_{C containing e} x_C = 1,
r(G)   = |V(G)| - number_of_components(G).
```

The finite LP dual has free signed edge weights:

```
max y(E(G)),       y(C) <= 1 for EVERY simple cycle C.             (0.1)
```

All auxiliary *caps* defined below are simple even graphs. Temporary routing and quotient graphs may have parallel edges; no rank bound for a simple graph is applied to those multigraphs.

Isolated vertices cost nothing. The main cap theorem is stated for a connected graph and a partition into at least two nonempty vertex sets. Other components can be treated separately.

---

## 1. What an arbitrary separator must remember

### Lemma 1.1 — exact one-cycle configuration across a vertex separator

Suppose `G=G_1 union G_2`, the edge sets are disjoint, and `V(G_1) intersect V(G_2)=S`. A *proper path configuration* on side i is a nonempty union `L_i` of pairwise vertex-disjoint, positive-length simple paths, all of whose endpoints lie in S. In particular it has no closed component. Define:

* `T_i`: its path endpoints;
* `M_i`: the perfect matching of `T_i` pairing the two endpoints of each path;
* `U_i`: the vertices of S used internally by its paths.

Then `L_1 union L_2` is one simple cycle meeting both sides if and only if

```
T_1 = T_2 = T != empty,
U_1 intersect U_2 = empty,
the multigraph M_1 union M_2 on T is connected.                  (1.1)
```

Every simple cycle meeting both edge sets arises in this way.

**Proof.** Within each configuration, degree is one on T, two on internal path vertices, and zero elsewhere. Also `T_i intersect U_i` is empty. With a common T, condition (1.1) makes the union degree two at every used separator vertex: a vertex of T has one edge from each side; a vertex of either U has two edges from that side and none from the other. Outside S, the sides are disjoint and all used vertices have degree two. Contract the interiors of all the paths. Since the U sets are disjoint and no U vertex is in T, these contractions preserve the connected components and give exactly `M_1 union M_2`. Thus the union is connected and 2-regular. It is a simple graph, so it is an actual simple cycle.

Conversely, a proper nonempty edge subset of one simple cycle has no closed component and consists of vertex-disjoint paths. An endpoint of its restriction to one side must have its other cycle edge on the other side, and hence lies in S. Such switching vertices are exactly the same T on both sides. A separator vertex cannot be internal on both sides of a simple cycle. Contracting the paths in the connected cycle gives a connected matching union. This proves necessity and completeness. □

For `|S|=1` no nonempty even T exists, recovering articulation locality. For `|S|<=3`, necessarily `|T|=2`, so each side contributes one path; but one must still remember whether the remaining separator vertex is used internally. For `|S|=4`, T has size two or four. In the four-endpoint case, equal matchings produce **two** components, whereas different matchings produce one.

**A three-vertex warning.** The paths `(a,c,b)` and `(a,x,c,y,b)`, on sides meeting in `{a,b,c}`, have identical endpoint pairs `{a,b}`. Their union is two triangles sharing c, not one simple cycle. The missing condition is `U_1 intersect U_2=empty`.

### Consequence for separator/elimination representations

For the trace of **one global cycle**, a finite separator state consists of `(T,M,U)`, together with empty/finished-cycle flags. On a tree of edge-set separations, apply Lemma 1.1 at a merge, or its version with some paths left open. A closed component cannot be included alongside an open component in the trace of one global cycle: a finished cycle cannot later be extended. This follows from the same degree-two argument.

Inductively, mutually vertex-disjoint paths remain mutually vertex-disjoint in every admitted *single-cycle* configuration. Forgotten vertices have no incident edges outside their region; they cannot be revisited from outside. Thus these states are complete for generating the simple-cycle columns, provided each local configuration is really realizable by such disjoint paths. They do not assert that every formal matching is realizable.

This is an exact configuration description, **not** a proof that its edge-covering LP is integral. In particular, it does not let one aggregate a whole partition into just endpoint-matching counts. Different local paths belonging to different eventual cycles may share an interior vertex. If one later routes them into the same cycle, that shared vertex must still be detected. The following theorem retains precisely that information.

---

## 2. Global port sewing and its single ledger

### Theorem 2.1 — sewing arbitrary path packets

Suppose the edges of an even simple graph G have been partitioned into:

* q already-paid simple cycles; and
* positive-length simple paths, with separate labelled ports at their endpoints.

At each original vertex, pair all path-end ports there in a perfect matching. Such a matching exists because their number is even: all other contributions to the degree come in pairs.

Form the routing multigraph A whose vertices are the paths and whose edges are the matched pairs of ports. Each path has two ports, so A is 2-regular. Its z components specify z edge-disjoint nonempty closed trails in G. For a routing component Q, let `R_Q` be its actual edge subgraph, and put

```
m_Q(v) = d_{R_Q}(v)/2,
D_Q    = sum_{v in V(R_Q)} (m_Q(v)-1),
D      = sum_Q D_Q.                                                (2.1)
```

Then there is an edge partition into actual simple cycles with

```
c(G) <= q + z + D.                                                (2.2)
```

The routed trail belonging to Q is already a simple cycle if and only if `D_Q=0`. Moreover, writing `R=union_Q R_Q` and

```
k(v)  = d_R(v)/2,
nu(v) = number of routing components Q using v,
```

the cost is one **global original-vertex ledger**:

```
D = sum_{v in V(R)} (k(v)-nu(v)).                                  (2.3)
```

No vertex is charged separately at every interface it traverses.

**Proof.** Ports paired at a vertex identify the successive paths of each component of A, producing a closed edge-simple trail. All its real edges are distinct because the original paths partition edges. Its edge subgraph is connected and even. Each passage through v accounts for two incident edges, so the number of passages is `m_Q(v)`.

Split a closed trail at two distinct occurrences of a repeated vertex v. Both resulting closed trails are nonempty and have disjoint edge sets. The quantity `sum_w (number_of_passages_at_w - 1)` decreases by one at v, and by an additional one for each other vertex occurring in both new trails. Thus the total excess decreases by at least one whenever the number of trails increases by one. Starting with Q, at most `D_Q` such splits are possible before all trails have distinct vertices. A nonempty closed edge-simple trail in a simple graph cannot have length one or two. The final trails are therefore actual simple cycles, at most `1+D_Q` of them. Add the q already-paid cycles.

Equivalently, `|E(R_Q)|=sum_v m_Q(v)`, so

```
beta(R_Q)=|E(R_Q)|-|V(R_Q)|+1=1+D_Q.
```

The condition `D_Q=0` says that the connected graph `R_Q` is 2-regular, exactly the simple-cycle condition. Finally sum the passages and subtract one for every pair `(Q,v)` with v used by Q. This gives (2.3). □

This theorem applies to a flattened general separator or elimination construction whenever its actual paths and port pairings have been retained. An endpoint matching determines A and z, but not D: the labelled original-vertex incidences of its paths are also needed. A local perfect-matching or blossom certificate says nothing about these incidences.

Notice that small D does **not** require bounded degree. A high-degree vertex may be used once by each of many different routing circuits, in which case `k(v)=nu(v)` and it costs zero. The problematic quantity is repeat visits *within the same circuit*.

---

## 3. Simple caps and a rank ledger for a flat interface system

Let G be connected and even, and fix a vertex partition

```
V(G)=V_1 disjoint_union ... disjoint_union V_p,   p>=2, V_i nonempty.
```

Let F be the set of edges with endpoints in different parts. Set

```
n_i = |V_i|,
b_i = |delta_G(V_i)| = 2 k_i,
B_i = {v in V_i : v is incident with an edge of F},
s_i = b_i-|B_i|.
```

Evenness gives even b_i; connectedness gives `b_i>=2`, so `k_i>=1`. Also

```
sum_i k_i = |F|.                                                   (3.1)
```

### Definition 3.1 — economical simple cap H_i

Start with `G[V_i]` and a new root `rho_i`. For every cut edge e incident with `v in V_i`, create a labelled cap arm from `rho_i` to v. At each boundary vertex v, use one direct root-v edge for one of its incident cut edges. For each remaining cut edge at v, use a length-two arm with a private subdivision vertex. There are exactly s_i such subdivision vertices.

All arm edges are auxiliary; their labels remember the corresponding original cut edge. No two direct edges have the same endpoints, and all subdivisions are private, so `H_i` is simple.

### Lemma 3.2 — cap properties and traffic count

The cap is connected and even, and

```
d_{H_i}(rho_i)=2k_i,
r(H_i)=n_i+s_i,
sum_i r(H_i)=n+sum_i s_i.                                         (3.2)
```

In every integral cap partition, exactly k_i cycles use the root. Removing their cap arms gives exactly k_i simple paths in `G[V_i]`, each with two labelled cut-edge ports; a path is allowed to be a single vertex. All other cap cycles are real cycles wholly inside the region.

In a fractional cap partition, the total mass of root-using cycles is exactly k_i. Consequently

```
f_i := c_f(H_i)-k_i >= 0                                         (3.3)
```

is exactly the minimum fractional mass of internal cycles in a local cycle/path cover with load one on every real edge and every labelled port. Similarly `c(H_i)-k_i` is the minimum integral number of internal cycles with these conditions, with no prescribed pairing of the ports.

**Proof.** An original vertex retains its degree from G: each removed cut edge is replaced by one arm edge at that vertex. The root has degree b_i and every subdivision vertex degree two. Every component of `G[V_i]` has a cut edge; otherwise it would be a proper component of G. The root thus connects all of them. The order is `n_i+1+s_i`, which proves (3.2).

A simple cycle through the root uses exactly two root edges and hence exactly two whole arms. Removing them leaves a simple real path. If both arms end at the same vertex, this real path is just that vertex; a nontrivial return to that vertex would contradict simplicity. A cycle avoiding the root cannot use a subdivision vertex, whose degree-two arm leads to the root. Thus all root-free cycles are real.

Counting the exactly covered root edges gives k_i cycles, or total fractional mass k_i. Conversely every simple port path caps to a simple cycle; even a trivial path does, because distinct arms at the same vertex have disjoint interiors and at most one is direct. The correspondences preserve all individual edge loads. Subtracting the fixed root-cycle mass proves (3.3) and its integral analogue. □

If F is a matching in the original graph, then all `s_i=0`, and the sum of cap ranks is exactly n. No simplicity-based theorem is being applied to a cap with unacknowledged parallel edges.

---

## 4. A signed dual gluing rule for every simple cycle

### Theorem 4.1 — anchored cap dual

Choose any feasible signed dual `y_i` on each simple cap `H_i`. For a cut edge e incident with region i, let `a_i(e)` be the sum of `y_i` along its labelled cap arm. Fix one anchor edge `e_0 in F`. Define weights y on the original G by

```
y(e) = y_i(e)                                  [e internal to V_i],
y(e) = a_i(e)+a_j(e)-1+1_{e=e_0}                [e in F, i--j].     (4.1)
```

Then y is feasible for the full dual of G and

```
y(E(G)) = sum_i y_i(E(H_i)) - |F| + 1.                             (4.2)
```

**Proof.** A simple cycle contained in one region retains its old inequality. Let C cross between regions and let `ell=|C intersect F|`. Its maximal regional segments are ell simple paths, allowing single-vertex segments. Each caps to a simple cycle of the relevant H_i, so the sum of their cap weights is at most ell. In that sum every real internal edge of C appears once, and each cut edge e contributes its arm weight from each of its two endpoint regions. Hence

```
y(C) <= ell - ell + 1_{e_0 in C} <= 1.
```

This checks every simple cycle, including those absent from all selected cap partitions. Summing edge weights gives (4.2), since every cap edge is either one real internal edge or belongs to exactly one arm. Signs are unrestricted throughout. □

Choosing optimal cap duals gives

```
c_f(G) >= sum_i c_f(H_i)-|F|+1 = sum_i f_i+1.                     (4.3)
```

Here finite LP duality only supplies optimal signed certificates; no integrality claim is involved.

For later use define the **fractional coupling credit**

```
Gamma := c_f(G)-sum_i f_i >= 1.                                  (4.4)
```

There is a direct primal check. Restrict an optimum fractional partition of G to all regions and cap each path segment. If I is the total mass of cycles contained in a single region and X the mass of crossing cycles, the resulting cap covers have total cost `I+|F|`. Thus `sum_i f_i<=I`, while `c_f(G)=I+X` and `X>=1` because any fixed cut edge has load one. This proves `Gamma>=X>=1`.

**Gamma is not asserted to equal a scalar traffic LP on the quotient.** Independent local cap optima may be mutually incompatible. Section 7 makes Gamma unbounded while there are only four cut edges.

---

## 5. Exact unrestricted reduction to local partitions and labelled connectivity

Choose any simple-cycle partition `D_i` of each cap. Write

```
ell_i = |D_i|,
q = sum_i (ell_i-k_i).
```

Keep the q root-free cycles. For each root cycle retain its simple real port path, including its actual original vertex set. Join the two ports labelled by each original cut edge using that edge. The auxiliary routing graph A has one vertex per local path and one edge per member of F. It is 2-regular; its components are the closed routed circuits.

Let z be its number of components. For a routing component Q and original vertex v, let `m_Q(v)` count the local paths of Q containing v. Define

```
D = sum_Q sum_{v used by Q} (m_Q(v)-1).                             (5.1)
```

A trivial regional path consumes two cut edges at its one vertex and counts as one passage. Thus in every case `d_{R_Q}(v)=2m_Q(v)`, and Theorem 2.1 gives

```
c(G) <= q+z+D.                                                    (5.2)
```

One may equivalently apply that theorem to the positive-length regional paths and the cut edges regarded as one-edge paths; at a trivial regional path pair its two cut-edge ports directly.

### Theorem 5.1 — exact interface objective

For any fixed nontrivial flat vertex partition and its caps,

```
c(G) = min_{all cap partitions D_1,...,D_p} (q+z+D).               (5.3)
```

Equivalently, putting `Delta_i=c(H_i)-c_f(H_i)`,

```
c(G)-c_f(G)
  = min_{all cap partitions} [sum_i (ell_i-c_f(H_i))
                              + z + D - Gamma].                  (5.4)
```

The minimization in (5.3) is over local cap partitions, **not necessarily locally minimum ones**. Its objective is computed from the local paths, their endpoint pairings, their original vertex incidences, and the connected components of A. It does not invoke an unknown minimum cycle decomposition of any routed residual.

**Proof.** Inequality (5.2) holds for every choice of cap partitions, so its minimum is at least `c(G)`. Conversely, start from a globally minimum actual partition of G. Keep every cycle contained in a region. Split each crossing cycle into its maximal regional segments and cap each segment separately. Every real edge and every arm is used exactly once, giving valid partitions of all caps. Sewing them along their labels recovers exactly the original crossing cycles. They have no repeated vertices, so `D=0`, and q+z is precisely the number of original cycles. This proves (5.3). Equation (5.4) follows from `sum k_i=|F|`, `f_i=c_f(H_i)-k_i`, and the definition of Gamma. □

The exact reduction does not itself assert a cheap choice of states. It identifies the cost that has to be optimized jointly; local minimization of each cap or of each perfect matching is not a substitute.

### A useful combinatorial bound on routing connectivity

Let J be the connected quotient multigraph with vertex set `{1,...,p}` and edge set F. Each routed component gives a nonempty even edge set in J; these sets are pairwise edge-disjoint. Fix a spanning tree of J. Every nonempty even edge set contains a non-tree edge, since a forest contains no nonempty even subgraph. Different routed components supply different such edges. Therefore

```
z <= |F|-p+1,
z-1 <= sum_i (k_i-1).                                             (5.5)
```

Also `z<=|F|/2`, since there are no loop cut edges. This is an elementary graphic spanning-tree argument, not an application of the false unrestricted binary-matroid extension.

---

## 6. The positive global theorem and its one cost account

### Theorem 6.1 — cap-gap and certificate gluing

For the setup of Section 3 define

```
L := sum_i (n_i+1)(k_i-1).                                        (6.1)
```

Then

```
c(G)-c_f(G) <= sum_i Delta_i + L.                                (6.2)
```

More constructively, choose arbitrary cap partitions D_i and arbitrary feasible cap duals y_i. There is an actual partition D_out of G and the explicit feasible global dual y of Theorem 4.1 such that

```
|D_out|-y(E(G))
  <= sum_i [|D_i|-y_i(E(H_i))] + L.                               (6.3)
```

**Proof.** Region i has exactly k_i retained paths. A vertex in V_i belongs to at most k_i of them. If it belongs to at least one, at least one routed component uses it. Its contribution to the global collision count (2.3) is therefore at most `k_i-1`; if it belongs to no retained path its contribution is zero. Hence

```
D <= sum_i n_i(k_i-1).                                            (6.4)
```

Sew and split as in Theorem 2.1. Using (4.2), the difference between the output count and the constructed global dual is at most

```
q+z+D - [sum_i y_i(E(H_i))-|F|+1]
 = sum_i [ell_i-y_i(E(H_i))] + z-1+D
 <= sum_i [ell_i-y_i(E(H_i))]
       + sum_i (k_i-1) + sum_i n_i(k_i-1).
```

The last inequality is (5.5) and (6.4), proving (6.3). Choosing minimum cap partitions and optimum signed cap duals gives (6.2), because `c(G)<=|D_out|` and `y(E(G))<=c_f(G)`. □

The three charges are explicitly:

* local certified cap slacks, once per final cap;
* at most `k_i-1` for each vertex in final region i, covering all its repeated visits across the whole routing;
* one additional `k_i-1` per region, for excess routing components beyond the single anchored dual credit.

There is **no sum of these bounds over separator depths**. The exact, potentially better ledger is (5.4); (6.2) deliberately discards the extra credit `Gamma-1` and replaces actual collisions by a worst-case boundary-volume bound.

### Corollary 6.2 — a genuine O(n) closure theorem

Suppose `b_i<=2K` for all final regions, where K is fixed, and suppose their simple caps independently satisfy

```
Delta_i <= C r(H_i)
```

for a fixed nonnegative C. Then

```
c(G)-c_f(G) <= [2K C + 2(K-1)] n.                                (6.5)
```

If the cut edges form a matching, the stronger bound is

```
c(G)-c_f(G)
 <= [C + (K-1)(1+1/(2K))] n.                                    (6.6)
```

**Proof.** Since every B_i is nonempty,

```
sum_i s_i = sum_i (2k_i-|B_i|) <= (2K-1)p.
```

Equations (3.2) and (6.1) give one combined budget

```
sum_i Delta_i + L
 <= C[n+(2K-1)p] + (K-1)(n+p)
 <= [2K C+2(K-1)] n,
```

using `p<=n`. This proves (6.5).

If F is a matching, `s_i=0` and `n_i>=2k_i`. Thus

```
sum_i n_i(k_i-1) <= (K-1)n,
k_i-1 <= [(K-1)/(2K)] n_i.
```

Add these bounds for L and the local slack bound `C sum_i r(H_i)=Cn`, proving (6.6). □

For example, a flat assembly of **exactly roundable** caps, each with at most four boundary edges, has `c(G)<=c_f(G)+2n`; if its cut edges form a matching the error is at most `5n/4`. These conclusions do not require the quotient to be a tree and do not bound the density of the regions.

Using the audited `c_f(G)<=r(G)`, these are actual O(n) simple-cycle theorems for the stated class. To express their additive errors in original graphic rank, a nonempty connected simple even component has at least three vertices, so `n<=3r(G)/2`. Sum componentwise and ignore isolated vertices. The constants depend on the fixed K and on the cap theorem C; K cannot be allowed to grow with the input and still be called a universal constant.

### Corollary 6.3 — two-port assemblies are lossless

If every `k_i=1`, then the quotient is a connected 2-regular multigraph, all local root traffic consists of one path, sewing gives one cross-cycle and no collisions, and

```
c(G)   = sum_i c(H_i)-p+1,
c_f(G) = sum_i c_f(H_i)-p+1.                                      (6.7)
```

**Proof.** Sewing arbitrary local partitions gives the integral upper bound. A crossing cycle must use the entire quotient cycle; in any global partition there is exactly one such cycle. Restricting and capping it increases the count by p-1, proving the converse.

Fractionally, the total crossing-cycle mass is one. Restriction gives the fractional lower bound. Conversely each cap has root-cycle mass one; couple these finitely supported probability distributions (for example by their product). One path from each disjoint region, joined along the quotient cycle, is a simple cycle. The coupling preserves every edge load and decreases the cap objective by p-1. This proves the upper bound and (6.7). □

Thus the general certificate agrees with the established exact two-edge-splice rule rather than charging a fresh linear loss there.

---

## 7. Sharp four-port obstruction: pairing alone does not pay for simplicity

Fix `h>=1`. Use shared vertices `s_1,...,s_h`, private `u_j,v_j` for `1<=j<h`, and six further vertices `a,b,c,d,x,y`. Let

```
P = (a,s_1,u_1,s_2,...,u_{h-1},s_h,b),
Q = (c,s_1,v_1,s_2,...,v_{h-1},s_h,d).
```

Take all edges of these two paths, and add

```
ax, cx, by, dy.                                                   (7.1)
```

Let V_1 contain the vertices of P and Q and let `V_2={x,y}`. This is a connected simple even graph with a fixed four-edge interface and

```
n=3h+4,      m=4h+4.
```

### Proposition 7.1 — exact values and sharp collision count

The two simple caps satisfy

```
c(H_1)=c_f(H_1)=2,
c(H_2)=c_f(H_2)=2,
```

but the original graph satisfies

```
c(G)=c_f(G)=h+1.                                                  (7.2)
```

There are minimum cap partitions whose sewing has

```
q=0,     z=1,     D=h.                                           (7.3)
```

Thus the sewing bound `q+z+D` is sharp.

**Proof.** The original graph is a chain of h+1 four-cycle blocks:

```
(s_1,a,x,c),
(s_j,u_j,s_{j+1},v_j)           [1<=j<h],
(s_h,b,y,d).
```

Successive blocks meet only at their displayed articulation vertex. A simple cycle cannot use edges on both sides of an articulation: it would have to visit that articulation twice. Hence these blocks are all the simple cycles. They partition the edges and each is forced. Uniform edge weights 1/4 give a feasible signed dual (in fact nonnegative) of value h+1. This proves (7.2).

The first cap adds a root adjacent to a,b,c,d. The two paths P and Q each close through the root, giving a two-cycle partition. Viewed on its junction vertices, this cap is a cyclic chain of h+1 links, each consisting of two internally disjoint length-two paths. A simple cycle either pairs two paths of one link or uses one path from each link. Its maximum length is `2h+2` (also for h=1). There are `4h+4` edges, so uniform weights `1/(2h+2)` prove the fractional lower bound two.

The second economical simple cap is two triangles sharing their root: each of x,y has two arms, one direct and one subdivided. Its two triangles prove both values two.

Deleting the root cycles leaves P,Q in the first region and the trivial paths x,y in the second. Their endpoint pairings are `{a,b},{c,d}` and `{a,c},{b,d}` respectively. Sewing creates one abstract circuit. It visits each s_j twice and every other original vertex once, so `D=h`. This proves (7.3). □

In particular, no bound

```
c(G) <= c(H_1)+c(H_2)+O(number of boundary ports)
```

can hold for arbitrary cap partitions/graphs, even with exactly four ports. The same proposed bound for c_f is false. The unlabelled path-conflict graph in the first region is always just `K_2`, independently of h: to quantify repair cost, the shared original vertices must also be counted.

This is **not** an additive-rounding counterexample: its rounding gap is zero. Here `sum f_i=0` and `Gamma=h+1`, so the refined gap ledger is `0+1+h-(h+1)=0`. The example separates local cap values, fractional compatibility, and simple-cycle sewing cost.

---

## 8. One wrong transition can cost linearly many cycles

### Proposition 8.1 — unbounded sensitivity at one degree-four vertex

Let `k>=1`. Take junctions `w_0,...,w_k`; put two private length-two paths between every successive pair, and two private length-two return paths from `w_0` to `w_k`. Denote the resulting simple Eulerian series-parallel graph by T_k. Then

```
|V(T_k)|=3k+3,       c(T_k)=c_f(T_k)=2.                            (8.1)
```

At w_0 impose the perfect matching of its four incident edges that pairs the two forward edges together and the two return edges together. Among partitions respecting this one prescribed transition matching, both integer and fractional optimum become

```
c^tau(T_k)=c_f^tau(T_k)=k+1.                                     (8.2)
```

**Proof.** Two cycles, each choosing one branch in every forward segment and a different return, partition T_k. Its simple cycles are forward local four-cycles, the return four-cycle, and long cycles of length `2(k+1)`: a cycle using the chain across more than one segment must return via a return path. Thus all cycle lengths are at most `2(k+1)`. There are `4(k+1)` edges, so uniform weights `1/[2(k+1)]` prove (8.1).

Under the specified matching a long cycle is forbidden, since at w_0 it uses one forward edge and one return edge. The only permitted cycles are the k forward four-cycles and the return four-cycle. They are edge-disjoint and cover all edges, forcing coefficient one on each in either the integer or fractional exact-cover problem. This proves (8.2).

Equivalently split w_0 into two degree-two copies, one incident with the forward pair and the other with the return pair. The resulting graph is a chain of k+1 four-cycle blocks. □

The local choice is a completely valid perfect matching and satisfies all local blossom inequalities. For `k>=2`, its extra cost is `k-1`. Therefore an arbitrary single degree-four detachment does not preserve c_f up to O(1), and there is no O(1) simple-cycle repair bound per changed local transition. This does not preclude a global O(n) ledger: the affected original vertices can collectively pay the loss. It precludes charging that loss only to the one vertex where the matching was changed.

---

## 9. The Petersen rings in the new objective

Use the notation and proved certificates of `ResearchRounding.md`, Sections 5–6. Partition the ring R_t into its t punctured line-graph blocks `H=L(P)-0`. Each has 14 vertices and four distinct boundary ports; its economical simple cap is exactly L(P). Consequently

```
k_i=2, s_i=0,
c(cap_i)=3, c_f(cap_i)=2, Delta_i=1, f_i=0.
```

Take the documented cap partition consisting of H00, its 12-cycle complement B, and the triangle. Deleting the root retains P00 and Q and keeps one internal triangle per region. On sewing around the ring:

```
q=t,        z=2,        D=0,        Gamma=c_f(R_t)=2.
```

Thus the exact gap objective is

```
sum_i Delta_i + z + D - Gamma = t+2-2=t,
```

matching the independently proved global minimum `c(R_t)=t+2`. The necessary gap here is local cap slack, not repeated-vertex repair. Local blossom feasibility does not remove it.

The anchored cap dual of Theorem 4.1 only has value one here. The known uniform whole-graph dual has value two. Accordingly the exact Gamma ledger saves one over the anchored certificate; no claim that the anchored certificate is always optimal is intended.

---

## 10. What remains, including a disproved over-strong structural shortcut

### Proposition 10.1 — cheap boundary volume cannot be universal

Let n be odd and at least five, and take `G=K_n`. For **every** nontrivial flat vertex partition, the ledger of (6.1) satisfies

```
L >= (n+2)(n-3)/2.                                               (10.1)
```

Nevertheless `c(G)=c_f(G)=(n-1)/2`.

**Proof.** A proper region of size a has `b=a(n-a)>=n-1`, so `k_i-1 >= (n-3)/2`. Therefore

```
L >= (n+p)(n-3)/2 >= (n+2)(n-3)/2.
```

The standard Hamilton partition of an odd complete graph supplies `(n-1)/2` cycles; uniform weights 1/n certify the same fractional value. These certificates are also used in the existing rounding checker. □

For singleton regions, every cap is series-parallel and exactly roundable. The crude ledger is `L=n(n-3)`, but the cap partitions induced by the Hamilton partition have

```
q=0,   z=(n-1)/2,   D=0,   Gamma=(n-1)/2,
```

so the **exact** objective (5.4) is zero. This shows precisely what is lost by replacing actual visits with `n_i(k_i-1)` and replacing Gamma with one.

Indeed, singleton caps are exactly roundable for *every* even simple graph: each has one original vertex, an even number of arms, and no real internal edges. Pairing arms gives `c=c_f=d_G(v)/2`. Thus local cap exactness alone cannot settle the conjecture. For singleton regions, (5.3) reduces the problem to choosing vertex transition matchings with a globally cheap `z+D`; it does not supply those matchings.

### Exact remaining burden

Equation (5.4) is a rigorous unrestricted reduction. A successful extension would have to select cap partitions and globally compatible routes, or an equivalent full separator configuration system, so that a **single** quantity

```
sum_i [|D_i|-c_f(H_i)] + (z-Gamma) + D <= C r(G)                 (10.2)
```

has an absolute constant C. The three terms cannot be bounded or rounded independently merely from their local marginals. The minimum over all cap partitions equals the original rounding gap, so (10.2) is not asserted as a newly proved existence theorem.

The proved sufficient bound `sum Delta_i+L` settles bounded-interface assemblies, but (10.1) rules out making L universally linear by a nontrivial flat partition alone. Large-interface/high-connectivity atoms require a genuinely stronger state-selection or cancellation theorem. A recursive decomposition does not fix this automatically: final regions can inherit many boundary incidences, and charging (6.4) afresh at each ancestor would pay for the same vertex repeatedly. One must use the final global incidences (2.3), or prove another genuinely amortized invariant.

The obstructions have distinct roles:

* Lemma 1.1 and the three-vertex example forbid forgetting used boundary vertices or connectivity.
* Section 7 forbids charging arbitrary sewing repairs only to the number of ports.
* Section 8 forbids an O(1) repair promise for each locally valid matching change.
* Petersen rings require real local rounding slack even when the final routing is already simple.
* Odd complete graphs require avoiding the worst-case boundary-volume estimate, even with exactly roundable caps and zero actual gap.

No TU, half-integrality, support-only partition, nonnegative dual, or general binary-matroid assertion has been assumed. The complete-graph and Petersen checks do not constitute evidence for an unproved uniform bound on (10.2). **The general Erdős–Gallai theorem and its universal additive-rank rounding form remain unresolved by this work.**

---

## 11. Verification and protected files

The proofs above are independent of numerical optimization. A targeted checker was run with deterministic random seed 18403, using the installed NetworkX, NumPy and SciPy packages. Numerical LP/IP solutions were used only to propose witnesses: all LP edge loads, all enumerated simple-cycle dual inequalities, and matching primal/dual objectives were checked with exact `Fraction` arithmetic. Integral partitions were checked edge by edge; their optimality was certified by the ceiling of the exact fractional bound, with an independent finite exact-cover search available if needed.

The verification covers:

* general separator states at interface sizes through six, testing their converse as well as necessity;
* every connected nonempty even graph in the NetworkX atlas through order seven, with all unordered bipartitions and additional multiway partitions;
* economical simple caps, fixed root traffic, exact cap rank formulas, reconstruction, the collision identities, the global signed dual against **all** enumerated original cycles, and lifting global minimum partitions to attain (5.3);
* arbitrary vertex transition systems, independently of the cap implementation;
* the sharp four-port family and the one-bad-transition family through parameter 100;
* Petersen rings through t=40, i.e. 560 vertices, with the exact ledger `q=t,z=2,D=0,Gamma=2` and the four-Hamilton fractional edge cover;
* singleton-interface Hamilton partitions through K_51, and all integer region-size partitions of odd complete graph orders 5 through 21.

The exact numerical report follows. These are finite checks of the stated identities, not extrapolations to unrestricted rounding.

```json
{
  "Petersen_ring_ledger_checks": 8,
  "all_cycle_inequalities_checked": 51371,
  "arbitrary_transition_system_checks": 1530,
  "atlas_capped_assemblies": 3214,
  "atlas_connected_even_graphs": 51,
  "certified_LP_IP_instances": 1371,
  "complete_graph_boundary_volume_tests": 1955,
  "configuration_pair_checks": 130409,
  "exact_variational_identity_lifts": 3221,
  "global_dual_cycle_inequalities_checked": 256538,
  "global_duals_with_negative_edges": 2481,
  "global_signed_cap_duals_checked": 3214,
  "large_port_complete_graph_checks": 7,
  "one_bad_transition_examples": 15,
  "preexisting_files_unchanged": 16,
  "sharp_four_port_examples": 15,
  "third_boundary_vertex_flag_test": 1
}
```

The protected specification hash is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

A separate before/after SHA-256 manifest comparison checked all 16 pre-existing Submission files. Only this new Markdown file is added. In particular `Spec.lean`, `ResearchRounding.md`, and `ResearchFractional.md` are unchanged. The temporary checker and JSON report were written under `/tmp`, not over an existing Submission file.

### Reproduction

The complete checker source is embedded below so that the checks persist with this note. From the project root, extract and run it without creating Python bytecode in Submission:

```sh
python3 - <<'PY'
from pathlib import Path
text = Path('Submission/ResearchInterfaces.md').read_text()
start = text.index('```python\n', text.index('\n<!-- INTERFACES_CHECKER_BEGIN -->\n')) + len('```python\n')
end = text.index('\n```', start)
Path('/tmp/ResearchInterfacesCheck.py').write_text(text[start:end] + '\n')
PY
OPENBLAS_NUM_THREADS=1 PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1 \
  python3 /tmp/ResearchInterfacesCheck.py
```

The checker imports read-only helper functions from the existing `ResearchRoundingCheck.py`. It snapshots pre-existing Submission files at startup, excludes this new note, and checks their hashes at the end. It also checks the specification against the fixed hash above. Its detailed report is `/tmp/ResearchInterfacesCheck.json`.

<!-- INTERFACES_CHECKER_BEGIN -->

```python
#!/usr/bin/env python3
"""Reproducible checks for ResearchInterfaces.md; no Submission file is edited."""
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, '/workspace/leanproject/Submission')
import ResearchRoundingCheck as old
import networkx as nx
import numpy as np
from scipy.optimize import linprog, milp, Bounds, LinearConstraint
from fractions import Fraction as F
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path
import random, json, hashlib

rng = random.Random(18403)
report = Counter()
BASELINE = {p.name:hashlib.sha256(p.read_bytes()).hexdigest()
            for p in Path('/workspace/leanproject/Submission').iterdir()
            if p.is_file() and p.name != 'ResearchInterfaces.md'}
E = old.edge
CE = old.cycle_edges
PE = old.path_edges
GE = old.graph_edges


def greedy(G):
    H = G.copy()
    D = []
    while H.number_of_edges():
        Z = nx.find_cycle(H)
        C = tuple(u for u, v in Z)
        CE(C)
        D.append(C)
        H.remove_edges_from(Z)
    old.assert_partition(G, D)
    return D


@lru_cache(None)
def certified(n, es):
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(es)
    if not es:
        return F(0), (), ()
    cycles = list(old.all_cycles(G))
    A, edges = old.incidence(G, cycles)
    lp = linprog(np.ones(len(cycles)), A_eq=A, b_eq=np.ones(len(edges)),
                 bounds=(0,None), method='highs')
    assert lp.success
    x = [F(float(v)).limit_denominator(10**6) for v in lp.x]
    y = {e:F(float(v)).limit_denominator(10**6) for e,v in zip(edges,lp.eqlin.marginals)}
    loads = {e:F() for e in edges}
    for C,t in zip(cycles,x):
        assert t >= 0
        if t:
            for e in CE(C): loads[e] += t
    assert all(t == 1 for t in loads.values())
    val = sum(x,F())
    old.assert_dual(G,cycles,y,val)
    ip = milp(np.ones(len(cycles)), integrality=np.ones(len(cycles)),
              bounds=Bounds(0,1), constraints=LinearConstraint(A,1,1))
    assert ip.success
    part = tuple(C for C,t in zip(cycles,ip.x) if t > .5)
    old.assert_partition(G,part)
    lower = (val.numerator+val.denominator-1)//val.denominator
    if len(part) != lower:
        # Independent exact finite search rules out all smaller partitions.
        ix = {e:i for i,e in enumerate(edges)}
        masks = [sum(1<<ix[e] for e in CE(C)) for C in cycles]
        containing = [[m for m in masks if m>>i&1] for i in range(len(edges))]
        @lru_cache(None)
        def cover(mask,budget):
            if not mask: return True
            if budget <= 0: return False
            candidates = min(([m for m in containing[i] if m&mask == m]
                              for i in range(len(edges)) if mask>>i&1), key=len)
            return any(cover(mask^m,budget-1) for m in candidates)
        assert not cover((1<<len(edges))-1,len(part)-1)
        report['exact_nontrivial_IP_lower_searches'] += 1
    report['certified_LP_IP_instances'] += 1
    report['all_cycle_inequalities_checked'] += len(cycles)
    return val, part, tuple(y[e] for e in edges)


def solve(G):
    vs = sorted(G); mp = {v:i for i,v in enumerate(vs)}
    J = nx.relabel_nodes(G,mp)
    val,D,_ = certified(len(J),tuple(sorted(GE(J))))
    return val,[tuple(vs[i] for i in C) for C in D]


def dual(G):
    vs=sorted(G); mp={v:i for i,v in enumerate(vs)}
    J=nx.relabel_nodes(G,mp); es=tuple(sorted(GE(J)))
    _,_,ys=certified(len(J),es)
    return {E(vs[a],vs[b]):y for (a,b),y in zip(es,ys)}


def make_caps(G, parts):
    owner = {v:i for i,S in enumerate(parts) for v in S}
    assert set(owner) == set(G)
    cuts = [e for e in sorted(GE(G)) if owner[e[0]] != owner[e[1]]]
    caps=[]
    root=max(G)+1
    for i,S in enumerate(parts):
        H=G.subgraph(S).copy(); H.add_node(root)
        arm={}; first=set(); nxt=root+1
        for j,(u,v) in enumerate(cuts):
            if owner[u] == i: w=u
            elif owner[v] == i: w=v
            else: continue
            if w not in first:
                first.add(w); H.add_edge(root,w); arm[w]=j
            else:
                H.add_edges_from([(root,nxt),(nxt,w)]); arm[nxt]=j; nxt+=1
        b=len(arm)
        assert b>0 and b%2==0 and nx.is_connected(H)
        assert all(d%2==0 for _,d in H.degree())
        assert len(H)-1 == len(S)+b-len(first)
        caps.append((H,root,arm))
    return cuts,caps


def sew(G,parts,cuts,caps,partitions,cf=None,cap_cf=None):
    paths=[]; internal=[]; port={}
    for i,((H,root,arm),D) in enumerate(zip(caps,partitions)):
        old.assert_partition(H,D)
        count=0
        for C in D:
            if root not in C:
                assert set(C) <= parts[i]
                internal.append(C); continue
            count+=1
            j=C.index(root)
            ends=(C[(j-1)%len(C)],C[(j+1)%len(C)])
            labels=[arm[u] for u in ends]
            realvs=set(C)&parts[i]
            reales=CE(C)&GE(G.subgraph(parts[i]))
            assert len(reales) == len(realvs)-1
            A=nx.Graph(); A.add_nodes_from(realvs); A.add_edges_from(reales)
            assert nx.is_connected(A) and max(dict(A.degree()).values())<=2
            pid=len(paths); paths.append((i,realvs,reales))
            for label in labels: port[(i,label)]=pid
        assert count == len(arm)//2
    owner={v:i for i,S in enumerate(parts) for v in S}
    A=nx.MultiGraph(); A.add_nodes_from(range(len(paths)))
    for j,(u,v) in enumerate(cuts):
        A.add_edge(port[(owner[u],j)],port[(owner[v],j)],label=j)
    assert all(d==2 for _,d in A.degree())
    components=list(nx.connected_components(A))
    k=Counter(v for _,vs,_ in paths for v in vs); visits=Counter()
    delta=0; answer=list(internal)
    for Q in components:
        R=nx.Graph()
        occurrence=Counter(v for pid in Q for v in paths[pid][1])
        for pid in Q:
            R.add_nodes_from(paths[pid][1]); R.add_edges_from(paths[pid][2])
        for _,_,data in A.subgraph(Q).edges(data=True):
            R.add_edge(*cuts[data['label']])
        assert nx.is_connected(R) and all(d%2==0 for _,d in R.degree())
        assert all(d//2==occurrence[v] for v,d in R.degree())
        d=sum(t-1 for t in occurrence.values())
        assert R.number_of_edges()-len(R)+1 == 1+d
        visits.update(list(R.nodes())); delta+=d
        D=greedy(R); assert len(D)<=1+d; answer+=D
    assert delta == sum(k[v]-visits[v] for v in k)
    old.assert_partition(G,answer)
    z=len(components); p=len(parts); cutn=len(cuts)
    assert z <= cutn//2 and z<=cutn-p+1
    L=sum((len(S)+1)*(len(cap[2])//2-1) for S,cap in zip(parts,caps))
    assert delta<=sum(len(S)*(len(cap[2])//2-1) for S,cap in zip(parts,caps))
    assert len(answer)<=len(internal)+z+delta
    if cf is not None:
        f=sum(cap_cf,F())-cutn
        Gamma=cf-f
        gap=sum(F(len(D))-v for D,v in zip(partitions,cap_cf))
        assert Gamma>=1
        assert len(internal)==f+gap
        assert F(len(answer))-cf <= gap+z+delta-Gamma <=gap+L
    return len(internal),z,delta,len(answer)



def arms_by_label(G,parts,caps):
    result=[]
    for S,(H,root,arm) in zip(parts,caps):
        result.append({j:((root,v) if v in S else
                          (root,v,next(w for w in H[v] if w!=root)))
                       for v,j in arm.items()})
    return result


def glue_dual(G,parts,cuts,caps,values):
    ys=[dual(H) for H,_,_ in caps]; arms=arms_by_label(G,parts,caps)
    owner={v:i for i,S in enumerate(parts) for v in S}
    y={e:ys[i][e] for i,S in enumerate(parts) for e in GE(G.subgraph(S))}
    for j,(u,v) in enumerate(cuts):
        a,b=owner[u],owner[v]
        y[E(u,v)]=(sum((ys[a][e] for e in PE(arms[a][j])),F())+
                   sum((ys[b][e] for e in PE(arms[b][j])),F())-1+(j==0))
    cycles=list(old.all_cycles(G))
    old.assert_dual(G,cycles,y,sum(values,F())-len(cuts)+1)
    report['global_signed_cap_duals_checked']+=1
    report['global_dual_cycle_inequalities_checked']+=len(cycles)
    if any(t<0 for t in y.values()): report['global_duals_with_negative_edges']+=1


def lift_partition(G,parts,cuts,caps,D):
    owner={v:i for i,S in enumerate(parts) for v in S}
    fid={e:j for j,e in enumerate(cuts)}; arms=arms_by_label(G,parts,caps)
    out=[[] for _ in parts]
    for C in D:
        if not (CE(C)&set(cuts)):
            out[owner[C[0]]].append(C); continue
        for j,v in enumerate(C):
            i=owner[v]
            if owner[C[j-1]]==i: continue
            P=[v]; h=(j+1)%len(C)
            while owner[C[h]]==i:
                P.append(C[h]); h=(h+1)%len(C)
            a=arms[i][fid[E(C[j-1],v)]]
            b=arms[i][fid[E(P[-1],C[h])]]
            out[i].append(tuple(a)+tuple(P[1:])+tuple(reversed(b))[1:-1])
    for (H,_,_),Di in zip(caps,out): old.assert_partition(H,Di)
    q,z,delta,total=sew(G,parts,cuts,caps,out)
    assert delta==0 and q+z==total==len(D)
    report['exact_variational_identity_lifts']+=1
    return out

def check_atlas_caps():
    graphs=[G for G in nx.graph_atlas_g() if len(G)>1 and nx.is_connected(G)
            and all(d%2==0 for _,d in G.degree())]
    for G in graphs:
        cf,globalD=solve(G); V=set(G); n=len(G)
        # All unordered two-way partitions.
        partitions=[]
        for mask in range(1,1<<(n-1)):
            S={i+1 for i in range(n-1) if mask>>i&1}
            partitions.append([S,V-S])
        # Additional genuinely multiway interfaces, deterministic.
        for _ in range(12):
            colors=[rng.randrange(min(4,n)) for _ in G]
            parts=[{v for v,c in zip(G,colors) if c==j} for j in sorted(set(colors))]
            if len(parts)>2: partitions.append(parts)
        for parts in partitions:
            cuts,caps=make_caps(G,parts)
            solved=[solve(H) for H,_,_ in caps]
            sew(G,parts,cuts,caps,[D for _,D in solved],cf,[v for v,_ in solved])
            glue_dual(G,parts,cuts,caps,[v for v,_ in solved])
            lift_partition(G,parts,cuts,caps,globalD)
            report['atlas_capped_assemblies']+=1
    report['atlas_connected_even_graphs']=len(graphs)


def check_configurations():
    for n,trials in [(4,12),(5,20),(6,12)]:
        G=nx.complete_graph(n); edges=sorted(GE(G))
        for _ in range(trials):
            rng.shuffle(edges); m=len(edges)//2
            left,right=edges[:m],edges[m:]
            S=set(sum((list(e) for e in left),[]))&set(sum((list(e) for e in right),[]))
            def states(es):
                out=[]
                for mask in range(1,1<<len(es)):
                    sub=[e for j,e in enumerate(es) if mask>>j&1]
                    # Degree queried below only on present nodes.
                    H=nx.Graph(); H.add_nodes_from(S); H.add_edges_from(sub)
                    if any(d>2 for _,d in H.degree()): continue
                    nonzero=H.subgraph([v for v,d in H.degree() if d])
                    if not nx.is_forest(nonzero): continue
                    T={v for v,d in H.degree() if d==1}
                    if not T<=S: continue
                    M=[]
                    for Q in nx.connected_components(nonzero):
                        ends=tuple(sorted(v for v in Q if H.degree(v)==1))
                        if len(ends)!=2: break
                        M.append(ends)
                    else:
                        U={v for v in S if H.degree(v)==2}
                        out.append((sub,T,M,U))
                return out
            for a,b in product(states(left),states(right)):
                X=nx.Graph(); X.add_edges_from(a[0]+b[0])
                iscycle=nx.is_connected(X) and all(d==2 for _,d in X.degree())
                M=nx.MultiGraph(); M.add_edges_from(a[2]+b[2])
                compatible=(a[1]==b[1] and bool(a[1]) and not(a[3]&b[3])
                            and nx.is_connected(M))
                assert compatible==iscycle
                report['configuration_pair_checks']+=1


def cactus_four_port(r):
    ids=iter(range(10*r+30))
    s=[next(ids) for _ in range(r)]
    a,b,c,d,x,y=[next(ids) for _ in range(6)]
    A1=[a,s[0]]; A2=[c,s[0]]; G=nx.Graph()
    for j in range(r-1):
        u,v=next(ids),next(ids)
        A1.extend([u,s[j+1]]); A2.extend([v,s[j+1]])
    A1.append(b); A2.append(d)
    G.add_edges_from(PE(A1)|PE(A2)); G.add_edges_from([(a,x),(c,x),(b,y),(d,y)])
    parts=[set(G)-{x,y},{x,y}]
    cuts,caps=make_caps(G,parts)
    root=caps[0][1]
    D0=[tuple([root]+A1),tuple([root]+A2)]
    D1=greedy(caps[1][0])
    q,z,delta,total=sew(G,parts,cuts,caps,[D0,D1],F(r+1),[F(2),F(2)])
    assert (q,z,delta,total)==(0,1,r,r+1)
    assert len(G)==3*r+4 and G.number_of_edges()==4*r+4
    blocks=list(nx.biconnected_components(G))
    assert len(blocks)==r+1 and all(len(B)==4 for B in blocks)
    if r<=7:
        cycles=list(old.all_cycles(G)); assert len(cycles)==r+1
        old.assert_dual(G,cycles,{e:F(1,4) for e in GE(G)},F(r+1))
        capcycles=list(old.all_cycles(caps[0][0]))
        old.assert_dual(caps[0][0],capcycles,
                       {e:F(1,2*r+2) for e in GE(caps[0][0])},F(2))
    report['sharp_four_port_examples']+=1


def theta_bad_transition(k):
    G=nx.Graph(); nxt=k+1; mids=[]
    for j in range(k):
        row=[]
        for _ in range(2):
            w=nxt; nxt+=1; row.append(w); G.add_edges_from([(j,w),(w,j+1)])
        mids.append(row)
    ret=[nxt,nxt+1]
    for w in ret: G.add_edges_from([(0,w),(w,k)])
    D=[]
    for branch in range(2):
        path=[0]
        for j in range(k): path.extend([mids[j][branch],j+1])
        D.append(tuple(path+[ret[branch]]))
    old.assert_partition(G,D)
    H=G.copy(); detached=nxt+2
    for w in ret: H.remove_edge(0,w); H.add_edge(detached,w)
    blocks=list(nx.biconnected_components(H))
    assert len(blocks)==k+1 and all(len(B)==4 for B in blocks)
    if k<=7:
        C=list(old.all_cycles(G))
        old.assert_dual(G,C,{e:F(1,2*(k+1)) for e in GE(G)},F(2))
        constrained=[]
        for cycle in C:
            if 0 in cycle:
                j=cycle.index(0); transition={cycle[j-1],cycle[(j+1)%len(cycle)]}
                if transition!=set(mids[0]) and transition!=set(ret): continue
            constrained.append(cycle)
        assert len(constrained)==k+1 and all(len(C)==4 for C in constrained)
    report['one_bad_transition_examples']+=1


def check_petersen():
    _,L=old.petersen_line(); H=L.copy(); H.remove_node(0)
    for t in [2,3,4,5,8,12,20,40]:
        G0,D0,F0,_=old.petersen_ring(t,H)
        label={(i,v):14*i+v-1 for i,v in G0}
        G=nx.relabel_nodes(G0,label)
        parts=[{14*i+v-1 for v in H} for i in range(t)]
        cuts,caps=make_caps(G,parts)
        Ds=[]
        for i,(_,root,_) in enumerate(caps):
            mp={v:(root if v==0 else 14*i+v-1) for v in L}
            Ds.append([tuple(mp[v] for v in C) for C in
                       [old.PETERSEN_HAMILTONS[0],old.PETERSEN_COMPLEMENT,old.PETERSEN_TRIANGLE]])
        q,z,delta,total=sew(G,parts,cuts,caps,Ds,F(2),[F(2)]*t)
        assert (q,z,delta,total)==(t,2,0,t+2)
        # Recheck the supplied four-Hamilton fractional certificate exactly.
        load=Counter(e for C in F0 for e in CE(tuple(label[v] for v in C)))
        assert load==Counter({e:2 for e in GE(G)})
        assert all(len(C)==len(G) for C in F0)
        report['Petersen_ring_ledger_checks']+=1


def check_arbitrary_transitions():
    graphs=[G for G in nx.graph_atlas_g() if len(G)>1 and nx.is_connected(G)
            and all(d%2==0 for _,d in G.degree())]
    for G in graphs:
        edges=sorted(GE(G)); eid={e:j for j,e in enumerate(edges)}
        for _ in range(30):
            A=nx.MultiGraph(); A.add_nodes_from(range(len(edges)))
            for v in G:
                incident=[eid[E(v,u)] for u in G[v]]; rng.shuffle(incident)
                A.add_edges_from(zip(incident[::2],incident[1::2]))
            assert all(d==2 for _,d in A.degree())
            delta=0; D=[]; comps=list(nx.connected_components(A))
            for Q in comps:
                R=nx.Graph(); R.add_edges_from(edges[j] for j in Q)
                assert nx.is_connected(R) and all(d%2==0 for _,d in R.degree())
                excess=sum(d//2-1 for _,d in R.degree())
                part=greedy(R); assert len(part)<=1+excess
                delta+=excess; D+=part
            old.assert_partition(G,D)
            assert len(D)<=len(comps)+delta
            report['arbitrary_transition_system_checks']+=1



def check_large_interfaces():
    for r in [1,2,3,4,5,10,25]:
        G=nx.complete_graph(2*r+1); parts=[{v} for v in G]
        cuts,caps=make_caps(G,parts); D=old.walecki(r)
        out=lift_partition(G,parts,cuts,caps,D)
        assert sew(G,parts,cuts,caps,out,F(r),[F(r)]*len(G))==(0,r,0,r)
        L=sum((len(S)+1)*(len(cap[2])//2-1) for S,cap in zip(parts,caps))
        assert L==len(G)*(len(G)-3)
        report['large_port_complete_graph_checks']+=1
    def integer_partitions(n,lo=1):
        if not n: yield ()
        for a in range(lo,n+1):
            for P in integer_partitions(n-a,a): yield (a,)+P
    for n in range(5,22,2):
        for sizes in integer_partitions(n):
            if len(sizes)<2: continue
            L=sum((a+1)*(a*(n-a)//2-1) for a in sizes)
            assert L>=(n+2)*(n-3)//2
            report['complete_graph_boundary_volume_tests']+=1
    G=nx.Graph(); G.add_edges_from(PE((0,2,1))|PE((0,3,2,4,1)))
    assert len(greedy(G))==2 and G.degree(2)==4
    report['third_boundary_vertex_flag_test']=1

def check_hashes():
    manifest=BASELINE
    for name,digest in manifest.items():
        p=Path('/workspace/leanproject/Submission')/name
        assert hashlib.sha256(p.read_bytes()).hexdigest()==digest
    assert manifest['Spec.lean']==old.SPEC_SHA256
    report['preexisting_files_unchanged']=len(manifest)


if __name__=='__main__':
    check_configurations()
    check_atlas_caps()
    for r in list(range(1,13))+[20,50,100]: cactus_four_port(r)
    for k in list(range(1,13))+[20,50,100]: theta_bad_transition(k)
    check_petersen()
    check_arbitrary_transitions()
    check_large_interfaces()
    check_hashes()
    result=dict(sorted(report.items()))
    Path('/tmp/ResearchInterfacesCheck.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
```

<!-- INTERFACES_CHECKER_END -->
