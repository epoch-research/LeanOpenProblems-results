# Exact-leading-constant progress; the rationality question remains unresolved

`Submission/Spec.lean` has not been changed or imported. Neither its asserted
statement nor its placeholder disproof is used. The results below are partial
structural consequences, not a proof of rationality and not a counterexample.

## 1. Main new result in this workspace: proper-quotient packing

Write `f(n) = ex(n,H)` and `h = e(H) > 0`. Fix an integer `k >= 2`.
A **proper k-bounded quotient** of H is obtained by partitioning V(H) into
independent blocks, each of size at most k, with strictly fewer than |V(H)|
blocks. There is an edge between two blocks precisely when H has an edge
between them. Multiple edges are suppressed. Denote the finite family of
these ordinary simple graphs by Q_k(H). Members of this family need not be
bipartite, even if H is bipartite.

### Finite theorem

For every ordinary H-free graph G on n vertices there is an edge-disjoint
collection of r ordinary copies of members of Q_k(H) such that

    k^2 e(G) <= f(kn) + k^2 h r.

Consequently

    r >= (e(G) - f(kn)/k^2)/h.

More precisely, if D is the union of the edge sets of the copies, then

    |D| <= h r,
    k^2 (e(G) - |D|) <= f(kn).

Vertex-disjointness is not claimed or needed.

### Complete proof

Take a maximal edge-disjoint collection of copies of graphs in Q_k(H).
This is a finite choice: the host and the family are finite, and every
member of Q_k(H) has at least one edge, since h > 0 and blocks are independent.
Let D be the union of its edge sets, and put F = G - D.

Let B_k(F) be the independent k-fold blowup: its vertex set is
V(F) x {1,...,k}, and (u,i) is adjacent to (v,j) exactly when uv is an edge
of F. Thus B_k(F) has kn vertices and exactly k^2 e(F) edges.

Suppose there is an ordinary injective copy psi: H -> B_k(F). Project psi
to V(F), obtaining an edge-preserving map phi: H -> F. Each fiber of phi
has size at most k, because psi is injective and there are only k clone
indices. Every fiber is independent, because F has no loops. If phi were
injective, it would give an ordinary H-copy in F, hence in G, contradicting
H-freeness of G. Therefore the fiber partition is proper. The resulting map
from the quotient by this partition into F is injective and edge-preserving.
Its image is a copy of a member of Q_k(H), and all its edges avoid D. This
contradicts maximality of the chosen collection.

It follows that B_k(F) is H-free. The definition of the ordinary extremal
number now gives k^2 e(F) <= f(kn). Since e(F) = e(G)-|D| and each quotient
has at most h edges, the asserted inequalities follow.

For completeness, every copy of a k-bounded quotient also lifts to an
ordinary H-copy in B_k(F): assign distinct clone indices to the vertices
within each partition block. Thus the forbidden projected patterns are
exactly the bounded-fiber quotient obstructions. No closure of H-freeness
under blowups is assumed.

### Exact-constant consequence

Suppose f(n) ~ c n^a, where c > 0 and a < 2, and choose any extremal G_n.
For fixed k,

    f(kn) = (c k^a + o(1)) n^a,
    e(G_n) = (c + o(1)) n^a.

The finite theorem therefore supplies an edge-disjoint proper-quotient
packing with

    r_n >= ((c/h)(1 - k^(a-2)) + o(1)) n^a.

The lower-bound convention is precise: for every

    b < (c/h)(1 - k^(a-2)),

all sufficiently large n and every extremal G_n admit such a packing with
r_n >= b n^a. Its union covers at least

    ((1 - k^(a-2)) + o(1)) e(G_n)

base edges. In particular, the coefficient is strictly positive already
for **k = 2**. This is where the exact leading constant is useful: unspecified
upper and lower Theta constants would not generally give a positive bound
at this fixed small blowup factor.

The same proof works for an H-free sequence with e(G_n) = f(n)-o(n^a).
It does not require that the hosts be bipartite. With k = 2, every quotient
has between ceil(|V(H)|/2) and |V(H)|-1 vertices.

### Lean implementation

`Submission/BlowupPacking.lean` formalizes this by packing projected edge
sets of actual ordinary copies of H in B_k(G). This avoids an additional
quotient-graph datatype while retaining all the mathematical content:

- `projectHom_not_injective`: H-freeness of G forces a proper projection.
- `projectHom_fiber_card_le`: every fiber has size at most k.
- `card_edges_blowup`: the edge count is exactly k^2 e(G).
- `exists_projected_packing`: pairwise disjoint projected edge sets, an
  H-free blowup after deleting their union, and both finite inequalities
  k^2 e(G) <= f(kn) + k^2 |D| <= f(kn) + k^2 e(H) r.
- `eventually_large_projected_packing`: every coefficient strictly below
  `(k^2-k^a)c/(k^2 e(H))` works for all sufficiently large n and every
  extremal host.
- `packing_coefficient_pos`: positivity for k >= 2, a < 2, and c > 0.

The formal packing consists of labelled H-copies in the blowup. The
nonempty, pairwise disjoint projected edge sets ensure these really give
an edge-disjoint collection of distinct ordinary quotient copies in the
base. The ordinary forbidden relation throughout is `SimpleGraph.Free`,
not induced freeness or homomorphism-freeness.

## 2. Companion result: asymptotically lossless induced cores

This consequence also uses the exact leading constant and was not in the
previous helpers. It concerns host graphs, not deletion of leaves from the
forbidden graph.

### Finite defect-controlled peeling theorem

Let p: N -> R be arbitrary. Starting with a finite graph G, delete a vertex
whenever the current m-vertex graph has a vertex of degree less than
p(m)-p(m-1). The process terminates at an induced subgraph K on m vertices.
Every deletion increases the potential

    e(current graph) - p(number of current vertices).

Indeed, a deletion of a vertex of degree d changes that potential by
p(m)-p(m-1)-d > 0. Hence

    min_degree(K) >= p(m)-p(m-1),
    e(K)-p(m) >= e(G)-p(n).

The degree condition is vacuous if K has no vertices. No monotonicity of p
is required.

Apply this to the potential (1-epsilon)p. Suppose G is H-free,

    e(G) >= p(n)-A,
    f(j) <= p(j)+B for every 0 <= j <= n.

The returned induced K remains ordinary H-free, so e(K) <= f(m) <= p(m)+B.
Combining upper and lower potential bounds gives exactly

    epsilon (p(n)-p(m)) <= A+B,
    e(G)-e(K) <= (1-epsilon)(p(n)-p(m)),
    min_degree(K) >= (1-epsilon)(p(m)-p(m-1)).

These are the formal theorems `exists_induced_degree_core` and
`exists_defect_controlled_core` in `Submission/ExactConstantCore.lean`.

### Complete asymptotic deduction

Assume a > 1, c > 0, and f(n) ~ c n^a. Let G_n be H-free with
s_n := f(n)-e(G_n) = o(n^a); extremal hosts are the special case s_n=0.
Define

    E_n := max_{0 <= j <= n} |f(j)-c j^a|.

Then E_n=o(n^a). To see this, given eta>0, choose M so that the error is
at most eta j^a for j>=M. The finitely many errors with j<M have a fixed
maximum C. Hence E_n <= max(C,eta n^a), and division by n^a proves the claim.
This uniform-error fact is also formalized as `eventually_uniform_power_error`.

For n>=1 set

    gamma_n := (2 E_n+s_n)/(c n^a),
    epsilon_n := sqrt(gamma_n+1/n).

Then epsilon_n>0 and epsilon_n->0, so epsilon_n<1 eventually. Apply the
finite theorem with p(j)=c j^a, A=E_n+s_n, B=E_n. It gives an induced K_n
on m_n vertices with

    n^a-m_n^a <= (gamma_n/epsilon_n)n^a <= epsilon_n n^a,
    e(G_n)-e(K_n) <= c epsilon_n n^a.

Here gamma_n/epsilon_n <= epsilon_n follows directly from the definition.
Since 0<=m_n/n<=1 and a>1, `(m_n/n)^a <= m_n/n`; therefore

    m_n >= (1-epsilon_n)n = n-o(n).

The edge loss is o(n^a), and the finite minimum-degree bound gives

    min_degree(K_n)
      >= (1-epsilon_n)c [m_n^a-(m_n-1)^a]
      >= (1-epsilon_n)c a (m_n-1)^(a-1).

The last inequality is the mean value theorem applied on [m_n-1,m_n],
using that x^(a-1) is increasing on the nonnegative reals. Since m_n/n->1,

    min_degree(K_n) >= (a-o(1)) c n^(a-1).

Thus almost all vertices and edges can be retained while imposing this
minimum degree. This does not assert an upper bound on the maximum degree
or full almost-regularity.

`eventually_near_spanning_core` is the formal fixed-error version: for all
fixed epsilon,rho in (0,1), all sufficiently large n, and every extremal
G on n vertices, it provides induced H-free K on m vertices with

    (1-rho)n <= m <= n,
    e(G)-e(K) <= rho c n^a,
    min_degree(K) >= (1-epsilon)c [m^a-(m-1)^a].

The diagonal choice and the mean-value-theorem formulation above are a
written mathematical deduction; the Lean theorem states the fixed-error
version explicitly.

## 3. Why these results do not complete the requested proof

Neither result supplies a polynomial residual or any equality forcing a
tie between finitely many integer monomial weights. Their displayed
numerical bounds do not distinguish rational from irrational a in (1,2);
this is not a claim that suitable graph sequences exist at every exponent.

In particular, a packing of many copies of a proper quotient Q does NOT
imply that ex(n,Q) has exponent a, or even a positive-constant power
asymptotic. Q need not be bipartite, and selecting one of finitely many
quotient types along a subsequence cannot transfer the assumed full
asymptotic to its own extremal number. Thus induction on the order of H
would have an unjustified missing step here.

No general argument establishing rationality has been found. The target
remains unchanged. The results above are rigorously proved partial progress,
not a claimed resolution of the forward rational-exponent conjecture.

## 4. Verification

The following commands compile the new Lean helpers:

    cd /workspace/leanproject
    lake env lean Submission/ExactConstantCore.lean
    lake env lean Submission/BlowupPacking.lean

The printed axiom audits for the main theorems contain only the standard
axioms `propext`, `Classical.choice`, and `Quot.sound` (the elementary
noninjectivity theorem uses no axioms). No `sorryAx` occurs.

The unchanged SHA-256 of `Submission/Spec.lean` is:

    539915b676ef3724fc90d170c6fa72d18c53a9289bbba9f6990a852d500c0c4d

Independent finite checks also passed (these supplement, not replace, the
proofs). A direct ordinary-injective-copy enumerator tested P3, C4, C6, and
K3,3. It checked 236 H-free hosts for exact blowup edge counts, proper
projection, equivalence with bounded-fiber homomorphisms, and residual
freeness; 44 packing inequalities against exhaustively computed extremal
numbers; and 131,670 potential/core instances, including irrational-power
and nonmonotone potentials. The enumerator explicitly rejects K4 as C4-free,
so it does not accidentally use induced exclusion. The script and log are
`/tmp/verify_exact_constant_progress.py` and
`/tmp/ExactConstantProgress.smallchecks.log`.

## 4. Verified degree-tail and minimum-repair tools

The conjecture remains unresolved. The following two additional modules do not
import or use either theorem in `Submission/Spec.lean`.

### Hereditary power bounds control degree tails

`Submission/DegreeTail.lean` proves a deterministic cut-averaging lemma and
uses it to show the following. Suppose every induced vertex set U of an
n-vertex graph G satisfies

    e(G[U]) <= C |U|^a,  C > 0,  1 < a < 2.

For S with |S| <= n/2,

    sum_{v in S} d_G(v) <= 8 C n |S|^(a-1).

Indeed, an equally sized set in the complement can capture at least the
proportional share of the cut edges. The hereditary bound on their union
controls that cut; internal edges are counted twice.

For L >= 4C and S_L = {v : d_G(v) > L n^(a-1)}, the file proves

    |S_L| <= n (8C/L)^(1/(2-a)),
    e_G(incident with S_L) <= 8C n^a (8C/L)^((a-1)/(2-a)).

It also proves exact edge accounting for the induced complement and the
remaining maximum-degree bound L n^(a-1). For every epsilon > 0 there is a
single cutoff L, uniform over n and all such G, whose incident-edge loss is
at most epsilon n^a. A positive lower bound for e(G)/n^a is required to
interpret this as a small fraction of the actual edges.

Together with the earlier potential-peeling argument, this justifies the
written near-lossless regularization discussed above. The combined
sequence-level theorem has not been formalized in this module. In
particular, a fixed maximum/minimum degree ratio at o(edge) loss is not
asserted.

### Global optimality equals a minimum-transversal condition

`Submission/RepairOptimality.lean` works with an H-free graph G, a graph R
edge-disjoint from G and itself H-free, and old-edge deletions D. Define

    tau_G(R) = min {|D| : D subset E(G), (G-D) union R is H-free}.

The minimum is over a nonempty finite family: deleting all of E(G) leaves
R. No assumption that the empty graph is H-free is made.

The file proves

    e(G) + e(R) <= ex(n,H) + tau_G(R),
    max_R (e(R) - tau_G(R)) = ex(n,H) - e(G).

The second equality uses integer subtraction. An actual extremal F attains
it with R = F minus G and D = E(G) minus E(F); that D is a minimum repair,
not just an upper bound on its cost.

For disjoint R, feasible D are exactly the subsets of E(G) meeting every
ordinary injective H-copy in G union R. Thus G is globally edge-extremal
if and only if every admissible R has minimum old-edge transversal at
least e(R). This is stronger than a Hall-neighborhood matching or
single-edge saturation, but it is also an exact reformulation of global
optimality. To derive a density increment one must independently construct
R and a feasible D with |D| < e(R). No universal construction doing this
at every irrational exponent has been proved.

### Independent verification

Both sources were read, freshly compiled with `autoImplicit=false`,
`relaxedAutoImplicit=false`, and `warningAsError=true`, and their imported
regression tests rerun. A parent audit checked all 128 declarations under
the two namespaces, including generated helpers: only `propext`,
`Classical.choice`, and `Quot.sound`, and no unsafe declarations.

Artifacts include:

- `/tmp/RepairTailParentAudit.lean` and `.log`;
- `/tmp/RepairOptimality.parent-{strict,audit,tests}.log`;
- `/tmp/DegreeTail.parent-{strict,audit,tests}.log`.

Neither file supplies the missing rational-exponent implication.

## 5. Combined fixed-error regularization is now formalized

`Submission/HostRegularization.lean` combines the previous two ingredients.
Assume `ex(n,H) ~ c n^a`, with `c > 0` and `1 < a < 2`. For every fixed
`epsilon in (0,1)` it proves the existence of `L > 0` and `N` such that
every exact H-free extremizer G on n >= N vertices has an induced H-free
core K on m vertices satisfying

    0 < m <= n,
    m >= (1-epsilon)n,
    e(G)-e(K) <= epsilon c n^a,
    min_degree(K) >= (1-epsilon)c [m^a-(m-1)^a],
    max_degree(K) <= L n^(a-1).

The same L,N work for every extremizer at every sufficiently large order.
All-sizes extremal and hereditary power bounds are derived from the given
asymptotic, including zero and the finitely many initial exceptions. The
proof never differentiates the extremal-number sequence. Its signed defect
parameter permits applying the peeling lemma directly to the trimmed host
while retaining the original n-scale for the error budget.

The parent independently read the full proof, rebuilt both dependencies and
the new module, checked its axiom/import audit, and reran the regression
which derives the minDegree/maxDegree version with real subtraction m-1.
All passed. Logs:

- `/tmp/HostRegularization.parent-{tail,core,strict,audit,tests}.log`.

The sequence-level diagonal choice with a subpolynomial varying cutoff is
still a written consequence, not a theorem exported by this file. Most
importantly, the rationality implication is still unproved.

## 6. A finite obstruction to fractional repair rounding

Here is an independently checked mathematical obstruction; this section is
not claimed as a Lean formalization or a disproof of the conjecture.

Let B be any C4-free graph with t vertices, m edges and matching number nu.
In its independent two-blowup W=B[2], choose one perfect matching in every
base-edge K2,2 block to form A, and let C be the complementary matchings.
Both A and C are C4-free. Every C4 of W has two A-edges and two C-edges.
The repair conflict graph on A-edges is the clique two-blowup of the line
graph of B: two old edges conflict exactly when their projected base edges
coincide or meet. Therefore

    tau_A(C) = 2m-nu,       fractional_tau_A(C) = m.

Choose a maximum matching M in B and add to A one C-edge above each member
of M, making S. Put G=A union S and R=C minus S. Then

    ex(W,C4) = 2m+nu,
    tau_G(R) = e(R) = 2m-nu,
    m-nu <= fractional_tau_G(R) <= m.

For the host upper bound, any block has at most three retained edges, and
the three-edge blocks must form a matching; the construction attains this.
The exact repair is attained by reversing the two complementary lifts and
adding one old A-edge over each edge of M. There are still no singleton-old
witnesses. If m/t tends to infinity, fractional repair nevertheless suggests
a positive leading-scale gain while every integral repair has zero gain.

For every fixed support size k, the old-edge retention vector z_e=1/k
satisfies all valid repair inequalities with support at most k: on any such
support it is a convex combination of the empty and singleton retentions,
each globally feasible. These local distributions are consistent. Yet true
repair can retain only 2nu=O(t) old edges. The missing constraints involve
growing rooted bundles (for the unaugmented pair, all old edges over a base
vertex's star form a conflict clique).

This invalidates a proposed bounded-local fractional-rounding shortcut.
It does not rule out full global/SOS aggregation, and optimality inside W
is not global optimality among all graphs on 2t vertices.

## 7. Fractional repair can have a leading-scale gap at global extrema

The previous restricted-host example is not the only obstruction. The
following mathematical argument was independently checked; it has not been
formalized in Lean and is not a proof of rationality.

Suppose H is connected with edge-connectivity lambda >= 2, and
`f(n)=ex(n,H) ~ c n^a`, `c>0`, `a<2`. Fix an integer k>=2. Every sufficiently
large exact global extremizer G, with m=f(n), admits a disjoint H-free
addition R such that

    e(R) = (k^(1-a)+o(1)) m,
    fractional_tau_G(R) <= [1/lambda+(1-1/lambda)/k+o(1)] m,
    tau_G(R) >= e(R).

Partition the vertices into k almost equal parts, choosing a partition
whose internal old-edge count M is at most `(1/k+o(1))m`. This follows by
averaging balanced partitions. Put an exact H-free extremizer on each part;
connectedness of H makes their disjoint union F free. Its edge count is
`(k^(1-a)+o(1))m`. Independent random relabellings inside the parts have
expected overlap with G at most `M * max_i f(n_i)/binom(n_i,2) = o(m)`.
Choose such relabellings and set R=F minus G.

Assign deletion weight 1 to internal old edges and 1/lambda to crossing
old edges. Every H-copy either uses an internal old edge, or occupies at
least two parts and uses at least lambda crossing old edges. Thus the
weights are a fractional transversal of cost
`M+(m-M)/lambda`. The integral inequality is genuine global optimality.
The argument uses fixed-scale asymptotics, not derivatives of f.

For lambda=k=2 this produces a positive fractional gain whenever

    a < log_2(8/3),

in particular throughout the hypothetical C8 range below 5/4. Global
optimality therefore cannot supply the fractional no-gain condition that
would be needed by the proposed rounding shortcut.

There is also an unconditional application at infinitely many actual C6
extremal orders, using only `ex(n,C6)=O(n^(4/3))`. For `b_j=f(2^j)`,

    limsup 2 b_(j-1)/b_j >= 2^(-1/3),

or else a strictly larger geometric growth rate contradicts that upper
bound. Along the resulting subsequence the same two-part construction has
fractional gain at least

    (2^(-1/3)-3/4-o(1)) f(n),

while every integral repair has nonpositive gain. This is not a statement
about arbitrary exponents: it is a counterexample to fractional rigidity
at true global extrema.

As a small independently checked example, the three-triangle friendship
graph on seven vertices has 9 edges and is globally C4-extremal. Let R be
the disjoint triangles on {1,3,6} and {2,4,5}, with old spokes 0i and old
matching 12,34,56. Then `e(R)=tau_G(R)=6`, but fractional repair is `9/2`.
Three disjoint triangles of pair-witness constraints give the exact lower
bounds. Retaining old edges 01,02,12 gives a feasible integral repair.
The numerical regression was rerun, but the exact claims follow from
these finite combinatorial arguments, not from floating-point LP output.

The required new step remains an integral global comparison/construction
that forces a rational exponent. None is supplied by this obstruction.
