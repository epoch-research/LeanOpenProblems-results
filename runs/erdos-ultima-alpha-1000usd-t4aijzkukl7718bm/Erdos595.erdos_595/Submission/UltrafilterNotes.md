# Exploratory ultrafilter construction (not a settlement)

The conjecture in `Spec.lean` is still unproved. The notes below distinguish verified scratch results from unresolved ideas.
In `Work.lean`, `no_four_fubini`, `ultrafilterGraph_cliqueFree`,
`ultrafilterGraph_trace_coloring`, and
`countable_union_ultrafilterGraph_of_countable` have now been Lean-verified
using only the permitted axioms. They are not a settlement of the conjecture.

Given a graph G on V and ultrafilters p,q on V, define

    A_q = {v : N_G(v) belongs to q},
    R(p,q) iff A_q belongs to p.

Use the symmetric relation R(p,q) and R(q,p) as adjacency.

## Finite clique preservation

If p_1,...,p_k satisfy R(p_i,p_j) for i<j, actual pairwise adjacent
vertices v_1,...,v_k can be selected in G. At step i choose v_i from:

* all N_G(v_j) for j<i, which belong to p_i by the earlier choices;
* all A_{p_j} for j>i, which belong to p_i by R(p_i,p_j).

The finite intersection belongs to p_i and is nonempty. Consequently a
K4 in the symmetric extension yields a K4 in G. Also, R(p,p) would give
cliques of every finite size in G. Thus when G is K4-free the symmetric
relation is automatically loopless.

For principal ultrafilters, adjacency agrees with the original graph,
and p is adjacent to the principal ultrafilter at v exactly when
N_G(v) belongs to p.

## Why one extension of a countable graph fails

If p is nonisolated, take a neighbor q. Then A_p belongs to q and is
nonempty. Any v in A_p is an original vertex adjacent to p. Hence the
original V dominates all nonisolated vertices of the extension.

If V is countable and the extension is K4-free, its nonisolated vertices
are covered by countably many triangle-free vertex sets N(v). The
isolated vertices form another triangle-free set. The verified vertex
partition closure lemma in Work.lean then gives a countable triangle-free
edge cover. Thus the one-step construction cannot be a witness.

There is also a trace bound: A_p is triangle-free, since a triangle in
A_p together with a point of the intersection of its three neighborhoods
would give a K4 in G. Moreover, adjacent p,q cannot have A_p=A_q:
that would imply R(p,p). Thus p -> A_p is a proper coloring with at most
2^{|V|} colors.

## Unresolved iteration

An iterated extension need not have the same countable dominating set.
For example, an ultrafilter at the next stage can avoid each member of
a countable cover while containing their union. This observation is
NOT a proof of any coloring obstruction.

The second iteration has now also been ruled out, as proved below.
No claim has been proved that:

* three or more iterations fail to admit a countable triangle-free cover;
* ultrafilter multiplication is a graph homomorphism for this symmetric
  Fubini relation;
* the extension preserves the Henson extension property or saturation.

The monad-homomorphism argument would require exchanging ultrafilter
quantifiers, which is not valid in general. None of these unresolved
claims may be used in a submitted proof.

## A concrete obstruction to the multiplication-homomorphism shortcut

The failure can already occur for a bipartite half-graph (this example is
mathematically checked here, but not yet formalized in Lean):

* V consists of a_i and b_j for i,j in N, with a_i adjacent to b_j iff i<j.
* Let p be a free ultrafilter supported on the a_i, and q a free
  ultrafilter supported on the b_j.
* In the first extension, A_p is empty, so p is isolated. The neighbors
  of q are exactly the principal ultrafilters at the a_i.
* Let P, an ultrafilter on the first extension, be the pushforward of p
  along the principal embedding. Let Q be principal at q.
* In the second extension, P and Q are adjacent: the neighborhood of q
  belongs to P. But their flattened ultrafilters are p and q, which are
  not adjacent in the first extension.

Thus ultrafilter multiplication is not generally a graph homomorphism,
even for a bipartite starting graph. This does NOT show that iterating
can create a witness: bipartiteness itself is preserved in this example.


## Two extensions are now ruled out (Lean-verified)

Write G1 and G2 for the first and second symmetric extensions. Suppose
P is nonisolated in G2. From an adjacent Q, choose q in Q such that
N_G1(q) belongs to P. Every p in N_G1(q) contains the original trace A_q.
Hence the set {p : A_q belongs to p} belongs to P.

The original induced graph on A_q is triangle-free. If S is any
triangle-free subset of the original graph, then:

1. G1 restricted to U_S = {p : S belongs to p} is triangle-free;
2. G2 restricted to {P : U_S belongs to P} is triangle-free.

Both follow by selecting actual vertices from finite intersections of
ultrafilter members. Consequently every nonisolated P lies in one of
these triangle-free sets, indexed by subsets S of the original V.

For countable V, there are at most continuum many such S. Assign a
suitable S to each nonisolated P, and any default to isolated vertices.
Each fiber is triangle-free, so the previously verified binary-fiber
lemma gives a countable triangle-free edge cover of G2.

Verified declarations in Work.lean:

* `ultrafilterGraph_support_cliqueFree`
* `ultrafilter_trace_cliqueFree`
* `second_ultrafilter_support`
* `countable_union_second_ultrafilterGraph_of_countable`

All use only propext, Classical.choice, and Quot.sound.

This proof does not automatically iterate: for the third extension the
analogous supporting triangle-free sets live in G1, whose power set is
not bounded by the continuum. No valid compression of that family, nor
any obstruction to a countable cover at the third stage, has been proved.


## Finite covers are preserved (Lean-verified)

`fubiniAdj_finite_iSup` proves that the directed Fubini extension
commutes with a finite union. Ultrafilters turn finite existential
quantifiers into a choice of one index, first for the inner ultrafilter
and then for the outer one.

`ultrafilterGraph_finite_cover` consequently proves that an r-piece
triangle-free edge cover of G yields an r-piece such cover of its
symmetric ultrafilter extension. Order the ultrafilters, and put an edge
p<q in piece i when the forward Fubini relation for the original piece i
holds. A monochromatic triangle would give three forward Fubini
adjacencies for a triangle-free original piece, an impossibility.

This rules out starting graphs with finite triangle-free edge covers,
regardless of how large the starting graph is. In particular, any finite
number of iterations from such a graph remains finitely coverable.
It does not establish preservation of countable covers. Countable
unions cannot be interchanged with ultrafilter membership in this way.

## Verified product reduction (continuation)

The following results now compile in `Work.lean`:

* `countable_union_of_hom`: covers pull back along arbitrary graph homomorphisms.
* `levelGraph`, with adjacency `(v,n) ~ (w,m)` iff `G.Adj v w ∧ n ≠ m`.
* `levelGraph_cliqueFree`, `levelGraph_coloring`, `countable_union_levelGraph`.
* `fiberUltrafilter v = map (fun n => (v,n)) (Filter.hyperfilter ℕ)`.
* `fubiniAdj_fiberUltrafilter`: Fubini adjacency of fiber ultrafilters is exactly
  original adjacency.
* `fiberUltrafilterHom`: the induced graph homomorphism to the extension.
* `no_cover_ultrafilter_levelGraph`: a hypothetical witness is recovered from a
  countably vertex-colorable base in a single ultrafilter extension.
* `all_cover_iff_countably_colorable_ultrafilter_cover`: universal coverability
  of `K₄`-free graphs is equivalent to coverability of extensions of countably
  vertex-colorable `K₄`-free graphs.

This is an equivalence, not a proof of either side. In particular, results for a
**countable vertex type** must not be generalized to countably vertex-colorable
bases. Applying the fiber construction to triangle-free graphs of arbitrarily
large vertex chromatic cardinal rules out a uniform continuum bound for the
chromatic cardinal of these extensions.

## The unrestricted adaptation lemma is false (verified)

Earlier notes treated this sufficient lemma for a negative answer as unresolved:

> Every triangle-free graph with natural-number edge labels admits a vertex
> labeling `g` such that no edge `ab` has `g(a)=g(b)=c(ab)`.

`exists_triangleFree_no_adapted` in `Work.lean` now **disproves that lemma**.
It does not disprove or prove the original conjecture.

Construction:

1. Let `X = ℕ → Fin 2` and let `d(x,y)` be the least differing coordinate,
   with `d(x,x)=0`.
2. For every `f : X → ℕ`, there are distinct `x,y` with
   `f(x)=f(y)=d(x,y)`. Build a binary path recursively to avoid color `n` at
   coordinate `n`: if some color-`n` sequence has the current prefix and next
   bit zero, choose bit one; otherwise choose zero. Applying `f` to the path
   gives either a direct contradiction or a matching pair.
   This is `firstDifference_no_adapted`.
3. Choose a triangle-free graph `B` with no proper coloring by `X → ℕ`.
   This is fully constructed using an ordered shift graph on increasing
   pairs from `Set (Set (X → ℕ))`. Any coloring of a shift graph by `C`
   injects its index set into `Set C`, contradicting Cantor's theorem for
   this index set.
4. Blow up each vertex of `B` by `X`, with adjacency determined only by `B`.
   Label an edge between `(v,x)` and `(w,y)` by `d(x,y)`.
5. An adapted labeling `g` would give a proper coloring of `B` by the functions
   `x ↦ g(v,x)`: equality of these functions at adjacent `v,w` contradicts
   step 2. This contradicts step 3.

The restricted theorem `adapted_firstDifference` remains valid: it assumes an
**injective binary encoding of the full vertex set**. The projection to `X`
in the counterexample is not injective.

All newly printed axiom dependencies are among `propext`, `Classical.choice`,
and `Quot.sound`. The main conjecture in `Spec.lean` remains unchanged and
unproved.

## Functoriality and failure of countable-target compression (verified)

New declarations in `Work.lean`:

* `fubiniAdj_map_hom` and `ultrafilterGraphHom`: pushing ultrafilters forward
  along a graph homomorphism preserves Fubini adjacency and symmetric adjacency.
* `binary_coloring_ultrafilterGraph_of_countable`: the ordinary vertex coloring
  by traces of a countable base can be encoded by binary sequences.
* `countable_union_ultrafilterGraph_of_countable_target`: if a `K₄`-free base
  maps to a countable `K₄`-free graph, its extension has a countable cover.
* `exists_countably_colorable_no_countable_cliqueFree_target`: there exists a
  countably vertex-colorable **triangle-free** graph with no homomorphism to
  **any** countable `K₄`-free graph.

For the last result, start with a triangle-free graph `B` with no coloring by
binary sequences, and take `levelGraph B`. If it mapped to a countable `K₄`-free
`H`, functoriality and the fiber-ultrafilter map would give

    B → U(levelGraph B) → U(H) → completeGraph(ℕ → Fin 2),

contradicting the choice of `B`. Thus proper countable vertex colorability must
not be mistaken for having a countable clique-preserving homomorphism target.
The witness to this auxiliary theorem is itself triangle-free and therefore is
not a witness to Problem 595.

## Nonextendability is compatible with a two-piece cover (verified)

`coneGraph G` adds a universal vertex to `G`.

* `coneGraph_cliqueFree`: a cone over a triangle-free graph is `K₄`-free.
* `coneGraph_two_pieces`: such a cone is the union of two triangle-free graphs,
  namely its base edges and its apex star.
* `countable_union_coneGraph`: the corresponding countable cover.
* `exists_nonextendable_coloring_of_coverable_cone`: the fixed coloring from the
  adapted-labeling counterexample cannot extend over its cone without a
  monochromatic triangle, **even though that cone has a two-piece cover**.

The distinction between a prescribed coloring and an arbitrary coloring is
therefore essential, and is checked explicitly rather than merely assumed.
None of these results proves or negates the original conjecture.

## Finite obstructions to the matched-pair hypergraph route (verified)

This continuation revisited the earlier abstract hypergraph on four-element
subsets. For an increasing sextuple `a < b < c < d < e < f`, use the three faces

    {b,d,e,f}, {a,c,d,f}, {a,b,c,e}.

They are obtained by deleting the matched pairs at positions `(0,2)`, `(1,4)`,
and `(3,5)`. Large-cardinal Ramsey arguments make the analogous full hypergraph
on a sufficiently large index set a tempting candidate. The finite computations
had found no Berge triangle for this pattern. That alone does not provide a
graph root.

Two new Lean files now verify obstructions:

### `Submission/RootObstruction.lean`

* `edge_realization_bound`: if a finite family of unordered pairs is generated
  from `s` seeds by repeatedly completing triangles, and the labels map
  injectively to those pairs, then the generated family has at most
  `choose (2*s+1) 2` elements. No new endpoint can appear when two sides of a
  triangle are already supported on the seed endpoints.
* An explicit certificate on twelve indices has twelve seeds and generates
  378 distinct four-subset labels. The endpoint bound is only 300.
* `matched_pair_no_root` verifies that this rules out an injective root in
  **any** graph, without a clique restriction.

The certificate uses kernel-checked `decide`, not an unchecked numerical result
or a `native_decide` axiom. It compiled with

    lake env lean -s 65536 Submission/RootObstruction.lean

### `Submission/RootCases.lean`

Global injectivity is not actually needed for a hypergraph homomorphism to
transfer a chromatic obstruction. This possible escape was checked separately.

* The eight-index restriction has 35 active four-subset labels and 28 triples.
* `no_root` proves that **no map**, even non-injective, sends all these triples
  to actual triangles of a `K₄`-free simple graph.
* `pattern_check` verifies that the displayed triples are exactly the faces
  of the matching pattern above.
* `matched_pair_no_cliqueFree_root` states the conclusion directly for maps
  on increasing four-tuples and constraints from increasing six-tuples.

The proof is an explicit endpoint-equality case analysis, split into helper
lemmas for efficient checking. Every surviving identification either creates a
loop or produces all six edges of a `K₄`. It was compiled successfully with

    lake env lean -j 1 -s 65536 Submission/RootCases.lean

Both final theorem axiom lists are exactly among `propext`, `Classical.choice`,
and `Quot.sound`. These are obstructions to this **particular** construction;
they do not establish a general countable cover theorem.

The measure-theoretic idea considered in this continuation yielded no theorem:
finitely additive measures do not exclude countable covers, while defining an
outer measure using the countable-cover ideal would merely restate the original
problem. No extra set-theoretic axiom has been assumed.

The original `erdos_595` in `Submission/Spec.lean` remains unproved and unchanged.

## Finite trace supports do not give a global support (verified)

`Submission/SupportObstruction.lean` imports the auxiliary `Work` module and
checks a concrete failure of a possible third-stage compression argument.
It does **not** settle the original conjecture.

The countable base graph H has vertices a_i, b_i, x_n, with edges

* a_i--b_i;
* a_i--x_n iff i<n;
* b_i--x_n iff n≤i.

H is triangle-free. Let G be its cone, with apex z. Thus G is K4-free and
has a two-piece triangle-free edge cover.

Let q be a free ultrafilter on the b_i, and let P be the ultrafilter on
first-stage vertices obtained from the principal ultrafilters at x_n along
a free ultrafilter on the natural numbers. The second-stage trace

    T = {p : N_{U(G)}(p) belongs to P}

contains the principal ultrafilter at z, all the principal ultrafilters at
a_i, and q. If an original set S belonged to every p in T, it would contain
z, every a_i, and some b_i. It would therefore contain a triangle.

Verified theorems:

* `G_cliqueFree`, `G_cover`;
* `apex_mem_trace`, `a_mem_trace`, `q_mem_trace`;
* `no_single_triangleFree_support`;
* `trace_cliqueFree`;
* `finite_trace_support`: for any K4-free base, every finite part of a
  second-stage trace has a common original triangle-free support;
* `finite_support_but_no_global_support`: the concrete trace above has all
  these finite supports but no global one.

For the general finite-support lemma, choose one first-stage vertex adjacent
to every member of the finite trace fragment, by taking a finite intersection
inside P. Its original trace is the required triangle-free support.

Hence finite simultaneous supports cannot simply be promoted to one common
original support by compactness. This only rules out that stronger proposed
compression statement; it does not rule out other proofs about third or later
extensions. In particular, the example itself has a finite cover, preserved
by all finite iterations.

The file compiles with `lake env lean Submission/SupportObstruction.lean`
(after building `Submission/Work.olean`). All printed axiom dependencies are
among `propext`, `Classical.choice`, and `Quot.sound`. The latest successful
check is logged in `/tmp/support.log`.

The triangle-corner selection approach remains unresolved as well: the earlier
order criterion gives a cover if the appropriate local countable colorings
exist, but no general selection/orientation theorem was established.

`Submission/Spec.lean` remains unchanged and contains its original `sorry`.

## Universal independent apex extensions preserve covers (verified)

The saturation/extension-property route was checked in
`Submission/ExtensionObstruction.lean` (importing the auxiliary `Work` module).

For a graph G on V ⊕ W with W independent, a valid old edge coloring c extends
**after renaming** old colors by n ↦ n+1: assign zero to every old--new edge.
Every mixed triangle has two zero cross edges and a nonzero old edge. Theorems:

* `extendedColor_valid`;
* `countable_cover_independent_extension`.

No K4-free hypothesis is needed for this cover-preservation statement. It does
not say that a prescribed coloring extends without renaming; the previous
nonextendable-coloring example remains valid.

The file also defines `apexFamilyGraph G`, with one independent new apex for
**each** subset S of the old vertices whose induced graph is triangle-free.
That apex has old neighborhood exactly S. Verified:

* `apexFamilyGraph_cliqueFree`: K4-freeness is preserved;
* `apexFamilyGraph_extension`: every allowable old neighborhood is realized
  exactly, without a finiteness restriction;
* `countable_cover_apexFamilyGraph_iff`: the extended graph has a countable
  triangle-free edge cover if and only if the old graph does.

Therefore adding arbitrarily many independent apices, even all allowable ones,
cannot turn a coverable graph into a witness in a single step. It also does not
settle long iterations. If an iteration has at most continuum many independent
birth layers and starts with a coverable graph, the earlier verified closure
under continuum many coverable vertex pieces still gives a cover of the whole
union. A proposed witness from such an iteration needs a genuinely new argument
beyond that range; merely citing one-point extension richness is insufficient.

The file compiles with

    lake env lean Submission/ExtensionObstruction.lean

and its printed axiom lists use only `propext`, `Classical.choice`, and
`Quot.sound`. The last successful log is `/tmp/extension.log`, and the built
module is at `.lake/build/lib/lean/Submission/ExtensionObstruction.olean`.

No construction or theorem in this continuation proves or negates `erdos_595`.
`Submission/Spec.lean` still has its original statement and original `sorry`.

## Quarter-measure graph candidate (basic properties verified; cover question open)

`Submission/QuarterGraph.lean` is a new candidate-family development file. It
imports `Submission.Work`, not the main conjecture. Let μ be a probability
measure and p an ultrafilter containing every conull set. Such a p exists as
`Ultrafilter.of (ae μ)`, using only the permitted axioms.

Vertices are measurable sets A satisfying μ(A)=1/4 and A∉p. Two vertices are
adjacent exactly when their underlying sets are disjoint.

Verified declarations in namespace `Erdos595Quarter`:

* `conullUltrafilter`, `conullUltrafilter_le`;
* `quarterGraph_cliqueFree`: the graph has no K4;
* `quarterGraph_not_triangleFree`: any four pairwise disjoint quarter-measure
  sets give a triangle, by discarding the one part selected by p;
* `finite_union_measure_lt_one`: every finite family of vertices has union
  of measure strictly less than one.

K4-freeness follows because four disjoint quarter-measure sets have conull
union. A finite union belongs to an ultrafilter only if some member does, but
all four proposed vertices are excluded from p. The same argument proves the
finite-union bound. This bound is strictly a finite statement; countable unions
cannot be interchanged with ultrafilter membership.

No result in the file proves that any member fails to admit a countable
triangle-free cover. That is the unresolved and essential step.

On a finite uniform probability space with 4k points, choosing the principal
ultrafilter at one point gives the Kneser graph KG(4k−1,k): its vertices are
k-element sets avoiding that point. This identification is a mathematical
observation, not yet a theorem in the Lean file.

Exploratory finite checks (not proof of the infinite conjecture):

* `/tmp/kneser_cover.py` generated the edge-triangle NAE constraints.
* KG(7,2): 21 vertices, 105 edges, 105 triangles. A two-color solution was
  found and checked directly; data are in `/tmp/kneser_cover_2.npz`.
* KG(11,3): 165 vertices, 4620 edges, 15400 triangles. The MILP solver reached
  its 90-second limit without a solution or an infeasibility proof. A separate
  local search also did not find a solution (best remaining violations: 8).
  **Neither failure is evidence sufficient to assert non-colorability.**
* Logs: `/tmp/kneser_cover.log`, `/tmp/kg11_search.log`.
* Exact NAE constraints: `/tmp/kg11.nae`; local-search source and executable:
  `/tmp/nae_search.cpp`, `/tmp/nae_search`.
* Sage's CryptoMiniSat and PicoSAT wrappers are installed, but their optional
  `pycryptosat` and `pycosat` backends are not. No SAT result was obtained.

A possible next investigation is a large, nonseparable product probability
space and a conull ultrafilter. No non-coverability argument is established,
and no regularity of an arbitrary edge coloring may be assumed.

The file compiles with `lake env lean Submission/QuarterGraph.lean`; all
printed dependencies are among `propext`, `Classical.choice`, and `Quot.sound`.
The latest verification log is `/tmp/quarter.log`.

The original `Submission/Spec.lean` remains unchanged and unproved.

## Update: quarter-measure family is now ruled out (verified)

The earlier section treating quarter-measure non-coverability as open within
this investigation is superseded. Every quarter graph considered there has
a countable triangle-free edge cover, without any separability restriction.

New files, all checked without holes and using only the permitted axioms:

* `Submission/NegativeInner.lean` (240 lines), namespace
  `Erdos595NegativeInner`:
  `countable_cover_of_negative_inner` proves countable coverability whenever
  graph edges have strictly negative real Hilbert-space inner products.
  The proof approximates each vector by finite packets in an orthonormal
  basis. An ordered pair code records packet sizes, coefficient signs and
  coordinate coincidences. In a triple with identical pair codes, all
  coincidences are diagonal and their products are nonnegative. This rules
  out a monochromatic triangle in the negative-dot approximants.

* `Submission/MeasureCover.lean` (58 lines), namespace
  `Erdos595MeasureCover`:
  `countable_cover_of_measurable_disjointness` applies this to centered
  indicator functions in L2 of a probability measure. Disjoint positive
  measure sets have centered inner product `-μ(A)*μ(B) < 0`.
  `quarterGraph_countable_cover` decisively rules out the quarter family.
  It does not need the ultrafilter's conull-set property.

* `Submission/TriangleHit.lean`, namespace `Erdos595TriangleHit`:
  `countable_cover_of_triangle_hit` weakens the sufficient condition to
  requiring just one strictly negative edge in every graph triangle. The
  negative-edge subgraph is countably coverable and its complement in G is
  triangle-free. `nonnegative_triangle_of_no_cover` is the contrapositive:
  any witness must have a triangle with three nonnegative inner products
  under every real Hilbert-space assignment.

* `Submission/VectorThree.lean`, namespace `Erdos595VectorThree`:
  `two_cover_of_zero_sum_triangles` uses an algebraic basis and the ordered
  additive group of lexicographic finitely supported coefficient vectors.
  If all vertex labels are nonzero and every triangle's labels sum to zero,
  signs of edge sums give a two-piece cover.
  `two_cover_of_unit_inner_le_neg_half` applies it to unit vectors with edge
  inner products at most -1/2: every triangle has vector sum zero.
  `three_cover_of_triangle_hit_neg_half` needs that threshold on only one
  edge per triangle and gives three pieces (indexed by `Option Bool`).

All four `.olean` files have been built in `.lake/build/lib/lean/Submission`.
Logs: `/tmp/negative-inner.log`, `/tmp/measure-cover.log`,
`/tmp/triangle-hit.log`, `/tmp/vector-three.log`.

### Still unproved / do not assume

* No Hilbert triangle-hitting assignment has been constructed for arbitrary
  K4-free graphs.
* Finite solvability with margins tending to zero does not justify an
  infinite strict-negativity conclusion by compactness.
* A fixed uniform negative triangle-hitting margin for all finite K4-free
  graphs would be an interesting sufficient route, but no such result has
  been proved. The -1/2 margin is too strong: the verified three-piece bound
  conflicts with the known finite Folkman theorem for three edge colors.
  The finite Folkman existence theorem itself has not been formalized here.
* No numerical search for these vector assignments was run. There is no
  evidence here that a smaller uniform margin works or fails.
* No argument here proves that the Hilbert triangle-hitting condition is
  necessary for countable coverability.

`Submission/Spec.lean` is still unchanged, with the original `sorry`.
None of these auxiliary results settles the conjecture or its negation.

## Exact Paley obstruction and separation (verified)

`Submission/PaleyObstruction.lean` now compiles (402 lines, only the permitted
axioms). Its Paley graph on 17 vertices is K4-free. There is no unit-vector
assignment whose inner-product sum on every triangle is at most -1, and no
unit-vector assignment with all edge inner products at most -1/3.

The kernel-checked certificate uses S = 17A + 51I - 11J and the identity
SᵀS + 901J = 3757I + 1445A. The graph has 68 edges, 68 triangles, and every
edge is in three triangles. Summation gives the contradiction exactly.

This does not obstruct the minimum-edge triangle-hitting condition. The
same file explicitly constructs unit vectors with at least one edge of each
triangle having inner product -1/2, and proves a three-piece triangle-free
edge cover. Thus the stronger convex condition cannot replace the weaker
condition. No settlement of `Spec.lean` follows.

## Ramsey transfer obstructs the uniform minimum-edge route (verified reduction)

`Submission/RamseyVectorObstruction.lean` is now checked, with dependencies
only on `propext`, `Classical.choice`, and `Quot.sound`. The `.olean` has been
built; the log is `/tmp/ramsey-vector.log`.

* `RamseyAgainstTriangle K G` says every red/blue edge cover of G with no
  blue triangle has a red homomorphic copy of K.
* `UnitTriangleHit G δ v` specifies unit vectors with at least one inner
  product at most δ in each triangle.
* `no_triangle_hit_of_ramsey` transfers an all-edge vector obstruction on K
  to a minimum-edge triangle obstruction on a Ramsey graph G. Colour edges
  red when their inner product is at most δ, and blue otherwise.
* `no_triangle_hit_third_of_paley_ramsey` applies this to the checked Paley-17
  obstruction at δ = -1/3.

Mathematical consequence using a standard theorem **not formalized here**:
the finite clique-preserving graph Ramsey theorem gives a finite K4-free
G that is Ramsey for a red Paley-17 graph or a blue triangle (one may instead
use a two-colour Ramsey graph for Paley-17, which itself contains a triangle).
Such a G cannot have the uniform minimum-edge margin 1/3. Thus the earlier
suggestion that this fixed margin might work for every finite K4-free graph
is not a viable route if that classical theorem is invoked.

More generally, that same Ramsey transfer, combined with finite triangle-free
graphs of arbitrarily large vector chromatic number, obstructs every fixed
positive margin. The required finite existence results have not been
formalized in this project; do not cite them as Lean-checked declarations.
The reduction itself is fully checked.

This does NOT rule out nonuniform, strictly negative triangle-hitting
assignments on infinite K4-free graphs. Nor does it prove they exist. No
settlement of `Spec.lean` follows, and its original `sorry` remains.

## Further candidate exploration: arc right adjoints (not Lean-verified)

A new powerset-based operation was investigated. Its vertices are nonempty
ordered bicliques (A,B) in a base graph: A x B consists of edges. Two vertices
(A,B),(C,D) are adjacent when B intersects C and D intersects A. Looplessness
follows from A and B being disjoint.

The usual arc-graph adjunction gives a useful mathematical clique test:
a K4 in this new graph is equivalent to a homomorphism from the directed
arc graph of K4 into the base. The latter has 12 vertices (ordered unequal
pairs of four indices), adjacent when one arc ends where the other begins.
This equivalence has not been formalized here.

Tests used the 2-section of the previously considered matched-pair
3-uniform hypergraph: vertices are four-element sets, and triangles on an
increasing sextuple delete the position pairs (0,2),(1,4),(3,5).

* `/tmp/arc_right_candidate.py` searches for a homomorphism from the arc
  graph of K4 to these finite base graphs. It found none for index sizes
  8 through 16. This is an exploratory computational result, not a Lean
  proof and not by itself an infinite nonexistence result.
* A separate exact Python search found no injective triangular prism in
  the bases for index sizes 8 through 14. Any such prism would use two
  disjoint hypergraph triangles, hence at most 12 underlying indices.
  This suggests a general prism-free explanation, subject to verifying
  that all graph triangles are precisely the displayed hyperedges.

There is also a serious coverability obstruction to this candidate:
when each base edge belongs to at most one triangle, a triangle in the
right-adjoint graph produces either an injective triangular prism in the
base, or a collapsed prism lying over one base triangle. In the collapsed
case the three bicliques all have singleton A-sides, or all have singleton
B-sides. If the base is prism-free, these two classes inherit a base cover;
all other edges lie in no triangle. This argument has not been formalized,
but it prevents treating the computational absence of K4 as a solution.
No lower bound on the new graph's triangle-edge chromatic number was proved.

Another possible candidate family is the exponential graph H^B, with H
countable and K4-free and B of uncountable ordinary chromatic number.
Adjacency is: for every edge xy of B, H relates f(x) to g(y) and g(x) to f(y).
A clique of four functions would give a homomorphism from B to the countable
loopless graph H^(K4), contradicting uncountable chromatic number. Hence the
exponential is K4-free. Its failure of countable triangle-free edge
coverability is entirely unproved. Finite H cannot work: a finite
obstruction to B -> H gives a finite loopless projection target. Likewise
B complete cannot work, since one may choose for each function a value
occurring at least twice, producing a homomorphism to H.

These are research notes only. No new proof was added to `Spec.lean`.

## Exponential family: basic facts now Lean-verified

`Submission/ExponentialCandidate.lean` now compiles, using only the permitted
axioms. Its `.olean` is built and its log is `/tmp/exponential.log`.

* `exponential H B hB` is defined when H is countable and `hB` asserts that
  B has no proper natural-number vertex coloring.
* `exponential_cliqueFree` preserves every finite clique bound of H, not
  only the K4 bound. A putative n-clique of functions colors B by its
  countably many n-tuples of values. A monochromatic B-edge yields an
  actual n-clique in H.
* `constantHom` maps H into the exponential by constant functions.
* `curryHom` turns a product map B x F -> H into F -> H^B.
* `no_cover_of_product_map` pulls a genuine non-coverability obstruction
  through this homomorphism. It is conditional on an already non-coverable
  F and therefore is not a construction or a settlement.

No non-coverable example in this family has been proved. `Spec.lean` still
has its original `sorry`.

## Exponential follow-up: verified coverability obstructions

`ExponentialCandidate.lean` has grown to 179 lines and still checks using
only the permitted axioms (same build command and `/tmp/exponential.log`).
New verified declarations:

* `crossingEdgesHom`: if every pair of B-edges has a cross-edge between
  their endpoint sets, H^B maps to H. Choose a B-edge on which each
  function is constant, and use the cross-edge for adjacent functions.
* `coloring_nat_of_crossing_edges` and `coloring_nat_complete_domain`:
  these domains give a countable proper vertex coloring, so cannot work.
* `badSet_coloring_nat`: for an exponential edge fg, the set of x where
  H does not relate f(x) to g(x) induces a countably vertex-colorable
  subgraph of B. Colour by the pair of values (f(x),g(x)). This is only
  a statement about that bad set, not about the whole domain B.
* `coloring_nat_of_finite_obstruction`: if a finite graph F maps to B but
  cannot map to H, the exponential is countably vertex-colorable by its
  restrictions to F. In particular, for a K4-free target, a useful domain
  cannot contain a K4.

Unformalized observation for future use: a countable domain obstruction
F (instead of a finite one) yields a proper vertex colouring by at most
continuum many restrictions, hence still a countable triangle-free edge
cover by the verified Work.lean criterion. Thus a potentially useful H,B
pair must have every countable subgraph of B homomorphically mapping to H.
Taking H to be a countable universal K4-free graph would meet that local
condition, but no non-coverability proof for its exponential is known here.

The original conjecture is still unproved. No change was made to `Spec.lean`.

## Structural follow-up: configuration and tuple-type checks (exploratory)

No proof or disproof of `erdos_595` was obtained in this continuation.
`Submission/Spec.lean` is unchanged.

Two exact finite combinatorial checks were run; neither is a Lean theorem:

* `/tmp/check_matched_pasch.py` checks the matched-pair hypergraph on four-subsets
  for the six-vertex, four-triple Pasch configuration. None was found for index
  sizes 8, 10, 12, or 14. A separate check found no Berge triangle for sizes
  8, 10, and 12. Thus a proposed shortcut through an unrestricted theorem about
  configuration-free linear hypergraphs must not be assumed. The previous
  graph-edge-root obstructions remain essential.
* `/tmp/check_tuple_cliques.py` exhausts relative-order/equality types of two
  increasing r-tuples, up to r = 7. For each type it tests consistency of a
  clique by union-find for required equalities and acyclicity for strict
  inequalities. Every type supporting a triangle also supported cliques of
  sizes 4, 5, 8, and 12. The numbers of triangle-supporting symmetric types for
  r = 1,...,7 were 1, 5, 20, 76, 285, 1065, and 3976. No single-type K4-free
  triangle construction was found. This finite computation is not a proof
  of the general order-type statement.

The cardinal-decomposition route also remains incomplete: the verified
closure under continuum many coverable vertex pieces does not supply a
method for covering the crossing edges in longer decompositions. No
singular-compactness or arbitrary-cardinal extension theorem was established.

## Triangle-radius normalization (Lean-verified)

`Submission/TriangleRadius.lean` now compiles (about 215 lines), using only
`propext`, `Classical.choice`, and `Quot.sound`. The build log is
`/tmp/triangle-radius.log`, and the `.olean` has been built.

For an arbitrary graph G, the enlargement has:

* two roots a,b;
* one port P_v and one original vertex X_v for each v;
* one pair vertex R_e for every unordered pair e (including diagonals).

Its edges are a--b, a--P_v, b--P_v, a--R_e, P_v--R_e and X_v--R_e when
v belongs to e, P_v--X_v, and the original edges X_v--X_w of G.

Verified declarations:

* `embedding`: G embeds inducedly into the enlargement.
* `cliqueFree`: if G is K4-free, so is the enlargement. The neighborhoods
  of every non-original vertex are triangle-free; a K4 would therefore
  consist entirely of original vertices.
* `Within`: reachability of an edge from a--b in at most n triangle-sharing
  steps, allowing waiting steps.
* `all_edges_within_four`: every edge has triangle-sharing radius at most 4.
* `no_cover_preserved`: a genuine non-coverability obstruction in G would
  transfer to the enlargement by its embedding.

This is a conditional normalization, NOT a construction of a non-coverable
G. It shows that merely imposing bounded triangle-sharing radius cannot
resolve the problem: radius four already contains induced copies of every
K4-free graph. The proposed local recoloring approach has not been completed.
`Submission/Spec.lean` still has its original `sorry`.

## Covering-space / group-presentation route (mathematical exploration only)

A possible way around direct graph-edge-root obstructions was investigated:
use hypergraph vertices as group generators and hyperedges as triangular
relators, then take a Cayley graph or a covering complex. No witness was
obtained, and no new theorem from this route was added to Lean.

The all-positive presentation is ruled out directly. For relators xyz = 1,
sending every generator to 1 in Z/3Z respects every relator. Its induced
homomorphism properly three-colors the Cayley graph with generator edges,
because each edge changes the value by +1 or -1. Thus high chromatic number
of the original hypergraph does NOT transfer to triangle-edge
non-coverability through this construction.

Mixed signs avoid this particular three-coloring, but neither the necessary
K4-freeness nor the transfer of arbitrary countable edge colorings was proved.
In particular, one must not assume that a coloring of translated generator
edges is translation-invariant. Recording the coloring on all translates
has a potentially enormous range and does not yield a countable hypergraph
coloring. Also, a triangle-free presentation link alone was not established
to prevent all additional triangles or K4s in the resulting Cayley graph.

`Submission/Spec.lean` remains unchanged, with its original `sorry`.

## Finite-adapted prescribed-color extension (Lean-verified)

`Submission/FiniteAdaptedExtension.lean` now compiles, with only the permitted
axioms. Its `.olean` has been built and the log is
`/tmp/finite-adapted-extension.log`.

* `Valid G c` is the no-monochromatic-triangle condition.
* `Adapted G c f` forbids an edge xy with f(x)=f(y)=c(xy).
* `extend_valid` preserves a prescribed old edge coloring when it has an
  adapted vertex labeling bounded by some natural m. Cross edges receive
  the old vertex label, while new--new edges receive d(e)+m for a valid
  coloring d of the new induced graph.
* `exists_extension` consequently extends such a prescribed coloring across
  any enlargement whose new induced graph is countably coverable. No K4-free
  assumption is needed for this extension lemma.
* `exists_finitely_adapted`: every nonempty countably coverable graph has a
  valid coloring with a two-valued adapted vertex labeling. Normalize all
  edges incident to one chosen vertex p to color zero and shift every other
  color up by one. Label p by 1 and every other vertex by 0.

These facts further limit arguments that use failure to extend one fixed
coloring as evidence of non-coverability. They do not provide coherent
colorings along arbitrary long transfinite constructions. In particular,
the extension formula need not preserve the same finite adapted labeling
or the normalization of the old coloring, so it cannot simply be iterated
through uncountable limits.

No proof or disproof of `erdos_595` was obtained. `Submission/Spec.lean` is
still unchanged and retains its original `sorry`.

## Least-common-neighbor rank coloring: explicit failure

An attempted natural-number coloring was tested exactly in
`/tmp/triangle_rank_test.py`. For an edge uv, choose its least common neighbor
w in a fixed vertex order. If w precedes both endpoints, give uv rank
1 + max(rank(uw), rank(vw)); otherwise give it rank zero. The recursion is
well-founded, but these ranks do NOT in general avoid monochromatic triangles
in K4-free graphs.

The six-vertex counterexample has edge set

  04, 05, 13, 15, 23, 24, 34, 35, 45.

Its central triangle 345 has rank one on all three sides: their respective
least common neighbors are 2, 1, and 0, and all six outer edges have rank zero.
The graph is K4-free (the three outer vertices have degree two; the remaining
three vertices form only a triangle). The computation first checked the
Paley-17 graph and all K4-free graphs on at most five vertices, then found this
counterexample among the six-vertex graphs. The failed rule is not a proof
of the conjecture's negation.

The mixed-sign, order-three group-presentation route also remains unresolved.
No global non-coverability transfer was established, and no theorem settling
`erdos_595` was added to `Submission/Spec.lean`.

## Finite triangle-orientation obstruction (Lean-verified)

`Submission/FiniteOrientationObstruction.lean` compiles, with only the permitted
axioms; its `.olean` has been built. Log: `/tmp/finite-orientation.log`.

With B = Set Nat and C = Set B, `free_triple` proves that for any finite-valued
maps

  f : Nat -> B -> Finset C,
  g : Nat -> C -> Finset B,
  h : B -> C -> Finset Nat,

there are a,b,c such that c is not in f(a,b), b is not in g(a,c), and a is not
in h(b,c). The proof first avoids the union of f using Cantor's cardinal
inequality, next avoids the countable union of g, and finally avoids h(b,c).

Interpretation: the triangles of the complete tripartite graph with these
three parts cannot be assigned to their edges with only finitely many
triangles assigned to each edge. In particular, a well-order of its edges
cannot make every edge the last edge of only finitely many triangles.
This defeats a sufficient greedy-coloring criterion even for a finitely
colorable K4-free graph. The interpretation as a graph-ordering statement
has not separately been formalized; the finite-valued-map theorem is checked.

This is not an obstruction to countable triangle-free edge covers: the
complete tripartite graph has a finite such cover. No settlement of the
original conjecture follows, and `Submission/Spec.lean` is unchanged.

## Countable-product / ultraproduct size obstruction (Lean-verified)

`Submission/CountableProductObstruction.lean` compiles and has a built `.olean`.
Its three printed axiom lists contain only `propext`, `Classical.choice`, and
`Quot.sound`; the log is `/tmp/countable-product-obstruction.log`.

* `mk_pi_le_continuum`: a countable product of countable sets has cardinality
  at most the continuum.
* `mk_quotient_pi_le_continuum`: the same bound holds for an arbitrary quotient
  of that product.
* `quotient_pi_countable_cover`: every graph on such a quotient has a
  countable triangle-free edge cover. No clique-freeness assumption is needed.

In particular, countable-index ultraproducts of finite Folkman graphs cannot
be witnesses, regardless of their failure to have covers by finitely many
triangle-free subgraphs. This statement concerns arbitrary external covers;
it is not restricted to internal colourings. The file does not assert a
bound for uncountable-index ultraproducts or for all saturated graphs.

This is a candidate-family obstruction, not a solution. `Submission/Spec.lean`
remains unchanged, and its original conjecture still has `sorry`.

## Middle-corner coloring is too strong, for every vertex order (Lean-verified)

`Submission/MiddleCornerObstruction.lean` compiles; its `.olean` is built.
Log: `/tmp/middle-corner-obstruction.log`. All printed axiom lists contain
only `propext`, `Classical.choice`, and `Quot.sound`.

Vertices are increasing triples `(a,b,c)` from a sufficiently large ordered
set. Join `(a,b,c)` to `(b,c,d)` (one-step shift) and to `(c,d,e)` (two-step
shift), symmetrically.

* `graph_cliqueFree`: the graph is K4-free. From the least-first-coordinate
  vertex of a purported K4, the other three first coordinates have only two
  possible values, while adjacency requires different first coordinates.
* `oneGraph_cliqueFree`, `twoGraph_cliqueFree`, `two_pieces`, `graph_cover`:
  the two shift lengths give two triangle-free edge pieces.
* `no_middle_coloring_on_four_powersets`: over four iterated power sets of a
  palette C, no C-edge-coloring can require the two consecutive edges of each
  triangle ordered by first coordinates to have distinct colors.
* `no_ordered_middle_coloring`: the obstruction holds even when an arbitrary
  linear order of the triple vertices may be chosen, by taking four power
  sets of `C × Bool` as the index set.

For the last theorem, append to each one-step edge color its orientation bit
in the chosen vertex order. Equal colors on consecutive one-step edges would
make all three windows monotone in that order, violating the middle-corner
condition. The resulting coloring properly colors the next shift graph.
Twice taking sets of outgoing colors reduces it to the ordinary pair shift
graph, whose coloring injects the index set into three power sets of the
palette. Cantor rules this out.

Thus selecting the middle corner of every triangle after choosing a vertex
order cannot provide a universal proof of countable covering. The example
itself has a TWO-piece cover and is not a witness for the original conjecture.
`Submission/Spec.lean` still has its original `sorry`.

### Exploratory right-adjoint check on the new shift-square family

These are exact finite computations, NOT Lean theorems and NOT a settlement.

* `/tmp/arc_right_shift.py` checks homomorphisms from the 12-vertex directed
  arc graph of K4 to the one/two-step triple-shift graph. None was found on
  index sets of sizes 6, 8, 10, 12, 15, 18, or 21. This does not establish
  the assertion for arbitrary index sets.
* Unlike the earlier matched-pair candidate, this base has an injective
  triangular prism already on seven indices. Its two matched triangles are
  `(012,123,234)` and `(235,356,023)`. Thus the old prism-free obstruction
  is not directly applicable to this base.
* `/tmp/right_shift_concepts.py` enumerates maximal bicliques of the finite
  base and tests the corresponding right-adjoint graph. For index sizes
  5 through 10, these graphs were K4-free and had two-piece triangle-free
  edge covers. The largest checked graph had 388 maximal-biclique vertices,
  5296 edges, and 1902 triangles. The Boolean assignments were checked
  against all triangle clauses, but this is not a Lean certificate or an
  infinite cover theorem.

No non-coverability result was obtained for this right-adjoint family.
In particular, the finite absence of K4 does not justify treating it as a
witness, and finite two-piece covers have not been asserted to extend to the
infinite graph without a proof.

## Countable-colour Hales--Jewett fails at every dimension (Lean-verified)

`Submission/CountableHalesJewettObstruction.lean` compiles and has a built
`.olean`. Log: `/tmp/countable-hales-jewett.log`. All four printed axiom lists
contain only `propext`, `Classical.choice`, and `Quot.sound`.

* `sqNorm_rigid`: finitely supported rational vectors x,y,z with
  x+z=y+y and equal sums of coefficient squares must have x=z.
* `exists_progression_free_coloring`: for every rational vector space,
  of arbitrary dimension, there is a natural-number coloring with no
  nonconstant monochromatic three-term arithmetic progression. Choose an
  algebraic basis and encode the rational sum of squares of the finitely
  many nonzero coefficients.
* `cube_countable_coloring`: for EVERY index type I, the full cube
  `(I -> Fin 3)` has a natural-number coloring with no monochromatic
  `Combinatorics.Line`. Embed the alphabet as 0,1,2 in the rational vector
  space `I -> Rat`; each combinatorial line is a nonconstant progression.
* `finite_palette_lines` records the contrasting finite-palette theorem,
  using Mathlib's Hales--Jewett theorem.

This blocks upgrading the Hales--Jewett step of a finite partite argument
merely by allowing a much larger (even arbitrary-cardinal) dimension. It does
NOT prove that every possible infinite Folkman construction fails, and it
is not a proof or disproof of Erdős Problem 595.

The purely model-theoretic and forcing discussions in this continuation
produced no additional theorem. In particular, no saturation principle for
arbitrary external color classes was assumed. `Submission/Spec.lean` remains
unchanged and still contains `sorry`.

## Orthogonality boundary case (Lean-verified)

`Submission/OrthogonalityObstruction.lean` now compiles and has a built `.olean`.
Log: `/tmp/orthogonality-obstruction.log`. All printed theorem axiom lists
contain only `propext`, `Classical.choice`, and `Quot.sound`.

Main result: `countable_cover_of_orthogonality_completion` gives a countable
triangle-free cover of a K4-free graph represented in a real Hilbert space
when (1) every edge has nonpositive inner product, and (2) EVERY zero-inner-
product pair is an edge. The hypotheses include diagonal pairs, so zero
vector labels are automatically excluded.

Proof: if the graph is triangle-free, there is nothing to do. Otherwise,
choose a triangle of three anchors. Every vertex has nonzero inner product
with at least one anchor, since otherwise the zero-pair hypothesis gives a
K4. Partition vertices by a chosen anchor and the sign of that inner
product. For anchor u, replace x by

  <u,u> x - <x,u> u.

Two adjacent vectors in the same part now have strictly negative inner
product. Apply the already verified negative-inner-product theorem in each
of the six vertex parts, then the vertex-partition closure theorem.

Corollaries:
* `countable_cover_of_orthogonality_graph`: induced orthogonality graphs
  represented by nonzero vectors, when K4-free, are countably coverable.
* `countable_cover_of_nonpositive_graph`: the same holds for the full
  nonpositive-inner-product graph, when K4-free.

IMPORTANT: this does NOT apply to an arbitrary subgraph of an orthogonality
graph. Arbitrary graphs embed as subgraphs of the orthogonality graph on an
orthonormal family, so dropping the zero-pair hypothesis would invalidate
the conclusion. Nor has a suitable representation/completion been proved
for every K4-free graph.

The finite-field polar-graph idea was not formalized. The rank-one adjacency
version has unique common neighbors on edges and therefore offers no route
past the existing common-neighborhood cover criterion. No witness or
universal decomposition was found. `Submission/Spec.lean` is unchanged and
still has its original `sorry`.

## The OR Fubini extension of a triangle-free base is two-piece coverable

`Submission/OneSidedUltrafilterObstruction.lean` compiles; its `.olean` is
built. Log: `/tmp/one-sided-ultrafilter.log`. Both final axiom lists contain
only `propext`, `Classical.choice`, and `Quot.sound`.

This is a different operation from the previous mutual Fubini extension:

  p ~ q iff R(p,q) OR R(q,p),
  R(p,q) iff {v : N(v) belongs to q} belongs to p.

For a triangle-free base, `no_three_fubini` forbids
R(p,q), R(p,r), R(q,r). Consequently:

* `orUltrafilterGraph_cliqueFree` proves that the OR extension is K4-free,
  since every tournament on four vertices has a transitive triangle.
* `orUltrafilterGraph_two_cover` proves that it has a TWO-piece triangle-free
  edge cover. Fix a vertex order and split edges by a Fubini direction in
  which the relation holds. A monochromatic triangle would give three
  forward Fubini adjacencies in one of the two vertex orders.

The file first proves both assertions abstractly for any directed relation
with no transitive directed triangle, then specializes to ultrafilters.

The OR extension can indeed introduce triangles: mathematically, take three
parts a_i,b_j,c_k and edges a_i-b_j iff i<j, b_j-c_k iff j<k, and c_k-a_i iff
k<i. The base is triangle-free, while free ultrafilters on the three parts
have cyclic Fubini adjacencies. This example has not separately been
formalized here; it is three-partite and is not a witness in any case.

Thus using OR instead of mutual adjacency does not amplify a triangle-free
base into a non-coverable graph. The search for a converse to the Hilbert
representation cover theorem also produced no valid result. None of this
settles `erdos_595`; `Submission/Spec.lean` remains unchanged with `sorry`.

## Root-lattice / Cayley reduction (Lean-verified)

`Submission/RootLattice.lean` constructs a graph on the integer-vector group
`V → ℤ`. Its allowed differences are precisely `unit a - unit b` for edges
`G.Adj a b` of the original graph.

Verified:

* `root_sub_root`: two nonzero roots whose difference is a root share their
  positive or their negative endpoint.
* `cliqueFree_three`, `cliqueFree_four`: triangles and K4s in the new graph
  give respectively triangles and K4s in the original graph.
* `unitHom`: the original graph maps into the new graph on unit vectors.
* `graph_iSup`: the construction commutes with arbitrary graph unions.
* `countable_cover_iff`: the root graph is countably triangle-free coverable
  **if and only if** the original graph is.
* `translation_invariant_cover`: for this specific root-graph family, any
  countable cover can be replaced by a translation-invariant countable cover.

The K4 proof uses the elementary fact that three ordered pairs which pairwise
share a coordinate all share the same first coordinate or the same second
coordinate. Their other coordinates, together with the shared coordinate,
then form a K4 in G.

This reduction constructs no non-coverable graph and proves no universal
cover theorem. In particular, translation-invariant covers have not been
assumed for arbitrary Cayley graphs. The theorem is proved for this family
by restricting to unit vectors and then lifting that restricted cover.

The file compiles, and all printed axiom dependencies are among `propext`,
`Classical.choice`, and `Quot.sound`.

## Arithmetic-progression edge labels: obstruction (Lean-verified, conditional transfer)

A new possible sufficient condition was considered: label edges by rational
vectors so that the labels of each triangle form a nonconstant arithmetic
progression. The earlier rational-vector sphere colouring would then give
a countable triangle-free edge cover.

This is not an established universal representation theorem. The new file
`Submission/ArithmeticProgressionObstruction.lean` verifies an obstruction:

* `F` is the K4-free complete tripartite graph on `Fin 9`, with part labels
  `v.val % 3`. Its order interleaves the three parts.
* `collapse_0`, `collapse_1`, `collapse_2` give explicit rational linear
  certificates for the three possible fixed midpoint positions in every
  increasing triangle. Respectively they force
  `f 0 1 = f 0 2`, `f 0 1 = f 0 5`, and `f 2 3 = f 2 4`.
  Each equality collapses two labels of an actual triangle.
* `no_fixed_midpoint` combines these certificates for any rational vector
  space, with no dimension restriction.
* `TriangleRamsey G` states the ordered **triangle** Ramsey property for F
  with three colours.
* `no_AP_assignment_of_ramsey` proves that a graph with this Ramsey property
  cannot have nonconstant arithmetic-progression labels on all its triangles.
  Colour each triangle by the position of its midpoint, obtain a homogeneous
  ordered copy of F, and apply the linear certificate.

The finite clique-preserving ordered Ramsey existence theorem has NOT been
formalized in this file. The verified transfer is conditional on the stated
Ramsey property; no explicit finite Ramsey witness has been certified here.
All printed axioms of the new file are permitted.

Exploration artifacts: `/tmp/ap_cert.py` produced the rational certificates,
which were independently checked in Lean by the `module` tactic. A separate
exact rational backtracking program found no AP assignment for K5, but that
search is not a Lean theorem and K5 would not be a relevant K4-free witness.
The exploratory MILP runs for K5 and Paley-17 both timed out without a result.

The original theorem in `Submission/Spec.lean` remains unchanged and unproved.

## A positive two-colour triangle Ramsey reduction (Lean-verified)

`Submission/TriangleArrowReduction.lean` gives a genuinely sufficient
condition for a positive answer, but does not prove its Ramsey existence
hypothesis.

The finite blue target `W` is a K4-free odd wheel on `Fin 6`. Its apex is 3
and its rim is `0--4--1--5--2--0`, with the usual order on `Fin 6`.
`wheel_forces_mono` verifies that if the consecutive edges in every ordered
triangle of W have equal colours, then triangle `0,2,3` is monochromatic.
The proof uses exactly these five equalities:

* triangle 023: c02 = c23;
* triangle 034: c03 = c34;
* triangle 134: c13 = c34;
* triangle 135: c13 = c35;
* triangle 235: c23 = c35.

The infinite red target R is supplied by the previously verified shift-square
construction: R is K4-free, is countably triangle-free coverable, but has no
natural-number edge colouring that makes consecutive edges different in every
ordered triangle. `exists_red_target` verifies this formulation explicitly.

`TriangleArrow R G` means that every two-colouring of the ordered triangles
of G has either an increasing red graph copy of R or an increasing blue graph
copy of W. `no_cover_of_triangleArrow` proves that any graph G with this property
is NOT countably triangle-free coverable. Given a hypothetical cover, colour a
triangle blue exactly when its consecutive edges receive equal natural-number
colours. A red copy contradicts the defining property of R; a blue copy of W
forces a forbidden monochromatic triangle.

Important limitations:

* The existence of a K4-free G satisfying `TriangleArrow R G` is **not proved**.
* The red target is infinite and of large cardinality. A finite-target ordered
  Ramsey theorem cannot be substituted for the missing existence theorem.
* The embeddings in this reduction must preserve the displayed orders. In
  particular, the wheel argument is not valid with its apex arbitrarily moved
  to an extreme of the vertex order.
* No saturation argument for an arbitrary external colouring is assumed.

All four printed theorems compile with only the permitted axioms. The final
`Submission/Spec.lean` is still unchanged and still contains its original sorry.

## Countably complete reduced products (Lean-verified)

`Submission/CompleteFilterProduct.lean` now compiles, with built `.olean`.
Log: `/tmp/complete-filter-product.log`. All printed axiom lists use only
`propext`, `Classical.choice`, and `Quot.sound`.

For a proper filter F, `graph F G` has product vertices x and adjacency
`∀ᶠ i in F, (G i).Adj (x i) (y i)`.

Verified results:

* `positive_fibre`: a countable partition has an F-positive cell when F is
  proper and countably complete. Positivity means the infimum of F with
  the principal filter of the cell is nonbottom; it does NOT mean the cell
  itself belongs to F.
* `colorable_of_positive`: if the coordinates with chromatic number at
  most n+1 form an F-positive set, the whole reduced-product graph has an
  (n+1)-colouring.
* `finitely_colorable`: if F is countably complete and EVERY coordinate
  graph is finitely vertex-colourable (without a uniform bound), the
  reduced product is finitely vertex-colourable.
* `finite_coordinates`: arbitrary finite coordinate vertex sets are a
  special case, with NO restriction on the index cardinality.
* `countable_cover` and `quotient_countable_cover`: the triangle-free
  covering consequence, also for the graph defined using chosen quotient
  representatives. In the usual eventual-equality quotient adjacency is
  independent of representatives.

The proof chooses an ordinary ultrafilter below a positive restriction of
F and takes its finite-palette limits. The ultrafilter is NOT asserted to
be countably complete. No large-cardinal assumption is used.

This strengthens the planned finite-coordinate obstruction to arbitrary
finitely vertex-colourable coordinate graphs. It does not cover countably
incomplete filters or coordinates of genuinely infinite chromatic number.

## Countable-coordinate representation (Lean-verified)

`Submission/CountableCoordinateRepresentation.lean` now compiles, with
built `.olean`. Log: `/tmp/countable-coordinate.log`. All printed axioms
are permitted.

Verified construction for an arbitrary graph G and chosen vertex v0:

* The index set consists of all countable subsets s of V, ordered by
  inclusion. Its tail filter `fine V` is proper and countably complete,
  because a countable union of countable lower bounds is still countable.
* The coordinate vertex set is s union {v0}; its graph is the corresponding
  induced subgraph of G. All coordinate vertex sets are countable.
* A vertex x projects to itself when x belongs to s, and to v0 otherwise.
  The resulting function into the product gives a graph embedding
  `embedding G v0`; `project_adj_iff` proves exact recovery of adjacency.
* `product_cliqueFree` proves that proper-filter reduced products preserve
  all finite clique exclusions, using only finite intersections.
* `representation_cliqueFree` applies it to this representation.
* `no_cover_preserved` transfers any genuine non-coverability of G to
  this product.

Thus countably complete products with COUNTABLE coordinate sets include
representations of every possible witness. Replacing finite colourability
of coordinates by countability in the preceding obstruction would not be
a routine extension: a universal covering theorem for that larger family
would settle the original problem negatively.

This is a fine FILTER, not a fine countably complete ultrafilter. No
existence of such an ultrafilter is needed or claimed.

No proof or disproof of `erdos_595` has been obtained.
`Submission/Spec.lean` remains unchanged and still has its original `sorry`.

## Arc / biclique adjunction (Lean-verified)

`Submission/ArcAdjoint.lean` compiles, with built `.olean`.
Log: `/tmp/arc-adjoint.log`. All printed axiom lists use only the permitted
axioms.

Definitions in namespace `Erdos595ArcAdjoint`:

* `Arc G`: ordered pairs of adjacent vertices of G.
* `arcGraph G`: two arcs are adjacent when they concatenate in either order.
* `Biclique H`: ordered pairs (A,B) with A x B contained in adjacency of H.
  Empty sides are allowed; relevant edges require nonempty intersections.
* `right H`: adjacency of (A,B),(C,D) means both B intersect C and D intersect
  A are nonempty.

Verified:

* `toRight`, `fromRight`, `hom_iff`: existence of a homomorphism
  `arcGraph G -> H` is equivalent to existence of `G -> right H`.
* `unit`: every G maps to `right (arcGraph G)`.
* `right_not_cliqueFree_iff`: the right adjoint contains K_n iff the arc
  graph of K_n maps homomorphically into its base. For n=4 the test graph
  has 12 vertices.
* `arc_triangle`: every arc-graph triangle is a directed three-cycle.
* `arc_cliqueFree_four`: every arc graph is K4-free. In fact each
  neighbourhood is bipartite, by splitting successors from predecessors.
* `right_can_create_four`: K4-freeness is NOT preserved by the right adjoint
  in general; applying it to `arcGraph K4` produces a K4.
* `right_cover_of_rainbow`: if the base admits a countable vertex colouring
  making every triangle RAINBOW, its right adjoint is countably
  triangle-free edge-coverable.

The last proof chooses a base edge from the two intersection witnesses of
an adjoint edge and records the unordered pair of its endpoint colours.
Three adjoint edges forming a triangle yield a triangular prism in the
base. If all three recorded pairs coincide, the three vertices of either
base triangle have at most two colours, contradicting the rainbow condition.

The rainbow requirement must NOT be weakened to merely no monochromatic
vertex triangle. In particular the forward/backward split of arc vertices
is not enough for this criterion.

### Additional finite exploration (not Lean-certified)

`/tmp/arc_iter_check.py` found no homomorphism from `arcGraph K4` to the
5-rim or 7-rim odd wheel, but DID find one from the SECOND iterated arc
 graph of K4 to the 5-rim wheel. Thus iterative clique preservation cannot
be assumed merely from a first-step finite test. These are exploratory
computations, not declarations in the verified Lean files.

No proof or disproof of `erdos_595` has been obtained from this adjunction.

## Right adjoint of the shift-square graph: clique bound (Lean-verified)

The earlier finite K4-freeness tests of this family have now been replaced
by a proof for EVERY linear order and arbitrary cardinality.

The verified file is:

`Submission/ArcShiftCertificateChunked.lean`

It imports `ArcAdjoint` and `MiddleCornerObstruction`. Its built `.olean`
is present, and `/tmp/arc-shift-chunked.log` ends with permitted axiom lists
for both main declarations:

* `Erdos595ArcShift.no_arc_four`: the arc graph of K4 has NO homomorphism
  into `Erdos595MiddleCorner.graph A`, for every linearly ordered A.
* `Erdos595ArcShift.right_shift_cliqueFree`: the biclique right adjoint of
  that shift-square graph is K4-free.

The proof is an exact symbolic certificate, not a numerical extrapolation.
Each of the 12 source vertices maps to an increasing triple, yielding 36
coordinate variables. Every source adjacency has four possibilities:
forward one-step shift, forward two-step shift, or their reverses.
Each branch terminates in an explicit strict-order cycle, proved using
only equality substitution, transitivity, and irreflexivity.

A minimum-first-coordinate argument, with a permutation of the four source
vertices, normalizes one source arc. The reduced search has 889 decision
nodes and 2,668 contradictory leaves. For compilation performance it is
split into 385 private helper lemmas; the verified file has about 41,000
lines. The final axiom lists contain no `sorryAx`.

Development scripts:

* `/tmp/shift_symbolic_hom.py`: initial symbolic search (7,567 nodes).
* `/tmp/build_arc_shift_certificate_small.py`: minimum-normalized certificate.
* `/tmp/chunk_arc_shift_certificate.py`: generates the modular checked file.
* `/tmp/arc_shift_optimize.py`: exploratory proof-search ordering comparisons.

`ArcShiftCertificate.lean` and `ArcShiftCertificateSmall.lean` are earlier
monolithic development versions. Their long builds were either interrupted
or required a decidability elaboration fix. Use the CHECKED CHUNKED FILE,
not those drafts, as the verified dependency.

Lean elaboration detail: `by decide` does not automatically synthesize a
`Decidable` instance for adjacency of the defined arc graph. The concrete
finite source-adjacency proofs use `by simp [arcGraph]` instead. The finite
permutation lemma uses `decide +kernel` and only permitted axioms.

This closes ONLY the K4-preservation gap for this candidate. There is still
NO non-coverability theorem for its right adjoint. The previous finite
experiments finding two-piece covers through index size 10 do not prove
universal coverability, but equally must not be disregarded as evidence of
non-coverability. A possible finite-parameter classification of maximal
bicliques remains an unformalized idea, not an established theorem here.

## Two-piece cover for direct arc graphs (Lean-verified)

`Submission/ArcTwoCover.lean` compiles and has a built `.olean`.
Log: `/tmp/arc-two-cover.log`. `Erdos595ArcAdjoint.arc_two_cover` uses only
permitted axioms.

Order the original vertices and divide arcs into forward and backward.
Every arc-graph triangle is a directed three-cycle, so it is not entirely
within either vertex class. Cross-class edges form a bipartite graph;
within-class edges form a triangle-free graph. These are a two-piece cover.

Thus the direct arc construction cannot witness the conjecture, even though
it is always K4-free and can have very large ordinary chromatic number.

The main conjecture remains unresolved. `Submission/Spec.lean` has not been
changed and still contains its original `sorry`. No incomplete proof has
been submitted for verification.

## Finite-neighborhood and tuple-type obstructions (Lean-verified)

New checked files, all with built `.olean` files:

* `Submission/NoetherianNeighborhoods.lean` (153 lines)
* `Submission/FiniteBicliqueAdjoint.lean` (107 lines)
* `Submission/TupleTypeCover.lean` (206 lines)
* `Submission/ShiftBicliqueTransport.lean` (183 lines)
* `Submission/ShiftBicliqueCover.lean` (about 220 lines)

Logs:
`/tmp/noetherian-neighborhoods.log`, `/tmp/finite-biclique.log`,
`/tmp/tuple-type-cover.log`, `/tmp/shift-biclique-transport.log`,
`/tmp/shift-biclique-cover.log`.
All printed axiom lists contain only the three permitted axioms.

### Noetherian finite-coordinate topology

`Erdos595Noetherian.noetherian_pi_cofinite` proves that a finite product of
cofinite spaces is Noetherian. The proof considers a coordinate pushforward
of an ultrafilter: it is either pure, in which case its fixed value holds
eventually, or below the cofinite filter, in which case it converges to
every point. Finitely many coordinate conditions can be imposed on a point
of any given supporting set, proving every subset compact.

`finite_closed_intersection` proves that any intersection of closed sets
in a Noetherian space is a finite subintersection (compactness of the
complement).

`shift_finiteCommonNeighbors` applies this to the increasing-triple
shift-square graph. Its neighborhoods are finite unions of coordinate
equality cylinders in the induced finite-product cofinite topology.

The property `FiniteCommonNeighbors G` says every common neighborhood is
determined by finitely many of its defining vertices. It does NOT by
itself assert countable coverability.

`trace_has_common_neighbor` realizes any ultrafilter neighborhood trace
by a common neighbor in G, using finite determination and the finite
intersection property.

`ultrafilterFold` consequently gives a homomorphism from the mutual
ultrafilter extension back to G, when G is K4-free and satisfies finite
neighborhood determination. `ultrafilter_cover` pulls back covers.

### Finite-parameter right adjoint

Namespace `Erdos595FiniteBiclique`.
For the polarity `common G S`, the pair `(common S, common (common S))`
is a completed biclique. Under finite neighborhood determination every
biclique is contained in one of these with finite parameter S.

`finiteRight G` is the graph on finite subsets obtained from these
completed bicliques. `finiteToRight` and `rightToFinite` give homomorphisms
in both directions. `cover_iff` proves equivalent countable coverability.

### General order-type obstruction, now a theorem

Namespace `Erdos595TupleType`.

`homogeneous_three_to_four` replaces the earlier finite tuple-type tests
with a general theorem. For tuples indexed by ANY finite type I over an
infinite linear order A, if the three directed pair weak-order types of
x0,x1,x2 agree, then four tuples can be made with that same pair type.

Proof: prescribe a total preorder on four rows of coordinates, using the
uniform pair type. Any three row indices can be compressed into `Fin 3`,
so transitivity follows from the original three tuples. Antisymmetrize
the finite total preorder and order-embed the quotient into A.

`countable_cover` proves: a K4-free graph on `I → A` whose adjacency depends
only on the pair weak-order type is countably triangle-free coverable.
Sort each edge's endpoints by an arbitrary well-order of the tuple
vertices and colour by the finite pair type. A monochromatic triangle
would produce a K4 by the previous theorem.

The hypothesis `OrderTypeInvariant` is essential; it has NOT been shown
for arbitrary graphs. This theorem does not settle Erdős 595.

### Full right-shift candidate is now ruled out

**New main obstruction:**

```
Erdos595ShiftCover.right_shift_cover (A : Type*) [LinearOrder A] :
  Erdos595Work.IsCountableUnionOfTriangleFree
    (Erdos595ArcAdjoint.right (Erdos595MiddleCorner.graph A))
```

This is verified for EVERY linear order and cardinality, not merely a
finite experiment or a dense-order special case.

Proof stages:

1. Reduce to completed bicliques with finite parameter sets, as above.
2. Over a dense nonempty linear order without endpoints, show adjacency
   of these bicliques is invariant under the order type of their finite
   parameters. `ShiftBicliqueTransport.lean` uses finite partial order
   isomorphisms from `Order.PartialIso`; each can be extended to include
   any increasing triple on either side. This transports both common
   neighborhoods and double-common neighborhoods, including their
   universal quantifiers. No informal quantifier elimination assumption
   is used.
3. Encode a family of n triples as 3n scalar coordinates. Invalid codes
   are isolated in `codeGraph`. Its adjacency is pair-type invariant.
4. The verified `ArcShiftCertificateChunked.right_shift_cliqueFree` gives
   the K4 bound, so `TupleTypeCover.countable_cover` covers each fixed n.
5. Combine the countably many parameter-size pieces with the vertex-piece
   closure theorem from Work. This proves `right_shift_cover_dense`.
6. Embed arbitrary A in the lexicographic order `A ×ₗ ℚ`, which is dense
   without endpoints. The shift construction and the biclique right
   adjoint are functorial under the corresponding graph homomorphisms,
   so pull back the dense-order cover. Handle empty A separately.

Thus the earlier right-shift K4-freeness certificate cannot yield a
witness to the main conjecture. Do not revive this candidate as unresolved.

### Lean details learned

* The actual cofinite topology definitions are in
  `Mathlib/Topology/Constructions.lean`.
* A local `LinearOrder (I → A)` clashes with existing Pi lattice/order
  instances. The tuple covering proof uses a private structure wrapper
  for tuple vertices before imposing an arbitrary well-order.
* `Order.PartialIso.definedAtLeft/definedAtRight` and `.isCofinal` are
  convenient finite partial-isomorphism extension APIs.
* For lexicographic pairs, normalize `x.2` versus `(ofLex x).2` with an
  explicit `change` before `linarith`.

The conjecture in `Submission/Spec.lean` remains unresolved and unchanged,
with the original `sorry` at line 37. No incomplete submission was made.

## Countable sampling and finite-ultraproduct normal form (Lean-verified)

New files, with built `.olean` files and permitted axiom lists:

* `Submission/SampledFilterProduct.lean`
  Namespace `Erdos595SampledProduct`.
  Log: `/tmp/sampled-filter-product.log`.
* `Submission/FiniteUltraproductRepresentation.lean`
  Namespace `Erdos595FiniteUltraproduct`.
  Log: `/tmp/finite-ultraproduct-representation.log`.

### Countable sampling obstruction

`exists_sampler` proves that a proper countably generated filter F admits
`s : ℕ → I` with `Tendsto s atTop F`: choose one point from each member of
a decreasing countable basis.

`cover_of_sampler` proves that if such a sampler exists and every coordinate
graph has a proper countable vertex colouring, the reduced-product graph is
countably triangle-free edge-coverable. Record all sampled coordinate
colours as a sequence of naturals, then encode this sequence by a binary
sequence. Adjacent product vertices disagree at some sampled coordinate,
so this is a proper continuum-valued vertex colouring.

`countably_generated_cover` combines the two results. It applies regardless
of the cardinality of the original index set, and does not assume K4-freeness.

Do NOT confuse this hypothesis with merely having a countable index set.
Nonprincipal ultrafilters on countable sets need not be countably generated.
Countable-index products of countable carriers are independently ruled out
by the earlier cardinality argument in `CountableProductObstruction.lean`.

### Genuine finite-coordinate ultraproduct representation

Use `Finset V` as index set and the tail filter `fine V := atTop`.
`fineUltra V := Ultrafilter.of (fine V)` is an ordinary ultrafilter extending
this filter. At coordinate S, use the induced graph on `S ∪ {v₀}`, a finite
nonempty carrier. Project v to itself when v belongs to S and to v₀ otherwise.

Unlike the earlier countable-coordinate representation, this file passes
to the actual eventual-equality quotient `Filter.Product`, not just the raw
function space. `quotientGraph` uses `Quotient.out`; `quotientGraph_adj`
verifies that the resulting adjacency equals the usual eventual coordinate
adjacency on all representatives. Thus there is no unproved
representative-independence assumption.

Verified:

* `not_countably_complete`: any proper filter finer than `fine V` is NOT
  countably complete if V is infinite. Otherwise intersecting the eventual
  membership conditions of an injected copy of ℕ would put infinitely many
  distinct points in a finite coordinate set.
* `countable_of_sampler`: a sampler converging to such a fine filter forces
  V to be countable, since its countably many finite coordinate sets cover V.
* `embedding`: exact graph embedding of G into the quotient product.
* `quotient_cliqueFree`: all finite clique exclusions pass to this product.
* `no_cover_preserved`: any hypothetical witness remains non-coverable.
* `infinite_of_no_cover`: a non-coverable graph has an infinite vertex type.
* `finite_ultraproduct_iff`: the original existential proposition (using
  Work's definitionally identical covering predicate) is equivalent to the
  existence of a non-coverable ultraproduct of finite K4-free graphs, with
  arbitrary index type and ordinary ultrafilter.

This equivalence is NOT a construction of a witness. It explains why an
unrestricted finite-ultraproduct argument is already as hard as the
original problem. No external countable edge colouring has been assumed
internal, definable, measurable, or saturated.

### Remaining mathematical gap

For large index sets and ultrafilters without the preceding sampling or
completeness properties, no non-coverability result has been proved.
Finite Folkman obstructions and saturation of an uncoloured ultraproduct do
not, by themselves, handle arbitrary external countable edge colourings.
The normal-form theorem must not be presented as settling that gap.

`Submission/Spec.lean` is unchanged and still has its original `sorry` at
line 37. The main conjecture remains unresolved. No incomplete submission
was sent to the verifier in this continuation.

## Finite support compression fails, including at the third stage (verified)

This continuation revisited the stronger support-compression statement that
had remained unresolved after `SupportObstruction.lean`. It is now disproved.

File: `Submission/FiniteSupportObstruction.lean`
Namespace: `Erdos595FiniteSupport`
Build log: `/tmp/finite-support-obstruction.log`
All printed axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`.
The file builds without warnings or holes.

### The countable base

Start with the shift-square graph on increasing triples of natural numbers.
For each natural n, add an independent new vertex q_n whose neighborhood is

    S_n = {(a,b,c) : a ≤ n < b}.

Every S_n is independent in the shift-square graph: a forward edge requires
the next first coordinate to equal the previous second or third coordinate,
which is impossible when both triples cross the same cutoff n.
Consequently this base G is K4-free. Its vertex type is explicitly countable.

More strongly, G has a verified three-piece triangle-free EDGE cover:
1. Original one-shift edges;
2. Original two-shift edges;
3. All edges incident with the added independent q_n.

### The first-stage ultrafilters and second-stage trace

Let U be the free hyperfilter on the naturals. For each a, define p_a as the
iterated U-limit over b,c of the triple (a,b,c), restricting implicitly to
increasing coordinates. The Lean definition uses a total `triple` function
with maximums; on U-large tails it equals the specified increasing triple.

Let P be the U-limit of the first-stage principal ultrafilters at q_n.
For every a and all n ≥ a, p_a is adjacent to the principal ultrafilter at q_n.
Thus all p_a lie in the first-stage trace of the second-stage vertex P.

For any original triangle-free vertex set S, however,

    {a : S belongs to p_a} does NOT belong to U.

If it did, finite intersections of U-members select a<b<c<d<e such that
(a,b,c), (b,c,d), and (c,d,e) all belong to S. These three triples form a
shift-square triangle. This is the verified `not_large_support` argument.

If finitely many original triangle-free supports covered every p_a, U would
select one of those finitely many supports, contradicting this fact.
Hence the entire second-stage trace cannot be covered by finitely many
lifted original triangle-free sets.

### An explicit third-stage edge without original support

Let X be the U-limit of the second-stage principal ultrafilters at p_a.
In the third extension, X is adjacent to the principal ultrafilter at P.
Nonetheless, for EVERY original triangle-free S, the threefold lifted support

    {R : {p : S belongs to p} belongs to R}

does not belong to X. This follows from `not_large_support` by evaluating
the principal ultrafilters in the definition of X.

Thus the second-stage theorem that every nonisolated vertex has an original
triangle-free support definitely does NOT extend to the third stage, even
with finitely many original supports allowed.

This does NOT establish non-coverability. `third_stage_three_piece_cover`
explicitly proves that this third extension still has a THREE-piece
triangle-free EDGE cover, by iterating finite-cover preservation.

### Main verified declarations

* `G_cliqueFree`, `G_cover`
* `p_mem_trace`
* `not_large_support`
* `no_finite_triangleFree_support`
* `third_stage_edge`
* `third_stage_no_original_support`
* `piece_cliqueFree`, `three_piece_cover`
* `third_stage_three_piece_cover`

### Status and remaining routes

The general third-stage coverability question for countable bases with NO
finite triangle-free edge cover remains unresolved. The finite-support
compression route is now ruled out, not merely unsupported.

The bad-edge-ultrafilter / isolated-marginals lemma described in the earlier
continuation summary was not formalized in this continuation. It remains a
mathematically reasoned auxiliary obstruction, not a Lean-verified theorem.

`Submission/Spec.lean` remains unchanged, with its original `sorry` at line 37.
Its SHA256 remains
`de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45`.
The main conjecture has NOT been settled. No incomplete proof was submitted.

## Arc/right-adjoint round trip preserves coverability (Lean-verified)

File: `Submission/ArcRoundTrip.lean` (316 lines)
Namespace: `Erdos595ArcRoundTrip`
Build log: `/tmp/arc-round-trip.log`
The file compiles without warnings or holes. All printed axiom lists contain
only `propext`, `Classical.choice`, and `Quot.sound`.

New main results:

* `right_arc_cover`: if G has a countable triangle-free edge cover, then
  `right (arcGraph G)` has one too. NO clique-bound assumption is needed.
* `right_arc_cover_iff`: the converse holds by pulling a cover back along
  the previously verified unit homomorphism `G →g right (arcGraph G)`.

Thus this round-trip operation cannot turn a coverable base into a witness.
This is NOT a settlement of the conjecture.

### Proof structure

Vertices of `right (arcGraph G)` are ordered bicliques (A,B) in the arc graph.
They are covered by five classes:

1. A is a subsingleton;
2. B is a subsingleton;
3. Positive stars: there is v such that every arc in A ends at v and every
   arc in B starts at v;
4. Negative stars: there is v such that every arc in A starts at v and every
   arc in B ends at v;
5. Neither side is a subsingleton and neither star condition holds.

The first two classes map homomorphically to `arcGraph G`, which has a
verified two-piece triangle-free edge cover. Empty-side bicliques are
isolated, handled by an arbitrary fallback arc (or by the empty-arc case).
The two star classes map homomorphically to G by their centers.

The fifth class induces a triangle-free graph. In fact a triangle cannot
contain even TWO vertices from this class. Key facts:

* Adjacent arcs have at most one common neighbor in an arc graph.
* If one side of a biclique is not a subsingleton, the other side is independent.
* Two distinct arcs in A with the same head force a positive star, unless B
  is a subsingleton. The analogous same-tail condition forces a negative star.
* Outside all four special classes, head and tail maps are injective on both
  sides. Selecting the six crossing witnesses from a right-adjoint triangle,
  and using the two possible orientations of an arc-graph triangle, forces
  two adjacent arcs into an independent side.

A general private helper combines a finite cover by coverable induced
subgraphs using `Work.countable_union_of_vertex_pieces` and binary cuts.

### Additional finite exploration (NOT Lean-certified)

1. `/tmp/arc_reflect_four.py` tests whether a homomorphism
   `arcGraph K4 → arcGraph G` must force a K4 in G. It enumerates the two
   orientations of each of the eight source triangles and both choices for
   each of the six reverse-arc edges (16,384 cases), identifying the 24
   endpoint variables accordingly. Results: 16,256 cases force a loop;
   128 remaining cases force a K4. No counterexample was found.

   This gives a finite computational argument suggesting K4-reflection by
   the arc functor, but it has NOT been Lean-certified. Do not use it as a
   proved theorem in a final submission. The new coverability theorem above
   does not depend on this computation or on clique reflection.

2. A twice-right-adjoint shift candidate was examined. By iterating the
   adjunction, its K4 test is `arcGraph (arcGraph K4) → shiftSquare A`.
   Equivalently test `arcGraph K4 → right (shiftSquare A)`.
   `/tmp/arc_to_right_shift.py` enumerates completed bicliques of finite shift
   bases and performs the latter exact homomorphism search.

   No homomorphism was found for underlying order sizes 5,6,7,8,9,10,12.
   Size 12 had 970 completed nonempty bicliques and took about 368 seconds.
   The size-15 run was stopped without a result. No search remains running.

   These finite tests prove neither the infinite K4 bound nor non-coverability.
   The ONE-step right-shift candidate is already rigorously coverable by
   `ShiftBicliqueCover.right_shift_cover`; this new test concerns TWO steps.
   No right-adjoint iteration is entitled to assume clique preservation.

### Status

`Submission/Spec.lean` is unchanged and still contains the original `sorry`
at line 37. No proof or disproof of `erdos_595` has been found. No incomplete
submission was sent to the verifier in this continuation.

## Finite-palette compactness and twice-right finite reflection (Lean-verified)

File: `Submission/FinitePaletteCompactness.lean`
Namespace: `Erdos595FinitePalette`
Build log: `/tmp/finite-palette-compactness.log`
The file builds without warnings or holes; all printed axiom lists contain
only `propext`, `Classical.choice`, and `Quot.sound`.

### Verified results

`HasColoring G C` means that the unordered pairs of G have a C-colouring
with no monochromatic graph triangle.

* `HasColoring.comap`: these colourings pull back through graph homomorphisms.
* `HasColoring.countable_cover`: a countable palette gives the original
  triangle-free edge-cover predicate.
* `compactness` / `compactness_iff`: for a FIXED finite nonempty palette C,
  G has such a colouring iff every finite induced subgraph does.
* `right_finite_witness`: a finite graph mapping to `right H` already maps
  to `right (H.induce S)` for a finite subset S of the original base H.
* `rightMap`: right-adjoint functoriality (another local copy of this lemma).
* `right_compactness_iff`: a fixed finite palette works on the full `right H`
  iff it works on right adjoints of all finite induced base subgraphs.
* `right_twice_finite_witness`: the finite-witness statement also holds for
  TWO successive right adjoints, with the final finite subset in the
  ORIGINAL base graph.
* `right_twice_compactness_iff`: corresponding fixed-finite-palette equivalence.
* `shift_finite_order_witness`: a finite graph mapping to the shift-square
  graph over any linear order already maps to one over some `Fin n`.
* `right_twice_shift_of_uniform_finite`: a fixed finite palette working for
  `right (right (shiftSquare (Fin n)))` for EVERY n works for the candidate
  over EVERY linear order, of arbitrary cardinality.
* `right_twice_shift_finite_obstructions`: a non-coverable candidate would
  therefore require unbounded finite palette obstructions among these finite
  order instances.
* `finite_obstructions_of_right_no_cover`: the analogous one-step result.

These are reductions, NOT a proof that the required uniform finite bound
exists, and NOT a non-coverability proof. Finite-palette compactness must
not be extended to a countably infinite palette.

### Compactness proof

Choose a valid C-colouring for each finite induced base subgraph and extend
it arbitrarily to all unordered pairs. Take an ultrafilter extending the
tail filter on `Finset V`. Every pair has a unique ultrafilter-large colour
because C is finite. A monochromatic triangle in the limit would, after
intersecting finitely many ultrafilter members and the three vertex-membership
tails, give a monochromatic triangle in one of the finite colourings.

For finite right-adjoint reflection, retain one original-base intersection
witness for each directed edge of the finite source graph. Intersect every
biclique side with the finite set of retained witnesses. This preserves all
source adjacencies. Applying this twice proves the two-step version.

### Exact finite tests (NOT Lean-certified)

`/tmp/right_twice_shift_cover.py` enumerates completed nonempty bicliques at
two levels, then solves the not-all-equal triangle clauses. Found solutions
were checked directly against every clause. Results:

| underlying order n | second-level vertices | edges | triangles | two-piece cover |
|---|---:|---:|---:|---|
| 5 | 20 | 58 | 6 | yes |
| 6 | 88 | 700 | 124 | yes |
| 7 | 432 | 11926 | 3692 | yes |
| 8 | 2060 | 228506 | 104852 | yes |

No K4 was found in any of these finite graphs. The n=9 run was stopped as
its memory use grew; no n=9 result is claimed. Files
`/tmp/right_twice_shift_cover_{5,6,7,8}.txt` contain the finite data and colour
assignments. These computations do not supply the uniform hypothesis needed
by the verified compactness theorem.

Further exploratory tests:

* The base shift-square graph has a proper three-colouring for n=5,6 but
  NOT for n=7 (`/tmp/shift_three_color.py`). Thus the n=7,8 two-piece covers
  above are not explained merely by preservation of ordinary three-colourability.
* Colouring a right-shift edge by the one/two-shift type of its least selected
  base rung fails already at n=7 (`/tmp/right_shift_rung_color.py`).
* Repeatedly peeling triangles with private edges leaves a nonempty core
  at first level from n=8 and second level from n=6. Hence that simple
  peeling explanation of the two-piece covers does not work.
* `/tmp/shift_common_basis.py` found minimal common-neighbour determining
  sets of maximum size 4 in finite shift bases n=10,12,15. A uniform bound
  of 4 for arbitrary orders has NOT been proved. In particular, the earlier
  Noetherian finite-determination theorem does not itself give a uniform bound.
* `/tmp/arc_to_twice_right_shift.py` tested the THIRD-right clique obstruction
  by looking for `arc K4 → right² shift(Fin n)`. None was found for n=5,6,7;
  the n=8 run was stopped. No general third-step clique theorem follows.

No computation remains running.

### Additional guardrail from this exploration

Do not try to derive a witness by forcing the large shift-square target
into an arc graph. Arc graphs already admit a two-colour VERTEX colouring
with no monochromatic triangle (orient the arcs using a vertex order).
Recording the ordered pair of those two colours on graph edges gives the
middle-different rule for every vertex order. The large shift-square target
lacks that rule, so such a homomorphism cannot supply a witness.

An exact but non-Lean-certified endpoint-identification check additionally
found that even the triangles of shift-square `Fin 7` cannot all be rooted
as triangles in an arc graph (`/tmp/shift_arc_root.py`). This finite check
is not needed by any of the verified lemmas above.

### Status

The original conjecture remains unresolved. `Submission/Spec.lean` is
unchanged and still has `sorry` at line 37. No incomplete proof was submitted.

## Further right-adjoint structural tests (exploratory, not Lean-certified)

This continuation did NOT settle the conjecture and added no new verified Lean
proof. `Spec.lean` remains unchanged with its original `sorry`.

### Completed common-neighborhood basis search

The previously pending `/tmp/right_shift_common_basis.py` finished. For the
completed first-right shift graphs its exact intersection-closure calculation
found the following largest minimum determining-set sizes:

| underlying order n | distinct common neighborhoods | maximum minimum size |
|---|---:|---:|
| 5 | 22 | 2 |
| 6 | 90 | 2 |
| 7 | 434 | 3 |
| 8 | 2062 | 4 |
| 9 | 9734 | 6 |
| 10 | 40766 | 7 |

Log: `/tmp/right_shift_common_basis.log`.
Examples: `/tmp/right_shift_max_basis_N.txt`.
This refutes the proposed small numerical bounds, not every uniform bound.
It also does not refute finite determination for arbitrary infinite bases.

The n=9 example includes four bicliques indexed by a 2-by-2 grid. For fixed
central indices 3<5, their sides have the form

    A = {triples (t,l,3)} union {triples (5,r,t)}
    B = {(l,3,5)} union {triples (3,m,5)} union {(3,5,r)},

with l in {1,2} and r in {6,7}, together with two endpoint bicliques.
No exhaustive infinite biclique classification has been proved.

### Matched-pair SHADOW graphs, not edge-root graphs

A new exploratory base uses four-subset labels as VERTICES. For each ordered
sextuple a<b<c<d<e<f, make the three labels

    (b,d,e,f), (a,c,d,f), (a,b,c,e)

pairwise adjacent. This is different from the previously refuted proposal
that these labels be GRAPH EDGES. The old `RootCases` obstruction does not
by itself rule out right adjoints of these shadow graphs.

Script `/tmp/right_matched_shadow.py` enumerated completed nonempty bicliques
and then solved triangle NAE clauses for their right graphs:

| n | base vertices | displayed base triangles | right vertices | right edges | right triangles | K4 found | 2-color solution |
|---|---:|---:|---:|---:|---:|---|---|
| 6 | 15 | 1 | 6 | 9 | 2 | no | yes |
| 7 | 35 | 7 | 28 | 64 | 14 | no | yes |
| 8 | 70 | 28 | 122 | 549 | 56 | no | yes |
| 9 | 126 | 84 | 384 | 3472 | 168 | no | yes |
| 10 | 210 | 210 | 1030 | 17557 | 420 | no | yes |
| 12 | 495 | 924 | 5714 | 263907 | 1848 | no | yes |

For n=8,9,10,12, every first-right edge belongs to at most one triangle.
There are exactly twice as many right triangles as displayed base triangles.
The data files are `/tmp/right_matched_shadow_N.txt`, with log
`/tmp/right_matched_shadow.log`. These scripts use Sympy's SAT solver;
none of these computations is a Lean certificate.

The second iteration was tested by `/tmp/right_twice_matched.py`:

| n | second-right vertices | edges | triangles | K4 found | 2-color solution |
|---|---:|---:|---:|---|---|
| 6 | 18 | 57 | 6 | no | yes |
| 7 | 118 | 803 | 42 | no | yes |
| 8 | 1148 | 32078 | 168 | no | yes |
| 9 | 9032 | 1431654 | 504 | no | yes |

Log: `/tmp/right_twice_matched.log`.
Data: `/tmp/right_twice_matched_N.txt`.
These have exactly six times as many triangles as the displayed base family.
No general clique bound, local bipartiteness, or covering theorem for this
new family has been established. The finite results do not supply the uniform
hypothesis of `FinitePaletteCompactness`.

### Possible structural observation, NOT proved or formalized

For a base in which every edge has at most one common neighbor, consider the
additional property that every homomorphism from the triangular prism
`arcGraph K3` sends its two disjoint source triangles to the SAME target
triangle. Under that additional property, selecting the six crossing
witnesses of a right-adjoint triangle appears to force each of its bicliques
to have a singleton side. The singleton-side pieces map to the original
base, which could yield a covering theorem.

Do not assume this prism property from edge-disjointness of triangles alone:
`arcGraph K4` has edge-disjoint triangles but its right adjoint contains K4.
No theorem above verifies the prism property for all matched-pair shadows,
and no preservation under repeated right adjoints has been proved.

### Current status

All processes from this continuation have finished (PIDs 27697, 27827, 27864
are defunct, not running computations). No Lean build is running.
The conjecture is still unresolved. `Spec.lean` SHA256 remains
`de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45`.
No incomplete proof was submitted in this continuation.

## Bad-edge ultrafilter and adapted-limit failure (Lean-verified)

This continuation added two auxiliary files. Both build without warnings or
holes and their printed axiom dependencies are only `propext`,
`Classical.choice`, and `Quot.sound`. Neither settles Erdős 595.

### `Submission/BadEdgeUltrafilter.lean` (203 lines)

Namespace `Erdos595BadEdge`; log `/tmp/bad-edge-ultrafilter.log`.
The built olean is in `.lake/build/lib/lean/Submission`.

Definitions:

* `FiniteCover G`: finitely many triangle-free graphs cover every G-edge.
  The pieces need not be subgraphs, which is harmless after intersecting with G.
* `Avoids G D`: D is an ultrafilter on directed G-edges and contains the edge
  set of NO triangle-free graph on the original vertex type.

Verified results:

* `exists_avoiding`, `no_finite_cover_iff`: failure of FINITE covering is
  equivalent to existence of such an avoiding ultrafilter. The proof applies
  the ultrafilter lemma to complements of triangle-free edge sets, whose
  finite intersection property is exactly the no-finite-cover hypothesis.
* `endpoint_agreement`: for every vertex subset S, the two endpoints agree
  on membership in S D-almost everywhere. Otherwise D would contain the
  triangle-free cut determined by S.
* `marginals_equal`: the two endpoint marginals of D are equal.
* `marginal_ne_pure`, `marginal_le_cofinite`: the common marginal is
  nonprincipal. If it were pure at v, D would concentrate on the impossible
  directed loop (v,v).
* `neighborhoodPiece_cliqueFree`: in a K4-free graph, edges internal to any
  fixed vertex neighborhood are triangle-free.
* `neighborhood_not_mem`: that common marginal contains NO original
  neighborhood, since both endpoints in such a neighborhood would put a
  triangle-free edge set in D.
* `marginal_isolated`: the common marginal is therefore an isolated vertex
  of the mutual-Fubini ultrafilter extension.
* `FiniteCover.countable`: intersect the finite pieces with G and pad by
  empty graphs to obtain the original countable-cover predicate.
* `isolated_marginal_of_no_countable_cover`: the checked necessary condition
  for a hypothetical counterexample combines all the preceding conclusions.

IMPORTANT: the avoiding ultrafilter characterizes failure of finite covering,
NOT failure of countable covering. It cannot be used as a witness for the
original conjecture without another argument. In particular, an ultrafilter
can avoid each member of a countable cover.

This finally formalizes the bad-edge-ultrafilter / isolated-marginals lemma
that earlier continuation summaries repeatedly marked as unverified.

### `Submission/AdaptedLimitObstruction.lean` (173 lines)

Namespace `Erdos595AdaptedLimit`;
log `/tmp/adapted-limit-obstruction.log`.
The built olean is in `.lake/build/lib/lean/Submission`.

Main verified theorem: `exists_adapted_limit_failure`.

There are a TRIANGLE-FREE graph G, one fixed valid edge coloring c, and an
increasing sequence S_n of vertex subsets exhausting G, such that:

1. On G[S_n], the restriction of c admits an adapted vertex labeling f_n
   with f_n(v) < n+2.
2. On the full union G, c admits NO natural-number-valued adapted labeling
   at all (not merely no bounded one).

The edge colorings in this statement are coherent: they are restrictions of
one fixed c. It is the ADAPTED-LABELING invariant that fails at the limit.
The limiting edge coloring remains valid. G itself is triangle-free and
therefore is trivially countably coverable; this is NOT a counterexample to
Erdős 595.

Construction:

* X = {0,1}^N, with distinguished zero sequence z.
* d(x,y) is the least differing coordinate for unequal x,y.
* Define l(x,y)=0 when x=y, and l(x,y)=d(x,y)+1 otherwise.
* `label_no_adapted`: for every f:X->N, there are x,y (possibly equal)
  with f(x)=f(y)=l(x,y). If f ever takes value 0, use x=y. Otherwise apply
  the earlier binary diagonal lemma to f-1.
* Choose a triangle-free B with no proper coloring by X->N, using the
  previously verified arbitrarily-high-chromatic ordered shift construction.
* G is the blow-up on B x X, adjacent according to B alone; c on an edge
  is l of its two X-coordinates. An adapted labeling would give a proper
  (X->N)-coloring of B by the profiles at each base vertex, contradiction.
* S_n consists of all (v,z), together with (v,x) satisfying d(x,z)<n.
* On S_n, label (v,z) by n+1 and (v,x) for x!=z by d(x,z)+1.
  The latter value is <=n. For two nonzero sequences with equal such label,
  their first differing coordinate from each other cannot be their shared
  first nonzero coordinate (both bits there are 1). Equal sequences have
  edge label 0, whereas these adapted labels are positive. This verifies
  the adapted condition and the bound n+2.

Other checked declarations include `d_symm`, `d_spec`, `label_no_adapted`,
`stage_mono`, `stages_cover`, `stageLabel_bound`, and `stageLabel_adapted`.

Consequences for the transfinite approach:

* Do not assume bounded adapted labelings at every finite stage pass to a
  countable limit, even when all edge colorings are coherent and the whole
  graph is triangle-free.
* A particular construction might maintain a stronger invariant and still
  succeed; no theorem here excludes every transfinite construction.
* No general coherent covering theorem or genuine non-coverable construction
  was found in this continuation.

### Status

`Submission/Spec.lean` is unchanged and still contains its original `sorry`.
SHA256: `de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45`.
No proof or disproof of the original conjecture has been obtained, and no
incomplete proof was submitted. No computation or Lean build is running.

## Hilbert triangle hitting is strictly stronger in general (Lean-verified)

File: `Submission/HilbertHitStrictness.lean` (185 lines).
Namespace: `Erdos595HilbertStrictness`.
Log: `/tmp/hilbert-hit-strictness.log`.
It builds without warnings or holes, and all printed axiom dependencies are
only `propext`, `Classical.choice`, and `Quot.sound`. Its olean is built.
No completeness assumption on the real inner-product space is needed.

### Checked results

* `inner_sum_le_diagonal`: for a family with pairwise nonpositive inner
  products, the squared norm of any finite sum is at most the sum of the
  individual squared norms.
* `sum_sq_anchor_le`: if the family consists of unit vectors, has pairwise
  nonpositive inner products, and every vector has negative inner product
  with a fixed anchor u, then the finite sums of squared anchor products
  are bounded by inner(u,u).
* `countable_of_negative_anchor_unit`: the squared anchor products therefore
  form a summable family of strictly positive real numbers. Countability of
  its support implies the index type is countable.
* `countable_of_negative_anchor`: normalize nonzero vectors to remove the
  unit-vector hypothesis.
* `countable_of_pairwise_negative`: every pairwise strictly obtuse indexed
  family is countable. Fix one member as an anchor and apply the preceding
  result to all the other members.
* `countable_of_triangle_hit_complete`: if every three distinct indices
  contain a strictly negative pair, the whole index type is countable.
* `binary_not_countable`: Cantor's theorem applied to characteristic binary
  sequences proves that N -> Fin 2 is not countable.
* `coverable_without_hilbert_hit`: the complete graph on binary sequences
  has a countable triangle-free edge cover, but admits no Hilbert-space
  assignment hitting every triangle with a strictly negative pair.

### Proof of the triple lemma

On the index set make an auxiliary graph whose edges are distinct pairs with
NONNEGATIVE inner product. Under the no-all-nonnegative-triple hypothesis,
each neighborhood is a pairwise strictly obtuse family, hence countable.
The earlier verified locally-countable graph coloring theorem gives a proper
natural-number coloring of this auxiliary graph. Each color fiber is again
pairwise strictly obtuse and therefore countable. The entire index set is a
countable union of countable fibers.

### Scope and remaining gap

The separation example is a COMPLETE uncountable graph and contains K4.
It is NOT a counterexample to Erdős 595. It proves only that the Hilbert
triangle-hitting condition is not necessary for countable edge coverability
on unrestricted graphs.

It remains unproved whether every K4-free graph has a nonuniform strictly
negative triangle-hitting assignment. No counterexample to that restricted
claim was obtained, and no universal assignment was constructed. Earlier
finite obstructions still rule out fixed uniform margins, not this
nonuniform condition.

Speculation about infinite vertex-Ramsey constructions, saturated graphs,
or infinite asymmetric Ramsey transfer was NOT used in these proofs. No
new theorem asserting such an existence result was established.

`Submission/Spec.lean` remains unchanged with its original `sorry` and hash
`de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45`.
The original conjecture is still unresolved. No incomplete proof was
submitted, and no computation or Lean build is running.

## Restricted finite-tuple families (Lean-verified)

`Submission/RestrictedTupleCover.lean` now compiles, including the final
`pattern_family` addition. The proof no longer requires the full tuple space:
the family of tuple labels may be arbitrary, provided adjacency is relatively
order-type invariant among those labels.

`four_cycle_second_diagonal` proves that an order-type-homogeneous three-edge
path with a homogeneous shortcut has a homogeneous second diagonal, using
the four EXISTING tuples. It works for any coordinate type. Coloring each
ordered edge by its pair type and one Boolean (whether it extends to a later
homogeneous triangle) prevents monochromatic triangles in a K4-free graph.
`pattern_family` gives this palette explicitly. For finite coordinate type
it is finite; `countable_cover` packages the countable cover.
`induced_countable_cover` applies to arbitrary induced restrictions of an
order-type-invariant ambient graph; only the restriction must be K4-free.
Arbitrary edge deletions are NOT covered unless relative invariance remains.

The main conjecture in Spec.lean is still unresolved and unchanged.

## Finite descriptions and finite-prefix locality (Lean-verified)

File: `Submission/LocalTupleCover.lean`.
Namespace: `Erdos595LocalTuple`.
Log: `/tmp/local-tuple-cover.log`.
The file compiles without errors or warnings, its olean is built, and all
printed axiom dependencies are only `propext`, `Classical.choice`, and
`Quot.sound`.

Checked declarations:

* `cover_iSup`: countable unions of countably coverable edge subgraphs are
  countably coverable, by flattening the two natural-number indices.
* `cover_of_countable_fibers`: if a countable vertex partition has coverable
  INDUCED fibers, the whole graph is coverable. No compatibility of fiber
  colorings is needed. This packages the older binary-palette vertex-piece
  closure lemma, with isolated vertices handled by a homomorphism into a
  nonempty fiber (or the empty graph when there is no such fiber).
* `pairType_swap`: equality of tuple pair types is preserved by swapping
  both ordered pairs.
* `forced G v`: a subgraph with adjacency on a,b precisely when EVERY
  actual pair with the same tuple comparison type is adjacent in G. It is
  symmetric, loopless, a subgraph of G, and relatively order-type invariant.
* `forced_invariant`: the preceding invariance statement.
* `cover_of_finite_descriptions`: countably many finite tuple descriptions
  suffice if every edge is forced by at least one description. Descriptions
  need not be nested. Each forced subgraph is K4-free and covered by the
  restricted finite-tuple theorem; then flatten the countably many covers.
* `FinitelyLocal`: for countable tuple labels, every actual edge has some
  finite initial comparison pattern that forces adjacency for every actual
  pair with that pattern.
* `cover_of_finitelyLocal`: every K4-free graph with such a finitely local
  countable tuple labeling is countably coverable.
* `cover_of_finite_shapes`: partition vertices into countably many shapes,
  each carrying finite tuple labels with relatively order-type-invariant
  adjacency in its INDUCED graph. A K4-free graph of this kind is coverable,
  even with completely arbitrary CROSS-SHAPE edges.

Scope restrictions are important:

* Countable tuple labels by themselves do NOT suffice; the finite locality
  hypothesis has not been proved for arbitrary type-invariant relations.
* Arbitrary deletions of same-shape edges can destroy relative invariance.
* No general representation of arbitrary K4-free graphs by these schemes
  has been found.
* These are auxiliary covering theorems, not a settlement of Erdős 595.

One apparent structural lead in the older finite tables was checked and
rejected: the number of common-neighborhood sets of the first-right graph
is two more than the number of SECOND-right completed nonempty bicliques.
This is the usual polarity parameterization (the two omitted cases have an
empty side), not a coincidence with the first-right vertex count and not a
new simplification. For n=5,6,7,8, first-right vertex counts are 8,24,58,120;
second-right counts are 20,88,432,2060. No new computation establishes a
uniform palette bound for the twice-right candidate.

### Current task status

`Submission/Spec.lean` is unchanged and still has the original `sorry` at
line 37. No proof or disproof of `erdos_595` has been obtained. No incomplete
submission was sent to the verifier during this continuation. No build or
search is running.

## Triangle-fiber right-adjoint gluing (Lean-verified; route ruled out)

Two new files compile without errors or warnings. All printed axiom lists
contain only the permitted axioms. Neither settles Erdős 595.

### `Submission/TriangleFiberAdjoint.lean`

Namespace `Erdos595TriangleFiber`; log `/tmp/triangle-fiber-adjoint.log`.

* `TrianglesInFibers G f` means that the three vertices of EVERY G-triangle
  have equal f-values.
* `arc_four_triangle_constant` proves that a map on the 12 vertices of
  arc(K4) which is constant on every triangle is constant everywhere. Seven
  explicit oriented triangles connect all twelve arcs; finite cases are
  checked by Lean's ordinary proof-producing tactics.
* `right_cliqueFree_of_fibers`: if every triangle of G is in one fiber and
  the right adjoint of every induced fiber is K4-free, then right G is K4-free.
  A purported K4 gives an arc(K4) homomorphism to G, whose fiber label is
  constant by the preceding result. This factors through one fiber.
* `right_cliqueFree_of_hom`: right-adjoint K4-freeness pulls back through a
  graph homomorphism of base graphs.
* `glue H B c` has vertices (h,i), with edges either inside one H-copy,
  or across a B-edge between vertices of equal c-color. The c-palette may
  have arbitrary cardinality.
* `glue_triangles`: if c is proper on H and B is triangle-free, all glue
  triangles are within one H-copy.
* `right_glue_cliqueFree` applies the fiber theorem to this construction.
* `glue_cover` shows that the BASE gluing is coverable if H is coverable.
* `sourceHom R : arcGraph R ->g R` takes the first endpoint of an arc.
* `arcSourceGlue R B` specializes H to arcGraph R and c to its source map.
* `right_arcSourceGlue_cliqueFree` and the shift specialization
  `right_arcSourceGlue_shift_cliqueFree` certify K4-freeness of the proposed
  enlarged right-adjoint family.

This initially appeared to be a positive construction route. The companion
file below rules it out completely when the original right fiber is coverable.
Do NOT retain arcSourceGlue as an unresolved non-coverability candidate.

### `Submission/RightFiberCover.lean`

Namespace `Erdos595RightFiber`; log `/tmp/right-fiber-cover.log`.

* `restrict` restricts both sides of a base biclique to one induced fiber.
* `restrict_adj` preserves a right edge when its two intersection witnesses
  belong to the chosen fiber.
* `witness_fibers`: the six chosen intersection witnesses around a triangle
  p,q,r of right G form two triangles in G. Under triangle confinement their
  fiber labels have the pattern

      (p->q, q->r, r->p): i,i,i
      (q->p, r->q, p->r): j,j,j.

* `cover_of_fibers`: if every base triangle is confined to one fiber and the
  right adjoint of EVERY induced fiber is countably coverable, right G is
  countably coverable. There is NO cardinality bound on the fiber index set.
* `rightHom` is a local functoriality map obtained by composing the adjunction
  maps rather than repeating the image-of-biclique construction.
* `right_glue_cover` applies the preceding covering theorem to glue H B c.
* `right_arcSourceGlue_cover`: for EVERY triangle-free B, of any size or
  ordinary chromatic number, a coverable R gives coverable
  right(arcSourceGlue R B). It uses the already checked arc/right round-trip
  covering theorem.
* `right_arcSourceGlue_shift_cover` rules out the explicit shift specialization.

The covering proof uses a countable palette N + Bool. Well-order the fiber
indices and right-adjoint vertices. For an ordered edge, inspect the fiber
labels i,j of its two chosen intersection witnesses. If i=j, use the chosen
natural-number coloring of the right adjoint of fiber i on the restricted
bicliques. If i!=j, use the Boolean comparison i<j. The tag separates these
two cases. In a triangle the labels have the displayed pattern. In the
same-fiber case all three restricted edges lie in one valid fiber coloring;
in the different-fiber case the comparison on the long ordered edge is
reversed, so the three Boolean colors cannot coincide.

### Other exploration and status

The first-neighborhood-difference idea yielded no valid coloring theorem.
The asymmetric infinite-target triangle Ramsey existence statement remains
unproved. No new non-coverability argument was obtained.

`Submission/Spec.lean` remains unchanged with its original `sorry` at line 37.
No incomplete proof was submitted to the verifier during this continuation.
No search or build is running.


## Exact countably complete filter reformulation (latest continuation)

`Submission/CountableBadEdgeFilter.lean` compiles with allowed axioms only.
Namespace: `Erdos595CountableBadEdge`. Log: `/tmp/countable-bad-edge-filter.log`.

* `cover_of_countable_family`: arbitrary countable-index edge covers convert to
  the exact countable-supremum definition, after intersecting with G.
* `Avoids G F` means F contains the complement of EVERY triangle-free edge set.
  It is complement membership, not just failure of membership.
* `coveringFilter G := Filter.countableGenerate (generators G)` is the canonical
  countably COMPLETE filter generated by these complements. The construction
  does NOT assert a countable basis and it is NOT an ultrafilter.
* `coveringFilter_avoids`, `le_coveringFilter`, `avoids_coverable`,
  `no_cover_of_filter`, `coveringFilter_neBot_iff`, `no_cover_iff_exists_filter`:
  properness of this filter is exactly equivalent to non-coverability.
  This is a reformulation, NOT a construction of a proper avoiding filter.
* `endpoint_agreement`, `marginals_equal`: its endpoint marginals agree.
* `countable_labels_agree`, `binary_labels_agree`, `no_binary_coloring`: properness
  forces equal endpoint labels eventually for every countable/binary-sequence
  labeling, and rules out a vertex coloring by binary sequences.
* `avoids_neighborhood`, `avoids_countable_neighborhoods`: for K4-free G, both
  endpoints avoid every fixed countable union of original neighborhoods.
* `large_graph_no_cover`: every graph containing an F-LARGE set of original
  edges is non-coverable. F-positive alone is insufficient for this argument.

Do not extend the filter to an ultrafilter and assume completeness survives.
No witness to properness for a K4-free graph has been obtained.

## Stronger complete-filter product obstruction (verified)

`Submission/CompleteFilterEdgeCover.lean` compiles successfully.
Namespace: `Erdos595CompleteFilterEdgeCover`.
Log: `/tmp/complete-filter-edge-cover.log`.
All printed axiom lists contain only propext, Classical.choice, Quot.sound.

* `CoversWith G n` is a triangle-free edge cover with n pieces.
* `cover_of_positive`: if n pieces suffice at each coordinate in an F-POSITIVE
  set S, then n pieces suffice for the whole F-product graph. Extend
  F restricted to S to an ordinary ultrafilter U, and take U-limits of the
  finitely many coordinate edge pieces. Finite intersections reflect any
  purported monochromatic triangle back to a good coordinate.
* `finite_cover`: if F is proper and countably complete and EVERY coordinate
  graph has SOME finite triangle-free edge cover, the product itself has a
  FINITE triangle-free edge cover. No uniform coordinate bound is assumed.
  Countable completeness gives a positive fiber of the natural-valued bound.
* `countable_cover` is the immediate corollary.

This strengthens CompleteFilterProduct, which required finite VERTEX
colorability at each coordinate. No countable completeness of the auxiliary
ultrafilter is asserted or used. It does NOT cover arbitrary countably
coverable coordinates: a countable graph may have no finite edge cover.

Other discussion in this continuation supplied no new settlement. In
particular, saturation does not internalize arbitrary external color classes;
finite-palette compactness cannot supply countable-palette compactness; and
properness of the canonical countably complete avoiding filter remains the
missing issue. The network reference lookup still fails at DNS resolution.

The original conjecture in Spec.lean remains unchanged and unproved.

## Delayed ultrafilter fibers (Lean-verified)

`Submission/DelayedUltrafilter.lean` compiles with permitted axioms only.
Namespace: `Erdos595DelayedUltrafilter`; log: `/tmp/delayed-ultrafilter.log`.

Given G, the base `delayed G` has vertices ((v,n),i) and adjacency

    G(v,w) and n != m and m < i and n < j.

It is K4-free when G is, and is countably vertex-colorable by n. It is
countable when G is countable. Let U be a free ultrafilter on N.

    first(v,n) = lim_i ((v,n),i),
    second(v)  = lim_n first(v,n).

* `first_fubini`, `first_adj`: the first vertices induce levelGraph G in
  the first mutual extension.
* `second_fubini`, `secondHom`, `second_injective`, `secondEmbedding`:
  the second vertices give an INDUCED graph embedding of G into the
  second mutual extension of delayed G.
* `flatten := P.bind id`, with `mem_flatten` giving membership explicitly.
* `flattened_neighborhood_empty`, `flattened_trace`: flatten(second(v))
  contains NONE of the original neighborhoods of delayed G. For a fixed
  original ((w,m),j), adjacency to ((v,n),i) requires n<j; the outer free
  ultrafilter rejects that bounded set.
* `cover_of_empty_trace_fiber`: proving coverability of this whole empty-trace
  fiber for every base would imply coverability of the arbitrary input G.
* `empty_trace_fiber_can_contain_triangle`: an explicit Fin 3 input gives a
  countable delayed base whose empty flattened-trace fiber has a triangle.

Separate useful general lemma:
* `flatten_ne_of_adj`: for any K4-free base, adjacent SECOND-stage vertices
  P,Q have different flattened ultrafilters. If flatten(P)=flatten(Q), the
  first adjacency gives P-almost every p a P-large set of q with R(q,p).
  Four successive choices form six directed Fubini adjacencies, contradicting
  base K4-freeness. This does NOT make flatten a graph homomorphism.

Distinguish equality of flattened ULTRAFILTERS from equality of their original
NEIGHBORHOOD TRACES. The former separates edges at stage two; the latter can
have triangles and, for arbitrary bases, arbitrary K4-free induced subgraphs.
No universal countable-base third-stage covering or non-covering theorem has
been proved.

## Symbolic Pasch check (exploratory, NOT a Lean certificate)

`/tmp/matched_pasch_symbolic.py` checks the old matched-pair hypergraph pattern
symbolically, independent of index-set size. A putative Pasch configuration
has four hyperedges, whose six shared labels form the edge incidence pattern
of K4. Assign its three face roles at each hyperedge (6^4 cases), identify the
four coordinates of each shared label, and test strict-order consistency.
Results: 1290 order contradictions, 6 cases with collapsed labels, 0 cases
with six distinct labels. Thus this computation rules out the proposed
Pasch-only explanation for this candidate's chromatic behavior. It has not
been translated into a kernel-checked proof and is not used by any theorem.

Other ideas discussed (saturation, finite-template Ramsey transfers, affine
representations, tree-metric colorings) yielded no complete covering theorem
or non-coverable K4-free graph. In particular, a proposed universal tree
coloring must not secretly imply the already-refuted universal
MiddleDifferent coloring property.

Spec.lean is still unchanged and contains its original sorry. No incomplete
submission was sent to the verifier during this continuation.

## F₃ linearization obstruction (new, Lean-verified)

`Submission/F3Obstruction.lean` compiles. Namespace `Erdos595F3Obstruction`.
Log: `/tmp/f3-obstruction.log`. Only permitted axioms appear.

The proposed assignment sends each graph edge to a vector in an arbitrary
F₃-vector space and requires the three vectors on every triangle to sum to
zero without collapsing. This would have supplied a countable cover by
coefficient-pattern coloring, but the assignment does not exist universally.

* `collapse`: on the existing K4-free Paley graph on 17 vertices, a linear
  combination of 53 triangle equations forces f(0,1) = f(0,2).
* `no_assignment`: the triangle (0,1,2) therefore violates nondegeneracy.

The exploratory exact Python calculation in `/tmp/triangle_f3.py` finds rank
67 for the 68-by-68 unsigned triangle/edge matrix over F₃, so all solutions
are constant. The Lean theorem only uses and certifies the specific displayed
collapse, not the full rank claim. Certificate generator: `/tmp/f3_cert.py`.
`match_scalars <;> decide` verifies the characteristic-three coefficients;
plain `module` fails because its final `ring` step does not reduce modulo 3.

## Order-oriented Fubini extension (new, Lean-verified)

`Submission/OrderedUltrafilter.lean` compiles. Namespace
`Erdos595OrderedUltrafilter`. Log: `/tmp/ordered-ultrafilter.log`.
All printed axiom lists contain only propext, Classical.choice, Quot.sound.

Fix ANY linear order on `Ultrafilter V`. Define

    graph G:  p ~ q iff
      (p < q and fubiniAdj G p q) or
      (q < p and fubiniAdj G q p).

This differs from both the mutual extension and the unrestricted OR extension.

* `adj_of_lt`: ordered adjacency is exactly the forward Fubini relation.
* `cliqueFree_four`: preserves K4-freeness. Sort the four clique vertices;
  the six forward Fubini adjacencies contradict Work.no_four_fubini.
* `cliqueFree_three`: preserves triangle-freeness.
* `mutual_le`: every mutual extension is a subgraph of this extension.
* `trace_coloring`: original neighborhood traces properly vertex-color it.
* `countable_base`: consequently, ONE extension of a countable base is
  countably coverable, for every chosen order.
* `finite_iSup`: finite suprema commute with the extension exactly.
* `finite_cover`: finite triangle-free edge covers persist with the same bound.
* `pureEmbedding`: the original graph embeds as an induced subgraph.

No non-coverability theorem was obtained. A SECOND or later order-oriented
extension of a countable base WITHOUT a finite edge cover is not ruled out
by these results. The older proof for two MUTUAL extensions must not be
silently applied to this larger construction. No preservation of countably
infinite suprema or covers has been proved.

Other discussion in this continuation (online colorings, generalized tree
patterns, saturated models, finite-positive-index quadratic forms) yielded
no settlement. The measurable-disjointness theorem already rules out the
quarter-measure boundary case too; it requires only positive measure, not
a uniform strict gap above one quarter. Do not revive that candidate.

`Submission/Spec.lean` remains unchanged with its original sorry. These two
new auxiliary files are NOT a proof or disproof of the original conjecture.

## Triangle-bearing third-stage support failure (new, Lean-verified)

`Submission/ThirdTriangleSupportObstruction.lean` compiles. Namespace
`Erdos595ThirdTriangleSupport`. Log: `/tmp/third-triangle-support.log`.
All printed axiom lists contain only propext, Classical.choice, Quot.sound.

This strengthens FiniteSupportObstruction: restricting attention to vertices
that actually lie in triangles does NOT rescue original-support compression.

Construction: start with the countable shift-square/cutoff-apex base G from
FiniteSupportObstruction. Add a second independent apex family C_m. Its old
neighborhood is all first-family apices, together with the cutoff triples
whose first coordinate is <= m and whose second coordinate is > m. Each
such neighborhood is bipartite: the cutoff triples are independent, and the
old apices are independent. Thus the enlarged countable base H is K4-free.
The two apex families are completely joined to one another.

Let p'_a be the image of the old p_a in the first extension. Let P' and Q'
be second-stage ultrafilters obtained by taking free limits of the principal
vertices from the two apex families. Let X' be the third-stage free limit of
the second-stage principal vertices at p'_a.

* `secondCutoff_triangleFree`, `H_cliqueFree`, `H_cover`.
* `p'_old_apex`, `p'_new_apex`: both cutoff families approach p'_a.
* `P'_neighbor`, `Q'_neighbor`, `P'_Q'`.
* `third_triangle`:

      H₃.Adj X' (pure P') and H₃.Adj X' (pure Q') and
      H₃.Adj (pure P') (pure Q').

* `no_original_support`: for EVERY triangle-free original vertex set S,
  X' does not contain its threefold lifted support. Pull S back to the old
  base and apply FiniteSupport.not_large_support.
* `third_stage_four_piece_cover`: nevertheless H₃ has a FOUR-piece
  triangle-free edge cover. Three pieces come from the old base; the fourth
  covers the new independent extension. Finite covers persist through all
  three mutual extensions.

Consequently neither a third-stage nonisolated point NOR a third-stage
triangle-bearing point without original support proves non-coverability.
Do not revive the idea that all third-stage vertices lying in triangles have
one original triangle-free support.

No proof/disproof of Erdos595.erdos_595 was obtained. Spec.lean remains
unchanged and retains its original sorry. The reference website was retried
and remains unreachable (DNS failure). Other theoretical discussion in this
continuation supplied no theorem about generic/saturated graphs, forcing,
online colorings, or Cayley constructions.

## Disjoint quadruple right adjoints: classified and ruled out (new)

The latest candidate direction was disjoint quadruple order-type graphs.
Vertices are strictly increasing 4-tuples; adjacent tuples have disjoint
coordinates and one of specified binary interleaving words (first symbol 0).
The sorted list of 35 words is indexed from 0, and family masks use 1 << index.

Exploratory exact programs (NOT Lean certificates):

* `/tmp/disjoint_type_candidates.py`: triples. Only individually triangle-free
  type is 001011; no disjoint-triple type family has triangles but excludes K4.
* `/tmp/disjoint_four_types.cpp` and binary `/tmp/disjoint_four_types`:
  5,775 three-tuple order words and 2,627,625 four-tuple words. It found 45
  small triangle-bearing type families avoiding K4.
* The 8 individually triangle-free quadruple types are indices
  1,2,5,6,7,8,16,33, words respectively
  00010111,00011011,00100111,00101011,00101101,00101110,01001011,01110100.
* `/tmp/disjoint_arc_sat_all.py`, `/tmp/disjoint_arc_256.py` encode
  arc(K4) homomorphisms by total orders on the 48 coordinate positions.
  The latter tested all 247 subsets of size at least two of those eight types.
  Logs: `/tmp/disjoint_arc_sat_all.log`, `/tmp/disjoint_arc_256.log`.
  The maximal UNSAT masks are 102, 480, 65728, 8590000196.
  Masks 480 and 8590000196 are triangle-free. Thus the only maximal
  triangle-bearing survivors in this search are:

      102:   00010111, 00011011, 00100111, 00101011
      65728: 00101011, 00101101, 01001011.

The CaDiCaL binary is bundled with Lean:
`/root/.elan/toolchains/leanprover--lean4---v4.27.0/bin/cadical`.
These SAT calls take fractions of a second. SAT outputs have explicit checked
Python homomorphism witnesses. UNSAT outputs have NOT been replayed in Lean.

Both surviving candidates are now ruled out by a GENERAL LEAN THEOREM,
independent of their clique certificates or the SAT classification:

### `Submission/NoAlternatingBiclique.lean` (verified)

Namespace `Erdos595NoAlternating`, about 212 lines.
Log `/tmp/no-alternating-biclique.log`.
Printed axioms: only propext, Classical.choice, Quot.sound.

`NoAlternating G` means there are no a<b<c<d with edges ab,bc,cd,da.
`right_cover`: the biclique right adjoint of ANY such ordered graph has a
countable triangle-free edge cover. No cardinality bound, definability,
finite-support assumption, or clique hypothesis is used.

Proof:
* `inner_or`: every complete biclique has one side A such that every point
  of the other side B lies wholly before or wholly after A. Otherwise two
  opposite interleavings produce an alternating C4.
* `cut A` is the strict lower cut of A, a member of `LowerSet V`.
* Within the class whose first side is inner, adjacent vertices have distinct
  lower cuts. A four-cycle increasing in those cuts yields an alternating
  four-cycle of intersection witnesses in the original graph.
* `cover_of_label` uses direction and extension flags to cover graphs whose
  linearly ordered labels forbid alternating C4s. Palette is a product of
  three Bool values (the statement is phrased as countable coverability).
* Swap the biclique sides for the other class and combine the two vertex
  classes using the existing vertex-piece covering theorem.
* `right_cover_of_label` handles possibly noninjective ordered labels, as
  long as adjacent base vertices have distinct labels. Ties are broken with
  a well-order using a lexicographic linear-order lift.

This rules out EVERY right-adjoint candidate admitting a no-alternating-C4
order, not just the two particular quadruple families.

### `Submission/DisjointQuadrupleCover.lean` (verified)

Namespace `Erdos595DisjointQuadruple`, about 100 lines.
Log `/tmp/disjoint-quadruple-cover.log`.
Printed axioms: only the permitted three.

We use larger, relaxed graphs, omitting all inessential coordinate-distinctness
conditions. For x=(a,b,c,d), y=(e,f,g,h):

* `conjunction` (mask 102): b<e<d<g and c<f.
* `disjunction` (mask 65728): a<e<c<f<d<h and (b<e or d<g).

The graphs symmetrize these forward relations. Both have first-coordinate
labels with no alternating C4. Hence `conjunction_right_cover` and
`disjunction_right_cover` hold for EVERY linear order, including orders with
large ascending AND descending segments. Infinite staircase profiles in the
second candidate do not evade the new theorem.

The original strict-interleaving graphs are subgraphs of these relaxed graphs,
so their right adjoints also pull back such covers. Do not silently infer the
relaxed graphs' K4 exclusion just from the SAT test; no such exclusion is
needed for these cover theorems.

Other exploratory calculations, now unnecessary for these candidates:
* `/tmp/disjoint_right.py` and `/tmp/disjoint_right_tri.py`: finite right
  adjoints for mask 65728 on 12,14,16 points admit 2-edge-colorings avoiding
  monochromatic triangles. At n=16 there are 71,568 concepts, 25,986
  triangle-relevant concepts, and 651,926 right triangles. This is only
  finite evidence, not a proof of a uniform two-color theorem.
* The finite right adjoints tested have bipartite neighborhoods. No general
  local-bipartiteness theorem was proved (and is not needed for right_cover).
* `/tmp/disjoint_prism.py`: every individual type admits a triangular-prism
  homomorphism with all three matching edges of that type. Thus coloring
  right edges solely by the type of two chosen intersection witnesses fails.
* `/tmp/disjoint_anchor.py`: adding one pair of arbitrary anchors to each
  biclique does not make the naive full pair-order-type coloring valid.
* `/tmp/disjoint_core.py`: three core bicliques with independent first sides
  CAN form a right triangle. Do not claim that class is triangle-free.
* `/tmp/no_alt_arc_general.py`: exploratory UNSAT for no-alternating orders
  on arc(K4), arc(W5), arc(W7), arc(W9), arc(Paley17), and arc(arc(K4));
  SAT for arc(W6) and arc(K4 minus an edge). No general equivalence with
  local bipartiteness or preservation of no-alternation by right was proved.

`Submission/Spec.lean` remains unchanged and still contains the original
sorry. These new obstruction theorems do NOT settle Erdős 595.

## New five-coordinate search (exploratory; NOT yet ruled out)

After the quadruple obstruction above, the search was extended to disjoint
increasing 5-tuples. Scripts and data:

* `/tmp/disjoint_five_types.cpp` and binary: enumerate 126,126 three-vertex
  order words, giving 105,830 type-family masks. There are 45 individually
  triangle-free 5-tuple types (out of 126 types) and 1,093 minimal
  triangle-bearing families consisting only of such types.
* Data `/tmp/disjoint_five_results.txt`, `/tmp/disjoint_five_timing.txt`.
* `/tmp/disjoint_five_sat.py`: for each family, first test an alternating C4
  in first-coordinate order. Skip UNSAT families by the new cover theorem.
  Then test arc(K4) homomorphism on 60 distinct coordinate positions.
  Exact exploratory totals: 277 excluded by first-coordinate no-alternation,
  488 admit arc(K4) homomorphisms, 328 survive both tests.
  It took 38.4 seconds. No UNKNOWN cases. Log `/tmp/disjoint_five_sat.log`.
* Survivors `/tmp/disjoint_five_survivors.txt`.
* Projecting away one fixed coordinate into a surviving quadruple family
  eliminates 66 of the 328. Remaining list:
  `/tmp/disjoint_five_no_quad_projection.txt` (262 rows).
* `/tmp/five_other_coords.py`: testing no-alternating C4 using coordinates
  1,2,3,4 as labels eliminates 35 more. Final current list:
  `/tmp/disjoint_five_no_coordinate_cover.txt` (227 rows).

There are exactly TWO two-type families left in this filtered search:

1. mask 134217730:
       0000101111, 0010101011
   Triangle order word: 001010210212122.
2. mask 9223372036854775936:
       0001010111, 0100101101
   Triangle order word: 010021012102212.

Both admit alternating C4s with respect to EVERY individual coordinate, and
neither has a fixed-coordinate projection into the covered quadruple families.
Neither currently has a non-coverability proof, nor a Lean clique certificate.
Do not interpret this finite classification as a solution to Erdős 595.

`/tmp/five_selected_tests.py` gives further exact SAT observations:
* Family 1 admits an ordered C4 but no ordered C5 (or C6,C7,C8) in
  first-coordinate order. For a forward edge x<y, it forces
  x[4] < y[3] (or even x[4]<y[1]); chaining four forward edges puts the
  last first-coordinate above the first last-coordinate, contradicting
  the closing edge. Thus a simple algebraic no-ordered-C5 proof is available.
* Family 2 admits ordered C4,C5,C6,C7,C8 in first-coordinate order.
* BOTH admit an alternating K2,2 but no alternating K3,3 or K4,4 in
  first-coordinate order (SAT evidence only).

Family 1 is a strict-inequality thickening of the old equality shift-square.
An exploratory embedding sends a triple (a,b,c) to
   ((a,-2),(a,2),(b,0),(b,3),(c,1))
in a lexicographically expanded linear order. A one-step shift gives type
0010101011, and a two-step shift gives 0000101111. This reasoning has NOT yet
been formalized. The old equality-shift right-cover theorem does NOT transfer
in the direction needed: a subgraph of a coverable base can transfer a cover,
but here the new base contains the old one, not conversely.

Possible next mathematical question: does bounded alternation of biclique
sides (e.g. forbidding alternating K3,3) give a general right-adjoint cover
criterion, extending NoAlternatingBiclique? This is UNPROVED. Splitting each
biclique into finitely many run pieces does NOT automatically lift triangles
consistently; finite-fiber quotients can create arbitrary triangles (compare
bipartite double covers). Do not use that invalid shortcut.

No process from these searches is still running (PID 34815 finished).
Spec.lean is unchanged, SHA256
  de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45.

Additional final notes from the same continuation:
* `NoAlternatingBiclique.right_cover_of_base_hom` was added and checked. It
  transports a cover along the right adjoint of any base homomorphism, using
  `toRight (f.comp (fromRight Hom.id))` and the existing cover pullback.
* `DisjointQuadrupleCover.conjunction_right_cover_of_le` and
  `disjunction_right_cover_of_le` explicitly check coverability for every
  stricter base subgraph. Both files were rebuilt successfully after adding
  these lemmas.
* `/tmp/arc_reflect_four.py` found no homomorphism arc(K4) -> arc(W5),
  arc(W7), or arc(Paley17), using finite-domain SAT. This does NOT establish
  that arc reflects K4-freeness for all graphs. No general reflection theorem
  or countable-cover preservation for arbitrary right adjoints was obtained.

## Subsequent odd-wheel and parity tests (exploratory, not Lean certificates)

`/tmp/five_arc_wheel.py` finds homomorphisms from arc(W5) and arc(W7) into
BOTH remaining two-type five-coordinate candidates. The source is not
vertex-transitive: the invalid global-first-coordinate symmetry break was
removed for these tests. Thus both right adjoints contain odd wheels and
are not locally bipartite.

`/tmp/five_cycle_color.py` finds triangles with type multiset (0,1,1), not
(0,0,1), in each candidate. It also finds four-cycles of types (0,0,0,1)
and (0,1,1,1). An even-parity potential on biclique four-cycles is therefore
not available.

Warning on bounded biclique alternation: for ANY base G, two arcs p,q
with distinct tails have common neighbors a only with a.tail=p.head or
a.tail=q.head. Indeed adjacency says a.head=p.tail or a.tail=p.head,
and likewise for q; the two head alternatives contradict distinct tails.
There cannot be three common neighbors with distinct tails. Ordering arcs
primarily by tails therefore precludes alternating K3,3 for every G.
Hence bounded alternation alone cannot imply right-adjoint coverability:
such a theorem would cover the right adjoint of arc(K) for huge complete K,
but K maps into that adjoint. Adding K4-freeness could make such a proposed
criterion as hard as the original question. This guardrail is not yet
formalized and is not a proof of either side of Erdős 595.

## Arc/right K4 reflection (new Lean-verified result)

`Submission/ArcRoundTrip.lean` now also proves:

* `common_tail_two`, `common_tails_three`: the bounded-tail common-neighbor
  guardrail above. The first is axiom-free, the second uses only propext.
* `right_arc_cliqueFree`: G K4-free implies right(arc G) K4-free.
* `right_arc_cliqueFree_iff`: the converse follows from the unit homomorphism.
* `arc_four_hom_iff`: arc(K4) -> arc(G) exists exactly when G contains K4.

Proof of preservation: a K4 in the right graph has no singleton-side biclique,
since a singleton side would give a K4 in the base arc graph. Each remaining
biclique is Pos, Neg, or Good using the previous classification. A Good side
has at most two elements, by tail/head injectivity and adjacency to one
opposite-side arc. Two Good vertices cannot occur in a triangle. Mixed Pos/Neg
triangles are impossible, since mixed edges identify centers whereas same-
orientation edges have distinct adjacent centers. Therefore a hypothetical
Good vertex in a K4 has three same-orientation neighbors with three distinct
side elements, a contradiction. All four bicliques consequently have the same
orientation and their centers form a K4 in G.

Build log `/tmp/arc-reflection.log`: no errors, all audited axioms permitted.
Backup before this addition: `/tmp/ArcRoundTrip.before_reflection.lean`.
Together with the older `right_arc_cover_iff`, both conjecture conditions are
preserved and reflected by this round trip. This is NOT a settlement: it
cannot create a witness from a covered graph.

`no_alternating_five` was also added to ArcRoundTrip and compiled: if five
arc tails increase, the alternating K3,2 pattern (three common neighbors
of the other two) is impossible. It uses `common_tails_three`. Thus even
that stronger five-vertex forbidden ordered pattern occurs for arc bases
of arbitrary G; no universal right-cover theorem based only on this
pattern can work.

This continuation obtained no proof or disproof of the main conjecture.
`Spec.lean` remains unchanged, with its original sorry and SHA256
`de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45`.
No build or search remains running.

## Two five-coordinate SECOND right adjoints are ruled out (new, Lean verified)

`Submission/FiveTupleIterationObstruction.lean` compiles. Namespace
`Erdos595FiveIteration`, about 239 lines. Log `/tmp/five-iteration-lean.log`.
Both printed axiom lists contain only propext, Classical.choice, Quot.sound.

The file defines the exact strict-disjoint-order base graphs on natural
five-tuples for the two surviving type pairs:

* H1: 0000101111 OR 0010101011.
* H2: 0001010111 OR 0100101101.

Full interleaving chains are used, so edges have increasing tuples and
no shared coordinate. Non-increasing tuples are harmless isolated vertices.
It checks two explicit homomorphisms

    arc(arc(K4)) -> H1,  arc(arc(K4)) -> H2.

Each source has 60 vertices and 270 edges. The coordinate data use respectively
177 and 131 ordered values. The finite homomorphism certificates are checked
with `decide +kernel`, not native_decide. Applying the adjunction twice gives

* `twice_right_not_cliqueFree1`
* `twice_right_not_cliqueFree2`.

Thus SECOND right adjoints of these two candidates cannot be witnesses.
Their FIRST right adjoints remain unresolved; this result does not prove
anything about their coverability or certify their first K4 exclusions.

Exploratory generation:
* `/tmp/five_rank_sat.py` uses bounded integer ranks encoded as bit vectors.
  The rank bound exceeds the number of coordinate positions, so it represents
  every finite order pattern, not a numerical approximation.
* `/tmp/five-rank-arc2.log`: both arc^2(K4) maps found (15.13s, 7.88s).
* `/tmp/five_rank_arc2K4_{1,2}.cnf.witness.json`: raw, Python-checked witnesses.
* `/tmp/five_arc2K4_{1,2}.compressed.json`: monotone rank compression.
* `/tmp/build_five_iteration.py`: generates the Lean data and certificates.
  Its generated hom `map_rel'` lines were subsequently fixed to
  `fun {e d} h => certificateN e d h`; regenerate with that fix if needed.
* Control `/tmp/five-rank-check.log` agrees with the previous UNSAT arc(K4)
  results for both families.

## Additional exact order-constraint tests (NOT Lean certificates)

A more efficient total-order/total-preorder encoding is generated by
`/tmp/order_type_cnf.cpp` and its compiled binary `/tmp/order_type_cnf`.
Input source tables are `/tmp/shift_arc2.source`, `/tmp/five_local_{1,2}.source`.

For equality-shift tuples, use a total PREORDER on the 180 coordinate positions:
reflexivity is implicit, totality for every pair, transitivity for all distinct
triples, strict internal inequalities, and the four original shift adjacency
choices (one-step or two-step, in either direction). This accounts for coordinate
equalities; a strict total order would incorrectly rule them out.

`/tmp/shift_arc2_preorder.satlog` is UNSAT: no arc^2(K4) map into the old
equality shift-square over ANY linear order. Its CNF is about 115MB. This is
strong exploratory evidence for K4-freeness of the SECOND right adjoint, NOT
a Lean theorem and NOT non-coverability. The earlier rank-bit encoding timed
out after 300 seconds (`/tmp/shift-rank-arc2.log`).

For local coloring, the source is arc(cone(Mycielski(C5))), with 62 vertices
and 331 edges. A homomorphism would exhibit a neighborhood of the right
adjoint that is not three-colorable. The rank encodings timed out at 300s
for BOTH families (`/tmp/five-rank-local.log`). The full strict-order encoding
for FAMILY 1 returned UNSAT (`/tmp/five_local_1.order.satlog`, ~196MB CNF).
This excludes only this particular four-chromatic triangle-free neighborhood
witness; it is not a general local three-color theorem.

`/tmp/arc_noalt_order.py` and `/tmp/arc_noalt_odd.py` test whether arc(K4),
arc(W5), arc(W7), arc(W9) admit an order with no alternating C4. All four
are UNSAT. None has been certified in Lean; no universal local bipartiteness
or arbitrary-odd-wheel exclusion theorem has been established from these
finite tests. In particular, do not infer that right adjoints preserve the
NoAlternating property.

Final updates to this continuation:

* `FiveTupleIterationObstruction.H1` and `.H2` were generalized from natural
  coordinates to ANY linearly ordered type A. The finite natural certificates
  were retained, bounded by 177 and 131, and transported along finite order
  embeddings. New checked theorems:

      infinite_twice_right_not_cliqueFree1
      infinite_twice_right_not_cliqueFree2

  prove the second-right K4 obstruction over EVERY infinite linear order.
  `nonempty_orderEmbedding_of_finite_infinite` supplies the needed finite chain;
  no increasing infinite sequence is assumed. The file is now about 307 lines.
  All four printed axiom lists remain permitted. Backup before generalization:
  `/tmp/FiveTupleIterationObstruction.before_general.lean`.

* FAMILY 2's full strict-order local test timed out after 300s:
  `/tmp/five_local_2.order.satlog` says `c UNKNOWN`. Thus local arc(cone(M(C5)))
  exclusion was found only for FAMILY 1, and even that is not Lean-certified.

* The tempting orientation of each right edge by comparing its two selected
  intersection witnesses does NOT always make right triangles cyclic, even
  for a no-alternating-C4 base order. For the triangular prism with arc vertices
  [(0,1),(1,2),(2,0),(1,0),(2,1),(0,2)], order (0,1,5,2,3,4) has no alternating
  C4 but the three reverse-pair comparisons have signs (true,true,false).

* Do NOT use plain `bv_decide` or `bv_check` for submitted certificates: the
  installed tactic uses `ofReduceBool`, which introduces an unpermitted axiom.
  Its SAT/LRAT proof would need a separate kernel-only check or an explicitly
  reconstructed Lean proof. The positive witnesses above use `decide +kernel`.

No process remains running. Spec.lean is still unchanged and retains its
original sorry (same SHA256 recorded above). No proof or disproof of the
conjecture has been obtained, and no incomplete proof was submitted.

## Continuation: no-alternating right iterations and even-cycle WIP

`NoAlternatingIteration.lean` compiles, with permitted axioms. It proves
`Orderable.right`: a graph admitting a no-increasing-C4 linear order has a
right adjoint admitting such an order. Consequently EVERY finite right
iteration of the equality shift-square is countably triangle-free coverable
and K4-free, over every linear order. This supersedes the former unresolved
second and later shift candidates, and previous warnings against assuming
this property have now been resolved by an actual proof. Main declarations:
`Orderable.cover`, `Orderable.cliqueFree`, `iterate_orderable`, `iterate_cover`,
`iterate_cliqueFree`, `shift_iterate_cover`, `shift_iterate_cliqueFree`.
Proof labels bicliques by a Boolean orientation and the lower cut of the
inner side. BOTH signs use the same increasing order of cuts. Five possible
increasing-cycle sign patterns are excluded using inner-side overlap facts.
Auxiliary orderability-from-label theorem breaks ties by a well-order.

Active WIP: `BoundedIncreasingPath.lean` and `EvenCycleBicliqueCover.lean`.
The intended general theorem: excluding an increasing EVEN cycle of one
fixed length makes every neighborhood of `right H` countably properly
colorable, hence gives a countable triangle-free edge cover of `right H`.
Verified infrastructure includes length-indexed chains, odd Boolean endpoint
lemma, finite ranks from a uniform finite path bound, arc coloring pullback,
arc functor/reversal, and assembling countably colored fibers. A separated
biclique anchor lemma is almost done. Remaining plan: rank alternating
increasing chains across a biclique (odd chain closes to the forbidden even
cycle); partition vertices by the two endpoint ranks so each fiber has
separated anchors; apply the separated-anchor lemma, reversing arcs when
needed. Apply to each right neighborhood using `fromRight` intersection
witnesses, then the earlier-neighbor coloring criterion.

This criterion would rule out FIRST right(H1), because four increasing H1
steps force initial[4] < final[0], preventing closing edges. H2 has no such
known obstruction. Neither first-adjoint candidate is presently settled.
No proof/disproof of the main conjecture has been found; Spec remains original.

## Even-increasing-cycle criterion completed; H1 first adjoint ruled out

New compiled files, all audited axioms permitted:

* `BoundedIncreasingPath.lean`: `Chain` (append/prepend/map/constant/mono,
  split_last, odd_bool), `finite_rank`, `coloring_of_arc`, `arcMap`,
  `reverseArc`, `coloring_of_countable_fibers`.
* `EvenCycleBicliqueCover.lean` (~214 lines): `NoClosing H n` excludes an
  increasing path of length n with adjacent endpoints. For n=2*k+3,
  `neighborhood_coloring` proves each neighborhood of right(H) properly
  countably colorable, and `right_cover` proves the desired countable
  triangle-free edge cover. `right_cover_of_label` uses arbitrary ordered
  labels with distinct labels at adjacent vertices instead of an order on
  the full vertex type. Key lemmas `separated_coloring`, `anchor_coloring`.
* `FiveTupleFirstCover.lean` (~58 lines), namespace `Erdos595FiveFirst`:
  `first_right_cover` proves coverability of right(H1) over EVERY linear
  order. Four forward edges force initial[4] < after4[0]; a fifth step
  and closing edge give a contradiction. Uses the even-cycle theorem
  with k=1 (no increasing C6).

Thus H1 is entirely eliminated: first right is covered, second contains K4.
H2 first right remains unresolved. Spec is unchanged; no settlement exists.
Build logs: /tmp/bounded-increasing-path.log, /tmp/even-cycle-biclique.log,
/tmp/five-tuple-first-cover.log. No processes remain running.

Additional exploration after the even-cycle result (NOT Lean certificates):
`/tmp/right_matching_types.py` tests arc(K3)'s six witnesses with all three
reverse-pair edges forced to the same directed base type. Removed the default
first-coordinate minimum symmetry break, which is invalid with these extra
ordered-edge constraints. H1 is UNSAT for each of its two types; H2 is SAT
for EACH of its two types. Hence simply coloring a right edge by the type of
its two chosen intersection witnesses does not work for H2.
`/tmp/right-matching-types.log` records the results. The 600-second local H2
search was killed by the shell tool's 300-second timeout; its log has no
conclusion, and no search remains running. Do not count it as UNSAT.

## H2 first right adjoint is now ruled out (Lean-verified)

`Submission/FiveTupleSecondCover.lean` (~341 lines), namespace
`Erdos595FiveSecond`, compiles. All printed axioms are permitted.
Log `/tmp/five-tuple-second-cover.log`.
Main results:
* `arc_source_cover`: if arc(F) maps to H2, F has a countable triangle-free
  edge cover. The actual palette constructed is EIGHT colors.
* `first_right_cover`: applies this to right(H2), over EVERY linear order.

Proof idea: color each ordered right edge by the directed order type of
its two chosen reverse intersection witnesses (four possibilities), plus
one Boolean saying that this edge extends to a later triangle of the same
witness type. A monochromatic triangle then gives a monochromatic-type
ordered diamond (edges ab,ac,bc,ad,cd for a<b<c<d). This is impossible in H2.

The exact finite obstruction is proved without SAT/reflection axioms:
* Every increasing H2 triangle has types (P21,P20,P21): long edge P20.
* A right triangle with all three matching reverse-witness pairs of one
  fixed positive type has only TWO possible orders for its cyclic witness
  triangles. In notation ab,ba,ac,ca,bc,cb these are
      T(ab,bc,ca) AND T(ac,ba,cb), or
      T(bc,ab,ca) AND T(ac,cb,ba),
  with T(x,y,z) := P21 x y AND P20 x z AND P21 y z.
* Applying this to both diamond triangles gives four cases. For each of the
  two matching types, either the bc--cd or cb--dc base adjacency is impossible.
* Reversing all arcs handles the two negative matching types.

The 68 impossible uniform-triangle cases and 32 diamond subcases use explicit
short chains of strict inequalities returning to their start. These ordinary
Lean transitivity proofs were generated by `/tmp/generate_h2_cycles.py`.
Do NOT regenerate that script blindly: it edits identified ranges in the
pre-generation file and will no longer find those ranges in the final file.
Exploration scripts: `/tmp/right_matching_flags.py`, `/tmp/h2_diamond_cases.py`.
Logs `/tmp/right-matching-flags.log`. No certificate is external to the Lean file.

Performance note: `aesop (add safe tactic (by order))` and even repeated direct
`order` on the many large cases took more than 300s and ~6GB. Explicit cycle
proofs resolve this and the full final file builds quickly. The older processes
were killed; no build remains running. Both H1 and H2 first-stage candidates
are now eliminated, and both second stages already have K4 obstructions.

Spec remains original and unproved. None of these results settles Erdős 595.

## Broader diamond filter (exploratory, NOT Lean-certified)

`/tmp/five_diamond_filter.py` applied the H2-style fixed-matching-type diamond
exclusion test to all 227 earlier five-coordinate survivors. For each family,
all its positive matching types were tested; reversing all arcs accounts for
negative matching types. No invalid source symmetry break was imposed.
Results: 177 pass this sufficient exclusion test; 50 admit at least one
uniform-type diamond; zero UNKNOWN. Runtime ~17 seconds.
* `/tmp/five-diamond-filter.log`
* `/tmp/disjoint_five_no_diamond_cover.txt` (50 rows)
* `/tmp/disjoint_five_diamond_unknown.txt` (empty)
The exclusions of the other 175 families besides H1,H2 are not Lean proofs.
In particular a generic claim that every arc(K4)-free finite-type base excludes
uniform matching diamonds is FALSE according to these exact order tests.

The two-type families are now fully ruled out at the first two right stages.
Other three-or-more-type families remain possible candidates, with no actual
non-coverability proof. Do not confuse this restricted search through minimal
triangle-bearing families with a classification of all possible unions of
order types. No general right-preservation theorem has been obtained.

## Homogeneous fan criterion and four remaining three-type families

`Submission/FanCoverCriterion.lean` compiles with permitted axioms.
Namespace `Erdos595FanCover`; theorem `cover_of_bounded_fans`.
It ranks ordered edges under homogeneous triangle extension with a fixed
root: (a,b) -> (a,c) when a<b<c and all three triangle edges have one type.
A type-dependent finite path bound gives natural-valued ranks, which together
with the type prevent monochromatic triangles. Finite type palettes yield
finite covers. This supplies the general mathematical justification for the
next exact order-constraint filter (its individual exclusions remain uncertified).

`/tmp/five_fan_filter.py` tested uniform matching-type fans on 5,6,8 vertices
for the 50 diamond survivors. 46 were excluded already at fan size 5 for ALL
their types. Four three-type families have a surviving type even at fan size8:

0. 4722366482873948569600:
   0010011011, 0010110110, 0101001011; surviving type 0010011011.
1. 649037107316853453566314197024768:
   0010011011, 0010110101, 0110110100; surviving type 0010011011.
2. 649037107316853453566316344508416:
   0010011011, 0010110110, 0110110100; surviving type 0010011011.
3. 664613997892457936451903530677043328:
   0001010111, 0010101110, 0111010100; surviving type 0001010111.

Logs /tmp/five-fan-filter.log, /tmp/disjoint_five_no_fan_cover.txt.
No UNKNOWN in this filter. Runtime ~14s. This is NOT non-coverability evidence
beyond failure of the particular bounded-fan sufficient criterion.

A one-anchor finite-profile coloring shortcut fails in all four families:
`/tmp/five_paw_profile.py` found a uniformly typed right triangle plus a fourth
neighbor of its root such that the other two root-neighbor witness-pair labels
have IDENTICAL complete comparison profiles relative to the fourth neighbor's
witness-pair label. These are SAT witnesses, not Lean certificates; strict-order
encoding is adequate to exhibit these positive instances. Log
`/tmp/five-paw-profile.log`. It does not exclude other local-coloring arguments.

Active follow-up: uniformly typed odd wheels. Slow script
`/tmp/five_wheel_filter.py` was stopped after excluding all 12 ordered W5
patterns for family0. Its W7 phase was slow and unfinished. A faster exact
reformulation `/tmp/five_wheel_fast.py` is now running, log
`/tmp/five-wheel-fast.log`. Fix the root least, and one rim vertex least among
the rim. The remaining rim PATH edges have 2^(n-2) possible orientations;
each extends to a linear order, and these orientations encode every ordered
wheel up to a source automorphism. Test W5 and W7 for all four families, on
their previously surviving positive matching type. The root's matching
edges all have the positive orientation. Negative types follow by reversing
all arcs. The original script redundantly enumerated full rim orders.

## Final state of this continuation

The faster uniformly typed odd-wheel tests finished successfully:
`/tmp/five-wheel-fast.log` records, for EACH of the four surviving families,
UNSAT on all 8 W5 rim-orientation patterns and all 32 W7 patterns, with no
UNKNOWN. No W9 or arbitrary-odd-cycle exclusion was proved. Thus local
bipartiteness of the fixed-type subgraphs is a possible next structural
question, NOT an established theorem. All four families still admit long
uniform matching-type fans; none has a non-coverability argument or a Lean
K4-freeness certificate.

No Lean build or SAT search remains running. New verified files this turn:
* BoundedIncreasingPath.lean
* EvenCycleBicliqueCover.lean
* FiveTupleFirstCover.lean  (H1 first right covered)
* FiveTupleSecondCover.lean (H2 first right covered)
* FanCoverCriterion.lean
The older NoAlternatingIteration result was recorded at the start of this
turn; all finite right iterations of the equality shift-square are covered.

The main result of this continuation is elimination of BOTH previously open
two-type five-coordinate first-right candidates. The original conjecture is
still unresolved. Submission/Spec.lean has not changed and retains its sorry:
SHA256 de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45.
No incomplete submission was sent to the verifier.

## Four remaining minimal three-type five-coordinate candidates ruled out (verified)

New files compile, with only propext, Classical.choice, Quot.sound:
* `LocalIntervalCoverCriterion.lean` (~62 lines), namespace
  `Erdos595LocalInterval`. `MonoTri` is a homogeneous triangle with its
  least vertex designated the root. `countable_cover` applies when labels
  of the two root edges differ and every homogeneous two-edge neighborhood
  path fails to increase monotonically. Color an edge by its old type and
  one bit recording a lower-labelled neighbor at the same root.
* `ThreeTypeFiveCover.lean` (~1100 lines), namespace `Erdos595ThreeFive`.
  `P f k` defines the three exact strict interleaving types for each of
  f=0,1,2,3, in the order listed immediately above. `G f` is their symmetric
  union. `arc_source_cover` covers ANY F with arc(F)->G f. The theorem
  `first_right_cover` rules out right(G f) over EVERY linear order.
  Its constructed palette has 12 colors (six directed types plus a bit).

Structural proof:
* Each base has exactly one ordered triangle type pattern: (2,0,1) for
  family0; (2,1,0) for families1,2,3. All triangles use all three types.
* A right triangle with a common reverse-pair matching type must have
  matching type0. The other two matching types have no such triangle.
* The type0 uniform triangle has exactly TWO possible orders for its
  two cyclic base-witness triangles. This is proved in `uniform_triangle`.
* For a root edge with outgoing/incoming witnesses x,y, use interval
      (x[3],y[1]).
  Type0 always makes it nonempty. Uniform triangles force the intervals
  of the two root edges to be DISJOINT (`uniform_intervals`).
* A homogeneous two-edge path at a fixed root cannot increase through
  three such intervals (`interval_no_path`). The proof uses both possible
  rim matching orientations, so it does not assume the rim path follows
  the chosen global vertex order. This proves the local-color criterion,
  not merely exclusion of finitely many odd wheels.

All finite order contradictions are ordinary transitivity cycles in Lean.
Generators `/tmp/build_three_five.py` (creates the initial file) and
`/tmp/add_three_five_path.py` (adds the no-path proof) were used before the
handwritten pullback and cover lemmas were appended. Do NOT rerun the first
script without preserving the appended material. No SAT or native reflection
certificate occurs in these Lean proofs.
Exploration: `/tmp/five_local_intervals.py`, `/tmp/five_interval_path.py`,
`/tmp/five_interval_core.py`. Logs `/tmp/five-local-intervals.log`,
`/tmp/five-interval-path.log`. The simpler conjecture that the root biclique
forbids THREE disjoint intervals is false (SAT for each family, script
`/tmp/five_three_intervals.py`). The no-monotone-path argument, not that false
packing claim, is what the final proof uses.

Thus all 227 minimal five-coordinate families left by the earlier filters
are now either individually Lean-covered (the two two-type and four final
three-type families) or have exploratory finite diamond/fan exclusions.
The other 221 exclusions have not been individually Lean-certified. This
is NOT a classification of nonminimal type unions, and NOT a settlement
of Erdős 595. Spec remains unchanged with its original sorry.

## Third-stage unsupported vertices need not be independent (new, verified)

`Submission/ThirdBadEdge.lean` compiles. Namespace `Erdos595ThirdBadEdge`.
Log `/tmp/third-bad-edge.log`. Printed axioms: only propext, Classical.choice,
Quot.sound. This result is NOT a settlement of the original conjecture.

For any triangle-free graph B, the new base H B has vertices
    (v, (a<b<c)),  v in B.
Within each v-fiber it is the old equality shift-square. Cross-fiber edges are
    B(v,w) and x.a < y.b and y.a < x.b and x.b < y.c and y.b < x.c.
`H_cliqueFree` proves H B is K4-free. Its proof handles 3+1 and 2+2 fiber
splits by elementary coordinate inequalities; a 2+1+1 split would give a
triangle in B. The base is countable whenever B is countable.

Using the free ultrafilter U on N, define
    p_v(a,b) = lim_c (v,(a,b,c))       (first stage),
    P_v(a)   = lim_b p_v(a,b)         (second stage),
    X_v      = lim_a P_v(a)           (third stage).
An increasing-triple totalization is used outside the relevant tails.
`first_cross`, `second_cross`, `third_cross` verify the adjacencies. For
B(v,w), first-stage cross adjacency holds once a<d and c<b; the second-stage
P_v(a), P_w(c) are adjacent for EVERY a,c; consequently X_v, X_w are adjacent.

`no_original_support`: for every original triangle-free vertex set S,
its threefold lifted support is not in X_v. Otherwise five successive free
coordinates produce the three shift-square vertices
    (a,b,c), (b,c,d), (c,d,e)
inside S, an actual triangle. This is the ordinary finite-intersection
argument, not an assumption about external colorings.

`badHom` maps any triangle-free B into the third-stage subgraph of unsupported
vertices. `exists_bad_edge` specializes to the countable base from B=K2.
`unsupported_no_color_bound` shows that, when arbitrary bases are allowed,
there is no fixed bound on the ordinary vertex chromatic number of this bad
part. It does NOT say this for countable bases.

`three_pieces` and `third_three_pieces` prove a THREE-piece triangle-free edge
cover of the base and of the third extension. The base pieces are the two
shift types and the cross-fiber subgraph pulled back from B. Thus a bad-bad
edge is not non-coverability evidence.

This rules out the stronger proposed independence claim. It does NOT rule
out the narrower possibility that the unsupported third-stage part is always
TRIANGLE-FREE. No such theorem has been proved. All three previously checked
vertices of a third-stage triangle were not all unsupported.

## Fourth-stage unsupported vertices CAN form a triangle (new, verified)

`Submission/FourthBadTriangle.lean` compiles, with permitted axioms only.
Namespace `Erdos595FourthBadTriangle`; log `/tmp/fourth-bad-triangle.log`.
The base is countable, K4-free, and has FOUR triangle-free edge pieces.
Its fourth mutual extension contains a triangle all of whose vertices lack
any lifted original triangle-free support. The fourth extension still has
FOUR edge pieces, so this is not a counterexample to the main conjecture.

General construction `D B lab` refines the preceding `ThirdBadEdge.H B`:
for cross-fiber edges, in addition to the four overlap inequalities, require
    lab(v)<lab(w) -> middle(x)<middle(y)
(and the reversed condition). `mono B lab` keeps equal-level base edges.
`D_cliqueFree`: if B is K4-free and mono B lab is triangle-free, D B lab is
K4-free. The key lemma `same_level` says every common neighbor of an INTERNAL
shift edge has the same level as that edge. Any four-clique with two vertices
in one fiber would therefore lie entirely in one level, where the earlier
H-clique exclusion applies. Four distinct fibers would give a K4 in B.

For the concrete example take B=K3 and lab(0)=lab(1)=0, lab(2)=1. Define
    p_v(a,b) = lim_c (v,(a,b,c)),
    P_v(a) = lim_b p_v(a,b),
    A_v(a) = lim_b pure(p_v(a,b)).
The selected fourth-stage vertices (`Z`) are
    Z(0,true) = lim_a A_0(a),
    Z(1,true) = lim_a A_1(a),
    Z(2,false) = lim_a pure(P_2(a)).
Their integration-level profiles, outer-to-inner, are respectively
    (4,3,1), (4,3,1), (4,2,1).
`fourth_triangle` proves their three adjacencies. `no_original_support` proves
all their fourfold original supports fail, by the same five-coordinate shift
triangle argument. `unsupported_not_triangleFree` packages the conclusion.
`fourth_four_pieces` explicitly proves the finite covering bound through all
four extensions. No external SAT certificate is used in these proofs.

Exploration `/tmp/bad_profile_clique.py` found this profile choice by exact
finite order constraints (log `/tmp/bad-profile-clique.log`). Its stage-three
triple-profile test had no survivor, but that does NOT prove that arbitrary
unsupported third-stage vertices form a triangle-free graph. The stage-three
triangle-freeness question remains open within this investigation.

## Third-stage unsupported triangle, and a universal reduction (new, verified)

This SUPERSEDES the preceding entries that left third-stage bad-part triangle-
freeness unresolved. It is FALSE, even for a COUNTABLE base with a finite edge
cover. `Submission/ThirdBadTriangle.lean` (368 lines) now compiles with only
propext, Classical.choice, Quot.sound. Log `/tmp/third-bad-triangle.log`.
Namespace `Erdos595ThirdBadTriangle`. No holes or external certificates.

The decisive extra coordinate was found by the exact finite-order exploration
`/tmp/bad_profile_decorated.py`, log `/tmp/bad-profile-decorated.log`:
* all three points use integration profile (3,2,1,1);
* the internal shift-square projects the quadruple to coordinates (0,2,3).
The search stopped after finding this survivor for four coordinates. It did
not establish any classification. All properties needed below have ordinary
Lean proofs, independent of that search.

Construction for an ARBITRARY K4-free B on V:
* Original vertices are (v,x), x=(a<b<c<d) a natural-number quadruple.
* Within each v-fiber use the shift-square on project(x)=(a,c,d).
* Cross-fiber adjacency is B(v,w), the four inequalities
      x.a<y.b, y.a<x.b, x.b<y.c, y.b<x.c,
  and disjoint last blocks: x.d<y.c OR y.d<x.c.
* `no_common_cross`: an internal fiber edge has NO cross-fiber common
  neighbor. Thus a clique with two vertices in one fiber lies entirely
  in that fiber; a clique with all fiber indices distinct projects to B.
  `H_cliqueFree` proves preservation of K4-freeness without assuming B TF.
* `base_countably_colorable`: projection to the natural-number quadruple is
  a proper countable vertex coloring. This holds for arbitrary V. The base
  itself is COUNTABLE when V is countable, not in general.

Let U be the ordinary free ultrafilter on N. Define
    p_v(a,b) = lim_c lim_d (v,(a,b,c,d)),
    P_v(a)   = lim_b p_v(a,b),
    X_v      = lim_a P_v(a).
`first_cross` verifies the mutual adjacency once a<d and c<b for the two
fixed coordinate pairs (a,b),(c,d). The last-block disjunction accommodates
both orders of the first-stage Fubini quantifiers. `second_cross` and
`third_cross` then give B(v,w) -> H_3(X_v,X_w).

`no_original_support`: every X_v rejects every threefold lift of an original
triangle-free vertex set S. If such a lift were large, eight successive
coordinates a<b<c<d<e<f<g<h give three vertices of S:
    (a,b,c,e), (c,d,e,g), (e,f,g,h).
Their projections (a,c,e), (c,e,g), (e,g,h) form a shift triangle. All selections
use only finite intersections of ordinary ultrafilter members.

Main declarations:
* `badHom`: EVERY K4-free B maps into the unsupported part of H_3.
* `unsupported_can_contain_triangle`: specialize B=K3. This is a countable
  K4-free base with a genuinely all-unsupported triangle at stage THREE.
* `all_cover_iff_bad_cover`: universal countable edge coverability of K4-free
  graphs is equivalent to coverability of the unsupported parts in this
  family. Their original bases are countably VERTEX-colorable; this must not
  be misread as saying the bases are always countable.
* `base_finite_cover`, `third_finite_cover`: an r-piece cover of B gives an
  (r+2)-piece cover of H and its third extension.
* `concrete_four_pieces`: for B=K3 the whole third extension has FOUR pieces.

Consequences: neither independence NOR triangle-freeness of the unsupported
third-stage part can supply a general compression theorem, even if one insists
on a countable base. Coverability of this part for arbitrary countably vertex-
colorable bases is already equivalent to the original universal question.
There is still NO non-coverable graph and NO universal cover theorem here.

Latest task status: Spec.lean is unchanged, SHA256
  de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45,
and still contains the original sorry. No incomplete proof was submitted.
No Lean build or SAT search is left running. This continuation added three
verified auxiliary files: ThirdBadEdge.lean, FourthBadTriangle.lean, and
ThirdBadTriangle.lean. The original conjecture remains unresolved.

## Explicit countable finite-extension base and degree-one ultrafilters (verified)

`CountableExtensionGraph.lean` constructs a countably infinite K4-free graph G
with the full finite allowable-neighborhood extension property. Its vertices
are finite hereditarily triangle-free child forests with natural-number tags.
Rank orients every edge toward a child. The highest-rank vertex of a K4 would
have three mutually adjacent children, which is forbidden. `finite_extension`
adds a fresh tagged node with exactly a prescribed finite triangle-free set
as old neighbors, and no neighbors in a disjoint prescribed finite set.
Countable universality and homogeneity are NOT yet formalized.

`GenericUltrafilterFailure.lean` now compiles with permitted axioms only.
For each original vertex v, take a fine ultrafilter limit of fresh vertices
adjacent to v and nonadjacent to each other eventually tested original vertex.
The resulting nonprincipal point p_v has original trace exactly {v}.
`point_neighbors` proves p_v has exactly one neighbor in the mutual extension,
the principal point at v. Distinct p_v,p_w thus have no common neighbor.
`core_pair_failure` shows that removing isolated vertices does not restore even
the common-neighbor property for nonadjacent pairs. `extension_cover` records
that this first extension nevertheless has a countable triangle-free edge cover.
The remaining singleton-finset elaboration issue was avoided by applying
finite_extension to {v,v}, directly using pair_triangleFree v v.

Neither result settles the conjecture. Spec.lean remains unchanged.

## Infinite alphabet, two colors: Hales--Jewett obstruction (verified)

`InfiniteAlphabetHalesJewettObstruction.lean` compiles (about 200 lines),
with only permitted axioms. Log: /tmp/infinite-alphabet-hales-jewett.log.
This is distinct from the older THREE-letter/COUNTABLE-palette obstruction.

* `split_countable_family`: every countable family of infinite sets has a
  simultaneous Boolean splitter. Choose globally distinct witnesses by
  well-founded recursion, two for each set.
* `split_quadratics`: a single two-coloring of Q splits the natural-number
  range of every rational quadratic with positive leading coefficient.
* `sqNorm_affine`: the finite-support squared coordinate norm along a
  nonconstant rational affine ray is such a quadratic.
* `affine_ray_two_coloring`: every rational vector space, in ANY dimension,
  has a two-coloring with no monochromatic full nonconstant N-affine ray.
* `natural_cube_two_coloring`: for ANY index type I, the cube I -> N has a
  TWO-coloring with no monochromatic full combinatorial N-line.

Thus enlarging dimension does not repair the infinite-alphabet HJ step,
not even with two colors. This does NOT disprove the separate asymmetric
ordered-graph TriangleArrow hypothesis; a full monochromatic infinite line
is a different demand. No theorem about asymmetric HJ was established.

## Countable universality of the explicit base (verified)

`CountableGenericUniversality.lean` compiles (about 150 lines), permitted
axioms only. Log: /tmp/countable-generic-universality.log. Starting from the
finite_extension theorem, coherent partial induced embeddings on initial
segments of N are extended one vertex at a time. `universal_nat` and
`universal_countable` establish an INDUCED embedding into
Erdos595CountableExtension.G of every COUNTABLE K4-free graph. Countable
vertex colorability is NOT enough for this theorem.

`GenericUltrafilterUniversality.lean` compiles (about 125 lines), permitted
axioms only. Log: /tmp/generic-ultrafilter-universality.log.
* `fubini_map_iff`, `ultrafilterEmbedding`: induced graph embeddings lift
  to induced embeddings between mutual ultrafilter extensions.
* `Carrier`, `tower`, `towerEmbedding`: finite mutual towers, with clique
  bounds packaged as subtypes.
* `tower_universal_countable`: each finite tower over a countable base
  embeds into the same-stage tower over the ONE explicit generic base.
* `support_map_iff`, `preimage_triangleFree`, `bad_map`: lack of lifted
  original triangle-free supports is preserved by these embeddings.
* `third_bad_universal_countable`: combining ThirdBadTriangle with the
  preceding results, EVERY COUNTABLE K4-free graph maps homomorphically
  into the unsupported third-stage part over that ONE fixed countable base.
  The conclusion here is a homomorphism, not an asserted induced embedding.

This supplies a canonical candidate and rules out finite-pattern exclusions
for its bad part. It does NOT establish a countable-color obstruction, nor
formalize finite Folkman's theorem. No non-finite-edge-coverability claim
has been certified from these results alone.

## New possible weaker support route (UNPROVED; not yet ruled out)

The previous support counterexamples concern original subsets whose INDUCED
GRAPHS ARE TRIANGLE-FREE, or finitely many such vertex subsets. They do not
rule out supports whose induced graphs have FINITELY MANY TRIANGLE-FREE EDGE
PIECES. For example, each bad vertex in ThirdBadTriangle is supported on its
own shift-square fiber, which has a two-piece edge cover despite having no
triangle-free vertex support.

Potential lemma: for every K4-free G and q in U^2(V), there is S subset V
with a FINITE triangle-free edge cover of G[S] such that every p in the
original-U(V) trace
    A_q = {p : Ultrafilter V | neighborSet_{UG}(p) belongs to q}
contains S. Equivalently, A_q is contained in {p | S belongs to p}.
This is a STRONG proposed sufficient lemma, not a known fact.

Why it would be useful: a nonisolated P at stage three contains the
stage-two neighborhood of some q. The reverse mutual-adjacency condition
then forces P to contain the twice-lifted S. Finite edge covers persist
through all finite mutual extensions. For a countable original base there
are at most continuum many choices of S, so the vertex-piece closure lemma
would give a countable edge cover of stage three. Neither the proposed
support lemma NOR this full conditional packaging has been formalized.
It would rule out a candidate stage, not settle Erdős 595 itself.

Known facts that may help test it:
* Every finite subset of A_q has a common TRIANGLE-FREE original support
  (SupportObstruction.finite_trace_support).
* Global triangle-free support can fail; finite edge-cover support remains
  a genuinely weaker assertion.
* A_q has no forward directed Fubini triangle: three forward relations
  among its points, together with a common first-stage neighbor selected
  from q, would produce a K4 in the base. This observation alone has NOT
  yielded the proposed finite-edge-cover support.
* The finite-edge-cover vertex-subset ideal is closed under finite unions
  (cross edges between finitely many pieces can be split bipartitely).
  An ultrafilter avoiding this ideal is isolated at the first extension.
  Whether finite-depth higher representatives can be nonisolated while
  their fully flattened ultrafilter avoids the ideal is UNPROVED here.

Latest status: Spec.lean is unchanged and retains its original sorry.
No settlement and no proof submission. All five useful files from this
continuation (including the repaired GenericUltrafilterFailure) are built.

Further mathematical reduction for testing that UNPROVED weaker support lemma:
Suppose A is a family of original ultrafilters such that every finite subfamily
has a common triangle-free original support. Add independent apices z_(F,S)
for all such finite-subfamily supports S. Their principal first-stage points
have neighborhoods containing every p in F. A fine ultrafilter q on these
principal apices then has A contained in its first-stage trace A_q. Thus any
finite-support-compatible family A can be installed inside such a trace after
an independent apex extension. Each principal point at p in A is adjacent
to q at stage two. A fine third-stage limit of those principal p points is
therefore adjacent to the principal point at q at stage three.

If A has NO common support whose original induced graph is finitely edge-
coverable, the complements of its finitely-edge-coverable support sets have
the finite-intersection property (use closure of that vertex-subset ideal
under finite unions). A suitable limit would then give a nonisolated
third-stage point with NO original finite-edge-cover support. This is a
conditional mathematical reduction only: such A has NOT been constructed,
and the reduction itself has NOT been put into Lean. For countable bases,
adding all the independent apices may make the new base uncountable; a
countable selection of witnesses would suffice only if A were countable.
Do not overlook this cardinality issue.

The weaker support route is still unresolved at the end of this continuation.

## Finite Folkman and finite-edge-cover support route (verified; supersedes above)

The previously UNPROVED weaker support lemma is now REFUTED. This does NOT
settle Erdős 595. All files below compile with only propext, Classical.choice,
and Quot.sound. Spec.lean is still unchanged and has its original sorry.

* SuffixSupportTemplate.lean: for any finite K4-free role graph B, a countable
  suffix-row template has row ultrafilters with common independent supports
  for every finite subfamily, while every global common support contains B.
* FiniteFolkman{Amalgamation,Partite,Step,Homogenize,Ramsey}.lean and
  FiniteFolkman.lean: finite triangle Folkman is now fully formalized, using
  finite Hales--Jewett, free amalgamation, and finite-palette compactness.
  For each finite palette C there is a finite K4-free graph not admitting a
  triangle-avoiding edge coloring by C. Consequently the one countable generic
  base has no FINITE palette. It does have a countable palette.
* FiniteEdgeSupportFailure.lean: disjoint union of the finite Folkman suffix
  templates, with countably many independent cutoff apices, gives a countable
  K4-free graph and a second-stage trace with no common original support whose
  induced graph has a finite triangle-free edge cover.
* FiniteEdgeCoverIdeal.lean: original subsets admitting finite edge covers
  form a finite-union ideal. A filter construction gives an ultrafilter on
  labels avoiding all rejection-complements for this ideal.
* ThirdFiniteEdgeSupportFailure.lean: an ACTUAL nonisolated third-stage point
  lacks every original finite-edge-cover support.
* ThirdTriangleFiniteEdgeSupportFailure.lean: a second independent apex family
  makes this point lie in a triangle. Only ONE of the three triangle points
  is shown to lack all finite-edge-cover supports.
* GenericFiniteEdgeSupportFailure.lean: transfers that triangle and that one
  unsupported point to stage three of the fixed countable generic base.
  Its theorem generic_third_triangle_with_no_finite_support is verified.

Important guardrail, now proved for this concrete example:
* FiniteExceptionUltrafilterTarget.lean: a countable target with a finite
  exceptional set E, finite degrees outside E, and a dummy vertex adjacent to
  all of E admits a collapse of mutual ultrafilter relations. This lifts
  homomorphisms through every finite tower of a K4-free source. The target
  need NOT be K4-free.
* FiniteEdgeSupportTowerCover.lean: the support-failure example maps to such
  a countable target (finite complete role components, two global apex labels,
  and a dummy). Thus EVERY FINITE TOWER of this example has even a countable
  proper vertex coloring, hence a countable triangle-free edge cover.

Therefore original finite-edge-cover support failure, even on a triangle,
is NOT evidence of non-coverability. The generic tower remains undecided.
Do not equate its no-finite-palette theorem with no-countable-palette.

Possible further support construction, NOT PROVED OR FORMALIZED: combine
suffix templates with a third-stage outer-graph encoding, interval-separated
prefix coordinates, and a final-block disjunction, to put arbitrary outer
K4-free graphs in the all-finite-edge-unsupported part. This would be another
reduction/obstruction only, not a settlement, so has not been prioritized.

## Binary versus three-letter infinitary Hales--Jewett (new, verified)

`BinaryInfiniteHalesJewett.lean` compiles. Namespace
`Erdos595BinaryInfiniteHalesJewett`; log /tmp/binary-infinite-hales-jewett.log.
All audited axioms are permitted, and there are no holes.

* exists_binary_dimension: for ANY palette C (not necessarily countable),
  some binary cube has a monochromatic combinatorial line for every coloring
  by C. Take dimension Set C with a well order, color its chain of initial
  segments, use Cantor to find a collision, and vary the intervening interval.
* no_lines_of_three_quotient: for ANY alphabet E surjecting onto Fin 3 and any
  index type I, a countable coloring of E^I avoids all E-alphabet lines. Pull
  back the earlier three-letter coloring and push a putative line forward.
* alphabet_boundary packages the binary/three-letter countable distinction.

This does NOT repair the infinite Folkman partite argument. Its bipartite
edge alphabets may have at least three elements. Nor does forcing equality
of two edges in a bipartite partite step force equality of the two incident
edges of a TRIANGLE: identifying the other two vertices into one part would
violate proper part labeling. No infinitary graph Ramsey theorem was proved.

The pending GenericFiniteEdgeSupportFailure theorem has also been compiled
and audited successfully in this continuation. All the previous finite
Folkman/support-failure results have now been recorded above, superseding the
old unproved finite-edge-support proposal.

Latest status: no settlement. Spec.lean still has its original sorry, with
SHA256 de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45.
No incomplete proof was submitted. No Lean build or search is left running.

## Exponential candidate restrictions (new, Lean-verified)

Two new files compile with only permitted axioms; they contain no holes.
These are restrictions on candidate constructions, NOT a settlement.

### ExponentialCompactness.lean

Namespace Erdos595ExponentialCompactness; log /tmp/exponential-compactness.log.

* finite_evaluation: every finite induced subgraph of H^B maps to the countable
  target H, when B has no countable proper vertex coloring. Simultaneously
  color B by the finitely many function values, find a monochromatic B-edge,
  and evaluate at one endpoint.
* finite_palette: every FINITE triangle-free edge palette of H transfers to
  H^B, by the existing finite-palette compactness theorem. This cannot be
  extended to countable palettes by the same argument.
* cover_of_countable_obstruction: if a COUNTABLE graph K maps to B but cannot
  map to H, restricting functions to K gives a proper vertex palette of size
  at most continuum, hence a countable triangle-free edge cover of H^B.
  This completes the old unformalized countable-obstruction observation.
* no_triangle_equal_at_center: if B[N(v)] has uncountable vertex chromatic
  number and H is K4-free, any triangle f,g,k of H^B has f(v) != g(v).
  Only equality of TWO values is needed for the contradiction. A monochromatic
  edge in B[N(v)] for the triple of function values gives an H-triangle, all
  three of whose vertices are adjacent to f(v), contradicting K4-freeness.
* cover_of_uncountable_neighborhood: accordingly such a domain is ruled out.
  Evaluation at v has triangle-free fibers (in fact it is rainbow on triangles).

Thus a useful pair H,B must have H requiring infinitely many edge pieces,
no countable domain homomorphism obstruction to H, and every neighborhood
of B countably vertex-colorable. Triangle-free B meets the last condition.
The countable universal K4-free H meets the local homomorphism condition
for any K4-free B. No conclusion for all such pairs has been obtained.

### ShiftExponentialCover.lean

Namespace Erdos595ShiftExponential; log /tmp/shift-exponential-cover.log.

For the ordered shift graph B on increasing pairs of A, set F = H^B. For
f in F and index a define the H-biclique profile
  A(f,a) = { g(x,a) : x<a and g is F-adjacent to f },
  B(f,a) = { f(a,y) : a<y }.
The cross-adjacency condition of the exponential makes this a biclique.
If f,g are F-adjacent and their profiles at a,b coincide, then a=b:
for a<b, f(a,b) lies in both sides of the common biclique, impossible;
the reverse inequality is symmetric.

* profile_coloring: if A does not inject into Set(Bool x W), each function
  has a profile repeated at two distinct indices. Use a repeated profile as
  its vertex color. Equal colors for adjacent functions would force both
  distinct indices to equal one index of the other function. Therefore this
  is a proper palette of size at most continuum when W is countable.
* standard_shift_cover: the standard index A = Set(Set N) is ruled out.
* shift_coloring_of_binary: any binary encoding of A gives a countable proper
  shift coloring, by choosing one differing bit per increasing pair and
  recording that bit index and its value at the first endpoint.
* all_shift_domains_cover: the hypothesis that B is not countably colorable
  itself forces the required noninjection of A into the profile palette.
  Thus EVERY ordered-shift domain satisfying the exponential hypothesis is
  ruled out, for EVERY countable H. No clique bound on H is needed here.
* precomposeHom and cover_of_shift_hom: contravariance rules out every domain
  receiving a homomorphism from any such uncountably chromatic ordered shift.

This does not rule out higher-shift domains, nor prove a universal exponential
covering theorem. Repeating the profile idea seems to increase the palette
past continuum; no countable edge-cover conclusion from that was proved.

Other reasoning in this continuation (good vertex orders, topological/forcing
representations, infinite partite methods) produced no new proved main route.
The earlier-neighborhood coloring sufficient criterion was already in Work.lean;
its universal existence must not be assumed.

Spec.lean is unchanged, with SHA256
  de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45.
The original sorry remains. No proof/disproof has been submitted.

## Countable common-neighbor detectors and first U vertex coloring (verified)

`CommonNeighborDetector.lean` compiles; namespace
Erdos595CommonNeighborDetector; log /tmp/common-neighbor-detector.log.
All audited axioms are permitted; there are no holes.

* countable_coloring: if G is K4-free and d:N->V detects every existing common
  neighbor of every PAIR (allowing equal entries), G has a COUNTABLE PROPER
  VERTEX coloring. For v choose first(v)=i with v adjacent to d_i. Tag v by
  a j with v and d_i both adjacent to d_j, or none if no such j exists.
  Two adjacent vertices with equal i cannot both have the none tag, by the
  detector hypothesis. If they have equal j, they and d_i,d_j form K4.
  The palette is N x Option N. Isolated vertices cause no difficulty.
* principal_detector: in the mutual ultrafilter extension, any two vertices
  having a common neighbor already have a principal common neighbor. If r
  is common to p,q, r contains BOTH original traces; choose an original point
  in their intersection. This also handles p=q.
* first_extension_countable_coloring: the FIRST mutual extension of EVERY
  COUNTABLE K4-free graph has a countable proper vertex coloring.

This strengthens the older continuum-sized trace coloring of the first
extension. It does NOT assert countable proper vertex colorability of higher
extensions or extensions of merely countably vertex-colorable bases. Indeed
levelGraph of an arbitrary graph is countably vertex-colorable and its first
extension contains that arbitrary graph, so that weakening is invalid.

Potential further application (mathematical sketch ONLY, not yet formalized):
If a base H has a countable biclique EDGE cover, there is a countable family
of H-bicliques cofinal for FINITE positive side-membership constraints. Given
finite A0,B0 forming a biclique, choose one covering rectangle for each pair;
intersect its left sides along rows and right sides along columns, then union
rows/columns. These are still a complete biclique containing A0,B0. Countably
many finite matrices index all such choices; include the empty-side cases.
This family detects common neighbors of pairs in right H (keep the finitely
many intersection witnesses), so if right H is K4-free the detector theorem
would make it countably vertex-colorable.

For countable original H, right H has a countable biclique EDGE cover: an
adjacency is witnessed by two original points x,y, and the corresponding
membership conditions define a complete rectangle of right-H vertices.
Thus the preceding sketch would make right^2 H countably vertex-colorable
when it is K4-free. A graph embeds into its right adjoint via
v |-> (neighborSet v,{v}); hence right^3 H K4-free implies right^2 H K4-free.
The existing right_cover_of_rainbow would then cover right^3 H countably.
NONE of this additional right-tower application has been put into Lean yet.
It would rule out candidates, not settle the conjecture.

No active builds/searches remain. Spec.lean is unchanged and unresolved.

## Right towers over countable bases (now Lean-verified)

The preceding right-tower sketch has now been superseded by the complete
`RightTowerCountableCover.lean`, namespace Erdos595RightTowerCountable.
It compiles; /tmp/right-tower-countable-cover.log audits only permitted axioms.

* HasRectangleCover: a countable ordered biclique edge cover.
* matrixBiclique: row/column intersections of a 2x2 covering matrix suffice.
* detector_of_rectangle_cover: a countable rectangle cover of H gives a
  countable common-neighbor detector for right H.
* right_countable_coloring: with right H K4-free, that detector supplies a
  countable proper vertex coloring.
* witnessRectangle and right_rectangle_cover: right H has a countable
  rectangle edge cover whenever the original vertex type of H is countable.
* second_right_countable_coloring: right^2 H is countably vertex-colorable
  when K4-free, for countable original H.
* singletonHom and cliqueFree_of_right: v maps to (N(v),{v}), so K4-freeness
  reflects from right H to H.
* third_right_countable_cover: consequently right^3 H is countably
  triangle-free edge-coverable when K4-free, for countable original H.

These results rule out candidates, not settle Erdős 595. They do not yet
rule out all higher right towers or the third mutual-ultrafilter tower.
In particular, countable proper vertex colorability does NOT imply a
countable rectangle edge cover (uncountable induced matchings obstruct it).

## Countable detector completion and exact first-U reduction (new, verified)

`DetectorExtensionReduction.lean` compiles; namespace
Erdos595DetectorExtension; log /tmp/detector-extension-reduction.log.
All audited axioms are permitted. This supersedes the older unformalized
omega-stage detector-completion warning: just THREE families suffice.

Given a proper countable vertex coloring c of K4-free H, retain H and add:
* independent D(n,m), adjacent to old vertices of colors n or m;
* independent F(n), adjacent to old color n and to every D;
* one e, adjacent to every D and every F, but to no old vertex.

K4-freeness follows by three independent apex-family extensions: each new
neighborhood is triangle-free at the time it is added. The D/F/e vertices
are a countable UNIVERSAL common-neighbor detector, including equal pairs:
old-old use D(c(a),c(b)); old-D use F(c(a)); old-F/old-e use D(c(a),c(a));
D-D/D-F/F-F use e; D-e use F(0); F-e/e-e use D(0,0).

Verified declarations:
* completed_cliqueFree and oldEmbedding;
* new_common_neighbor and universal_detector;
* completed_countable_coloring;
* detectorBase: apply completion to levelGraph G;
* intoFirst: arbitrary K4-free G maps into U(detectorBase G), by the old
  fiber-ultrafilter homomorphism and U functoriality;
* all_cover_iff_detector_ultrafilter_cover: universal coverability of K4-free
  graphs is equivalent to coverability of FIRST U extensions of K4-free bases
  having a countable universal pair detector;
* no_vertex_palette_preservation: for ANY palette C there is such a base,
  countably vertex-colorable, whose first U extension has NO proper C-coloring.

Thus the detector condition alone cannot bridge the third-U gap. A universal
countable EDGE-cover preservation theorem under this condition would already
be a complete negative answer to Erdős 595. Proper vertex-color preservation
is actually false. The vertex TYPE of these bases is not asserted countable.
Spec.lean is unchanged and unresolved; no proof/disproof has been submitted.

## Infinite-palette triangle Ramsey bound (new, Lean-verified)

`InfiniteTriangleRamsey.lean` compiles and has an olean; namespace
Erdos595InfiniteTriangleRamsey; log /tmp/infinite-triangle-ramsey.log.
All audited declarations use only propext, Classical.choice, Quot.sound.
It supplies a positive infinite-palette Ramsey tool, NOT a K4-free witness.

Construction/proof:
* For a well-ordered vertex set and ordered edge labels c, recursively put
  u in pred(v) iff u<v and c(t,u)=c(t,v) for every t in pred(u).
* pred_trans, separation, pred_chain, pred_initial establish the canonical
  Erdős--Rado tree. A first disagreement is a common predecessor.
* With no monochromatic triangle, colors c(u,v) on pred(v) are injective.
* paths_rigid: a color-preserving order isomorphism of two predecessor paths
  is pointwise the identity. The proof is well-founded induction, using
  equality of predecessor sets and their edge-color profiles.
* code(v) records the set of ancestor colors and their order relation;
  code_injective proves it determines v.
* complete_no_mono_code: for ANY palette C, absence of a monochromatic
  triangle injects the vertex set into Code C = Set C x Set(C x C).
* complete_no_mono_binary: if C is countable, this gives an injection into
  N -> Fin 2, the sharp continuum upper bound in encoding form.
* complete_cover_iff_binary: a COMPLETE graph has a countable triangle-free
  edge cover iff its vertex set admits an injective binary-sequence encoding.
* arbitrary_palette_triangle_ramsey: the complete graph on Set(Code C)
  forces a monochromatic triangle under EVERY C-edge coloring, by Cantor.
* large_complete_no_cover: the complete graph on Set(N -> Fin 2) has no
  countable triangle-free edge cover. It has K4s and is NOT a witness.

Relevance/gap: this supplies the infinite-palette OUTER complete Ramsey graph
in a Folkman-style argument. The existing homogenization is still finite-
part, finite-palette; no infinite-part clique-preserving homogenization has
been established. Neither this Ramsey theorem nor finite Folkman permits
countable-palette compactness or external-coloring saturation arguments.

Lean details:
* Specify (wellFounded_lt (α := V)).induction; leaving the type implicit
  made the induction tactic generalize order-instance metavariables.
* For a fresh well-order instance, WellFoundedLT is installed explicitly as
  `⟨(inferInstance : IsWellOrder V WellOrderingRel).wf⟩`.
* Apply the generic-V theorem to Set(Code C), rather than installing its
  order locally in the final application: Set's existing subset order can
  otherwise be selected for polymorphic < / .ne expressions.
* Avoid simp_all over the entire binary-code injectivity context; it hit
  the heartbeat limit. Direct membership cases and simp only suffice.

Current status: Spec.lean is unchanged with its original sorry. No proof or
negation of erdos_595 has been submitted. No process remains running.

## Arbitrary-palette induced P4 Ramsey step (new, Lean-verified)

`HalfGraphRamsey.lean` compiles and has an olean; namespace
Erdos595HalfGraphRamsey; log /tmp/half-graph-ramsey.log.
All printed audits use only propext, Classical.choice, Quot.sound.
This is a positive infinitary partite lemma, NOT a settlement of Erdős 595.

* halfGraph A: left and right copies of a well order, with L(a)--R(b)
  iff a<b. It is bipartite and triangle-free.
* path: the bipartite P4 on Fin 2 + Fin 2, edges L0-R0,L0-R1,L1-R1.
* pathEmbedding: a<b<d embeds this path using left a,b and right b,d.
* ordered_triangle: the existing Erdős--Rado tree proves an ordered
  monochromatic triangle whenever A does not inject into Code C.
* arbitrary_palette_path: for ANY palette C, some half-graph forces an
  INDUCED monochromatic P4 in every edge coloring, preserving both parts.
  Its index set is Set(Code C) with a chosen well order.
* path_step: if K4-free H has designated induced subgraph H[D] isomorphic
  to P4, free amalgamation gives K4-free G such that every C-edge coloring
  has a copy of H whose designated P4 is monochromatic. Neither H nor C
  needs to be finite. The designated D is the four-vertex path.

Construction: apply the half-graph Ramsey theorem, then amalgamate copies
of H along EVERY induced embedding of H[D] into that half-graph. Existing
FiniteFolkmanAmalgamation.cliqueFree already handles infinite carriers.

This distinguishes the failure of infinite Hales--Jewett from the separate
induced bipartite Ramsey question. It does not establish an arbitrary
infinite bipartite partite lemma, or coherent homogenization of infinitely
many pairs. Even repeated P4 steps do not by themselves ensure compatible
copies of the original graph. An induced P4 cannot contain two sides of
one triangle, so path_step is not a triangle Ramsey theorem in disguise.

Other exploration this continuation (exponential evaluation, saturation,
ordered-tree decompositions, vector representations) yielded no new main
proof. The finite-palette exponential transfer cannot be upgraded by
ordinary compactness. No theorem resolving higher-shift exponentials or
the third generic mutual-ultrafilter extension was obtained.

Lean detail: install the well order in host_from_noninjection on a fresh
generic carrier B, and only then specialize to Set(Code C). Installing it
directly on Set again let the preexisting subset order leak into inference.
Use an explicit Type u for the existential host to avoid an unintended
independent universe parameter.

Current status: Spec.lean is unchanged, with its original sorry and SHA256
  de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45.
No settlement has been submitted. No background process remains running.

## Free-amalgamation cover preservation (new, Lean-verified)

`AmalgamationCover.lean` compiles and has an olean; namespace
Erdos595AmalgamationCover; log /tmp/amalgamation-cover.log.
All printed axioms are permitted; no holes or external certificates.

For the general graph in FiniteFolkmanAmalgamation (arbitrary carriers,
arbitrary family of induced attaching embeddings):
* palette: if H and K each have a triangle-free edge coloring with palette
  C, the amalgam has one with palette Option C. Use `some` of the old color
  on base-base and private-private edges, and `none` on all crossing edges.
  A mixed triangle has both some and none. An all-private triangle projects
  to H; an all-base triangle lies in K.
* countable_cover: consequently a free-amalgamation step preserves countable
  triangle-free edge coverability, with no cardinality assumptions.
* countable_cover_iff: if the family of attaching embeddings is nonempty,
  the amalgam is coverable iff BOTH H and K are coverable (both embed).
* triangleFree_base_iff: when K is triangle-free and at least one H-copy
  is attached, the amalgam is coverable iff H is coverable.

In particular, the positive arbitrary-palette P4 lemma from the previous
continuation does not create a non-coverable graph in one step. Finite
iterations starting with coverable graphs remain coverable. The existing
vertex-piece closure also blocks a naive countable/continuum-layer union
argument. A genuinely compatible long-limit construction would still need
a new theorem; no such theorem was proved here.

Exploration of ultraproduct saturation, club filters, graph roots over F3,
and possible uncountable focusing constructions did not yield a settlement.
Do NOT infer external-countable-color saturation from an ordinary graph
ultraproduct or from finite Ramsey properties. The neighboring conjecture
files are not present locally, and external DNS access still failed.

Spec.lean remains unchanged with its original sorry, SHA256
  de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45.
No proof or disproof has been submitted. No background process is running.

## Countably supported coordinate conflicts (Lean-verified)

`CountableConflictCover.lean` compiles; namespace Erdos595CountableConflict;
log /tmp/countable-conflict-cover.log. Printed audits use only permitted axioms.
For partial assignments p : V → I → Option Bool with countable support at each
vertex, if each graph edge witnesses opposite bits at a common coordinate,
then the graph is a countable union of triangle-free graphs. No clique bound,
cardinality bound, topology or summability is assumed. The proof indexes each
vertex's active coordinates by ℕ and colors an ordered edge by the two local
indices of a chosen conflict coordinate and its first endpoint's bit.
A monochromatic triangle forces all three witnesses to coincide and forces
opposite bits at its middle vertex.
Corollaries cover locally countable disjoint-sided rectangles (rectangles
may contain extra nonedges) and countably supported real coordinate families
where every graph edge has opposite signs at some coordinate.
This rules out these constructions as witnesses. No universal representation
of K4-free graphs by such conflicts, or triangle-hitting version, is proved.
Spec.lean remains unchanged and unresolved.

## Fixed generic reduced-power normal form (new, Lean-verified)

`FixedGenericReducedPower.lean` compiles and has an olean; namespace
Erdos595FixedGenericReducedPower; log /tmp/fixed-generic-reduced-power.log.
All five printed audits use only propext, Classical.choice, Quot.sound.

Let H be the ONE explicit countable generic K4-free graph from
CountableExtensionGraph. For any carrier V let I be its countable subsets,
with the atTop/fine filter from CountableCoordinateRepresentation. This
filter is proper and countably complete. Form the constant-coordinate
reduced power H^I with adjacency holding eventually in that filter.

* Coordinate.model: embed each countable induced coordinate of a K4-free G
  into H using CountableGenericUniversality. Countability of the coordinate
  carrier is essential, not just countable proper colorability.
* Coordinate.embedding: every nonempty K4-free G on V embeds INDUCEDLY into
  this power. The power graph depends only on V, NOT on G. Choose a default
  vertex, project into each countable coordinate, then apply its embedding
  into H. Adjacency is recovered on coordinates containing both endpoints.
* Coordinate.power_cliqueFree: the whole reduced power remains K4-free.
* Coordinate.no_cover_preserved: a genuine witness transfers to this power.
* all_cover_iff_fixed_reduced_powers: universal coverability of K4-free graphs
  is equivalent to coverability of every proper countably complete reduced
  power of this ONE H.
* all_cover_iff_fine_powers: it is enough to use just the canonical fine
  filter on countable subsets, one power for each carrier V.

Neither side of either equivalence is proved. This is a faithful candidate
normal form, not a non-coverability result or a countable-palette compactness
argument. The fine filter is NOT asserted to be an ultrafilter.

Other exploration this continuation (hypergraph root restrictions, earlier
neighbor orders, higher-shift exponentials, and ultrafilter traces) gave no
new main lemma. The third generic mutual-U stage and the higher-shift
exponential family remain unresolved. Do not infer saturation for an external
countable edge coloring from saturation of the pure graph, or infer a
countably complete ultrafilter from the proper countably complete filter.

Lean detail: use `include hG v₀ in` for no_cover_preserved because its displayed
type mentions neither hypothesis, although its proof uses the embedding.
The empty-carrier case is handled by is3Clique_iff and isEmptyElim.

Spec.lean remains unchanged with its original sorry and SHA256
  de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45.
No proof or disproof has been submitted. No build/search is running.

## Triangle-component reduced-product obstruction (new, Lean-verified)

`TriangleComponentProduct.lean` compiles and has an olean. Namespace
Erdos595TriangleComponentProduct; log /tmp/triangle-component-product.log.
All printed audits use only the three permitted axioms.

* Edge G is the subtype of actual unordered graph edges. Step relates two
  edges of one triangle. Component G is the quotient by its equivalence
  closure, so components are chains of triangles sharing EDGES, not ordinary
  graph connected components. Different components may share vertices.
* tag labels an arbitrary pair by some component if it is an edge, else none.
* piece G q is the spanning edge subgraph belonging to q.
* cover_of_pieces: countable triangle-free edge palettes can be reused on
  ARBITRARILY MANY such components. All three sides of a triangle have the
  same tag, so there is no cardinality restriction on the component family.
* component_eventually: edges in the same component of a proper-filter product
  have equal coordinate component tags eventually. Only finite intersections
  are needed for this lemma (a component connection has finite length).
* anchorHom: choose one representative product edge of a component. At each
  coordinate choose that edge's coordinate component, or the empty graph
  where the anchor is not an edge. The whole product component maps into the
  product of these coordinate pieces.
* pieces_finite: if EVERY triangle component of EVERY coordinate graph has a
  finite triangle-free edge cover, then each triangle component of a proper
  COUNTABLY COMPLETE filter product also has a finite cover. Bounds can vary
  both with the coordinate and with the component. Uses finite_cover from
  CompleteFilterEdgeCover only after choosing the anchor pieces.
* countable_cover: the entire product is consequently countably coverable.
  There is NO countability or clique hypothesis on the coordinate carriers.
  Disjoint finite Folkman pieces therefore cannot evade the finite-coordinate
  obstruction just by combining them into one infinite target. More general
  vertex-gluings also qualify IF their actual triangle components stay finitely
  coverable; arbitrary gluings must not be assumed to preserve that hypothesis.
* countable_hom_reflection: any hom from a COUNTABLE graph into a countably
  complete product reflects into one coordinate. This asserts a homomorphism,
  NOT an induced embedding, and gives no reflection for uncountable graphs.

The fixed countable generic target is not shown to satisfy the finite-per-
triangle-component hypothesis. This does not give a cover of its reduced
powers, or a non-coverable example.

Lean details: clear the equality hypothesis after obtaining EqvGen via Quot.eq,
otherwise induction generalizes it into unwanted premises. Work with spanning
edge pieces so anchorHom can be the identity on vertex functions. Exceptional
coordinates use the empty graph rather than requiring every anchor coordinate
pair to be an edge.

## Radius-three finite cover versus radius-four universality (new, verified)

`TriangleRadiusThree.lean` compiles and has an olean. Namespace
Erdos595TriangleRadiusThree; log /tmp/triangle-radius-three.log.
All three printed audits use only permitted axioms.

Near allows waiting or moving between two edges of a triangle. RadiusThree
is exactly three such moves, with waiting allowed.
* first_hits: after one move from ab, the edge contains a or b.
* second_inside: after two moves, BOTH endpoints belong to N(a) union N(b).
* radius_three_touches: after three moves, at least one endpoint belongs to
  N(a) union N(b). These facts do NOT need K4-freeness.
* three_cover_of_touch: any K4-free G all of whose edges touch N(a) union N(b)
  has a THREE-piece triangle-free edge cover. The pieces are the union of
  the two induced-neighborhood edge sets, the cut across N(a), and the cut
  across N(b). The first union is triangle-free: if a triangle's sides are
  covered by two induced neighborhoods, two sides belong to the same one,
  which would put all three vertices in that neighborhood and yield a K4.
* radius_three_finite_cover: hence global triangle-sharing radius at most
  three gives a finite (indeed three-piece) cover, at every cardinality.

This is a sharp threshold between this finite-cover result and the already
verified radius-FOUR normalization in TriangleRadius. It is NOT a claim that
three is the optimal number of pieces for radius-three graphs.

A contemplated application to ultrafilter towers is blocked: one cannot assume
that every triangle at stage two/three has an edge within radius three of an
original principal edge. In DelayedUltrafilter, second(v) has no adjacency to
any twice-principal original vertex (adjacency there is original neighborhood
membership in flatten(second(v)), which flattened_neighborhood_empty forbids).
For a triangle input, its three second vertices give a triangle all of whose
edges therefore fail the necessary radius-three touching condition. This
observation combines existing results mathematically; no new packaged Lean
counterexample for it was added here.

Other exploration (locally finite target products, higher shifts, topology,
and model-theoretic color saturation) did not settle the main conjecture.
No claim about those unproved routes should be inferred.

Spec.lean is unchanged, with its original sorry and SHA256
  de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45.
No proof/disproof has been submitted. No build/search remains running.

## Locally finite chromatic neighborhoods in complete-filter products (new, verified)

`LocalChromaticProduct.lean` compiles and has an olean. Namespace
Erdos595LocalChromaticProduct; log /tmp/local-chromatic-product.log.
All four printed axiom audits use only propext, Classical.choice, Quot.sound.

* cover_of_neighborhood_colorings packages the general local criterion:
  if every induced vertex neighborhood has a countable proper vertex
  coloring, the whole graph has a countable triangle-free edge cover.
  Reuse the local coloring at the larger endpoint of each ordered edge.
* localPiece is the spanning induced-neighborhood edge graph, with isolated
  vertices outside the neighborhood. Its finite proper coloring is obtained
  by reserving one additional color for those isolated vertices. This avoids
  incorrectly requiring every coordinate neighborhood to be nonempty.
* neighborhoodHom maps a product neighborhood into the product of its
  coordinate localPieces. All three required adjacencies hold eventually;
  coordinate membership in the neighborhood need NOT hold everywhere.
* neighborhoods_finitely_colorable: for a proper COUNTABLY COMPLETE filter,
  if every induced neighborhood of every factor has SOME FINITE proper
  coloring, then every induced neighborhood of the product has a finite
  proper coloring. Neither the coordinate bounds nor the resulting bounds
  across product vertices must be uniform.
* countable_cover: the resulting product is countably edge-coverable.
* locally_finite_cover: in particular all locally finite coordinate graphs
  are ruled out, even with infinite carriers and infinite global chromatic
  number. No K4 bound or other clique hypothesis is used in these results.

This is a local VERTEX-chromatic hypothesis, not just finite triangle-free
EDGE-coverability of the coordinate neighborhoods (the latter is automatic
for K4-free coordinates and must not be substituted). The fixed generic
countable target is not shown to satisfy this finite-local-chromatic
hypothesis. Consequently the canonical generic fine powers remain unresolved.

Exploration of countably supported conflict representations, Boolean-valued
names, local ordering strategies, and asymmetric ordered-triangle Ramsey
extensions did not establish a new universal representation/cover theorem
or a non-coverable graph. In particular, do not assume a countably complete
ultrafilter extension, external-color saturation, or coherent infinitary
partite embeddings.

Spec.lean remains unchanged and unresolved, with its original sorry.
No proof/disproof has been submitted. No background build/search is running.

## Chromatic-domain filter for exponential graphs (new, Lean-verified)

`ExponentialChromaticFilter.lean` compiles and has an olean. Namespace
Erdos595ExponentialChromaticFilter; log /tmp/exponential-chromatic-filter.log.
All six printed axiom audits use only propext, Classical.choice, Quot.sound.

* chromaticFilter B is generated under COUNTABLE intersections by complements
  of independent vertex subsets of B.
* avoids_labeled and avoids_colorable: every countably vertex-colorable
  subset has complement in this filter.
* mem_iff: S belongs to the filter EXACTLY when the induced graph on its
  complement has a proper natural-number vertex coloring. Thus this is the
  dual of the countable VERTEX-chromatic ideal, not the edge-cover ideal.
* filter_neBot: if B has no countable proper vertex coloring, the filter is
  proper. It is countably complete by construction. No ultrafilter extension
  retaining countable completeness is asserted.
* eventually_adj: if f,g are adjacent in H^B, the bad set where H(f(x),g(x))
  fails is countably vertex-colorable by (f(x),g(x)). Therefore pointwise H
  adjacency holds eventually in chromaticFilter B.
* toPower: the identity on functions is an injective graph HOMOMORPHISM from
  H^B to the constant-H reduced power over chromaticFilter B. It is NOT an
  induced embedding; the converse adjacency implication is not established.
* cover_of_finite_neighborhood_colorings: the new local-chromatic product
  theorem applies to ALL exponential domains B of uncountable vertex
  chromatic number, if every target neighborhood has some FINITE proper
  vertex coloring. The bounds may vary with the target vertex. No clique
  bound or finite global target edge palette is required.
* locally_finite_target: every countable locally finite target is ruled out,
  including targets with unbounded finite/global chromatic parameters.
* cover_of_finite_triangle_components: the earlier finite-per-triangle-
  component product theorem also transfers to all exponential domains.
  These components are formed by triangles sharing EDGES, not graph
  connected components.

The fixed countable generic target is not covered by either proved
hypothesis. In particular the finite proper-neighborhood-coloring condition
must not be weakened to finite triangle-free EDGE-coverability of each
neighborhood, which would be automatic for K4-free targets.

This continuation also investigated second-shift profiles, saturation,
finite-pattern senders, and topological/Boolean-valued representations.
No higher-shift countable-cover or non-cover theorem was established.
Iterating the first-shift profile palette beyond the continuum does not
supply the required countable edge cover. A profile graph's external
common-neighbor detectors cannot be used with K4-freeness of only a subgraph:
the detector vertices need not lie in that subgraph. Likewise, pure-graph
saturation gives no automatic saturation of an external countable coloring.

Spec.lean remains unchanged with its original sorry and checksum
  de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45.
No proof/disproof has been submitted. No background build/search remains.

## One-sided cone supports at the third mutual stage (new, verified)

`OneSidedSupport.lean` compiles and has an olean. Namespace
Erdos595OneSidedSupport; log /tmp/one-sided-support.log. All five printed
axiom audits contain only propext, Classical.choice, Quot.sound.

For an original ultrafilter r, cone G r consists of first-stage p with the
ONE-SIDED Fubini relation R(r,p). This is not its mutual neighborhood.
* cone_triangleFree: the first-stage induced graph on this cone is
  triangle-free. Three mutually adjacent points in it, together with r,
  would have all six forward Fubini relations of a transitive four-clique.
* trace_subset_cone: the first-stage neighborhood trace of a second-stage
  Q is contained in cone(flatten Q). Uses only the reverse half of mutual
  first-stage adjacency and the definition of ultrafilter flattening.
* second_supported: if P,Q are adjacent at stage two, cone(flatten Q) is
  a member of P.
* third_supported: every nonisolated stage-three X contains the lifted
  cone of some r. Concretely, {P | cone G r belongs to P} belongs to X.
* third_support_triangleFree: this double lift of a fixed cone is
  triangle-free in the third-stage graph.

This formalizes the previous unformalized observation. It does NOT yield
countable edge coverability: the indices r range over Ultrafilter V, not
Set V. For countable V this index set can exceed the continuum. No
compression of these cone indices has been proved. Flattening is still
NOT claimed to be a graph homomorphism.

Other exploration in this continuation did not close either main gap in
infinitary partite Ramsey (arbitrary bipartite targets and compatible
infinitely many part pairs), nor establish a cover/non-cover result for
second ordered-Fubini or third mutual-Fubini powers. Direct DNS-over-HTTPS
attempts to 1.1.1.1 and 8.8.8.8 timed out; no reference was retrieved.

Spec.lean remains unchanged with the original sorry; no settlement has
been submitted. No background build or search is running.

## Continuum-complete vertex-cover filter (new, verified)

`VertexCoverFilter.lean` compiles and has an olean. Namespace
Erdos595VertexCoverFilter; log /tmp/vertex-cover-filter.log. All printed
axiom audits use only propext, Classical.choice, Quot.sound.

* span G S retains the carrier and only the edges internal to S.
* On G S means that span has a countable triangle-free EDGE cover.
  on_iff_induce identifies this with coverability of the induced graph.
* on_iUnion proves closure under families whose index type embeds into
  binary sequences. This follows from Work's vertex-piece gluing, including
  the empty-index and empty-fiber cases; it does NOT restrict |V|.
* vertexFilter G is dual to this vertex-subset ideal. In Type 0 it is a
  CardinalInterFilter at succ(continuum), hence countably complete.
* proper_iff: it is proper EXACTLY if G is non-coverable. No proper example
  satisfying K4-freeness has been constructed.
* inter_mem intersects at most continuum many large vertex sets.
* large_no_cover: every large vertex set is still non-coverable.
* avoids_neighborhood_family: for K4-free G, the vertex filter simultaneously
  avoids the neighborhoods of any family of at most continuum many vertices.

Do not transfer this stronger completeness to CountableBadEdge's EDGE
filter. These are different filters on different carriers. Neither is
claimed to be an ultrafilter. A countably/continuum-complete ultrafilter
extension is still unjustified.

The attempted direct coloring-killing construction is blocked by the
EXISTING FiniteAdaptedExtension theorem: any coverable old graph has a valid
finitely adapted coloring extending unchanged across every extension whose
new induced piece is coverable. This does not supply compatible colorings
at long limits.

## Arbitrary-palette finite bipartite Ramsey theorem (new, verified)

Three new compiled files, all with oleans and clean permitted-axiom audits:
* InfiniteFourRamsey.lean, namespace Erdos595InfiniteFourRamsey,
  log /tmp/infinite-four-ramsey.log (about 150 lines).
* PairBoxRamsey.lean, namespace Erdos595PairBoxRamsey,
  log /tmp/pair-box-ramsey.log (about 85 lines).
* FiniteBipartiteInfinitePalette.lean, namespace
  Erdos595FiniteBipartiteInfinitePalette,
  log /tmp/finite-bipartite-infinite-palette.log (about 225 lines).

This genuinely strengthens the prior arbitrary-palette P4 result:
EVERY FINITE BIPARTITE target has an induced, two-side-preserving bipartite
Ramsey host for an arbitrary palette. The host is not asserted finite.
The palette may be empty in the final ramsey and finite_bipartite_step
statements (that case is vacuous on a nonempty host).

Proof:
1. InfiniteFourRamsey extends the existing predecessor tree from avoiding
   monochromatic triangles to avoiding monochromatic K4s in a complete
   ordered graph. Along a branch, each color occurs at most twice. The label
   (original color, Boolean indicating an earlier occurrence) is injective.
   Existing path rigidity plus these labels encodes vertices in
   Code (C x Bool); Cantor gives four homogeneous ordered points.
   host: for any C, there is A with a linear order such that every
   col : A -> A -> C is constant on all six increasing pairs of some
   strictly increasing Fin 4 copy. No symmetry hypothesis on col is needed.
2. PairBoxRamsey gives a FINITE PRODUCT of four-point pair Ramsey spaces.
   For the last coordinate, color its ordered pairs by FUNCTIONS from all
   previous coordinate pair choices to C. Homogenize this coordinate, then
   apply the induction hypothesis. This avoids needing a general higher-arity
   Erdos-Rado theorem. Axis packages a carrier and linear order. Pair, Family,
   SmallPair, pairMap, boxMap are the auxiliary definitions.
3. For E : L -> R -> Prop with L,R finite, use coordinates
      L + (R + L x R).
   Left and right codes take values in Fin 4. Dedicated L/R coordinates
   separate same-side vertices. At a nonedge (a,b), the corresponding
   coordinate has left(a)=2 and right(b)=1; all other comparisons there are
   positive (other left values 0, other right values 3). Therefore
      E a b iff forall k, left a k < right b k.
   A host is the bipartite dominance graph on two copies of the product of
   axis carriers. Its edges correspond exactly to families of increasing
   pairs. The box theorem makes ALL edges of the encoded target one color.

Main final theorems:
* ramsey E C: an induced two-side-preserving monochromatic copy of graph E
  in a triangle-free host for every edge coloring by C.
* finite_bipartite_step E H hH D e, where
      e : graph E ~=g H.induce D,
  and only L,R are finite: a K4-free host contains a copy of the arbitrary
  ambient H whose designated finite induced bipartite D is monochromatic.
  The ambient carrier and palette can be arbitrary. This uses the existing
  free amalgamation, just as path_step did for P4.

CRITICAL LIMITATIONS / UPDATED NEXT-STEPS:
* It is now incorrect to list the FINITE bipartite arbitrary-palette Ramsey
  lemma as missing. It is proved above.
* Arbitrary INFINITE bipartite targets remain outside this proof. Coordinate
  count in inequalities_iff depends on the size of the finite target. Later
  partite intermediate graphs are infinite after the first arbitrary-palette
  step, so the finite-source theorem does not iterate as FiniteFolkmanStep did.
* The final bipartite theorem preserves TWO SIDES, NOT a separate original
  vertex label on every point of each side. This distinction prevents using
  it to simultaneously homogenize arbitrary different original part pairs.
* Finite products only: box does not cover infinitely many coordinates.
* No compatible selection across infinitely many part pairs is proved.
* Arbitrary families of free amalgamations of covered graphs are still
  countably coverable by AmalgamationCover. Thus no finite or countable chain
  of these steps is itself a witness.
* Bounded finite degree on one side does not imply finite dominance/order
  dimension: incidence graphs of all pairs are a cautionary example. No
  theorem extending this Ramsey lemma to those infinite incidence targets
  has been established.

Spec.lean remains unchanged with original sorry and SHA256
  de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45.
No settlement has been submitted, and no background build or search remains.

## Prescribed-color extension across bipartite amalgamations (new, verified)

The main conjecture in `Spec.lean` is still unresolved and unchanged.

### `Submission/BipartiteAmalgamationExtension.lean`

Namespace `Erdos595BipartiteAmalgamationExtension`.

This strengthens mere cover preservation: an arbitrary valid natural-number
edge coloring on a distinguished old copy extends **literally unchanged** to
its free amalgamation with a triangle-free, finitely vertex-colorable base.
It requires no finiteness of the attaching subgraph or of the copy family.
In particular, it applies to all bipartite Ramsey bases constructed so far.

Declarations:

* `fallback`: cross edges have the finite vertex-side color of their base
  endpoint; private-private edges use the old coloring shifted above the
  finite side palette.
* `color`: overrides the fallback on every unordered pair in the distinguished
  old copy, using `Function.extend`.
* `color_copy`: literal preservation on all pairs of old vertices, not just
  adjacency or color-equality patterns.
* `color_other_private`: pairs incident with another private copy keep the
  fallback color.
* `valid_at_distinguished`: a triangle touching a distinguished private
  vertex is wholly contained in the distinguished copy.
* `color_valid`, `exists_extension`.

For triangles outside the distinguished private copy: all-base triangles
are absent; a triangle with one private vertex has two cross-edge colors
that differ by the base's proper vertex coloring; a triangle with two
private vertices has cross colors below the private-private palette;
all-private triangles inherit validity from the old coloring.

Build log `/tmp/bipartite-amalgamation-extension.log`; `.olean` built.
`exists_extension` uses only `propext`, `Classical.choice`, `Quot.sound`.

### `Submission/WellOrderedColorExtension.lean`

Namespace `Erdos595WellOrderedColorExtension`.

A separate generic transfinite extension theorem for ternary
triangle-avoidance constraints, any nonempty palette, and any well-ordered
stage type. Variables have ranks `r : X → I`. `Before` tests constraints
whose three ranks are strictly below a stage; `Through` tests ranks at
most that stage. `Step` requires validity through the stage and literal
agreement at every earlier rank.

* `stage`: well-founded recursion choosing a stage extension when it exists.
* `stage_spec`: stage validity and compatibility with earlier fixed colors.
* `global_coloring`: if **every** valid coloring before **every** stage
  extends through it, then a global valid coloring exists.

This is NOT countable-palette compactness: the prescribed-extension
hypothesis is essential. The proof takes the maximum of the three ranks
in each constraint and uses compatibility with that stage.

Build log `/tmp/well-ordered-color-extension.log`; `.olean` built.
`global_coloring` uses only the permitted axioms.

### Consequence and scope

These theorems identify a stronger barrier than incompatible selections
at a merely countable limit: continuously iterating the same bipartite
free-amalgamation steps along a well order preserves a compatible
countable coloring. The direct system/graph-isomorphism bookkeeping of
this combined corollary is not formalized as a single theorem; the two
extension ingredients above are formalized.

Therefore a hypothetical Ramsey theorem for the infinite bipartite
incidence targets would still NOT, by a straightforward continuous
transfinite partite construction, settle Erdős 595. An inverse-limit or
other genuinely different construction would need a separate argument.
No infinite bipartite incidence Ramsey theorem was proved or disproved in
this continuation. External access to erdosproblems.com again failed DNS.

## Countable base palette in the prescribed-extension lemma (strengthened, verified)

`BipartiteAmalgamationExtension.lean` has been strengthened in place.
The base need only be triangle-free and have a proper **countable** vertex
coloring `side : B → ℕ`; a finite proper palette is no longer required.
This supersedes the finite-palette hypothesis in the preceding entry.

The fallback uses `2 * side b` on base/private pairs and
`2 * c(old_pair) + 1` on private/private pairs. Parity, rather than a finite
upper bound, separates mixed triangles with two private vertices. The two
cross colors in a triangle with two base vertices still differ because
`side` is proper. Overriding on the distinguished old copy works exactly
as before, so `color_copy` still preserves every old unordered-pair color
literally.

The updated `exists_extension` compiles and its axiom audit is exactly
`[propext, Classical.choice, Quot.sound]`.
Log: `/tmp/bipartite-amalgamation-extension.log`.
No original conjecture statement or import was changed.

This continuation also reconsidered saturation, higher-shift exponentials,
third-U cone supports, and triangle couplings of avoiding edge filters.
No theorem handling arbitrary external countable colorings in those
constructions was obtained. In particular, no saturation assertion or
countably complete ultrafilter extension is justified by this exploration.
The original `Spec.lean` remains unresolved and unchanged, SHA256
`de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45`.

## Missing-color and finite-attachment amalgamation extensions (new, verified)

`Submission/UnusedColorAmalgamationExtension.lean` compiles and has an olean.
Namespace `Erdos595UnusedColorAmalgamationExtension`.
Log `/tmp/unused-color-amalgamation-extension.log`.

* `exists_extension`: a prescribed valid coloring `c` on a distinguished old
  copy extends literally across free amalgamation with ANY triangle-free base,
  provided some natural-number color `k` is absent on edges of the attaching
  induced subgraph `H.induce D`.
* `exists_extension_finite`: the missing-color condition holds automatically
  when `D` is finite. There is NO vertex-chromatic bound on the base, and no
  cardinality bound on the old graph or the copy family.

Construction: base/base fallback is `k+1`, cross fallback is `k`, and private
fallback is `c(old_pair)+k+1`. Override all pairs of the distinguished copy
by `Function.extend`. A base edge either has fallback `k+1` or an old attaching
edge color, so is never `k`. This handles triangles with one nondistinguished
private vertex. Triangles with two private vertices use distinct palettes;
triangles wholly private inherit validity; triangles touching distinguished
private vertices are contained in that old copy. The base has no triangles.

Axiom audits for both existence theorems are precisely the three permitted
axioms. No `sorry` was introduced in this auxiliary file.

Together with `WellOrderedColorExtension.global_coloring`, this strengthens
another barrier to straightforward transfinite amalgamation: finite attaching
subgraphs allow literal extension even when the triangle-free Ramsey bases
have arbitrarily large vertex chromatic cardinal. The combined direct-system
bookkeeping is still not one Lean theorem; the extension ingredients are.

### Odd-cycle discussion (mathematical, not formalized)

The fixed odd closed-walk Ramsey observation in the previous continuation is
valid: combine countably many avoiding edge-colorings into a palette N^N;
if every fiber has no odd closed walk, it is bipartite, yielding a proper
vertex coloring by `(N^N) -> Fin 2`. A triangle-free graph of larger chromatic
cardinal contradicts this. In fact, finite odd-cycle targets can also be
forced in high-cardinal ordered shift graphs by finite-set Ramsey arguments.
No new odd-cycle Lean theorem was added in this continuation.

This does not produce monochromatic triangles. A single free amalgamation
still preserves coverability (`AmalgamationCover`, even without a bipartite
base), and the new finite-attachment extension theorem prevents a naive
continuous transfinite finite-attachment repair.

External access remains unavailable: direct-IP HTTPS attempts timed out.
No mathematical reference or updated solution was obtained.
`Submission/Spec.lean` still contains its original unresolved `sorry`; no
proof or disproof of the conjecture has been submitted.

## Countable-palette adapted reflection is false (new, Lean-verified)

`Submission/AdaptedReflectionObstruction.lean` compiles without warnings,
with an olean. Namespace `Erdos595AdaptedReflection`.
Log `/tmp/adapted-reflection-obstruction.log`.

Main theorem `exists_reflection_failure` supplies a graph G and natural-number
edge coloring c such that:

* G is K4-free and countably triangle-free-edge-coverable (indeed a cone over
  a triangle-free graph, so two pieces suffice);
* c is valid: no monochromatic triangle;
* EVERY triangle-free INDUCED subgraph, with this SAME c restricted to it,
  admits an adapted natural-number vertex labeling;
* G itself admits NO adapted natural-number vertex labeling for c.

Thus failure of adapted labeling cannot be assumed to reflect to a
triangle-free induced subgraph, even with the actual countable palette.
This is NOT a covering counterexample: G has a different two-color cover.

Construction:

* X = N -> Fin 2, p = the zero sequence, Y = X minus p.
* Take triangle-free R on B with no proper vertex coloring by X -> N,
  using Work.exists_triangleFree_not_colorable.
* The base A has vertices B x Y, with adjacency R(b,b') AND x != y.
  The unequal-code condition is essential: omitting it can make the
  first-difference pullback invalid at the cone apex.
* G is the cone over A. Map its apex to p and (b,x) to x. Color each edge
  by the first differing bit of its endpoint codes.
* A hypothetical adapted f on G gives profiles h_b:X->N, taking f(apex)
  at p and f(b,x) elsewhere. Equal profiles on an R-edge contradict the
  first-difference diagonal lemma. If a diagonal witness is p, it violates
  adaptation on an apex edge; otherwise it violates adaptation on a base
  edge. Hence profiles properly color R, a contradiction.
* Any induced subset omitting the apex has the adapted labeling given by
  the colors of its apex spokes; validity on the corresponding cone triangles
  proves this. Any triangle-free induced subset containing the apex has an
  independent base part and hence is bipartite, so has an adapted labeling.

The main theorem's axiom audit is exactly
`[propext, Classical.choice, Quot.sound]`.

An initial exact finite test also found a two-color failure on W5 and on
K_{2,2,2}; script `/tmp/test_adapted_obstruction.py`. These finite searches
are not Lean certificates and are superseded, for the intended route, by
the verified countable-palette construction above.

### Other exploration in this continuation

No proper avoiding countably complete edge filter or correlation-preserving
K4-free compactification was constructed. No saturation theorem for arbitrary
external countable edge colorings was established. The false adapted-reflection
lemma must not be used to bridge that gap. Spec.lean remains unchanged and
unresolved; no proof/disproof has been submitted.

## Four-dimensional quadratic-space candidate ruled out (new, Lean-verified)

The proposed graph on unit vectors of
`Q(x)=x0^2+x1^2+x2^2+d*x3^2`, with orthogonality adjacency and nonsquare d,
is NOT a route to a witness. A stronger covering theorem is now verified.

### CountableCodegreeColoring.lean

Namespace `Erdos595CountableCodegree`; 233 lines, compiled olean.
Log `/tmp/countable-codegree-build.log`.

* `coloring_nat_of_countable_common_neighbors`: if EVERY DISTINCT PAIR
  of vertices has countably many common neighbors, the graph has a proper
  natural-number vertex coloring. No cardinality restriction on the carrier.
* `coloring_of_rank`: a general helper combining proper countable colorings
  of rank classes with a well-founded height coloring, when every vertex has
  at most one lower-rank neighbor.

Proof: enumerate common neighbors by countably many binary operations. Their
first-order substructure closure has cardinal at most `max aleph0 #S`.
Use an initial-cardinal well order and rank each vertex by the least closed
initial segment containing it. Finite character ensures that the strict
predecessor closure omits that vertex; hence it has at most one lower-rank
neighbor. Cardinal induction colors each small rank class, and well-founded
height handles edges between classes. This is actual cardinal induction,
not a countable-palette compactness assertion.

### FiniteDimensionalOrthogonalityCover.lean

Namespace `Erdos595FiniteDimensionalOrthogonality`; compiled olean.
Log `/tmp/finite-dimensional-orthogonality.log`.

* `local_common_subsingleton`: in the projective nonisotropic orthogonality
  graph of a nondegenerate symmetric bilinear form in dimension at most 4,
  two distinct vertices in a fixed neighborhood have at most one common
  neighbor WITHIN that neighborhood.
* `neighborhood_coloring`: all those neighborhoods have proper countable
  vertex colorings, by the preceding countable-codegree theorem.
* `countable_cover`: the full projective graph has a countable triangle-free
  edge cover. NO K4-freeness assumption is necessary.
* `countable_cover_of_representation`: the cover pulls back to ANY graph G
  with a vector map p such that `B(p v,p v) != 0` for every vertex and
  `B(p v,p w)=0` on every edge. The representation need not be injective,
  need not reflect adjacency, and the field can have arbitrary cardinality.

Linear algebra: a center x and two projectively distinct neighbors a,b are
linearly independent (use B(x,x) != 0 and B(x,a)=B(x,b)=0). Their orthogonal
complement has dimension at most one. All common projective neighbors lie
there, so they coincide. Passing to projective points removes the opposite-
vector/twin issue. This argument applies to the unit quadratic candidate
without needing its determinant-based K4-freeness proof.

All printed final axiom lists in both files are exactly
`[propext, Classical.choice, Quot.sound]`; neither file has holes.

### Exact finite experiments (not Lean certificates)

`/tmp/quadratic_sat.py` enumerates the unit-vector graph over F_p, identifying
opposite vectors, and asks CaDiCaL for a two-edge-coloring without a
monochromatic triangle. Results in `/tmp/quadratic_sat.log`:

* p=3, d=2: 15 vertices, 45 edges, 15 triangles — SAT.
* p=5, d=2: 65 vertices, 325 edges, 325 triangles — SAT.
* p=7, d=3: 175 vertices, 2450 edges, 2450 triangles — SAT.
* p=11, d=2: 671 vertices, 22143 edges, 36905 triangles — SAT.
* p=13, d=2: 1105 vertices, 43095 edges, 100555 triangles — UNKNOWN
  after the 120-second timeout. This is NOT an UNSAT result.

The structural countable-cover theorem supersedes these experiments for
assessing the candidate. The actual solver is
`/root/.elan/toolchains/leanprover--lean4---v4.27.0/bin/cadical`.

Spec.lean remains unchanged and unresolved. The investigation of stability,
higher-dimensional forms, infinitary amalgamation, ultrafilter towers,
higher-shift exponentials, and asymmetric Ramsey methods in this continuation
has NOT produced another theorem or a settlement. In particular, no general
stable-graph covering theorem, no infinite-attachment Ramsey principle, and
no countable-palette compactness principle has been established.

## Latest infinitary-route review (no settlement)

Reviewed the higher-shift exponentials, generic ultrafilter towers, finite
bipartite arbitrary-palette Ramsey theorem, and asymmetric triangle-arrow
reduction. No new verified theorem was obtained. In particular:

* The finite-target bipartite theorem does not give infinite-target induced
  Ramsey hosts or compatible homogenization across infinitely many part pairs.
* Pure-graph saturation still does not control arbitrary external edge colors.
* Triangle hypergraphs of K4-free graphs are linear and have no Berge triangle,
  but these abstract conditions alone are insufficient: the previously studied
  matched-pair hypergraph already obstructs that shortcut. Graphical realization
  also imposes finite endpoint-support/closure bounds (RootObstruction.lean).
* Possible arguments using graphic-matroid closure, countably closed forcing,
  higher-dimensional Witt-index-one forms, or generic Gram representations were
  only explored informally. No required representation, forcing-absoluteness,
  countable-cover, or non-cover theorem was proved. Do not use them as results.

External reference requests again failed at DNS resolution. No updated source
or solution was obtained. Submission/Spec.lean remains unchanged, with the
original unresolved sorry. No proof/disproof has been submitted.

## Continuous transfinite amalgamation cover (new, Lean-verified)

Submission/TransfiniteAmalgamationCover.lean compiles without warnings and
has an olean. Namespace Erdos595TransfiniteAmalgamation. Build log:
/tmp/transfinite-amalgamation-cover.log. This completes the graph-level
bookkeeping previously left implicit between the local prescribed-color
extension lemmas and WellOrderedColorExtension.global_coloring.

Definitions:
* Earlier/Through and their induced graphs use a vertex rank r:V->I.
* StageExtension requires every valid coloring of the strict predecessor
  graph to extend literally to the through-stage graph, on ALL old pairs.
* AmalgamationStage packages an actual graph isomorphism from the free
  amalgam to the through-stage induced graph, and requires its distinguished
  old copy to equal the literal predecessor inclusion. Its base is triangle-free.

Theorems:
* cover_of_stage_extensions: global countable cover from these extensions,
  for an arbitrary well-ordered I, with no cardinal bound on V or I. Uses
  pair rank max(r a,r b), and transports triangle constraints to the earlier
  generic well-founded theorem. Not a compactness assertion.
* AmalgamationStage.finite_extension: applies the missing-color finite-
  attachment extension theorem; there is no vertex-chromatic bound on the base.
* AmalgamationStage.countably_colorable_extension: no finiteness requirement
  on attachments when the triangle-free base has a proper N-coloring.
* cover_of_finite_amalgamation_stages and
  cover_of_countably_colorable_amalgamation_stages: the combined graph-level
  theorems. Initial stages may have any countably edge-coverable graph, not
  just a triangle-free graph. Every other stage must have the stated actual
  presentation, including the old-copy compatibility condition.

The three audited global theorems depend exactly on propext,
Classical.choice, Quot.sound. No holes were introduced.

This rules out the stated continuous well-ordered construction schemes,
NOT arbitrary transfinite constructions. The exploration of copy-code
saturation did not repair the infinitary Ramsey gap: homogenizing a fixed
finite set of edges is not hereditary under arbitrary smaller copies.
Homogenizing ALL edges between two parts would be hereditary, but requires
an infinite-target step. Moreover a straightforward continuous iteration of
bipartite free amalgams is now explicitly covered by the theorem above.
Ordinary inverse limits with graph-homomorphic projections to coverable
factors are also coverable by pullback; merely proposing an inverse limit
is not an escape from this issue.

No theorem handling arbitrary external countable edge colors of higher-
shift exponentials or the third generic mutual-U stage was obtained.
Spec.lean is still unchanged, with its original unresolved sorry. No proof
or disproof of erdos_595 has been submitted.

## Subsequent ultrafilter investigation (no new theorem)

Reviewed the third mutual-U and second ordered-Fubini candidates, edge-filter
couplings, generic-apex iterations, and prescribed/adapted colorings. No new
verified theorem or settlement resulted.

Important distinctions retained:
* The proper countably complete avoiding edge FILTER cannot simply be
  replaced by a countably complete ultrafilter.
* Finite intersection arguments yield triangle couplings, not compatible
  four-clique couplings. No coupling-amalgamation theorem was proved.
* First-U common-neighbor failure for the explicit generic graph is already
  certified in GenericUltrafilterFailure.lean, including after deleting
  isolated vertices. Do not assume the Henson extension property survives.
* Normalizing an edge coloring at a fixed vertex gives a finite adapted
  labeling, but the standard literal extension introduces zero-colored
  edges away from that vertex. It does NOT preserve that normalization
  through arbitrary stages. No compatible global normalization invariant
  was constructed.
* Pointwise-minimal/Grundy edge colorings do not obviously bound colors by
  countability: recursively glued triangles can support arbitrarily high
  ordinal Grundy labels while the underlying graph stays easily coverable.
  This was an informal warning, not a new Lean theorem.

Submission/Spec.lean remains unchanged with its original sorry. The most
recent actual verified advance is TransfiniteAmalgamationCover.lean above.
No proof or disproof of erdos_595 has been submitted.

## Avoiding marginals are isolated in both Fubini directions (new, verified)

Submission/AvoidingMarginalIsolation.lean compiles with an olean, no warnings,
and only the permitted axioms. Namespace Erdos595AvoidingMarginalIsolation.
Log: /tmp/avoiding-marginal-isolation.log.

* triangleFree_set_not_mem: the common endpoint marginal of an edge
  ultrafilter avoiding every triangle-free edge piece contains NO vertex
  subset whose induced graph is triangle-free. This does not need K4-freeness.
  Equal endpoint marginals would otherwise put both endpoints inside that
  subset, contradicting avoidance of its triangle-free spanning edge graph.
* no_outgoing: in a K4-free graph each original neighborhood trace is
  triangle-free, so the marginal has no outgoing Fubini adjacency.
* no_incoming: the previously known empty neighborhood trace excludes
  incoming Fubini adjacency.
* both_directions: the marginal is isolated even for the OR relation, hence
  also for every order-oriented Fubini extension. This strengthens the old
  mutual-isolation result.
* pure_isolated, principalIterate_isolated: an isolated vertex stays isolated
  through its principal images at every later FINITE mutual-U stage.
* marginal_stays_isolated: applies that persistence to the avoiding marginal.

This is not a countable-cover theorem or a witness construction. In
particular it only obstructs trying to recover the lost finite-cover edge
correlations by carrying these marginals farther up the tower; it does not
rule out the whole tower by some other argument. No transfinite tower or
external-coloring compactness theorem was proved in this continuation.
Spec.lean remains unchanged with its original unresolved sorry. No proof or
disproof of erdos_595 has been submitted.

## Higher-shift / adjoint review (no new theorem)

Rechecked ExponentialCompactness, ShiftExponentialCover, ArcAdjoint,
RightTowerCountableCover, RightFiberCover, and the arc/right round-trip
restrictions. No new countable-cover or non-cover theorem was obtained.

In particular finite evaluation of exponential subgraphs still does not
control an arbitrary external countable edge coloring. The second-right
proper-coloring and third-right edge-cover results require their stated
countable-carrier/rectangle-cover hypotheses and K4-freeness of the relevant
FULL right adjoint. They cannot be applied just because an exponential maps
into a K4-free subgraph of a larger profile graph. No new higher-shift
universality theorem, general arc-iteration clique-reflection theorem, or
finite-Folkman homomorphism-unavoidability theorem was proved.

No edits to Spec.lean; no submission. Its original sorry remains unresolved.

## Structural covering review (no new theorem)

Examined cardinal/normal-filter, coloring-poset, graphic-closure, and
nonuniform Hilbert-kernel approaches. No new verified theorem was obtained.
Do not replace the all-distinct-pairs countable-codegree hypothesis by
K4-freeness: K4-freeness only makes the common neighbors of an EDGE
independent, with no cardinal bound. No normality/precipitousness theorem
for the avoiding filter or universal negative-inner-product representation
was established. Local finite feasibility of colorings or kernels was not
promoted to a global strict/countable solution.

Spec.lean is unchanged and unresolved. No proof or disproof was submitted.

## Further candidate review (no new theorem)

Revisited the infinite bipartite incidence Ramsey gap, apex/saturated
extensions, finite-depth mutual-ultrafilter profiles, and algebraic/Cayley
constructions. No new proof of coverability or non-coverability was obtained.

The existing transfinite prescribed-extension theorem already prevents a
straightforward continuous bipartite-amalgamation iteration from producing a
witness, even if a stronger infinite-target bipartite Ramsey lemma were
available. That observation is not a disproof of the infinite-target lemma.
No saturation or finite-depth profile argument was established that controls
arbitrary external countable edge colorings of the remaining candidates.

No edits to Spec.lean and no proof submitted. The original conjecture remains
unresolved.

## Countable-tuple order-type covering (new, Lean-verified)

`Submission/CountableTupleTypeCover.lean` now compiles, with its `.olean`
built. Namespace `Erdos595CountableTupleType`; log
`/tmp/countable-tuple-type-cover.log`. The file has 316 lines and no build
warnings. Its main axiom audits contain only `propext`, `Classical.choice`,
and `Quot.sound`.

This strengthens the FULL-tuple order-type theorem from finite coordinate
sets to countable coordinate sets, in two ambient-order cases:

* any nontrivial dense linear order, of arbitrary cardinality;
* any uncountable well order.

The full graph on `I → A` must be K4-free and its adjacency must depend only
on `pairType` (including both internal tuple types), with `I` countable.
No finite-prefix locality of adjacency is required.

Main declarations:
* `RealizesThree`: the ordered pair type occurs on all three pairs of a
  triple of tuples.
* `four_of_all_three_tests`: if every restriction to three coordinate
  indices realizes such a triple, the full pair type realizes four tuples.
  This is proved over a dense order.
* `finite_witness`: every actual edge has three coordinate indices whose
  restricted pair type cannot be homogeneous on a triangle.
* `countable_cover_of_finite_witness`: a generic covering lemma using these
  finite witnesses; its palette is an optional pair of three indices and
  a comparison relation on six labeled positions.
* `countable_cover`: the dense-order conclusion.
* `four_of_all_three_tests_wellorder`, `finite_witness_wellorder`,
  `countable_cover_wellorder`: the uncountable well-order versions.

Proof mechanism: local tests give a total transitive preorder on four
copies of the entire coordinate set. Its countable antisymmetrization embeds
in a dense ambient order. For the well-order variant, each of its four
coordinate fibers is well-founded; a finite union of well-founded subsets
of a linear order is well-founded. The resulting countable well order embeds
in any uncountable well order, by comparison of initial segments. The four
realized tuples contradict K4-freeness. A witness to failed transitivity uses
only three coordinate indices, yielding a countable edge palette.

IMPORTANT SCOPE: this is a FULL-tuple invariance theorem. Do not apply it to
an arbitrary restricted family satisfying only `RelativeInvariant`, or to a
K4-free restriction of a full graph that may contain K4s. The earlier finite-
coordinate restricted-family theorem remains stronger in that separate
respect. No representation of arbitrary K4-free graphs by the new family
was proved.

The asymmetric triangle-arrow investigation still lacks a K4-free host;
no Ramsey, forcing-absoluteness, or external-color saturation gap was closed.
Spec.lean remains unchanged and unresolved. No proof was submitted.

## Directed two-stage profiles and canonical second-shift exponentials (new, verified)

`DirectedRightTower.lean` and `SecondShiftExponential.lean` compile with oleans.
Namespaces: `Erdos595DirectedRight`, `Erdos595SecondShiftExponential`.
Logs: `/tmp/directed-right-tower.log`, `/tmp/second-shift-exponential.log`.
All printed main audits use only propext, Classical.choice, Quot.sound.

Directed arrows are retained through the two right-adjoint stages; only
then is the relation made mutual. Iterating the symmetric right adjoint
would not justify the profile construction.

* DirectedRightTower: `curry`, `curry_rel`, `cycle_pullback`, `right_rectangles`,
  `detector`, `twice_triangleFree`, `twice_countable_coloring`.
  For TRIANGLE-FREE countable H, the mutual graph of directed right^2 H is
  countably properly vertex-colorable. Countable directed rectangle covers
  yield countable common-neighbor detectors via the 2-by-2 matrix.
* SecondShiftExponential: `eval_rel` maps directed two-step walks in
  F x A (with the order direction in A) into H. Currying twice gives `profile`.
  `profileHom` maps F into the final mutual directed right^2 H, provided each
  profile row has a cofinally repeated value. `countable_coloring_of_cofinal`
  gives a countable PROPER VERTEX coloring for triangle-free countable H.
* `Index C` is the initial order of succ(max(aleph0,#C)). `index_cofinal`
  proves cofinal repetition, using successor regularity, infinite_pigeonhole,
  and the strict size bound on proper initial segments.
* `CanonicalIndex H` uses C = Biclique(right H.Adj) x Set(Set Nat).
  `canonical_not_colorable` proves the second ordered-shift domain has no
  countable proper coloring (a putative coloring injects A into Set(Set Nat)).
  `canonical_cofinal` supplies the profile assumption, and
  `canonical_countable_coloring` is the resulting explicit example theorem.

This does NOT cover arbitrary K4-free countable targets. The full second
profile graph can contain K4, so external detectors cannot be combined with
K4-freeness of only a profile image. No triple homogeneous-set theorem or
local-neighborhood coloring extension is proved here. Spec.lean is unchanged
and still has its original unresolved sorry. No settlement was submitted.

## Exact triangle-filter coupling and diamond gluing (new, Lean-verified)

`Submission/TriangleFilterCoupling.lean` compiles cleanly and has an olean.
Namespace `Erdos595TriangleFilterCoupling`; log
`/tmp/triangle-filter-coupling.log`. All printed axiom audits use only
propext, Classical.choice, Quot.sound (the generic Fiber.map_left does not
need choice).

* Triangle G is the carrier of ordered actual triangles; side indexes its
  three actual directed edges.
* triangleFilter is countableGenerate of the sets of triangles all of whose
  sides avoid one specified triangle-free graph.
* map_side: EVERY edge marginal equals coveringFilter G exactly. This is
  stronger than just containing the canonical filter. The reverse inclusion
  uses the triangle-free graph consisting of residual edges missing the
  proposed marginal set in either orientation.
* triangleFilter_neBot_iff: the triangle filter is proper iff G has no
  countable triangle-free edge cover. No proper K4-free example is constructed.
* triangleFilter_eq_inf: it is precisely the infimum of the three comaps of
  coveringFilter G, not an ultrafilter construction.
* Fiber.filter is the pullback of P x Q to {(a,b) | f(a)=g(b)}. If map f P =
  map g Q, Fiber.map_left/right show that its projections equal P and Q.
  Fiber.neBot and its countable-completeness instance are verified. No
  ultrafilter or extra completeness axiom is needed for this gluing.
* diamondFilter glues two triangle filters over their first oriented edge.
  diamond_first/second preserve the full triangle marginals. diamond_neBot
  gives properness conditional on non-coverability.
* opposite_nonadjacent: for K4-free G the two opposite vertices are NOT
  adjacent, pointwise on the diamond carrier. They are allowed to coincide.
  not_eventually_opposite_adjacent rules out even eventual adjacency in a
  proper diamond filter.

This supersedes the earlier note saying no coupling-amalgamation lemma was
formalized: gluing over a shared edge IS now verified, but it yields a
DIAMOND, NOT a four-clique. Equal triangle/edge marginals do not supply the
missing opposite adjacency. No general four-clique coupling principle,
proper K4-free avoiding filter, or contradiction from countable completeness
was established. The original conjecture remains unresolved.

Other reviewed routes (infinite partite Ramsey, algebraic representations,
external-color saturation, and coloring extension/recoloring) produced no
new main lemma. The website request again failed DNS resolution.
Spec.lean was not edited and retains its original sorry; no submission.

## Exact endpoint marginals and continuum-sized neighborhood avoidance (new, verified)

`Submission/EdgeVertexFilterMarginal.lean` compiles cleanly with an olean.
Namespace `Erdos595EdgeVertexMarginal`; log
`/tmp/edge-vertex-filter-marginal.log`. Main axiom audits use only propext,
Classical.choice, Quot.sound. No holes.

* map_fst/map_snd: BOTH endpoint marginals of the canonical coveringFilter G
  equal VertexCoverFilter.vertexFilter G exactly. The reverse implication
  extracts a countable family of triangle-free graphs covering the induced
  graph on the complement of a proposed large vertex set. The forward
  implication uses endpoint agreement plus avoidance of that induced span.
* endpoint_cardinalInter: the endpoint marginal is a CardinalInterFilter
  at succ(continuum). This does NOT assert that coveringFilter G itself is
  continuum-complete.
* triangle_vertex: each of the three vertex marginals of triangleFilter G
  is exactly vertexFilter G. triangle_vertex_cardinalInter transfers the
  stronger completeness to these vertex marginals.
* avoids_neighborhoods: for K4-free G, BOTH endpoints eventually avoid all
  neighborhoods of a fixed family of at most continuum many vertices.
  This strengthens CountableBadEdgeFilter.avoids_countable_neighborhoods
  for the CANONICAL filter, using the newly identified marginals rather
  than an unsupported continuum intersection in the edge filter.

No argument upgrading the whole edge filter's completeness, supplying the
missing opposite edge in the diamond coupling, or constructing a proper
K4-free avoiding filter was proved. Equal unary marginals are still not a
four-clique coupling. Spec.lean remains unchanged with its original sorry.

Further informal exploration of finite/tower profiles, Cantor limits of
support indices, Ramsey/representation ideas, and transfinite recoloring
produced no main theorem. In particular a pointwise limit of triangle-free
supports must not be treated as an actual ultrafilter support; earlier
unsupported-triangle examples still apply. No submission was made.

## Reassessment after exact endpoint marginals (no new settlement)

Reviewed the canonical endpoint and triangle marginals, the directed
second-shift profiles, and the prescribed adapted-coloring obstructions.
No additional Lean theorem was established in this continuation.

The apex-extension route still needs a genuinely new assertion: an arbitrary
valid countable edge coloring of an appropriate K4-free graph must admit a
K4-free extension on which that PARTICULAR coloring cannot extend. The
existing non-adapted examples concern prescribed colorings and do not prove
this assertion. The verified adapted-reflection counterexample remains a
barrier to inferring such an obstruction from failure of a global adapted
labeling. Pure-graph saturation does not supply saturation for an arbitrary
external coloring.

Likewise, exact unary marginals and shared-edge filter gluing do not imply
a four-clique coupling. The second-shift profile homomorphism does not allow
using K4-freeness of its source to exclude cliques involving external
profile detectors. No upgrade of either argument was found.

Spec.lean was not edited and still contains the original sorry. No proof or
disproof has been submitted.

## Further Ramsey and representation reassessment (no new Lean theorem)

Re-read TriangleArrowReduction, FiniteBipartiteInfinitePalette, the partite
step, RestrictedTupleCover, and the existing geometric exclusions.

The asymmetric ordered-triangle Ramsey hypothesis is still unproved. The
available induced bipartite Ramsey theorem has a FINITE target. It supplies
neither the large infinite red shift-square copy nor simultaneous compatible
homogenization over infinitely many part pairs. Infinite-alphabet Hales--
Jewett and a pure-graph saturation assertion cannot replace this missing step.

The proposed real-Hilbert zero-inner-product boundary case was already
settled as a candidate exclusion in OrthogonalityObstruction.lean: every
orthogonal pair must be an edge and every edge must have nonpositive inner
product. Do not omit the completion assumption. Arbitrary subgraphs of an
orthogonality graph are not covered by that theorem.

Additional informal consideration of maximal triangle-free decompositions,
edge recoloring, finite-term algebraic constructions, finite-dimensional
representations, and hypergraph roots gave no proof of the conjecture or
its negation. No new representation theorem, infinite Ramsey theorem, or
recoloring extension claim was established. Spec.lean remains unchanged.

## Critical-cardinality reduction (new, Lean-verified)

`Submission/CriticalCardinality.lean` compiles cleanly and has an olean.
Namespace `Erdos595CriticalCardinality`; log `/tmp/critical-cardinality.log`.
All audited declarations use only propext, Classical.choice, and Quot.sound.

* `cover_of_small_cofinality`: if V is infinite, every strictly smaller
  induced vertex set is coverable, and cf(#V) <= continuum, then G is
  coverable. No clique assumption is needed for this closure theorem.
  The proof identifies V with the initial ordinal of #V, takes a cofinal
  subset of size cf(#V), and applies the established continuum-indexed
  vertex-union closure to its coverable proper initial segments.
* `critical_cofinality`: a non-coverable graph all of whose smaller induced
  vertex sets are coverable has continuum < cf(#V).
* `continuum_lt_size`: the elementary size obstruction, via binary encoding.
* `on_induce_of_image`: transfers induced-piece coverability through the
  subtype inclusion; used for minimizing within a given graph.
* `exists_minimal_induced`, `exists_critical_induced`: every HYPOTHETICAL
  obstruction contains a cardinal-minimal induced obstruction, with all
  smaller induced pieces covered and cofinality strictly above continuum.
  The minimum is taken only among subsets of the given vertex type.
* `exists_critical_cliqueFree`: retains K4-freeness in this reduction.

IMPORTANT: this is not a bounded reflection theorem, does not prove that
an obstruction exists, and does not exclude regular cardinals (or singular
cardinals of cofinality greater than continuum). It gives no countable-palette
compactness theorem. The finite-palette theorem cannot fill that gap.

Further review of adapted-labeling bounds, stationary/cofinal color choices,
and partite constructions did not produce a main theorem. In particular,
cofinally repeated colors need not have jointly cofinal occurrence sets, and
no countably complete ultrafilter extension of the cofinal filter is asserted.
Spec.lean remains unchanged with its original sorry; no proof submitted.

## Infinite-target Ramsey and large second-shift exclusion (new, verified)

Four new compiled files, all with oleans and clean axiom audits using only
propext, Classical.choice, and Quot.sound:

* `ExponentialNeighborhoodTransfer.lean`, namespace
  `Erdos595ExponentialNeighborhood`, log
  `/tmp/exponential-neighborhood-transfer.log`.
* `InfinitePairRamsey.lean`, namespace `Erdos595InfinitePairRamsey`, log
  `/tmp/infinite-pair-ramsey.log`.
* `InfiniteTripleRamsey.lean`, namespace `Erdos595InfiniteTripleRamsey`, log
  `/tmp/infinite-triple-ramsey.log`.
* `LargeSecondShiftExponential.lean`, namespace
  `Erdos595LargeSecondShiftExponential`, log
  `/tmp/large-second-shift-exponential.log`.

### Genuine neighborhood restriction

`restrictionHom H B hB D hD hno g w j hj` maps the induced neighborhood
of g in H^B into `(H[N_H(w)])^D`, provided j:D ->g B is an ACTUAL graph
homomorphism, g(j x)=w for every x, and D has no isolated vertices.
For f adjacent to g, restriction x |-> f(j x) lies in N_H(w), by using
an actual D-neighbor y of x. Exponential adjacency restricts along j.
`neighborhood_coloring` pulls back a countable PROPER vertex coloring.
`cover_of_homogeneous_domains` applies this at each g and then uses the
verified local-neighborhood proper-coloring criterion for an edge cover.
The domain D may depend on w.

`neighborhood_triangleFree` proves H[N_H(w)] triangle-free for K4-free H.
`oneGraph_no_isolated` uses a no-maximum index order. The theorem
`secondShift_cover_of_homogeneous_triples` is the initial conditional
application to the existing canonical second-shift domain for each target
neighborhood. Its Ramsey hypothesis has now genuinely been supplied in
the large-domain file below.

### Infinite-target pair Ramsey is now available

`InfinitePairRamsey.pair_ramsey_host A C` works for ANY well-ordered
carrier A, including uncountable A, and ANY palette C:
there is a well-ordered V such that every c:V->V->C has an order embedding
f:A -> V and a single k:C with c(f a,f b)=k whenever a<b.
No symmetry, finiteness, or countability assumption on C.

Proof: code each predecessor branch using an arbitrary injection into T,
recording its subset of T, its order relation, and its color labels. Existing
colored-path rigidity makes the vertex-to-code map injective. Cantor's
injection obstruction supplies a branch longer than any prescribed well
order. InitialSeg.total gives a pigeonhole result in encoding form:
if X does not inject into A x C, a coloring X->C has a monochromatic
ordered copy of A. Combining these yields the pair theorem.
`end_homogeneous_host`, `exists_long_branch`, `order_pigeonhole`, and
`treeCode_injective` are useful intermediate theorems.

### Infinite-target triple Ramsey is now available

`InfiniteTripleRamsey.triple_ramsey_host A C` supplies a well-ordered V
such that every c:V->V->V->C has a monochromatic increasing copy of A
on all triples a<b<t. Again A and C may be arbitrarily large well-ordered
set-sized carriers; there is no finite-target restriction.

The new predecessor tree records c(s,t,a)=c(s,t,v) for ALL increasing
pairs s<t in pred(a) when a belongs to pred(v). Transitivity and separation
are proved directly. `pred_chain` requires well-founded induction: the
lower witness in a separating pair lies on the common shorter branch.
Colored-pair branch rigidity gives an injective code using
  Set T x Set(T x T) x Set(T x T x C).
Cantor supplies long end-homogeneous triple sequences; the verified pair
Ramsey theorem homogenizes their pair labels. This is a complete proof,
not an assumed Erdős--Rado axiom. No sharp beth-number bound is asserted.

### Unconditional eventual second-shift exclusion

`LargeSecondShiftExponential.order_family_host` embeds every member of an
indexed family of well orders into a single well order. The proof uses
InitialSeg.total and a Cantor enlargement of the disjoint union.
`homogeneous_triples_host H` applies triple Ramsey to an order containing
every `CanonicalIndex (H.induce (H.neighborSet w))`.

`exists_covered_domain H hH`, for countable nonempty W and K4-free H on W,
produces a well-ordered A such that:
* oneGraph A has NO countable proper vertex coloring;
* exponential H (oneGraph A) has a countable triangle-free EDGE cover.

No coverability assumption on the exponential occurs in this theorem.
The triangle-free neighborhood exponential proper colorings are supplied
by `SecondShiftExponential.canonical_countable_coloring`.

`precomposeHom` and `cover_of_domain_hom` make the direction of domain
variance explicit: j:B ->g D gives H^D ->g H^B, so a cover of H^B
transfers to H^D, NOT conversely.
`exists_eventual_cover` shows that every ordered index X containing the
constructed A also has a coverable second-shift exponential. Its domain
is still uncountably chromatic, since oneGraph A maps into oneGraph X.

LIMITATIONS: this eliminates sufficiently LARGE second-shift domains,
not all intermediate/smaller domains. It is not universal coverability,
not non-coverability, and not a settlement of the main conjecture.
The new Ramsey theorems concern complete ordered index sets; they do not
produce K4-free Ramsey hosts. In particular arbitrary INFINITE bipartite
induced Ramsey hosts and compatible infinite partite stages remain missing.
Do not confuse the now-proved infinite-target pair/triple theorems with
those stronger forbidden-configuration assertions.

Spec.lean remains unchanged with its original sorry. No proof was submitted.

## One-edge triangle-closure normalization (new, verified)

`Submission/TriangleClosureNormalization.lean` compiles cleanly and has an
olean. Namespace `Erdos595TriangleClosure`, log
`/tmp/triangle-closure-normalization.log`. All audited declarations use only
propext, Classical.choice, Quot.sound; some do not need choice.

The proposed shortcut was: perhaps adjoining one edge to a triangle-closed
old graph cannot create complicated all-new triangles. A direct finite
check refutes even triangle-freeness of the new layer in the octahedral
K_{2,2,2} graph. Old edges (0,2),(0,3),(1,2) form a closed set; adjoining
(0,4) generates new edges (0,4),(1,3),(1,4),(2,4),(3,4), including a
triangle on 1,3,4. Script `/tmp/triangle_closure_check.py`. This computation
is only exploratory; the following stronger universal result IS Lean-verified.

Use the existing TriangleRadius enlargement F=graph G. Its spanning old
subgraph M consists of:
* b--port(v);
* a--pair(e);
* port(v)--orig(v).
`oldColoring` explicitly two-colors M. `old_le` proves M <= F.
`no_two_old` proves that NO F-triangle contains two M-edges. Consequently
`old_closed` holds for triangle completion, not merely triangle-freeness.
The distinguished edge a--b belongs to F but not M.

`Closed F K` means two K-sides of an F-triangle force its third side into K.
`generates` proves that ANY Closed F K containing M and a--b contains ALL
of F. Four rounds of explicit deductions suffice:
1. a--port(v), from a--b and old b--port(v);
2. port(v)--pair(e), from the previous edge and old a--pair(e);
3. pair(e)--orig(v), from the previous edge and old port(v)--orig(v);
4. orig(v)--orig(w), from the two pair(v,w)--orig endpoint edges.
All other F-edges were old or already obtained in the first three rounds.
`closed_eq` expresses uniqueness of the closed intermediate spanning graph.

`normal_form` retains K4-freeness (using TriangleRadius.cliqueFree), the
induced copy of G, the bipartite closed base, and single-edge generation.
`newEmbedding` is stronger: G embeds inducedly into F \\ M, entirely among
the NEW edges. `no_cover_new` transfers a HYPOTHETICAL non-coverability
obstruction to that new-edge graph.

Therefore single-edge generation over a bipartite triangle-closed base,
or a finite bound on the number of completion rounds, does not itself
simplify the main problem. No assertion of coverability or non-coverability
of an arbitrary G follows. In particular this is NOT a disproof of Erdős 595.

Other reviewed ideas this continuation (infinite partite selection,
graphic-matroid growth, cofinal color choices, non-Archimedean Gram
representations, and large shift/reduced-power bridges) gave no main lemma.
Infinite-target pair/triple Ramsey is available from the preceding update,
but arbitrary infinite bipartite induced Ramsey hosts AND coherent
homogenization over infinitely many part pairs remain separate gaps.

Spec.lean remains unchanged with its original sorry; no proof was submitted.

## Exact generic trace realization and rich-core failure (new, verified)

`Submission/GenericTraceRealization.lean` compiles cleanly with an olean.
Namespace `Erdos595GenericTrace`; log `/tmp/generic-trace-realization.log`.
All audited theorems use only propext, Classical.choice, Quot.sound.

The initial idea of preserving the generic extension property was already
refuted by GenericUltrafilterFailure (degree-one points). The new file
strengthens that result and identifies the full range of original traces.

For ANY S subset of the original explicit generic graph with G[S]
triangle-free, `point S hS` is an ultrafilter whose original trace is EXACTLY S.
For each finite test set F, finite_extension supplies a fresh witness outside
F adjacent to precisely S intersect F among the tested vertices. Push the
existing fine ultrafilter on Finset Vertex through this witness map.
`trace_point` identifies the trace; `point_no_singleton` and
`point_not_pure` prove the resulting point is nonprincipal.
`trace_exists_iff` states the full equivalence:
  (exists p, trace p = S) iff G[S] is triangle-free.
The reverse necessity is the earlier ultrafilter_trace_cliqueFree theorem.
This does not assert that S belongs to its realizing ultrafilter.

`no_common_of_disjoint_trace` proves disjoint traces forbid a common
neighbor in the FULL first mutual-U extension: a proposed neighbor must
contain both traces as ultrafilter members. `point_in_triangle` and
`point_infinite_neighbors` transfer an edge and infinitude of S to the
realizing point's neighborhood.

`Rich` consists of U-vertices on triangles and with infinite neighborhoods;
`RichGraph` is the induced subgraph on Rich.
`rich_pair_failure` constructs distinct p,q in Rich such that:
* BOTH have infinite neighborhoods INSIDE RichGraph;
* BOTH lie on triangles INSIDE RichGraph;
* they have NO common neighbor even in the FULL extension U.

Construction: embed the disjoint union of two countable complete bipartite
graphs K_{omega,omega} into the countable generic base. Their two disjoint
vertex sets S(false), S(true) are infinite, triangle-free, and contain edges.
Use their trace-realizing points. All corresponding principal points also
belong to Rich: each has infinitely many principal opposite-side neighbors,
and the realizing point supplies triangles. This verifies the stronger
claims inside the induced rich core, not merely in U.

Therefore removing isolated vertices, removing finite-degree vertices, or
restricting to vertices on triangles does NOT repair the generic pair
extension property. No transfinite pruning theorem is asserted. The known
first-U countable proper vertex coloring and edge cover remain valid; this
file does not construct an obstruction to countable covering.

The exact principal common-neighbor detector is already in
CommonNeighborDetector.principal_detector; do not rediscover it as a new
lemma. More general avoiding-filter/coupling, binary-cube, cardinal reflection,
and algebraic routes were reviewed but yielded no main theorem this time.
Spec.lean remains unchanged with its original sorry; no proof submitted.


## Positive countable sampling range and triangle components (verified)

`CountableComponentProduct.lean` has compiled successfully, including axiom audits
using only `propext`, `Classical.choice`, and `Quot.sound`. Log:
`/tmp/countable-component-product.log`.

For a proper filter F, a countable sampling range which meets every F-large set
suffices to obtain a countable triangle-free cover of the reduced product when
the coordinate graphs are countably properly vertex-colorable. In particular
this holds for ANY proper filter on a countable index set, not just countably
generated or countably complete filters.

Using `TriangleComponentProduct.anchorHom`, this extends when each coordinate
TRIANGLE COMPONENT admits a countable proper vertex coloring; the entire
coordinate graphs need not have such colorings. The sampled variant for
`Tendsto s atTop F` is also verified.

This rules out the recent countable-index products of large graphs assembled
from finite Folkman triangle components, regardless of finite cover numbers
tending to infinity. It is a candidate exclusion, not a main settlement.


## Infinite matching and half-graph Ramsey steps (new, verified)

`Submission/InfiniteBipartiteRamsey.lean` compiles cleanly, with an olean.
Namespace `Erdos595InfiniteBipartite`; log `/tmp/infinite-bipartite-ramsey.log`.
All printed axiom audits use only propext, Classical.choice, and Quot.sound.

This genuinely extends the finite-target bipartite results in two families:

* `half_ramsey A C`: for an ARBITRARY well-ordered A, the whole bipartite
  half-graph on A has an induced, part-preserving monochromatic copy in a
  larger half-graph under every C-edge coloring. Both A and C may be infinite.
* `pair_box A C`: a two-coordinate product of ordered-pair Ramsey spaces
  admits a homogeneous box whose two axes are order-isomorphic to all of A.
  Only the number of coordinates (two) is finite.
* `matching_ramsey A C`: an induced MATCHING indexed by an arbitrary type A
  has a bipartite induced, part-preserving edge-Ramsey host for any palette C.
  Choose a well order on A and double each position as (a,0)<(a,1). The host
  has left/right points in B x D and adjacency
       left(x,t) -- right(y,s) iff x<y and s<t.
  Two pair-Ramsey axes give matching vertices
       left(f(a,0),g(a,1)), right(f(a,1),g(a,0)).
  The two cross inequalities are equivalent to a<=b and b<=a, so the copy
  is INDUCED, not just a subgraph copy.
* `step_of_ramsey`: abstract free-amalgamation transfer for any designated
  induced target with a K4-free Ramsey host.
* `half_step`, `matching_step`: apply it to an arbitrary K4-free ambient H.
  The designated induced subset S can be infinite or uncountable.

These are positive infinitary amalgamation tools, NOT a settlement. They
still do not provide arbitrary infinite bipartite targets, nor compatible
homogenization of infinitely many part pairs, nor the asymmetric ordered-
triangle host required by TriangleArrowReduction.

## Countably infinite pair boxes fail (new, verified)

`Submission/InfiniteBoxObstruction.lean` compiles cleanly, with an olean.
Namespace `Erdos595InfiniteBoxObstruction`; log `/tmp/infinite-box-obstruction.log`.
Its audited axioms are exactly the permitted three.

For every dependent family A_n of arbitrary types, choose one representative
of each eventual-equality class in the product. Color x by the least N such
that x_n agrees with its representative for every n>=N.

* `unbounded_on_box`: this SINGLE natural-number coloring is unbounded on
  every nonempty product of sets S_n whose factors contain distinct elements
  at arbitrarily large n. Given N, modify one coordinate n>=N to a value
  different from the representative. A finite modification retains the same
  representative, so its color exceeds n.
* `no_mono_binary_box`: no full product of two-point coordinate choices is
  monochromatic.
* `no_countable_pair_box`: for ANY choice of ordered axes indexed by N,
  a countable coloring of their pair-product has NO homogeneous full box of
  Fin 4 order embeddings. Use (0,1) and (2,3) as the two pair choices.

Thus increasing the cardinalities of countably many axes cannot extend
PairBoxRamsey.box_finite to infinitely many coordinates. This is different
from the earlier Hales--Jewett obstruction and directly blocks the naive
countably infinite dominance-coordinate extension of the bipartite theorem.
It does NOT rule out all infinite bipartite Ramsey methods or all infinite
targets; the positive matching and half-graph results above remain valid.

## Additional candidate review in this continuation (SUPERSEDED below)

The recent countable-index product exclusion assumes countable PROPER vertex
colorings of coordinate triangle components. A different candidate family
would use finite triangle-free EDGE cover numbers tending to infinity, but
with genuinely large vertex-chromatic triangle components, e.g. large generic
K4-free graphs with n named triangle-free edge colors. The existing countable-
component theorem does not directly exclude their ordinary countable-index
reduced products. Merely attaching a high-chromatic triangle-free piece to a
finite Folkman graph is not a lower-bound proof; the attachment can retain a
uniformly simple cover. No non-coverability theorem for the genuine generic
product family was found. Pure-graph saturation still gives no control over
an arbitrary external countable edge coloring.

Further review of cardinal-minimal obstructions, canonical filters, graph
roots, group presentations, and transfinite recoloring did not settle the
conjecture. Spec.lean is unchanged, with the original sorry and SHA256
`de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45`.
No proof or disproof has been submitted.


## All countable-index products of coverable factors are excluded (verified)

IMPORTANT CORRECTION: the candidate in the immediately preceding review is
now ruled out by a much simpler and stronger argument. Do not revisit it as
an unexcluded construction.

`Submission/CountableEdgeProduct.lean` compiles cleanly, with an olean.
Namespace `Erdos595CountableEdgeProduct`; log `/tmp/countable-edge-product.log`.
All audits use only propext, Classical.choice, and Quot.sound.

* `cover_of_edge_detection`: given countably many maps f_i from G's vertices
  to vertices of countably edge-coverable H_i, if EVERY G-edge is adjacent
  under at least one f_i, then G is countably edge-coverable. The maps need
  NOT be graph homomorphisms. Pull back each triangle-free piece of H_i and
  use the countably many pairs (i,n) as cover indices.
* `countable_index_cover`: for ANY proper filter F on a countable I, the
  reduced-product graph of countably EDGE-coverable coordinate graphs is
  countably edge-coverable. A filter-large adjacency set is nonempty, so
  one coordinate witnesses each edge. No proper vertex-coloring assumption,
  uniform finite edge-cover bound, countable completeness, or countable-
  generation assumption is needed.
* `cover_of_positive_range`: the same result holds on an arbitrary index set
  with a countable sampling range meeting every F-large set.
* `cover_of_sampler`, `countably_generated_cover`: a convergent sampler is
  sufficient, hence so is any proper countably generated filter.
* `quotient_countable_index`: the representative/comap quotient version.
* `countable_index_components`: coordinate triangle components need only be
  countably EDGE-coverable, since cover_of_pieces first covers the coordinates.

This strictly improves SampledFilterProduct and CountableComponentProduct.
In particular ordinary countable-index ultraproducts of large generic
finite-edge-colored K4-free factors cannot be witnesses, even if their finite
edge-cover numbers are unbounded and their proper vertex chromatic numbers
are arbitrarily large. Earlier discussion that treated these products as
remaining candidates was mistaken and is superseded by this theorem.

The arbitrary uncountable-index fine countably-complete reduced-power normal
form remains unresolved: there is no positive countable sampling range in
general. No main proof or disproof was obtained. Spec.lean remains unchanged
and still produces its original sorry warning. No submission was made.


## Finite maximal-clique codes for the OR extension (new, verified)

`Submission/FiniteCliqueUltrafilterColoring.lean` compiles cleanly, with an olean.
Namespace `Erdos595FiniteCliqueUltrafilter`; log
`/tmp/finite-clique-ultrafilter-coloring.log`. All printed axiom audits use
only propext, Classical.choice, and Quot.sound.

This strengthens the first-stage proper-coloring theorem from MUTUAL to
OR Fubini adjacency, and relaxes the hypothesis to NO INFINITE CLIQUE.

* `FiniteCliques G` means every clique SET is finite, with no uniform finite
  clique bound required. `finiteCliques_of_cliqueFree` handles any fixed
  finite clique bound, including K4-freeness.
* `finite_maximal`: Zorn gives a maximal clique inside an arbitrary subset
  T of V. The hypothesis makes it finite. Its common neighborhood inside T
  is empty. The empty clique handles T=empty.
* `trace G p = {v | N_G(v) belongs to p}`.
* `code G hG p`: a finite maximal clique inside that original trace.
* `code_ne`: even ONE Fubini direction R(p,q) forces code(p) != code(q).
  If both codes are S, p contains every N(s), s in S, and also trace(q).
  Their finite intersection gives v in trace(q) adjacent to every s in S,
  contradicting maximality of S in trace(q).
* `orGraph`: adjacency R(p,q) OR R(q,p). Looplessness follows from code_ne.
* `cliqueColoring`: a proper vertex coloring of the OR graph by Finset V.
* `or_countable_coloring`: for COUNTABLE V this is a countable proper
  vertex coloring, even if the base has finite cliques of unbounded sizes.
* `ordered_countable_coloring`, `ordered_K4_countable_coloring`: every
  choice of order-oriented first extension inherits that proper coloring.
* `or_cover_of_size`: when #V <= continuum, Finset V has size <= continuum,
  so the OR first extension has a countable triangle-free EDGE cover. This
  does not require countability of V, only the finite-cliques hypothesis.

This supersedes the weaker trace-size bound for first ORDERED extensions,
which only gave countable edge coverability from a countable base. The OR
graph need not itself be K4-free; the proper coloring is valid nonetheless.
For arbitrary infinite V the clique code has palette of cardinal #V, rather
than the older 2^#V trace bound.

IMPORTANT LIMITATIONS:
* The first extension's carrier is still the full Ultrafilter V, not the
  countable palette. This gives no small K4-free homomorphism target.
* One cannot iterate the theorem using only countable proper vertex
  colorability of the base; its carrier-size hypothesis is essential.
* The SECOND ORDER-ORIENTED extension of a countable K4-free generic base
  remains an unexcluded candidate, distinct from the covered second MUTUAL
  extension. The THIRD MUTUAL stage also remains unresolved.
* No flattening homomorphism, stable-type compression, external-coloring
  saturation, or infinite-partite coherence theorem was established.

Further mathematical review of the root, finite partite, generic-apex, and
canonical-filter routes did not produce a proof or disproof of erdos_595.
Spec.lean remains unchanged with its original sorry. No submission was made.

## No countable K4-free target for the first generic mutual U (new, verified)

`Submission/NoCountableK4Target.lean` compiles with an olean. Namespace
`Erdos595NoCountableK4Target`; log `/tmp/no-countable-k4-target.log`.
The axiom audits contain only propext, Classical.choice, and Quot.sound.

* `finiteCover_coloring` turns a finite triangle-free edge cover into a
  coloring with finite palette `Option (Fin n)`.
* `generic_no_finiteCover` combines that with the verified finite Folkman theorem.
* `independent_escape` uses the common endpoint marginal of an avoiding edge
  ultrafilter to choose an independent sequence v_n outside prescribed
  triangle-free induced sets S_n. Repetitions are harmless. It reuses
  `AvoidingMarginalIsolation.triangleFree_set_not_mem`.
* `no_countable_target` is abstract: a K4-free old graph with no finite
  triangle-free edge cover, inside an extension realizing common neighbors
  of all independent old subsets, excludes homomorphisms from that extension
  to every countable K4-free graph. Enumerate the target vertices d_n; the
  old preimages of N(d_n) are triangle-free. An independent escaping sequence
  has a common neighbor in the extension, contradicting escape at its image.
* `generic_first_no_countable_target` applies this to the explicit generic G
  and its first MUTUAL ultrafilter extension, using exact trace realization.

This proves the compression obstruction proposed in the preceding summary.
It is NOT non-coverability: the first mutual extension already has a countable
proper vertex coloring. Its complete countable target has K4s. This theorem
only excludes countable K4-FREE targets; no countable target with merely
finite (but unbounded) cliques has been excluded by this argument.

Further informal review of second order-oriented U: the old second-mutual
support proof uses BOTH first-stage Fubini directions and cannot simply be
transferred. Points whose flattened ultrafilter avoids every original
triangle-free subset need not be isolated for the ordered-first extension.
No new covering or non-coverability theorem at that stage was obtained.
Spec.lean remains unchanged with its original sorry.

## Fixed FINITE-factor reduced-power normal form (new, verified)

`Submission/FixedFiniteReducedPower.lean` compiles with an olean. Namespace
`Erdos595FixedFiniteReducedPower`; log `/tmp/fixed-finite-reduced-power.log`.
All printed axiom audits use only propext, Classical.choice, and Quot.sound.

* `Template n` is the finite type of all K4-free graphs on Fin n.
* `Vertex n = Template n x Fin n` and `universal n` is their disjoint union.
  Every factor is FINITE and K4-free.
* `finiteEmbedding` embeds every n-vertex K4-free graph into `universal n`.
* `power V` has carrier `(S : Finset V) -> Vertex (S.card + 1)` and adjacency
  holds eventually in atTop on Finset V. The factors, size parameter, and
  filter are independent of the input graph to be embedded.
* `embedding`: every K4-free graph G on V embeds inducedly into `power V`.
  At S, use G induced on S plus one isolated default point. Relabel that
  finite graph into its component of `universal (S.card + 1)`. Original
  vertices in S map to their corresponding finite vertices; others map to
  the isolated default. Fineness recovers adjacency and injectivity.
* `ultraEmbedding`: the identical fixed sequence also gives a universal
  genuine quotient ultraproduct for any chosen ordinary fineUltra V.
* `conjecture_iff_fixed_powers`: the original existential covering problem is
  equivalent to existence of V for which `power V` is not countably covered.
* `no_finite_cover`: for EVERY infinite V, `power V` has no finite triangle-
  free edge cover. A hypothetical finite cover pulls back through an embedded
  finite Folkman graph (first place that graph injectively in V).
* `countable_base_cover`: for countable V, countable-index edge detection
  still supplies a countable cover, despite `no_finite_cover`.
* `countable_of_positive_sample`: if a countable range of finite subsets is
  positive for ANY proper fine filter, then V is countable. This strengthens
  the old obstruction which assumed convergence of a sampling sequence.

This is a NORMAL FORM, not a construction of non-coverability. The unresolved
part is an uncountable V. The atTop/fine-ultrafilter finite-subset filters are
countably incomplete for infinite V, and have no positive countable sample
for uncountable V, so neither of the existing product exclusions applies.
Pure-graph saturation and finite Folkman obstructions still do not control
arbitrary external countable edge colorings.

Further review of the canonical-filter, adapted-labeling, graphical-matroid,
and infinite partite approaches supplied no main theorem. In particular,
no upgrade of the canonical EDGE filter to continuum completeness, no
countable-palette compactness, and no general infinite bipartite Ramsey
principle were established. Spec.lean remains unchanged and unresolved.

## Exact canonical positivity and subgraph restriction (new, verified)

`Submission/CanonicalPositiveRestriction.lean` compiles with an olean.
Namespace `Erdos595CanonicalPositive`; log
`/tmp/canonical-positive-restriction.log`. All printed axiom audits contain
only propext, Classical.choice, and Quot.sound.

* `span G S` symmetrizes a set S of actual directed G-edges.
* `compl_mem_iff`: S-complement belongs to coveringFilter G iff span G S
  has a countable triangle-free edge cover.
* `positive_iff`: coveringFilter G restricted to S is proper iff span G S
  is NOT countably coverable. No properness premise on the original filter
  is needed for the equivalence.
* `positive_edges_iff`: for any graph H on the same vertices, positivity of
  its directed edges means non-coverability of G meet H.
* `positive_subgraph_iff`: when H <= G, canonical positivity is exactly
  non-coverability of H itself.
* `comap_inclusion`, `map_inclusion`: the canonical filter of a spanning
  subgraph H is exactly the restriction of the canonical filter of G along
  the directed-edge inclusion. This is not merely an arbitrary avoiding
  filter after restriction.
* `positive_diff_iff`: deleting any countably coverable edge graph preserves
  positivity of every directed edge subset for the canonical filter.

IMPORTANT CLARIFICATION to earlier notes: the warning that F-positive is
insufficient remains valid for an ARBITRARY avoiding filter F. For the
CANONICAL coveringFilter G, positive subgraphs ARE non-coverable, as now
verified. Positivity is still not largeness, positive sets need not have
positive intersections, and no countably complete ultrafilter extension
is supplied.

Review of third mutual-U support/code compression, intermediate second-shift
exponentials, infinitary partite coherence, and triangle couplings did not
construct a positive K4-free example or prove universal coverability. The
triangle/diamond coupling still forbids rather than supplies the missing
opposite edge. No new Ramsey theorem or saturation assertion was established.
Spec.lean is unchanged and still contains its original sorry.

## Continuation review: no further theorem established

Rechecked the original statement and the open construction routes. Reviewed
local adapted-label extension, independently adjoined apex stages, the second
order-oriented ultrafilter candidate, and the infinite asymmetric/partite
Ramsey gap. None supplied the missing countable-palette theorem.

In particular:
* Realizing all triangle-free neighborhoods at one independent-apex stage
  preserves coverability; iterating this observation does not produce
  coherent prescribed colorings at arbitrary uncountable limits.
* Local adapted labelings on all triangle-free induced subsets still do not
  imply a global adapted labeling (AdaptedReflectionObstruction).
* First-stage countable proper coloring does not compress the graph to a
  countable clique-preserving target. No higher-stage compression or new
  non-coverability result was proved.
* Generic/saturated pure graphs and fine finite-factor products do not gain
  control of arbitrary external countable edge colorings merely from finite
  Folkman or saturation.

An attempted external status check again failed at DNS resolution. There is
no new verified auxiliary Lean result in this continuation. Spec.lean remains
unchanged with its original sorry; no proof was submitted.

## Private-leaf Erdős--Rado tree obstruction (new, verified)

`Submission/ErdosRadoLeafObstruction.lean` compiles with an olean. Namespace
`Erdos595ErdosRadoLeaf`; log `/tmp/erdos-rado-leaf-obstruction.log`. Printed
axiom audits contain only propext, Classical.choice, and Quot.sound.

For an ARBITRARY graph G, attach one private leaf to every old vertex. Order
all leaves before all old vertices, using the same well-order within each
part. The graph retains G inducedly.

* `triangle_old`: every triangle consists entirely of original vertices.
* `cliqueFree`: the enlargement preserves K4-freeness.
* `cover_iff`: it preserves countable triangle-free edge coverability EXACTLY.
* `pred_leaf`: the Erdős--Rado predecessors of leaf(v) are leaf(u), u < v.
* `leaf_pred_old`: leaf(u) precedes old(v) in the ER tree iff u <= v.
* `old_not_pred_old`: no original vertex precedes another original vertex
  in that tree, irrespective of their adjacency in G.
* `pred_old`: the entire predecessor set of old(v) is leaf(u), u <= v.
* `positive_leaf`: the positive (adjacent) predecessor set of a leaf is empty.
* `positive_old`: the positive predecessor set of old(v) is {leaf(v)}.
* `at_most_one_positive`: every vertex has at most one positive predecessor.

Thus an EXISTENTIAL choice of ER-tree order with finitely many (even at most
one) positive predecessors gives no covering theorem: arbitrary original
edges and triangles lie between incomparable branches. K4-freeness does bound
positive predecessors for every order, but no way of exploiting that stronger
universal assertion to obtain a countable edge coloring has been established.

This continuation also rechecked the right-adjoint and exponential routes.
No new non-coverability transfer or infinite Ramsey theorem was proved.
Spec.lean remains unchanged and unresolved; no submission was made.

## Indefinite ordered-field unit orthogonality (new, verified)

`Submission/IndefiniteUnitOrthogonality.lean` compiles with an olean.
Namespace `Erdos595IndefiniteUnit`; log `/tmp/indefinite-unit.log`.
Both printed axiom audits use only propext, Classical.choice, and Quot.sound.

For an arbitrary ordered field K and natural numbers m,n, define

    form x y = dot(x.positive,y.positive) - dot(x.negative,y.negative)
    UnitPoint K m n = {x in K^m x K^n | form x x = 1}

with adjacency given by form x y = 0.

* `positive_independent`: positive projections of any finite orthonormal
  family are linearly independent. If their linear combination vanishes,
  the corresponding sum of squared coefficients equals the NEGATIVE of
  a sum of squares in the negative coordinates, so all coefficients vanish.
* `cliqueFree`: the graph is CliqueFree (m+1).
* `cliqueFree_four`: all signatures (3,n) yield K4-free graphs, with no
  Archimedean hypothesis on K.

IMPORTANT SCOPE CORRECTION: FiniteDimensionalOrthogonalityCover only covers
TOTAL dimension at most FOUR. Its file name and some condensed descriptions
must not be read as a theorem about ALL finite dimensions. In particular,
the present (3,2) family over arbitrary large ordered fields is not excluded
by that result. No claim that it is actually non-coverable is proved here.
Over a carrier of size at most continuum, the previous cardinal covering
result still applies. No new field or non-coverability construction has been
supplied. The remaining candidate would require a genuinely large field
and a new argument controlling arbitrary external countable edge colorings.

This continuation also rechecked first/third ultrafilter supports, finite-
clique countable targets, and adapted/apex routes. No cone-index compression,
countable finite-clique target theorem, or arbitrary-color forcing result
was established. Prescribed nonadapted colorings still cannot be substituted
for non-coverability.

Spec.lean is unchanged (SHA256
`de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45`).
Latest direct check: `/tmp/spec-continuation-check.log`, reporting the original
sorry warning. The original conjecture remains unresolved; no submission
has been made.

## Further ordered-field review: no settlement

Revisited the signature (3,n) family, positive-index matrix completions,
finite-support algebraic representations, and saturation of ordered fields.
No non-coverability theorem or extension/universality theorem was obtained.
The verified positive-index clique bound must not be mistaken for either
finite Folkman universality or countable-palette Ramsey behavior. Saturating
a field or its underlying graph does not by itself control arbitrary
external countable edge colorings. Conversely, no general covering theorem
for all higher-dimensional ordered-field cases has been established here.

The canonical-filter/coupling and graphical-root viewpoints were also
reviewed, without a new lemma resolving their existing gaps. No additional
auxiliary theorem was proved in this continuation. Spec.lean remains
unchanged with its original sorry, and no completed proof was submitted.

## Arc graph inside indefinite unit orthogonality (new, verified)

`Submission/ArcIndefiniteEmbedding.lean` compiles with an olean.
Namespace `Erdos595ArcIndefinite`; log `/tmp/arc-indefinite.log`.
All four printed axiom audits use only the permitted three axioms.

For any ordered field K, write d=a-b for a distinct ordered pair (a,b), and
map it to the signature (3,1) vector

    positive = (a/d, b/d, (ab-1/2)/d)
    negative = ((ab+1/2)/d).

Verified:
* `inner_formula`: the bilinear product of the images of (a,b) and (c,d)
  is (a-d)(c-b)/((a-b)(c-d)).
* `unit`: each image has norm one.
* `point_adj_iff`: orthogonality holds exactly when b=c or d=a, the full
  arc-graph adjacency relation.
* `point_injective`, `embedding`: this is an actual induced embedding of
  arcGraph(top on K) in the signature (3,1) graph.
* `color_sets`: any proper C-coloring of that orthogonality graph gives an
  injection K -> Set C. For each field element take the set of colors of
  its outgoing arcs; adjacency forces these sets to distinguish elements.
* `cardinal_bound`: a proper natural-number vertex coloring forces
  #K <= continuum.

Thus finite-dimensionality/stability must NOT be used to infer countable
PROPER vertex colorability. Already dimension four has the arc obstruction.
This is compatible with the existing countable triangle-free EDGE cover in
dimension at most four, and arcGraph itself has a two-piece edge cover.
The result is NOT non-coverability and does not resolve signature (3,2).

Broader review of finite-rank, transfinite recoloring, canonical-filter,
and infinite-dimensional representation routes supplied no missing main
lemma. Spec.lean remains unchanged with its original sorry; no completed
proof/disproof has been submitted.

## Refined third-stage cone indices and exact generic separation (new, verified)

`Submission/OneSidedSupport.lean` has a new compiled theorem
`third_supported_refined`; log `/tmp/one-sided-support-refined.log`.
For every third-stage edge X--Y, there exist an original ultrafilter r and
an original triangle-free set S such that

    S belongs to r, and {P | cone G r belongs to P} belongs to X.

The cone index is flatten Q for a nonisolated second-stage Q; applying
second_ultrafilter_support to Q proves the extra original support. This
refinement does NOT say that X is supported on the triple lift of S.
Existing third-stage original-support counterexamples still apply.

`Submission/GenericConeSeparation.lean` also compiles with an olean.
Namespace `Erdos595GenericConeSeparation`; log
`/tmp/generic-cone-separation.log`. All printed audits of both files contain
only propext, Classical.choice, and Quot.sound.

* `point_mem_cone`: membership of the generic trace-realizing point of S
  in cone(r) is exactly S membership in r, for triangle-free S.
* `eq_of_cone_eq_of_support`: if r contains any triangle-free S, equality
  cone(r)=cone(s) forces r=s. First this equality forces S into s too; then
  the points realizing A intersect S distinguish membership of every A.
* `eq_of_cone_eq_of_nonempty`: every nonempty cone determines its index.
* `cone_eq_iff`: equal cones mean equal ultrafilters, EXCEPT that all indices
  with empty cone have the same empty image.
* `injective_on_supported`: the cone map remains injective on ultrafilters
  containing any one fixed triangle-free original set S.

Consequently the refined support condition does not create redundant cones
by equality, even after fixing S. This is NOT a proof that a smaller family
of OTHER triangle-free supports cannot cover the third extension; it is
only an exact limitation of equality-based compression. No cardinality
formula for the set of ultrafilters was proved in this file.

The main conjecture remains unresolved, and Spec.lean has not been changed.
No proof/disproof has been submitted.

## Further review after cone separation (no settlement)

Rechecked finite adapted extensions, asymmetric triangle-arrow constructions,
and higher-dimensional ordered-field orthogonality. No fixed-bound adapted
invariant or coherent limit coloring was found. The normalization theorem
provides a favorable coloring of each coverable graph separately; it does
not provide compatible normalized colorings on an arbitrary chain.

Also considered graphical/group presentations and forcing-based generic
constructions informally. No K4-free high-chromatic graphical realization,
forcing theorem, absoluteness theorem, or ground-model witness was proved.
In particular, a hypothetical witness in a forcing extension cannot simply
be treated as a ZFC witness in the original universe. None of these informal
routes is a dependency or a verified new result.

No auxiliary theorem was added during this review. Spec.lean retains its
original statement and sorry; the conjecture remains unresolved.

## Edge-dependent finite-bound compactness (new, verified)

`Submission/FiniteEdgeBounds.lean` compiles with an olean. Namespace
`Erdos595FiniteEdgeBounds`; log `/tmp/finite-edge-bounds.log`.
All three printed axiom audits use only propext, Classical.choice, Quot.sound.

* `Bounded G b`: a valid natural-number edge coloring bounded pointwise by b.
* `compactness` / `compactness_iff`: a FIXED assignment b of finite bounds
  works globally iff its restrictions work on all finite induced subgraphs.
  The ultrafilter argument uses Fin (b e + 1) separately at each edge.
* `countable_cover_iff`: countable covering is equivalent to the existence
  of one such b working on every finite induced subgraph. Quantifier order
  is EXISTS b, FORALL finite S; b is not allowed to change with S.
* `finite_obstruction`: a genuinely non-coverable graph defeats every
  proposed b already on a finite induced subgraph.

This is an exact compactness criterion, NOT a construction of b for K4-free
G, and NOT countable-palette compactness without the bounds. No bound
assignment was obtained for arbitrary K4-free graphs. Further informal
review of finite-dimensional representations, closure methods, and local
color profiles supplied no main proof or counterexample. In particular,
no universal positive-index-three representation or bounded-VC covering
assertion was proved.

Spec.lean remains unchanged with its original sorry. No completed proof or
 disproof has been submitted.

## Backtracking in the second directed arc graph (new, verified)

`Submission/SecondArcBacktracking.lean` compiles with an olean.
Namespace `Erdos595SecondArcBacktracking`; log `/tmp/second-arc-backtracking.log`.
All five printed axiom audits use only propext, Classical.choice, Quot.sound.

Let L label directed length-two walks (a,b,c) of an ARBITRARY graph F by
vertices of a K4-free graph H, with overlapping walks receiving adjacent
H-labels. Label a directed edge ab by

    (L(a,b,a), L(b,a,b)).

* `no_three`: three consecutive edges ab,bc,cd cannot have the same label
  pair (x,y). Otherwise L(a,b,c) and L(b,c,d) are adjacent and both adjacent
  to x and y, which themselves are adjacent. This is a K4 in H. No order
  or distinctness hypothesis on a,b,c,d is needed.
* `heights`: every directed label class has no walk of length three, so
  BoundedIncreasingPath.finite_rank gives a height in Fin 4.
* `coloring_sequences`: for COUNTABLE H, the heights give a proper vertex
  coloring of F by N -> Fin 4, a continuum-sized palette.
* `countable_cover`: the corresponding countable family of height cuts
  covers F by bipartite (hence triangle-free) edge pieces. There is NO
  K4-freeness assumption on F.
* `uncurry` / `uncurry_rel` give the directed uncurrying operation.
* `twice_countable_cover`: the FULL mutual graph of directed right^2 H is
  countably covered when H is countable and K4-free. Crucially, the full
  right^2 graph need NOT itself be K4-free. This bypasses, rather than
  misuses, the earlier external-detector/K4-image limitation.
* `secondShift_cover_of_cofinal` / `canonical_secondShift_cover`: countable
  K4-free targets now work for the original canonical second-shift domains;
  the target need no longer be triangle-free for the edge-cover conclusion.

A preliminary exact Python quotient calculation identified the four-index
backtracking obstruction. The final result is the independent Lean proof
above, not an appeal to the calculation.

## All WELL-ORDERED second-shift exponential domains excluded (new, verified)

`Submission/WellOrderedSecondShiftCover.lean` compiles with an olean.
Namespace `Erdos595WellOrderedSecondShift`;
log `/tmp/well-ordered-second-shift.log`. All three audits use permitted axioms.

* `coloring_of_encoding`: any injection A -> Set(Set N) yields a proper
  countable coloring of oneGraph A (the ordered shift on increasing triples).
  First-difference witnesses give binary sequence codes for increasing
  pairs, and a second first-difference construction colors increasing triples.
* `size_lower`: an uncountably chromatic second-shift domain therefore has
  #A > #(Set(Set N)).
* `palette_bound`: for any countable target H, its two-stage directed profile
  palette Palette H has cardinality at most #(Set(Set N)).
* `canonical_embedding`: if A is WELL-ORDERED and oneGraph A is uncountably
  chromatic, it contains an order embedding of CanonicalIndex H. This uses
  the initial-ordinal cardinal bound, not an unjustified long increasing
  sequence in an arbitrary linear order.
* `all_well_ordered_domains_cover`: restrict to this canonical copy and
  apply the new backtracking cover. Thus ALL well-ordered second-shift
  exponentials with countable K4-free targets are now excluded, INCLUDING
  the previously unresolved intermediate sizes. The larger triple-Ramsey
  host from LargeSecondShiftExponential is no longer needed for this family.

SCOPE: This does not yet exclude every NON-WELL-ORDERED linear-order domain,
all higher shifts, arbitrary exponentials, or the third generic mutual U.
It does not settle Erdos 595. The earlier candidate inventory must no longer
list well-ordered intermediate second-shift exponentials as unresolved.

The cone review also noted informally that grouping third-stage supports
only by an original independent set S need not yield a triangle-free piece:
a triangle with three private leaves supplies a finite counterexample via
triple-principal points and principal cone indices. No new Lean theorem for
that observation was added in this continuation, and it says nothing against
countable covering of such groups.

Spec.lean remains unchanged with its original sorry. No completed proof or
disproof has been submitted.

## Exact characterization of second-arc targets (new, verified)

`Submission/SecondArcTargetCharacterization.lean` compiles with an olean.
Namespace `Erdos595SecondArcTarget`; log `/tmp/second-arc-target.log`.
All three printed audits use only the permitted axioms.

Let T be the arc graph of the complete graph on N × Fin 4. This is one
fixed countable K4-free target. `arcColor` uses a differing coordinate of
a proper sequence coloring; `label` then labels consecutive arcs by a
vertex of T. `fixed_target_iff` and `any_target_iff` prove:

  G properly colorable by N -> Fin 4
  iff the directed second arc graph of G maps into T
  iff it maps into ANY countable K4-free target (existentially chosen).

Thus this target condition is exactly a continuum bound on proper VERTEX
chromatic cardinal. It is stronger than countable triangle-free EDGE
coverability. Triangle-free graphs of arbitrarily large chromatic cardinal
prevent turning the result into a universal K4-free covering theorem.
Spec.lean remains unchanged; this does not settle the conjecture.

## Third-arc alternating tags fail already on a finite diamond (new, verified)

`Submission/ThirdArcBacktrackingFailure.lean` compiles with an olean.
Namespace `Erdos595ThirdArcFailure`;
log `/tmp/third-arc-backtracking-failure.log`.
All four printed audits use only permitted axioms.

A finite lookup function L : (Fin 4)^4 -> Fin 3 satisfies, by kernel-checked
finite decisions:

* `label_step`: if consecutive a,b,c,d,e are unequal, then
  L(a,b,c,d) != L(b,c,d,e).
* `label_alternating`: for a<b, L(a,b,a,b)=0 and L(b,a,b,a)=1.
* `diamond_cliqueFree`: K4 minus edge 03 is K4-free.
* `same_tag_three`: its path 0--1--2--3 has the same alternating ordered
  pair label (0,1) on all three directed edges.
* `target_cliqueFree`: the target K3 is K4-free.

Thus the exact no-three argument from SecondArcBacktracking cannot simply
be moved to the THIRD directed arc stage, even with K4-free source and
target. The generated finite table is independently kernel-checked; the
Python search is not a proof dependency. This is not a disproof of Erdős
595, and not a proof that all third-stage approaches fail.

Subsequent informal review considered adapted extensions, infinitary
partite constructions, exponentials, canonical covering filters and
first-difference tree colorings. None supplied the missing main theorem.
In particular, free amalgamation of finite colored K4-free graphs does not
justify an arbitrary-cardinal omitted-type construction: an infinite
palette is not a finite first-order disjunction, and newly created edges
can omit every named color. No such compactness claim has been used.

Spec.lean is still unchanged with its original sorry. No completed main
proof or disproof has been submitted.

## Literal prescribed-color extension from countably PROPER old graphs (new, verified)

`Submission/PrescribedCountableProperExtension.lean` compiles with an olean.
Namespace `Erdos595PrescribedCountableProper`;
log `/tmp/prescribed-countable-proper.log`.
All four printed axiom audits use only propext, Classical.choice, Quot.sound.

* `extend_valid` / `exists_extension`: on a sum V+W, retain ANY prescribed
  valid old edge coloring c on V. If the old induced graph has a proper
  natural-number VERTEX coloring f and the new induced graph W is countably
  edge-coverable with coloring d, put 2*f(v)+1 on crossing edges and 2*d on
  new-new edges. This is valid and leaves every old pair literally unchanged.
  Triangles with two old vertices have different crossing colors; triangles
  with one old vertex have an odd/even mismatch. No K4 assumption is needed.
* `along_embedding`: packages this for any induced graph embedding into an
  already edge-coverable larger graph. Uses an explicit sum/range-complement
  equivalence, not a renaming of prescribed old colors.
* `from_countable`: in particular, any countable old carrier works.
* `first_to_second`: EVERY valid prescribed countable edge coloring on the
  FIRST mutual U of a countable K4-free base extends literally to SECOND U.
  The first stage is properly countably vertex-colorable by the verified
  finite-maximal-clique theorem; the second stage is edge-coverable by Work.

Thus a strategy that tries to destroy EVERY prescribed first-stage coloring
at the next mutual-U stage is impossible, not merely unproved. This does not
say all colorings extend from SECOND to THIRD U, or that third U is covered.
Countably edge-coverable old graphs are not interchangeable with countably
PROPERLY vertex-colorable old graphs; the adapted-color counterexamples remain.

Further informal review in this continuation considered long towers,
Boolean-valued/reduced powers, closure ranks, generalized Ramsey modeling,
and algebraic root representations. No external-color compactness or main
construction was obtained. Two recurrent traps were checked against earlier
results: universal first-U preservation for countably properly colorable
bases is already equivalent to the main universal negative statement
(DetectorExtensionReduction); F3 triangle-linearization is already refuted
by the finite Paley-17 certificate. Unbounded FINITE chromatic number of an
elementary class alone does not force an uncountable example (C4-free graphs
illustrate the ordinary-graph failure).

Spec.lean remains unchanged with its original sorry. No proof or disproof of
Erdős 595 has been submitted.

## OR-directed right adjoints: stronger anchor bounds (new, verified)

`Submission/DirectedOrRightCover.lean` compiles with an olean.
Namespace `Erdos595DirectedOrRight`; log `/tmp/directed-or-right-cover.log`.
All four printed audits use only permitted axioms.

* `orGraph R`: adjacency is R(p,q) OR R(q,p), not mutual adjacency.
* `tag H p`: for a biclique p with both sides nonempty, choose one ordered
  anchor pair (a,b); otherwise use none.
* `no_two`: p -> q -> r cannot all have the same tag when H is K4-free.
  Both sides of q are automatically nonempty. Intersection witnesses x,y
  are adjacent and each adjacent to both common anchors a,b; a,b are also
  adjacent. This would be K4 in H. Empty-side tags are handled by the
  same observation at the middle point.
* `one_countable`: OR(right H) is PROPERLY COUNTABLY vertex-colorable for
  countable K4-free H. Finite ranks within countably many anchor classes
  supply the coloring. No clique bound on OR(right H) itself is assumed.
* `powersetColor`: a proper C-coloring of OR(R) yields a proper Set C
  coloring of OR(right R), using the color sets on incoming sides.
* `two_powerset`: OR(right^2 H) has a proper Set N palette. This strengthens
  the earlier mutual-only second-arc result; full OR graphs may contain K4.
* `one_pullback`, `two_pullback`: corresponding conclusions for maps from
  the first/second directed arc graphs of an arbitrary directed relation
  into countable K4-free H. The relation need not be symmetric.

## ALL second ordered-shift exponential domains excluded (new, verified)

`Submission/AllSecondShiftCover.lean` compiles with an olean.
Namespace `Erdos595AllSecondShift`; log `/tmp/all-second-shift-cover.log`.
Both audits permitted.

For EVERY linear order A, countable K4-free target H, and uncountably
properly chromatic second shift oneGraph A:

* `coloring`: the exponential H^(oneGraph A) has a proper Set N coloring.
* `countable_cover`: consequently it has a countable triangle-free EDGE cover.

Proof: color each two-stage directed profile by the new proper Set N
coloring of OR(right^2 H). For adjacent exponential vertices f,g, equality
of these colors at indices a,b forces a=b: a<b or b<a gives one directed
arrow and contradicts properness. For each f, two distinct indices have
repeated profile COLOR because otherwise A injects into Set N, contradicting
uncountable chromaticity of its second shift. A repeated profile color then
properly colors f. Exact profile equality and cofinal repetition are no
longer needed.

This supersedes the former frontier: NON-WELL-ORDERED second-shift domains
are ALSO excluded, including dense/lexicographic/reversed orders. No long
well-ordered subset was assumed or extracted. Higher/general exponential
domains, third generic mutual U, and second order-oriented U remain open.

## Strong index bounds for countable K4-free shift targets (new, verified)

`Submission/OrderedShiftTargetBounds.lean` compiles with an olean.
Namespace `Erdos595OrderedShiftTarget`;
log `/tmp/ordered-shift-target-bounds.log`. Both audits permitted.

* `first_index`: if orderedShiftGraph A maps to a countable K4-free H, then
  A injects into N (stronger than the continuum bound from ordinary proper
  countable coloring of the shift).
* `second_index`: if oneGraph A maps to a countable K4-free H, then A
  injects into Set N (stronger than the double-powerset bound for ordinary
  proper countable coloring of the second shift).

Both use directed currying and the OR-right bounds. These are proved for
arbitrary linear orders, not only well-orders. Converse target constructions
were discussed but not included in this file.

Further informal review of higher shifts and right adjoints of apex
extensions produced no main proof. A right adjoint of a single cone over a
triangle-free graph is not a convincing candidate: partition its bicliques
by which side contains the one apex (or neither); each induced part is
triangle-free, since same-part intersection witnesses avoid the apex. This
observation was not separately formalized. Independent families of many
apices need a separate analysis; no non-coverability was obtained.

Spec.lean remains unchanged with its original sorry. None of these results
settles Erdős 595; no proof/disproof has been submitted.

## Right adjoints with properly colored triangle transversals (verified)

`Submission/RightProperTransversal.lean` compiles with an olean.
Namespace `Erdos595RightProperTransversal`; log
`/tmp/right-proper-transversal.log`. All printed axiom audits are permitted.

For arbitrary H and S with triangle-free complement and a proper C-coloring
of H induced on S, label each right-adjoint biclique by the set of colors
appearing on its incoming side inside S. A same-label arrow witness cannot
lie in S: otherwise its color appears on the incoming side of the source,
giving an edge between equally colored S-vertices. Therefore a same-label
right-adjoint triangle yields a triangle outside S.

* `countable_cover`: if C is countable, right H is countably edge-covered.
  No cardinal bound is imposed on S or the rest of H.
* `two_cover_of_bool`: a Boolean vertex partition with triangle-free parts
  gives two triangle-free edge pieces (crossing and within-part edges).
* `independent_two_cover`: if S is independent and its complement is
  triangle-free, right H has a two-piece edge cover.
* `apexFamily_two_cover`: this excludes the first right adjoint of every
  independent-apex-family extension of a triangle-free base, without any
  K4 hypothesis on the right adjoint.

Pending, not proved: a possible second-right single-cone analysis. Pure
bicliques (one side exactly the apex) form a bipartite triangle transversal
if the triangle-free base has no closed 5-walk. An old exact computation
reported arc^2(K4) -> cone(C5); it has not yet been certified in Lean.
Combining the two would exclude K4-free second-right single cones.

The main conjecture in Spec.lean remains unchanged with sorry.

## All K4-free second-right SINGLE CONES excluded (new, verified)

`Submission/SecondConeRightCover.lean` and
`Submission/SecondConeCliqueCover.lean` both compile with oleans and permitted
axiom audits. Logs `/tmp/second-cone-right-cover.log` and
`/tmp/second-cone-clique-cover.log`.

Namespaces Erdos595SecondConeRight and Erdos595SecondConeClique.

* NoFive G forbids every closed five-step walk in G, repetitions allowed;
  in particular it implies triangle-freeness.
* Pure bicliques in right(cone G) have one side exactly {apex}. They induce
  a bipartite graph (pureColor is a Bool proper coloring).
* pure_transversal: if NoFive G, every triangle of right(cone G) contains
  a pure biclique. Normalize one cyclic intersection witness to the apex;
  the reverse cycle has its apex on one of two other arrows. If the
  minority-type biclique is not pure, a base vertex on its apex-containing
  side, together with four intersection witnesses, gives a closed 5-walk.
* Erdos595SecondConeRight.countable_cover: the existing properly-colored
  triangle-transversal theorem covers right^2(cone G) under NoFive G,
  with no cardinal bound.
* Erdos595SecondConeClique.label_adj: a 60-vertex arc^2(K4) -> wheel5 map
  is independently verified with decide +kernel. It uses a 256-entry table
  on raw coordinate quadruples, restricted to the actual second arc carrier.
* noFive_of_cliqueFree: any closed 5-walk in G gives wheel5 -> cone G;
  composing and currying twice yields K4 -> right^2(cone G).
* Erdos595SecondConeClique.countable_cover: EVERY K4-free second-right
  single cone is countably triangle-free edge-covered, even without
  assuming triangle-freeness of the original base separately.

This completes the pending single-cone candidate exclusion, not the main
conjecture. Independent families of apices at the second right stage need
additional analysis; their two cyclic apex witnesses may be different.
Spec.lean is unchanged with its original sorry. No submission.

## Second arcs have independent triangle transversals (new, verified)

`Submission/SecondArcTransversal.lean` compiles with an olean and permitted
axiom audits. Namespace Erdos595SecondArcTransversal; log
`/tmp/second-arc-transversal.log`.

Given any linear order on the vertices of G, select a second arc (e,f) if:
* e.head = f.tail and this shared vertex is less than both other endpoints;
  OR
* f.head = e.tail and this shared vertex is greater than both other endpoints.

* independent: two selected second arcs cannot concatenate. Same-direction
  cases give contradictory consecutive extrema; mixed cases require the
  same shared vertex to be both smaller and larger than the other endpoint
  of the middle arc.
* triangle_hit: every second-arc triangle comes from a directed cycle of
  three first arcs. At the original vertices either its minimum or maximum
  selects one second arc, depending on the orientation.
* base_triangleFree: the complement of Selected in arc^2 G is triangle-free.
* intoCone: collapse Selected to one apex, keeping all other vertices. This
  is a graph homomorphism arc^2 G -> cone(Base G).
* intoSecondRight: currying twice gives G -> right^2(cone(Base G)). There is
  NO K4-freeness assertion about this full target.
* right_second_arc_two_cover: using the existing independent-transversal
  theorem, right(arc^2 G) has TWO triangle-free edge pieces for EVERY G.

## Cone factorization fails K4 preservation already on the diamond (verified)

`Submission/SecondArcConeFailure.lean` compiles with an olean and permitted
axiom audits. Namespace Erdos595SecondArcConeFailure; log
`/tmp/second-arc-cone-failure.log`.

For the K4-free diamond on 0,1,2,3 with only edge 03 missing, these five
second arcs all avoid Selected and form a 5-cycle:

 ((0,1),(1,2)), ((1,2),(0,1)), ((0,1),(2,0)),
 ((2,0),(3,2)), ((1,2),(2,0)).

* not_selected and adjacent are independently checked by decide +kernel.
* not_noFive: Base diamond has a closed five-step walk.
* creates_four: the source diamond is K4-free, but
  right^2(cone(Base diamond)) is NOT K4-free, by the certified wheel map.

Therefore the new cone factorization cannot be combined with the K4-free
single-cone theorem to obtain a universal covering proof.

Additional exact Python check, NOT a Lean theorem: the minimal non-pure
triangle pattern for TWO different independent apices has base 5-cycle
0-1-2-3-4-0, alpha adjacent to {3,1,0}, beta adjacent to {3,0,2}. It is
3-colorable by [0,1,0,1,2,2,2]; the search found no arc^2 K4 homomorphism
into it. Thus the particular wheel certificate does not directly extend
from one apex to arbitrary independent-apex families.

No proof or disproof of erdos_595 has been obtained. Spec.lean is unchanged
with its original sorry. No completed proof has been submitted.

Final continuation review: third mutual-U, canonical edge-filter couplings,
and binary-matroid/adapted-coloring approaches supplied no additional main
lemma. In particular, the matched-pair hypergraph's symbolic anti-Pasch
check already blocks a Pasch-only shortcut; unrestricted adapted coloring
is already disproved in Work.lean. None of these routes was promoted to a
proof. Latest direct Spec.lean build: /tmp/spec-second-cone-review.log,
reporting only the unchanged original sorry warning.

## Full independent-apex families reduce to single cones (new, verified)

`Submission/FullApexSecondRightCover.lean` compiles with an olean; namespace
Erdos595FullApexSecondRight; log `/tmp/full-apex-second-right.log`. All audits
use only permitted axioms.

IMPORTANT FRONTIER CORRECTION: for a TRIANGLE-FREE base G, the FULL family
apexFamilyGraph G already contains a universal apex (the admissible subset
univ). Collapsing every independent apex to none gives a graph homomorphism
to coneGraph G, and including the universal apex gives a homomorphism back.
Thus their second right adjoints are homomorphically equivalent.

* second_cliqueFree_iff: K4-freeness agrees for these two second right adjoints.
* second_cover_iff: countable triangle-free edge coverability agrees as well.
* countable_cover: the full family's K4-free second right adjoint is covered.

The earlier statement that the full family's SECOND stage remained open was
too cautious; this elementary collapse excludes it. ARBITRARY PARTIAL apex
families, with no universal apex, are not excluded by this argument. The
seven-vertex two-apex pattern in the preceding notes is such a partial family.

## Exact second-cone clique criterion (new, kernel-verified)

`Submission/SecondConeCriterion.lean` compiles with an olean. Namespace
Erdos595SecondConeCriterion; log `/tmp/second-cone-criterion.log`.

* cliqueFree_iff_noFive: for arbitrary G,
    right^2(cone G).CliqueFree 4  iff  NoFive G.
  NoFive forbids closed five-step walks, including repetitions (so triangles
  are automatically forbidden too).
* no_hom: under NoFive G there is no arc^2 K4 -> cone G.

The finite certificate uses 60 actual second arcs of K4, 119 adjacency
constraints, and 44 actual five-cycles. An independent set cannot meet all
44 cycles. For a hypothetical homomorphism into cone G, the points sent to
the apex would be such an independent set, and every five-cycle must meet
it by NoFive G.

CERTIFICATE TRUST: an initial bv_decide version used compiler-trust axioms
and was REPLACED. The current file contains explicit propositional proofs
of 166 learned clauses (private step164 through step329), reconstructed
from an external LRAT search. Every implication is checked using ordinary
Or.elim, by_contra, and equality/negation reasoning. There is NO bv_decide,
ofReduceBool, trustCompiler, or sorry in the current file. The printed audits
of no_selector, no_hom, and cliqueFree_iff_noFive contain only propext,
Classical.choice, Quot.sound. Finite adjacency tables use decide +kernel.

Research artifacts: /tmp/arc2-no35-core.json, /tmp/arc2-no35-core.lrat,
/tmp/gen_kernel_rup_split.py. The generated proof in the Lean file has no
runtime dependency on them. The script still needs its unary-negation simp
line omitted if regenerated; by_contra already introduces the positive
hypothesis for a negated goal. The current Lean file contains that fix.

## Finite bounds for properly colored transversals (new, verified)

`Submission/FiniteTransversalRightCover.lean` compiles with an olean.
Namespace Erdos595FiniteTransversalRight; log
`/tmp/finite-transversal-right-cover.log`. All audits permitted.

* finite_cover: if H outside S is triangle-free and H induced on S has a
  proper Fin n vertex coloring, right H has n+1 triangle-free edge pieces.
  Use n Boolean cuts recording each color's occurrence on the incoming
  biclique side, plus the within-profile graph. The latter is triangle-free
  by RightProperTransversal.no_triangle.
* cone_three_cover: NoFive G gives THREE edge pieces for right^2(cone G).
* cone_three_cover_of_cliqueFree: the K4-free single-cone bound is therefore
  uniformly THREE, not merely countable.

`Submission/FullApexFiniteCover.lean` packages finite-cover pullback and the
same three-piece bound for the full independent-apex family's K4-free
second right adjoint. It also transfers the exact NoFive criterion. See
`/tmp/full-apex-finite-cover.log` for the build/audit status.

These are candidate exclusions, not a main settlement. Review of generic
saturation, graphic closure, canonical-filter couplings, and third-stage
cone supports yielded no new missing universal-cover or non-cover lemma.
Spec.lean remains unchanged with its original sorry. No submission.

## Prescribed edge colors cannot always be repaired by choosing an order (verified)

`Submission/PrescribedOrderObstruction.lean` compiles with an olean.
Namespace Erdos595PrescribedOrderObstruction; log
`/tmp/prescribed-order-obstruction.log`. All four audits use only propext,
Classical.choice, Quot.sound.

The graph has seven vertices and edges
  01,03,04,06,12,13,23,25,34,35,36,45,56.
Color 03,04,12,13,35,56 red and the other edges blue.

* valid: this is a two-coloring with NO monochromatic triangle.
* cliqueFree: the graph is K4-free.
* every_vertex_bad: every vertex a has neighbors b,c forming a triangle
  with a, and the two spokes ab,ac have equal colors. The checked witness
  pairs for a=0,...,6 are (3,4),(2,3),(3,5),(0,1),(3,5),(3,6),(0,3).
* no_order: for every injection r:Fin 7 -> I into ANY linear order, some
  a,b,c satisfy r(b),r(c)<r(a), form a triangle, and have equal-colored
  spokes at a. Take a of maximum rank and use its witness pair.

Thus a valid prescribed edge coloring need not become a proper
previous-neighbor coloring under ANY order. This refutes the specific
elimination/ordering shortcut for prescribed colors, not the existence of
some DIFFERENT coloring and a suitable order. The latter universal
sufficient condition for K4-free graphs remains unresolved.

The certificate was extracted from a two-coloring of the already verified
Paley-17 graph, then reduced to a seven-vertex induced colored core; the
final file checks its own graph and color tables directly with decide
+kernel and does not depend on the external search or on Paley-17.

Further review of ordered local colorings, generic independent-apex towers,
Hilbert triangle-hitting representations, and higher shift exponentials did
not yield a main proof or disproof. In particular:
* an order-based local proper-coloring criterion is sufficient, not a
  known necessary characterization of countable triangle-free edge covers;
* failure of one prescribed coloring to fit every order does not make the
  underlying graph non-coverable (the example above has TWO edge pieces);
* saturation does not constrain arbitrary external countable colors;
* fixed uniform Hilbert triangle-hitting margins are already obstructed by
  the earlier finite Ramsey-transfer argument; no nonuniform construction
  was obtained.

Spec.lean remains unchanged with its original sorry. No completed proof has
been submitted.

## Second symmetrized arc reflection and sparse-triangle normal form (NEW, verified)

This continuation resolves the previously unproved **TWO-STEP** K4-reflection
claim. It does NOT settle Erdős 595 and does NOT establish reflection for
arbitrary higher arc iterations.

### ArcRoundTrip.lean: triangle-connected reflection

The existing file was extended and rebuilt. All previous declarations remain.
Backup: `/tmp/ArcRoundTrip.before_second_reflection.lean`.
Build/audit log: `/tmp/arc-round-trip-triangle-connected.log`.

New public declarations in `Erdos595ArcRoundTrip`:
* `UniqueTriangleEdge G`: an edge has at most one common neighbor.
* `tailHom`: arcGraph G -> G.
* `triangle_connected_hom`: if G has UniqueTriangleEdge, a source F whose
  vertices are connected by triangle edges, and which has a triangle, maps
  into right(arc G) only if it maps into G. Connectivity is expressed as
  propagation of arbitrary predicates along triangles.
* `arc_unique_triangle_edge`: every arc graph satisfies UniqueTriangleEdge.

Proof mechanism, using the earlier biclique classification:
* A right(arc G) triangle containing a singleton-left biclique has ALL three
  bicliques singleton-left. Similarly for singleton-right.
* A Good biclique has two arcs on each side with injective tails and heads.
  If it lies on a right triangle, those arcs yield a four-cycle in G plus a
  diagonal. The two common neighbors of that diagonal contradict
  UniqueTriangleEdge. Thus there are NO Good vertices on such triangles.
* With small sides excluded, triangles are uniformly Pos or uniformly Neg.
  Pos and Neg cannot overlap at a nonsmall biclique.
* Triangle connectivity consequently confines the entire source image to
  one of the four families. Small families map to arc G and then G; Pos and
  Neg families map directly to G.

All new audits use only permitted axioms. `arc_unique_triangle_edge` uses
only propext.

### SecondArcReflection.lean

New file, namespace `Erdos595SecondArcReflection`, compiled with an olean.
Log: `/tmp/second-arc-reflection.log`.

* `reflects_four`, `arc_twice_four_hom_iff`:
    arc^2 K4 -> arc^2 G exists iff G contains K4.
* `unitTwice`: G -> right^2(arc^2 G).
* `right_twice_arc_twice_cliqueFree_iff`:
    right^2(arc^2 G) is K4-free iff G is K4-free.
* `source_cover_of_twice_cover`: covering the two-step target covers G.
  NO converse covering-preservation theorem is asserted.

The finite source arc K4 has 12 vertices. Its triangle-edge graph is connected
(in fact every vertex is within three triangle-edge steps of (0,1)). This
finite fact is certified independently by `decide +kernel`. Curry a map
arc^2 K4 -> arc^2 G once, apply triangle_connected_hom with base arc G, and
then use the existing one-step arc_four_hom_iff.

Exploratory precursor only: `/tmp/test_second_arc_reflection.py` checked
arc^2 K4 -> arc^2 W5 and arc^2 W7 using CaDiCaL; both were UNSAT. Those runs
are NOT used by the Lean proof, which is fully general. No SAT process remains.

### SecondArcTriangleStructure.lean

New file, namespace `Erdos595SecondArcTriangleStructure`, compiled with an olean.
Log: `/tmp/second-arc-triangle-structure.log`.

* `VertexDisjointTriangles`: two triangles through the same vertex have the
  same other two vertices (up to swapping).
* `arc_vertex_disjoint`: UniqueTriangleEdge G implies VertexDisjointTriangles
  (arc G).
* `second_arc_vertex_disjoint`: triangles of arc^2 G are vertex-disjoint for
  EVERY G, with no clique hypothesis.

The two printed theorem audits use only propext.

### SecondArcNormalForm.lean: exact reduction of the full problem

New file, namespace `Erdos595SecondArcNormalForm`, compiled with an olean.
Log: `/tmp/second-arc-normal-form.log`.

* `IndependentTriangleTransversal`: an independent vertex set has a
  triangle-free complement.
* `second_arc_transversal`: arc^2 G has this property, using the earlier
  order-based Selected set.
* `SparseTriangleBase`: IndependentTriangleTransversal AND
  VertexDisjointTriangles.
* `second_arc_sparse`: every arc^2 G belongs to this restricted class.
* `universal_cover_iff`, `witness_normal_form`: exact universal/existential
  reductions to K4-free second right adjoints of bases with independent
  triangle transversals.
* `universal_cover_sparse_iff`, `witness_sparse_normal_form`: the same exact
  reductions with the additional vertex-disjoint-triangle requirement.

Thus the remaining special-class question is genuinely equivalent to the
full covering problem, not merely an arbitrary candidate search:

  If H has vertex-disjoint triangles and an independent triangle transversal,
  and the FULL right^2 H is K4-free, must right^2 H be countably covered?

Neither answer to this question was proved. The K4 hypothesis on the full
second right adjoint is essential (H = arc^2 K4 itself satisfies the two base
properties but its second right adjoint contains K4). Do not collapse the
independent transversal to a universal apex: the earlier diamond counterexample
still blocks that operation. No universal countable homomorphism target for
this class can be inferred either.

All normal-form audits use only propext, Classical.choice, Quot.sound.

Spec.lean remains unchanged, SHA256
`de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45`.
Latest direct build: `/tmp/spec-second-arc-normal-form-review.log`, with only
its original sorry warning. No completed proof/disproof has been submitted.

## Proper-transversal shortcut fails in the exact sparse normal form (NEW, verified)

`Submission/SparseTransversalObstruction.lean` compiles with an olean.
Namespace `Erdos595SparseTransversalObstruction`; log
`/tmp/sparse-transversal-obstruction.log`. All five main theorem audits use
only propext, Classical.choice, Quot.sound. No holes or compiler-trust tactics.

Definitions:
* `VertexTriangleRamsey G C`: every C-coloring of vertices gives a
  monochromatic triangle.
* `CountablyProperTransversal H`: there is S with H outside S triangle-free
  and H induced on S properly colorable by Nat.

New results:
* `no_transversal_of_hom`: if G is vertex-triangle-Ramsey for Set Nat and
  G -> right H, H has NO CountablyProperTransversal. The existing incoming-
  color profile from RightProperTransversal.no_triangle would otherwise
  give a forbidden Set Nat vertex coloring of G.
* `shift_vertex_ramsey C`: for any nonempty palette C, an appropriate
  one/two-step shift-square graph is K4-free, has a TWO-piece edge cover,
  and is vertex-triangle-Ramsey for C. The arbitrary-palette triple Ramsey
  host on Fin 5 makes the three consecutive windows monochromatic.
* `covered_source_no_transversal`: choose that source G with C = Set Nat.
  Then G is K4-free and covered, right^2(arc^2 G) is K4-free, but
  right(arc^2 G) has NO countably properly colored triangle transversal.
* `sparse_no_transversal`: consequently there is H with BOTH
  SparseTriangleBase properties and FULL right^2 H K4-free, while right H
  has no CountablyProperTransversal.
* `covered_right_no_transversal`: a separate one-step example H = arc G
  has right H K4-free AND countably edge-covered, although H itself has no
  CountablyProperTransversal. This uses the existing one-step covering-
  preservation theorem, not an unproved two-step analogue.

IMPORTANT NEW GUARDRAIL: the sparse normal form CANNOT universally be settled
by finding a countably properly vertex-colored triangle transversal in its
first right stage. That proposed sufficient condition is now DISPROVED in
the exact normal-form class. Lack of such a transversal is NOT lack of a
countable edge cover. No covering assertion about the TWO-step target in
covered_source_no_transversal is proved; the source being covered does not
supply the unproved converse to source_cover_of_twice_cover.

Other review this continuation supplied no main lemma. In particular:
* finite determination of common neighborhoods does not remove dependence
  of next-stage adjacency on the original arbitrary graph; do not claim
  RelativeInvariant merely from finite biclique parameters;
* no external-color saturation, countably complete ultrafilter extension,
  or infinitary partite coherence gap was closed;
* the problem website again failed DNS resolution.

Spec.lean is unchanged, with its original sorry. Latest build log:
`/tmp/spec-sparse-transversal-review.log`; it reports only that sorry warning.
SHA256 remains de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45.
No completed main proof or disproof has been submitted.

## Adjacent intersection-trace support shortcut explicitly refuted (verified)

ThirdTriangleFiniteEdgeSupportFailure.lean now also proves:
* `adjacent_trace_no_finite_support`: Q0,Q1 are adjacent at stage two, but
  their first-stage trace intersection has NO common original support with
  a finite triangle-free edge cover.
* `common_trace_independent`: that trace intersection is independent in the
  first-stage graph, by the stage-two K4 bound.

Thus the special adjacent-intersection case suggested in the preceding
continuation is already blocked by the suffix-row example. Its finite common
INDEPENDENT supports do not compress to one global triangle-free support.
Build/audit log /tmp/adjacent-trace-support.log; only permitted axioms.
This is an auxiliary obstruction, not a settlement. Spec is unchanged.

## TWO-step arc/right round trip also preserves covers (NEW, verified)

SecondArcCover.lean compiles with an olean; namespace Erdos595SecondArcCover.
Log /tmp/second-arc-cover.log. Audits use only permitted axioms.

* `component` codes a triangle-connected component by the family of all
  triangle-closed vertex subsets containing the vertex.
* `component_connected` proves the predicate-propagation connectivity needed
  by ArcRoundTrip.triangle_connected_hom, without a quotient construction.
* `right_roundtrip_cover`: for H with UniqueTriangleEdge, a cover of right H
  gives a cover of right(right(arc H)). Each triangle-bearing component of
  right(arc H) maps to H by the earlier classification; triangle-free
  components are harmless. RightFiberCover.cover_of_fibers combines them.
* `twice_cover`, `twice_cover_iff`: for EVERY G, with no clique hypothesis,
      right^2(arc^2 G) is countably covered iff G is countably covered.

This supersedes earlier notes saying the forward two-step cover theorem was
missing. In particular, the two-step target of the covered source used in
SparseTransversalObstruction is now known covered as well as K4-free.
This is NOT a settlement of the main problem. It excludes two-step
round-trip amplification of a covered source. No higher-iteration statement
has been established. Spec.lean is unchanged with its original sorry.

SparseTransversalObstruction.lean now imports SecondArcCover and adds
`sparse_covered_no_transversal`: there is a sparse H whose FULL second-right
is K4-free AND covered, but whose first-right graph has no countably proper
triangle transversal. Log /tmp/sparse-covered-transversal.log, permitted
axioms only. This strengthens the old method obstruction, not Erdős 595.

A further mathematical review considered private edge-triangle attachments
and triangle-fiber matching bundles. No new witness or verified theorem from
those constructions was obtained. In particular, finite-color experiments
were NOT run and no infinite chromatic transfer was established. The two-step
round-trip theorem above should not be extended to arbitrary right towers.

Latest Spec build /tmp/spec-second-arc-cover-review.log still reports its
original sorry. SHA256 remains
`de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45`.
No completed proof/disproof has been submitted. No active build is pending.

## Successive MAXIMAL triangle-free deletions need not exhaust triangles (NEW, verified)

MaximalDecompositionFailure.lean compiles with an olean, no holes or warnings.
Namespace Erdos595MaximalDecompositionFailure; log
/tmp/maximal-decomposition-failure.log. All audited axioms are permitted.

Construction:
* Node has three root leaves and finite binary forks `fork n a b`.
* Raw edges join different root leaves or a fork to one of its children.
* A valid fork has valid adjacent children, and its natural label n is less
  than the label of their old edge. Root edges have label top in WithTop Nat.
* Recursive proper coloring picks one of three colors absent from the two
  children. Thus the resulting graph is countable, THREE-colorable, K4-free,
  and countably edge-covered.
* For every edge of label greater than n, the corresponding valid fork n
  is a common neighbor whose two incident edges both have label n.

Results:
* `piece_triangleFree`: edges labeled n form a triangle-free graph.
* `remaining_zero`: R_0 is the whole graph.
* `remaining_succ`: R_(n+1) = R_n minus piece n.
* `piece_le_remaining`, `piece_maximal`: each piece n is actually maximal
  triangle-free inside the corresponding remaining graph.
* `residual_triangle`: G minus the supremum of ALL natural-labeled pieces
  still contains the original root triangle.
* `not_cover`: that particular maximal-deletion sequence is not a cover.

This strengthens the old informal Grundy warning: even maximality at EVERY
stage does not make countably many deletions sufficient. It does NOT rule out
existence of a better sequence; this example has a finite cover. It is NOT a
counterexample to Erdos 595 and must not be submitted as one.

Other review this continuation did not close the asymmetric infinite-red /
finite-blue triangle Ramsey gap, construct coherent edge-dependent finite
bounds, or prove countable-palette compactness. Palette-capturing alone does
not force nonadaptability: the existing normalization theorem supplies a
finitely adapted coloring of any nonempty covered graph. No theorem extending
ordinary pure-graph saturation to arbitrary external colorings was obtained.
External website access still failed DNS resolution.

Spec.lean is unchanged with its original sorry; latest direct build log
/tmp/spec-maximal-decomposition-review.log reports that warning only. SHA256
`de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45`.
No completed main proof/disproof was submitted, and no active build remains.

## Further uncountable-product and Ramsey review (no new settlement)

Reviewed FixedFiniteReducedPower, the binary/three-letter Hales--Jewett
boundary, canonical edge-filter couplings, and infinite-target focusing.
No new Lean theorem or main proof was obtained.

Scope retained:
* The fixed uncountable-index power is an EXACT universal normal form.
  Its factors' finite palettes and the symmetry of the full carrier do not
  prove non-coverability or localize an external countable coloring.
* Three-letter Hales--Jewett fails for every index cardinal, but the resulting
  line-avoiding vertex/edge-alphabet coloring is NOT automatically valid on
  every graph triangle in a varying-factor product.
* Countable proper-coloring compactness cannot be inferred from unbounded
  finite chromatic numbers: the established countable-codegree theorem
  already supplies counterexamples to such a general inference.
* No coherent infinite partite homogenization or asymmetric infinite-red /
  finite-blue triangle Ramsey host was constructed.
* Neither ordinary ultrafilter extension nor generic-filter language supplies
  a countably complete ultrafilter. Pairwise marginal agreement still does
  not make a diamond-glued pair of leaves an edge.

An informal forcing check also found a simple obstruction to hoping that
countable partial valid edge-colorings automatically have a useful chain
condition for K4-free graphs: take a countable independent root R={r_n},
vertices a_i,b_i, all root-to-private edges, and private edges a_i--b_j exactly
when i!=j. This is three-partite and K4-free. The condition on R+{a_i,b_i}
assigning color n to both r_n spokes is valid, but two such conditions have
no common valid extension: the edge a_i--b_j would be forbidden every n.
This observation has NOT been formalized and is NOT non-coverability of the
three-partite graph, which plainly has a finite cover.

Spec remains unchanged with its original sorry. No build is running and no
completed proof/disproof has been submitted.

## Further matching-bundle and infinitary review (no settlement)

This continuation produced no new Lean theorem and no proof/disproof of
Erdos 595. Spec.lean remains unchanged.

One additional INFORMAL candidate exclusion was checked mathematically:
let R be an arbitrary graph with no closed five-walk. Make three vertices
A_i,B_i,C_i over each index i, put a triangle in each fiber, and join fibers
along R edges using either of the perfect matchings (A B) or (A C).
The choice of the two matchings can vary with the index edge.
Collapse all A_i to one cone apex. The remaining graph maps to the graph
on V(R) x Bool with vertical edges at a fixed index and horizontal R edges
at a fixed Bool. This two-layer graph has no closed five-walk: the number
of vertical steps in a closed walk is even, so projecting a five-walk
would give an odd closed R walk of length 1, 3, or 5; each is excluded by
looplessness and NoFive R. Hence the known second-right cone cover pulls
back to the matching-bundle second right adjoint. The simple example with
all A_i--B_j edges and C_i--C_j edges from R has the same collapse.
This observation is NOT formalized in a new Lean file. It is not a theorem
about arbitrary matching bundles: three-cycle matchings or more general
partial-apex incidences need not have this two-layer collapse.

Other review considered high-chromatic triangle hypergraphs and graph
roots, finite-dimensional ordered-field representations, countable partial
coloring extensions, reduced-product saturation, and the second ordered
ultrafilter stage. None supplied the missing countable-color mechanism.
In particular:
* no general theorem about uncountably chromatic Berge-triangle-free linear
  hypergraphs was established;
* a universal finite-pattern coloring of all sparse second-right normal
  forms would contradict the already verified finite Folkman theorem;
* countable proper coloring of a first ultrafilter stage does not turn its
  carrier into a countable set or a countable K4-free target;
* local finite satisfiability and pure-graph saturation still do not control
  an arbitrary external countable edge coloring.

No final proof was submitted. There is no pending build of a main proof.

## Full OR after a mutual first extension is covered (NEW, verified)

OrAfterMutualCover.lean compiles with an olean; namespace
Erdos595OrAfterMutual. Log /tmp/or-after-mutual.log. Audited results use
only propext, Classical.choice, and Quot.sound.

* target_supported: for K = mutual-U(G), one Fubini direction P -> Q at
  the next stage already puts Q on the double lift of an original
  triangle-free set. The SOURCE need not be supported.
* no_three_same_support: choosing one original support for each supported
  point and the empty set for unsupported points yields support-code fibers
  with no forward Fubini triangle.
* countable_cover: if the ORIGINAL carrier is countable and G is K4-free,
  the FULL symmetric OR Fubini extension of mutual-U(G) is countably
  triangle-free edge-covered. Unsupported points form an independent set;
  supported fibers have two-piece covers, and original support sets admit
  continuum many codes. No completeness beyond ordinary ultrafilters is used.
* ordered_countable_cover: consequently every order-oriented extension of
  the MUTUAL first stage is also covered.

This is stronger than the earlier second-mutual covering result but does
NOT cover two order-oriented stages. Its crucial inclusion is
N_mutual-U(G)(p) subset {q | trace_G(p) belongs to q}, which uses the
reverse first-stage Fubini direction and is unavailable for an arbitrary
ordered first stage. Third mutual and second fully ordered towers remain
unresolved. This is an auxiliary exclusion, not Erdős 595. Spec is unchanged.

Further review after the mixed-tower theorem did not yield a main proof.
In particular, no homomorphism of an arbitrary ordered first extension into
a mutual first extension of a countable base was constructed. The latter
would be an additional, substantial assertion, not a consequence of proper
countable colorability. No assertion about a known K5-free or larger-clique
countable-palette witness was verified; a direct-IP attempt to retrieve the
problem reference also timed out. No such alleged result is used.

## Unrestricted third right profiles can be non-coverable (NEW, verified)

ThirdRightProfileObstruction.lean compiles with an olean; namespace
Erdos595ThirdRightProfile. Log /tmp/third-right-profile.log. All audited
results use only propext, Classical.choice, and Quot.sound.

* inflation: an injection I x Bool into A gives a complete-graph homomorphism
  K_(Set I) -> right(K_A), using complementary selector bicliques. Distinct
  subsets supply witnesses in BOTH crossing intersections.
* base = arcGraph(K_Nat) is countable, K4-free, and has a two-piece TF edge cover.
* largeClique: K_(Set (Set Nat)) -> right^3(base), via two inflations and
  two applications of right functoriality to the adjunction unit.
* no_countable_cover: right^3(base) has no countable TF edge cover. Pullback
  would give an injection Set(Set Nat) -> binary sequences -> Set Nat,
  contradicting Cantor.
* not_cliqueFree_four: explicitly verifies that this target contains K4.

This is NOT a witness for Erdos 595. It shows that a countable K4-free,
even finitely edge-covered BASE does not make an unrestricted third profile
TARGET covered. The existing third-right cover theorem requires the FULL
third target to be K4-free. A map from an exponential into an unrestricted
third right target cannot by itself give a covering theorem. No theorem
about the third-shift exponential image itself is obtained.

Other investigations in this continuation (ordered-field orthogonality,
stable graph decompositions, graphical hypergraph roots, and two ordered
ultrafilter stages) did not produce a settlement or new formal sufficient
criterion. In particular, no general stable-graph covering theorem or
unsupported-second-stage triangle exclusion was proved. The original
Spec.lean remains unchanged with its sorry; no main proof was submitted.

## All matching bundles over TF index graphs are excluded (NEW, verified)

MatchingBundleRightCover.lean compiles with an olean; namespace
Erdos595MatchingBundle. Log /tmp/matching-bundle.log. All printed audits
use only propext, Classical.choice, and Quot.sound.

General hypotheses (`Assumptions H B π κ`):
* π : V -> I is the fiber map and κ : V -> Fin 3 distinguishes vertices
  within each fiber (the pair (π,κ) is injective).
* Every cross-fiber H edge projects to an edge of B.
* An outside vertex has at most one neighbor in each other fiber.
* B is TRIANGLE-FREE. The number/cardinality of fibers is unrestricted.

Verified structural results:
* triangle_fiber: all base triangles are confined to fibers.
* common_unique: distinct vertices in one fiber have at most one common
  neighbor in the whole graph.
* side_injective: a biclique with neither side a singleton has at most one
  vertex per fiber on either side.
* different_fibers: in a triangle of right H, a non-star biclique forces
  the two directed witness cycles into distinct base fibers.
* prism_sides: over two such fibers, the non-star biclique is a rigid
  four-cycle with exactly two vertices on each side. The TF INDEX hypothesis
  is essential here: an extra support fiber would create an index triangle.
* right_rainbow: a finite vertex label makes every triangle of right H
  rainbow. Star bicliques use the coordinate of their singleton center;
  non-stars use the coordinate set on their smaller support fiber. The
  palette is Fin 3 + Set(Fin 3).
* second_right_cover: the FULL right(right H) is countably TF edge-covered,
  without any K4 hypothesis on the full target.
* base_cliqueFree_four: the stated hypotheses imply H itself is K4-free.

Concrete `bundle B σ` puts a triangle at each index and an arbitrary perfect
matching on each index edge, specified by σ i j : Fin 3 ≃ Fin 3 in a chosen
linear order. `matching_bundle_second_right_cover` excludes ALL such
permutation choices whenever B is TF. This includes identity matchings,
three-cycle matchings, arbitrary mixtures of the three transpositions, and
edge-dependent choices. It strictly supersedes the earlier INFORMAL
exclusion of only two matching types over a no-five-walk index graph.
The general theorem also allows partial matchings and incomplete fibers.

SCOPE: this does NOT handle arbitrary triangle-fiber incidence quotients.
In particular, the quotient by triangle fibers of arc^2(G) can contain many
triangles even when G is K4-free (shared-edge books already cause this).
Thus the theorem cannot be applied to the exact second-arc normal form in
general. Nor does it prove the full second target K4-free. No general
partial-apex-family exclusion or main proof follows.

Other reasoning in this continuation revisited finite edge bounds, graphical
closure, external-color saturation, and longer universal apex iterations.
No coherent finite bound assignment or countable-palette Ramsey mechanism
was established. No new saturated-graph construction was formalized.
Spec.lean is unchanged with its original sorry; Erdős 595 remains unresolved.

## Full matching bundles with arbitrary index graphs are excluded (NEW, verified)

FullMatchingBundleRightCover.lean compiles with an olean; namespace
Erdos595FullMatchingBundle. Log /tmp/full-matching.log. Audited results
use only propext, Classical.choice, and Quot.sound.

This strengthens the previous matching-bundle result by removing the TF
INDEX assumption for FULL perfect matchings, provided all BASE triangles
stay inside the designated fibers.

Abstract criterion:
* Core H π κ assumes injectivity of (π,κ), κ : V -> Fin 3, outside-to-fiber
  matching, and confinement of every H triangle to one fiber. There is NO
  index graph and no TF-index assumption in Core.
* Internal H π p i: both biclique sides meet fiber i.
* TwoInternal H π: every biclique has at most two internal fibers.
* trim deletes side vertices whose fiber does not meet the opposite side.
* trim_six: all six witnesses of any right-adjoint triangle survive trimming.
* trim_support: TwoInternal forces the trimmed supports in a right triangle
  onto the two witness fibers. When the two coincide, the earlier
  common-neighbor uniqueness argument forces singleton-sided bicliques.
* trim_rainbow: applying the old finite code AFTER trimming makes every
  triangle of right H rainbow. Its proof reduces locally to a two-fiber
  graph, where the previous TF-index theorem applies.
* second_right_cover: Core + TwoInternal imply coverability of FULL right^2 H.

Concrete full-matching application:
* thirds_adj: in a permutation matching between three-point fibers, two
  matched pairs force the third. This uses FULL matchings essentially.
* full_twoInternal: three internal fibers in one biclique force a triangle
  on the three remaining fiber vertices, contradicting triangle confinement.
* full_matching_second_right_cover: for arbitrary B and permutations σ,
  right^2(bundle B σ) is covered if every base triangle lies in one fiber.
  B can have triangles and arbitrary cardinality.

Scope warning: this is NOT a covering theorem for arbitrary sparse
second-arc normal forms. Their cross-fiber matchings can be PARTIAL;
missing third matched pairs cannot be supplied without changing the graph
and potentially destroying triangle confinement. In a partial bundle one
can have A_i--B_j edges between every pair of fibers, C_i adjacent only to
its own A_i,B_i, and a biclique with every fiber internal. That simple
example is itself three-colorable; it illustrates failure of TwoInternal,
not a witness. No matching-completion theorem preserving the required
second-right properties has been proved.

Spec.lean remains unchanged with its original sorry. No main proof or
negation has been obtained or submitted.

## Private-triangle completion preserves the second-right K4 bound (new, verified)

`Submission/PrivateTriangleCertificate.lean` compiles with an olean. Namespace
Erdos595PrivateTriangleCertificate; clean log `/tmp/private-triangle-certificate.log`.
Both axiom audits use only propext, Classical.choice, and Quot.sound.

This is a finite homomorphism obstruction for A2 = arc^2(K4), on 60 vertices.
The symmetric five-state relation Allowed has rows:

    0 -> 1,2,3; 1 -> 0,2; 2 -> 0,1; 3 -> 0,4; 4 -> 3,4.

State 4 deliberately has a loop: this is a relation, not a simple graph.
States 1 and 2 represent the new private triangle vertices; 0 their old
center; 3 its other neighbors, which must be independent; 4 everything else.
`no_private` and `no_private_arc` prove that EVERY edge-preserving map from
A2 into this template avoids states 1 and 2 at EVERY source vertex.

The exact CNF has 3,361 initial clauses. A CaDiCaL LRAT search produced
282 addition steps; dependency pruning retained 99 steps and 770 initial
clauses. The generated Lean file reconstructs the certificate with ordinary
propositional proofs and kernel-checked finite facts. No native/SAT/compiler
axiom is used. The 60-point enumeration's surjectivity is kernel-checked too.
Generator: `/tmp/gen_private_triangle_certificate.py`; artifacts use
`/tmp/private_status_None.*`. The generated file is about 674 KB and requires
roughly 8 GB RAM to build. Do not run another heavy Lean build concurrently.

The first build failed solely because `by_contra` had already removed some
double negations, so the following `simp` reported no progress. The generator
now uses `try simp only` at that point. The corrected complete build is clean.

`Submission/PrivateTriangleCompletion.lean` also compiles with an olean;
namespace Erdos595PrivateTriangleCompletion; log
`/tmp/private-triangle-completion.log`. All checked audits are permitted.

* Bare H v means that the old neighborhood of v is independent.
* graph H retains H, and adds TWO private vertices at every Bare vertex,
  completing a private triangle there and adding no other new edges.
* state_adj: for each such center the graph maps into the five-state relation.
* no_new_image: a map arc^2(K4) -> graph H cannot enter any new vertex.
* factor: any such map factors through the old H.
* second_right_cliqueFree_iff:
      right^2(graph H) is K4-free iff right^2 H is K4-free.
* every_vertex_triangle: every vertex of graph H lies in a triangle.
* vertex_disjoint: vertex-disjointness of old triangles is preserved.
* independent_transversal: an independent triangle transversal is preserved.
  Retain its old vertices; at every new triangle whose center is not selected,
  select just the private false vertex. Old non-bare triangles and private
  triangles cannot mix.
* PartitionedTriangleBase G is SparseTriangleBase G together with the fact
  that every vertex belongs to a triangle.
* partitioned: private completion of a SparseTriangleBase has this property.
* witness_partitioned_normal_form: a K4-free non-covered graph exists iff
  a full K4-free non-covered right^2 G exists for a PartitionedTriangleBase G.
  Forwards, complete arc^2 of the original graph. Non-coverability pulls back
  along the original unit and right^2 of the old inclusion.

This is a sharper EXACT NORMAL FORM, NOT a settlement. Between the triangle
fibers there can still be PARTIAL matchings. The full-matching covering
result does not apply: filling missing pairs can create new triangles.
No general matching-completion, universal covering, or witness-existence
lemma was obtained.

Earlier finite exploration of completion of arc^2(K2), arc^2(C4), arc^2(C5),
and arc^2(diamond) returned UNSAT for arc^2(K4) homomorphisms. The analogous
Grotzsch-graph case TIMED OUT after 90 seconds; it was not an UNSAT result.
The now-verified five-state certificate establishes the general preservation
statement independently of those tests.

The additional `universal_cover_partitioned_iff` theorem is now also verified:
universal countable TF covering of K4-free graphs is equivalent to the same
claim for FULL second-right targets of PartitionedTriangleBase graphs. Its
axiom audit is permitted. The final completion-file build has no warnings.

No main proof or disproof has been obtained. Spec.lean is unchanged (SHA256
`de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45`), and its
latest direct build `/tmp/spec-private-completion-review.log` reports only
the original sorry warning. No completed proof has been submitted.

## Private completion also preserves second-right COVERABILITY (NEW, verified)

`Submission/PrivateTriangleRightReflection.lean` compiles cleanly with an
olean, namespace Erdos595PrivateTriangleRightReflection; log
`/tmp/private-triangle-right-reflection.log`. Every printed axiom audit uses
only propext, Classical.choice, and Quot.sound.

This proves a fact left open in the previous continuation:

    right^2(privateCompletion H) is countably TF edge-covered
      iff right^2 H is countably TF edge-covered.

There is NO K4 hypothesis for this equivalence. Private completion therefore
cannot amplify a covered base into a non-covered second-right target.

Structural proof:
* Both p means both biclique sides are nonempty; otherwise p is isolated.
* HasPrivate p u means a private vertex at center u occurs on either side.
* all_local: such a nonempty p is entirely contained in the induced graph
  on u, its old neighbors, and its two private vertices. This local graph
  is properly THREE-colorable because u was Bare (old neighborhood independent).
* private_unique: the private center of a nonempty biclique is unique.
* triangle_near_private and private_propagates: in a triangle of the FIRST
  right graph, if one biclique has a private vertex at u, all three do.
* kind labels nonempty private-containing bicliques by some u; all others
  by none. `kind_triangle` confines every first-right triangle to one kind.
* oldFiberHom maps the none fiber into right H by restricting to old vertices.
* newFiberHom maps the some u fiber into right K3 by local restriction and
  the local three-coloring.
* newSecondHom maps the RIGHT of each new fiber into K3 itself.
* second_cover uses the previously verified RightFiber.cover_of_fibers.
* second_cover_iff adds the pullback along right^2 of the old inclusion.
* second_cliqueFree and second_cliqueFree_iff give an alternative STRUCTURAL
  proof of the second-right K4 preservation, using the clique fiber theorem.
  These proofs do NOT use the large five-state SAT certificate.

New helper `Submission/RightThreeColor.lean`, namespace Erdos595RightThree,
proves `hom : right K3 -> K3`. For a nonempty biclique with singleton left
side {i}, color i; otherwise its right singleton {j} gets color j+1 mod 3.
Empty-side cases are harmless. The finite relation is kernel-checked on four
Finsets of Fin 3, then transferred to actual Set-based bicliques. Ordinary
Set(Fin 3) Fintype instances are noncomputable and must not be used directly
for the decide certificate. Log `/tmp/right-three-color.log`, audit permitted.

To keep the new structural proof genuinely independent of certificate imports,
the definitions Bare, Center, Vertex, graph, oldEmbedding were moved from
PrivateTriangleCompletion.lean to `Submission/PrivateTriangleBase.lean` in
the SAME namespace. Completion now imports Base. Reflection imports Base,
RightFiberCover, MatchingBundleRightCover, and RightThreeColor, NOT Completion
or PrivateTriangleCertificate. Base, Reflection, and Completion were rebuilt
successfully after this refactor. No conjecture-file import was changed.

Further exploration did NOT establish a finite/countable-internal-support
cover theorem for general partial matching bases. In particular, having
finite biclique parameters does not grant RelativeInvariant to next-stage
adjacency; restricted-family quantification still depends on the original
arbitrary graph. Likewise, no countably proper triangle transversal, no
well-order with countably chromatic earlier neighborhoods, and no covering
of two fully ordered ultrafilter stages was proved.

## Third-right SINGLE-cone review (exploratory only, no theorem)

The verified single-cone theorem concerns the SECOND right adjoint. No
covering theorem for all higher single-cone iterations was established.
For each fixed iteration k, taking a triangle-free base of sufficiently
large odd girth excludes maps arc^k(K4) -> cone G: otherwise delete the
independent preimage of the apex; the remaining finite graph is not
bipartite, since arc^k(K4) is not three-colorable (right K3 -> K3).
This is informal reasoning here, NOT a Lean theorem or non-coverability.

Exact exploratory homomorphism tests in `/tmp/third_cone_cycles.py`:
* arc^3(K4) has 540 vertices and 4,590 edges.
* arc^3(K4) -> cone(C7): timed out after 45 seconds; status UNKNOWN.
* arc^3(K4) -> cone(C9): UNSAT from CaDiCaL, NOT kernel-certified.
* arc^3(K4) -> cone(C11): UNSAT from CaDiCaL, NOT kernel-certified.
Log `/tmp/third-cone-cycles.log`; CNFs `/tmp/arc3K4_coneC*.cnf`.
No running solver remains. Do not infer the C7 result from the larger cycles.

Separate tiny exact UNSAT tests (not Lean-certified) ruled out proposed
simple wheel recurrences arc(W3)->W5, arc(W5)->W7, arc(W5)->W9,
arc(W7)->W9, and arc(W7)->W11, with Wm = cone(Cm). These therefore do not
supply a recursive extension of the existing second-cone wheel certificate.
No general higher-cone clique criterion or covering/non-covering theorem
was obtained. No claim that higher cones yield a witness is justified.

No proof or disproof of erdos_595 has been obtained in this continuation.
Spec.lean remains unchanged with its original sorry, and no proof has been
submitted. Latest direct main-file build:
`/tmp/spec-private-right-reflection-review.log` (original sorry warning).

## Third-cone boundary: NoFive does not suffice at stage three (NEW, verified)

`Submission/OddGraphSeven.lean` compiles with an olean. Namespace
Erdos595OddGraphSeven; log `/tmp/odd-graph-seven.log`; audit permitted.
It enumerates the 35 triples of Fin 7, with disjointness adjacency (KG(7,3)).
`noFive` proves absence of any closed five-step walk, including repetitions.
The incidence count is 15, but each of seven coordinates occurs at most twice,
so it is at most 14. The five-cycle Boolean bound is kernel-checked.

`Submission/ThirdConeObstruction.lean` also compiles with an olean. Namespace
Erdos595ThirdConeObstruction; log `/tmp/third-cone-obstruction.log`;
all printed audits contain only permitted axioms.
* `second_cliqueFree`: right^2(cone KG(7,3)) is K4-free.
* `third_not_cliqueFree`: right^3(cone KG(7,3)) contains K4.
* `second_covered`, `third_covered`: both are countably TF edge-covered.
  The third carrier is finite. This example is NOT an Erdős 595 witness.

Certificate: a map arc^3(K4) -> cone KG(7,3), found exactly by SAT, was
compressed to a map arc^2(K4) -> right(cone KG(7,3)). Each of 60 second-arc
vertices has a nine-entry incoming row and a nine-entry outgoing row.
Kernel-checked `rows_adj` verifies each row pair is a biclique; `rows_meet`
verifies the mutual intersections for source edges. Currying twice gives
`cliqueHom`. The 256-entry raw tables use the four original Fin 4 coordinates;
invalid codes are harmless defaults. No native or SAT axiom is used.
Generator `/tmp/gen_third_cone_obstruction.py`.
Build memory peaked near 10 GB; avoid simultaneous heavy Lean builds.

Exact exploratory artifacts, distinct from Lean certificates:
* `/tmp/arc3_independent_odd_transversal.py` found an independent 184-vertex
  set in arc^3(K4) meeting all triangles and five-cycles. The 356-vertex
  complement has 1,462 edges and no closed five-walk, but has a seven-cycle.
  Data `/tmp/arc3_independent_No5.json`.
* `/tmp/fold_no5_graph.py` folded that complement to 37 vertices/98 edges,
  preserving no-five-walks; SAT found it 3-colorable. This folded artifact
  was NOT formalized and is not needed for the final certificate.
* `/tmp/arc3_cone_oddgraph.py` found the cleaner Kneser target map, using
  217 apex labels, NOT the earlier 184-element apex set. Data:
  `/tmp/arc3_cone_oddgraph.json`, CNF/output with same stem. Each non-apex
  label has exactly three of seven bits and adjacent supports are disjoint.
  This map, after row compression, is now independently Lean-verified.

Scope: the exact NoFive criterion for SECOND single cones remains valid.
It cannot be reused as a sufficient K4 bound at the THIRD stage. No general
higher-cone K4 criterion, universal covering theorem, or non-covered K4-free
example was obtained. Spec.lean remains unchanged with its original sorry.

## Finite odd-walk bound for EVERY fixed higher-cone stage (NEW, verified)

`Submission/HigherConeOddBound.lean` compiles with an olean. Namespace
Erdos595HigherConeOddBound; log `/tmp/higher-cone-odd-bound.log`. Both printed
axiom audits are precisely the permitted three axioms.

* `NoShortOdd G n`: G has no odd closed walk of length STRICTLY LESS THAN n.
* `two_of_no_short_odd`: a finite graph on N vertices with no odd closed
  walk shorter than 2*N is two-colorable. Choose simple root paths in each
  component, of length < N. Their parity colors endpoints differently,
  since an edge joining equal parities closes an odd walk of length < 2*N.
* `three_of_cone_hom`: if F is finite on N vertices and G has NoShortOdd
  (2*N), any hom F -> cone G makes F three-colorable. The preimage of the
  apex is independent; its complement maps into G and is two-colorable by
  the preceding bound. No target-cardinality restriction is used.
* `three_of_arc_three`: three-colorability of arc H implies that of H,
  using currying and the verified right K3 -> K3 map.
* `Packed`, `arcP`, `rightP`: universe-polymorphic bundled graph iteration.
  `iter_hom_iff` establishes the iterated arc/right adjunction.
  `iter_finite`, `iter_three` establish finiteness and three-color reflection.
* `four` is K4 on ULift (Fin 4), so it lives in the base's universe.
* `bound.{u} n = 2 * Nat.card ((arcP^[n]) four).1` is finite.
* `cliqueFree`: if NoShortOdd G (bound n), then the FULL n-th right adjoint
  of cone G is K4-free. A K4 would uncurry to arc^n K4 -> cone G, contradicting
  `three_of_cone_hom` and the fact that arc^n K4 is not three-colorable.

This formalizes and gives an explicit (non-optimal) version of the earlier
informal higher-cone observation. The bound depends only on n, not the size
of G. It is only a K4 exclusion theorem: no non-coverability claim follows.
In particular no fixed-stage higher-cone witness for Erdos 595 has been
constructed, nor has universal higher-cone countable covering been proved.

Proof-development details: use `change` to expose the underlying subtype
inclusion before rewriting a hom evaluated on induced vertices. Use
`Fintype.card_le_of_injective` rather than forcing a different decidable
subtype enumeration. `bound` needs the explicit universe `four.{u}` in its
body and `bound.{u}` in the main hypothesis; no universe metavariable remains.

Further review of graph-edge roots, partial matching completion, prescribed
color extension, higher ordered ultrafilters, and ordered-field geometry did
not supply a new global countable-palette mechanism. None is asserted here.
Spec.lean remains unchanged with its original sorry; no settlement submitted.

## Split-triangle partial bundles cannot amplify vertex chromatic number (NEW, verified)

`Submission/SplitTriangleRightCover.lean` compiles cleanly with an olean.
Namespace Erdos595SplitTriangleRight; log `/tmp/split-triangle-right.log`.
Both audits (`five_cover`, `countable_cover`) use only the three allowed axioms.

Given an ARBITRARY relation D on I and an arbitrary triangle-free graph R on I,
`graph D R` has vertices A_i=(i,0), B_i=(i,1), C_i=(i,2), with:
* A_i--B_j exactly when i=j or D(i,j); D need not be symmetric.
* A_i--C_j and B_i--C_j exactly when i=j.
* C_i--C_j exactly when R(i,j).
* no A--A or B--B edges.
Thus every fiber is a triangle, and the only triangles are these fibers.
Cross-fiber matchings can be partial; in particular taking D constantly True
produces arbitrarily large bicliques with all fibers internal. The previous
TwoInternal hypothesis does NOT apply to that example.

Verified theorem: the SECOND full right adjoint has a FIVE-piece triangle-free
edge cover, without any K4 hypothesis on either right stage and with no size
or proper vertex-chromatic restriction on R. In particular, this family cannot
turn arbitrarily high chromatic triangle-free R into an Erdos 595 witness.

Proof:
* Good p (s,t) means a specified nonempty side of biclique p lies entirely in
  A (t=false) or B (t=true). There are four such states.
* `good_independent`: vertices with the same state are independent in right H.
* `selectedColor`: the union Selected of these states is properly four-colored.
* A biclique containing A_i on its left and B_i on its right has left side
  contained in A union {C_i} and right side contained in B union {C_i}.
  The point C_i cannot lie on both sides, so one side is pure A or pure B.
  `selected_of_AB`, `selected_of_BA` formalize this.
* `triangle_AB`: every base triangle contains a same-fiber A_i B_i pair.
* Three cyclic intersection witnesses in any right-H triangle form a base
  triangle. The corresponding biclique therefore lies in Selected.
  `selected_transversal` proves its complement triangle-free.
* Apply the finite proper-transversal theorem with four colors, obtaining
  five edge pieces in right^2 H.

Exact exploratory tests, NOT K4-freeness theorems:
`/tmp/partial_complete_bundle.py` tests D=True and R=C5,C7,C9.
`/tmp/partial-complete-bundle.log` records CaDiCaL UNSAT for arc^2 K4 -> H
in all three cases, in about 0.01--0.02 seconds each. CNF/output files are
`/tmp/partial_bundle_C{5,7,9}.{cnf,out}`. The safe normalization sends one
source triangle into fiber 0; these cycle targets are vertex-transitive.
No general K4 bound was inferred from these finite tests, and no such
certificate is needed for the uniform covering theorem above.

This result is still ONLY an exclusion of a candidate family. General partial
matching bases can have cross A--C and B--C edges, so their neighborhood shape
need not satisfy this proof. No such reduction for arbitrary sparse normal
forms has been proved. No proof or negation of erdos_595 has been obtained.

Further review of high-chromatic-base transfer, arbitrary-index finite-factor
products, Ramsey lifts, elementary-model decompositions, and group/complex
representations did not yield a valid global countable-palette argument.
In particular no claim that large vertex chromatic number alone forces large
triangle-edge chromatic number at a right-cone stage has been established.
Spec.lean remains unchanged, with its original sorry; no proof submitted.

## Size-two support already gives an EXACT reduced-power normal form (NEW, verified)

`Submission/FixedPowerSupportObstruction.lean` compiles with an olean.
Namespace Erdos595FixedPowerSupport; log `/tmp/fixed-power-support.log`.
All six printed audits contain only propext, Classical.choice, Quot.sound.

The investigation asked whether finite supports in the fixed finite-factor
power could supply the edge-dependent finite bounds required by compactness.
The simplest size-only proposal fails decisively:

* `coordinate_iff`: for the existing canonical point embedding of ANY K4-free
  G on V, adjacency of point(v),point(w) at coordinate S is EXACTLY
       v in S AND w in S AND G.Adj v w.
* `Supports x y T` means all coordinates S containing T are adjacent.
* `point_support_iff`: the supports of an embedded edge vw are exactly the
  finite sets containing both v and w. No support exists for a nonedge.
* `least_support`, `least_support_card`: each actual embedded edge has least
  support {v,w}, of cardinal TWO, independently of the complexity of G.
* `twoSupported V` retains only product edges with a support of size <=2.
* `twoSupported_le` and `twoSupported_cliqueFree`: this is a K4-free subgraph
  of the original fixed power.
* `twoEmbedding`: nevertheless it contains EVERY K4-free graph on V inducedly.
* `twoSupported_no_finite`: for every infinite V it has no finite TF edge cover;
  the finite Folkman obstructions embed with size-two supports.
* `twoSupported_countable`: when V is countable it IS countably TF covered.
* `conjecture_iff_twoSupported`: existence of a non-covered member of this
  bounded-support family is EXACTLY equivalent to the original conjecture.
  In particular the family is NOT an excluded candidate for uncountable V.
* `no_constant_bound`: every constant natural-number edge bound fails the
  Bounded criterion for twoSupported V when V is infinite.

Thus bounded support size, or a palette bound depending only on that size,
does not close the finite-edge-bounds compactness argument. A genuinely
edge-dependent bound using further information remains unconstructed. This
result does NOT rule out all possible support-based choices of such bounds.

Additional informal review of countable-palette Ramsey forcing, colored
saturation, graph-root patterns, and iterated ultrafilter extensions did not
produce a main proof. In particular ordinary saturation does not saturate an
arbitrary countably colored expansion, and no large-cardinal compactness or
universe-based reflection assertion was assumed. No finite-palette obstruction
was promoted to an obstruction for a countable palette.

Spec.lean remains unchanged with the original sorry. No proof or disproof has
been obtained or submitted. Latest direct main-file review is logged in
`/tmp/spec-fixed-support-review.log`.

## Direct finite-bound review (no settlement or new Lean theorem)

This pass focused on the missing stronger assertion: a SINGLE K4-free graph
must defeat EVERY edge-dependent natural-number bound on some finite induced
subgraph. The verified finite Folkman and size-two-support theorems only defeat
constant bounds and do not establish this assertion.

Reviewed high-vertex-chromatic candidate transfer, countable tuple families,
local triangle orientations, prescribed palette escape, group-presentation
representations, and finite-dimensional ordered-field geometry. No valid
non-coverability theorem or universal finite-bound construction emerged.

Specific scope retained:
* Large vertex chromatic number is not itself a lower bound on triangle-edge
  chromatic number; triangle-free pieces may already carry large vertex χ.
* The full countable-tuple invariance theorem does NOT cover arbitrary
  restricted countable-tuple families with only RelativeInvariant. It DOES
  require no finite-prefix locality in its full-space versions. Finite-prefix
  locality is a separate sufficient condition for restricted families.
* No theorem about all stable/NIP graphs, or about all finite-dimensional
  semialgebraic K4-free graphs, was established. Such observations in this
  discussion were exploratory, not dependencies.
* Infinite colored saturation cannot be inferred from uncolored saturation.
  No compactness for arbitrary natural-number edge bounds was supplied beyond
  the already verified fixed-bound criterion.
* No group representation or ordered-field representation of arbitrary K4-free
  graphs was constructed, and no non-coverability of a geometric family was
  proved.

There is no pending Lean build or SAT search from this review. No additional
axiom, sorry replacement, or disproof was added to Spec.lean. The original
conjecture remains unresolved and no completed proof has been submitted.
Latest direct main-file log: `/tmp/spec-direct-bound-review.log`.

## Further coherent-bound and triangle-propagation review (no settlement)

This pass revisited the fixed-bound criterion, local triangle orientations,
finite-support rank bounds, countable-target exponentials, and triangle-touch
propagation. No coherent bound for arbitrary K4-free graphs and no graph
defeating every bound was obtained. No new Lean theorem is claimed here.

A simple informal guardrail for propagation: given any K4-free G, add for
EACH original edge uv a private degree-two vertex p_uv adjacent to u and v.
The resulting graph is still K4-free. Its spoke graph is bipartite, and one
round of completing triangles with two spoke edges already adds every
original G-edge. Thus preservation of countable coverability under this
operation cannot be assumed as an easier local lemma. The previously verified
TriangleClosureNormalization gives a stronger normalization when the old
bipartite graph is additionally required to be triangle-closed.

Also retained: finite branching in a well-founded least-common-neighbor
recursion does not by itself supply useful global edge bounds. Private ears
placed before all original vertices can make every original edge have the
same shallow local witness shape while retaining an arbitrary original
K4-free induced graph. This observation does not rule out all choices of
orders or all edge-dependent bounds.

The original Spec.lean remains unchanged with its sorry. No completed proof
or disproof has been submitted, and no Lean build or search is pending.

## Three-colorable blue forcing targets are impossible (NEW, verified)

`Submission/MiddleEqualityThreeColor.lean` compiles with an olean.
Namespace `Erdos595MiddleEqualityThreeColor`; log
`/tmp/middle-equality-three-color.log`. All three printed axiom audits use
only propext, Classical.choice, and Quot.sound.

For ANY linearly ordered graph G with a proper Fin 3 vertex coloring d,
orient those three colors cyclically. Give an unordered edge ab the Boolean
bit that says whether its endpoints, read in the vertex order, follow the
three-cycle. In EVERY ordered triangle a<b<c:
* colors of ab and bc agree;
* the color of ac is different.

Verified declarations:
* `ordered_pattern`, `middle_equal`;
* `valid`: no monochromatic edge triangle, without an order assumption on
  the triple supplied to the theorem;
* `ForcesMono`: equality of consecutive edges of every ordered triangle
  forces a monochromatic triangle for NATURAL-NUMBER edge colors. The palette
  here is that of the ORIGINAL edge coloring, not the Boolean triangle test;
* `not_forces_of_three_colorable`, `not_three_colorable_of_forces`.

The Boolean coloring is encoded injectively into N in the final theorem.
Thus no properly three-colorable graph, including any complete tripartite
blow-up of a triangle, can replace the finite blue forcing target in the
asymmetric triangle-arrow strategy, regardless of vertex order. The odd
wheel's need for more than three proper vertex colors cannot be removed by
choosing an ingenious order on a three-colorable replacement.

Exploration preceding the proof checked the 90 order patterns of K_{2,2,2}
by a finite union-find calculation and found no forcing pattern. The Lean
result above is general and does not depend on that calculation.

This is ONLY a restriction on that sufficient Ramsey strategy. It gives
neither a K4-free host with the required infinite red target nor a universal
countable edge-cover theorem. A direct-IP external reference lookup also
failed to connect. Spec.lean remains unchanged with its original sorry.
No completed proof/disproof has been submitted; no job is pending.

## Four-cycle common-neighborhood criterion (NEW, verified)

`Submission/RankEdgeCover.lean` and `Submission/FourCycleCommonCover.lean`
compile with oleans. Final logs: `/tmp/RankEdgeCover-audit.log` and
`/tmp/FourCycleCommonCover-audit.log`. All printed axiom audits use only
propext, Classical.choice, and Quot.sound.

Namespace `Erdos595RankEdgeCover`:
* `cover_of_rank`: for any linearly ordered rank set, if every equal-rank
  induced graph is countably TF-edge-covered and every STRICT lower-rank
  neighborhood is properly countably vertex-colored, the whole graph is
  countably TF-edge-covered. There is NO countability assumption on ranks.
  Equal-rank and cross-rank edges use separate summands of a countable
  palette. Three distinct ranks are handled by the two spokes at the top.

Namespace `Erdos595FourCycleCommon`:
* `Cycle4 a b c d` requires the four cyclic adjacencies and opposite-pair
  inequalities; hence all four vertices are distinct. Chords are allowed.
* `common4` is the common neighborhood of all four vertices.
* `CountableFourCommon` says each actual Cycle4 has countable common4.
* `countable_cover`: CountableFourCommon implies a countable TF edge cover,
  with NO K4-freeness hypothesis.
  Proof: countably many four-ary operations enumerate common4 sets. Their
  first-order closure has finite character and cardinal <= max(aleph0,#S).
  Ranks are least closed initial segments. Each strict lower neighborhood
  has at most one common neighbor for distinct pairs: otherwise a four-cycle
  in it would put the current vertex in the predecessor closure. The existing
  countable-codegree proper-coloring theorem handles those neighborhoods.
  Cardinal induction covers each equal-rank fiber, and cover_of_rank assembles.
* `uncountable_common4_of_no_cover`: every non-coverable graph has an actual
  four-cycle with uncountably many common neighbors.
* `octahedron_of_two_common`: in a K4-free graph, two distinct common neighbors
  of a four-cycle produce an INDUCED embedding of completeEquipartiteGraph 3 2.
  K4-freeness forbids both cycle diagonals and the common-neighbor pair edge.
* `octahedron_of_no_cover`: every putative witness contains an induced octahedron.
* `cover_of_no_octahedron`: all K4-free induced-octahedron-free graphs are covered.

These are structural restrictions, NOT a settlement. In particular, a finite
properly three-colorable octahedron is itself covered and does not satisfy the
blue forcing condition from MiddleEqualityThreeColor.

## Signature (3,2) geometric candidate excluded (NEW, verified)

`Submission/IndefiniteFiveCover.lean` compiles with an olean and no warnings
in its final build. Namespace `Erdos595IndefiniteFive`; final log
`/tmp/IndefiniteFiveCover-audit.log`. All printed audits use only permitted axioms.

This NEW theorem goes beyond the earlier TOTAL-dimension-at-most-four result.
For every ordered field K, with no cardinality or Archimedean restriction:
* `complement_anisotropic`: the orthogonal complement of a complete positive
  unit frame x : Fin m -> UnitPoint K m n has no nonzero isotropic vector.
  Positive projections of x form a basis. Express a null orthogonal vector's
  positive projection in that basis and use sums of squares to show it is zero.
* `multipartite_bound`: if x_i,y_i are two NON-COLLINEAR unit vectors in each
  of m mutually orthogonal parts in signature (m,n), then m <= n.
  Set r_i = y_i - B(x_i,y_i) x_i. These residuals are nonzero, lie in the
  orthogonal complement, have nonzero norms, and are pairwise orthogonal.
  The combined frame x_i,r_i is linearly independent, so 2m <= m+n.
* `countable_cover K n hn`: for n<3, the FULL signature (3,n) unit orthogonality
  graph has a countable TF edge cover. In particular this now excludes (3,2).

IMPORTANT: the raw unit graph always has antipodal twins, so it need not be
induced-octahedron-free. The proof chooses min(x,-x) in an arbitrary vertex
order. These canonical representatives form an induced subgraph; the whole
unit graph maps homomorphically into it. Distinct canonical unit points cannot
be collinear (a scalar preserving unit norm must be +1 or -1). An octahedron
among canonical points would contradict multipartite_bound for m=3,n<3.
Apply FourCycleCommon.cover_of_no_octahedron and pull back its cover.

Do NOT extrapolate this to signature (3,n) for n>=3. The argument stops there.
Indeed over an ordered field the six vectors (e_i,0) and ((5/3)e_i,(4/3)e_i),
i=0,1,2, give a direct algebraic octahedron in signature (3,3), with no two
vertices collinear. This last example is explanatory algebra, not a separate
Lean theorem and not evidence for non-coverability.

The original main file is STILL unchanged, with its original sorry. Latest
main-file check `/tmp/spec-four-cycle-review.log` reports only that warning.
SHA256: de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45.
No completed main proof/disproof has been submitted; no build is pending.

## Exact-one triangle transversals and no-full-pair bundles (NEW, verified)

`Submission/ExactTransversalRightCover.lean` compiles with an olean and no
warnings. Namespace `Erdos595ExactTransversalRight`; log
`/tmp/exact-transversal-right-cover.log`. Printed axiom audits use only
propext, Classical.choice, and Quot.sound.

* `ExactTransversal G m`: a Boolean vertex marking has exactly one marked
  vertex in every G-triangle (the three Bool.toNat values sum to one).
* `two_cover`: such a marking gives CoversWith (right G) 2.
  IMPORTANT: the marked set need NOT be independent. A right-edge is colored
  by the OR of the marks of its two chosen opposite intersection witnesses.
  Around a right-triangle the six witnesses form TWO G-triangles, hence have
  exactly two marked occurrences. All three edge-ORs cannot be zero (no marks)
  or one (at least three marks). The six-bit assertion is checked by
  decide +kernel.
* `two_cover_of_rainbow`: a Fin 3 vertex labeling that is rainbow on every
  triangle gives this TWO-piece bound, by marking label zero. This improves
  the finite bound implicit in the general countable-rainbow theorem for
  the specific three-label case. It does not apply to a merely weak
  non-monochromatic three-label vertex coloring.

`Submission/NoFullMatchingSecondRightCover.lean` also compiles with an olean
and no warnings. Namespace `Erdos595NoFullMatching`; log
`/tmp/no-full-matching-second-right-cover.log`. All audits use permitted axioms.

Hypotheses are FullMatchingBundle.Core H pi kappa:
* at most three vertices per fiber, distinguished by kappa : V -> Fin 3;
* cross-fiber edges form partial matchings;
* all base triangles remain in their fibers.
No independent transversal, index clique bound, or right-target clique
hypothesis is needed for the new covering result.

* `FullPair H pi i j`: three disjoint cross edges between distinct fibers,
  indexed by injective Fin 3 tuples. Under Core these exhaust both fibers.
* `nonstar_fullPair`: if a triangle p,q,r of right H contains a non-star p,
  its two directed witness cycles lie in distinct fibers and produce a full
  matching between them. The matched pairs are (x,x'), (y,y'), (z,z').
* `triangle_star`: if there is NO FullPair, every vertex of every right H
  triangle is a star biclique.
* `right_rainbow`: label a star by the kappa-coordinate of its singleton
  center, and non-stars arbitrarily. Every right H triangle is rainbow:
  its three centers are distinct and belong to the same base fiber.
* `second_right_two_cover`: consequently CoversWith (right (right H)) 2.
* `second_right_cover`: the corresponding countable-cover conclusion.

This excludes arbitrary partial matching bundles in which every cross-fiber
matching has size at most TWO, even over index graphs with triangles. It is
NOT a theorem about arbitrary mixtures of two-edge and full three-edge
matchings. Nor does it assert that K4-freeness of the second right target
excludes FullPair. Full pairs occur in the actual second-arc normal form.

Informal structural review (NOT additionally formalized here): in arc(H)
with H having UniqueTriangleEdge, triangle fibers come from the two directed
orientations of each H-triangle. Opposite orientations give a full matching.
Distinct H-triangles sharing one vertex give two cross edges, while those
sharing an edge are forbidden by UniqueTriangleEdge. Thus the full-pair
index graph in the triangle-bearing part of arc^2(G) appears to be merely a
matching. This illustrates why bounding/chromatically coloring only the
FULL-pair index graph cannot be assumed sufficient. The existing theorem
for a TRIANGLE-FREE index graph requires that graph to contain ALL cross
edges, not just full matching pairs. No extension of that theorem was proved.

Other reviews of saturation, finite-coordinate representations, natural
valuations, and stable graphs produced no main lemma. In particular:
* uncolored saturation still does not control arbitrary external colors;
* no general stable/NIP/algebraic covering theorem was established;
* no universal positive-index-three representation was constructed;
* no new infinite-target partite Ramsey theorem was proved.

Spec.lean remains unchanged with its original sorry. These new finite
covering lemmas are not a proof or disproof of Erdős 595. No completed main
proof has been submitted, and no job is pending.

## Full matchings of second-arc triangles are reversal pairs (NEW, verified)

`Submission/ArcFullMatchingStructure.lean` now compiles with an olean and
no warnings. Namespace `Erdos595ArcFullMatching`; final log
`/tmp/arc-full-matching-structure.log`. Both printed axiom audits contain
only propext, Classical.choice, and Quot.sound.

* `reverse H p`: reverses the ordered endpoints of an H-arc.
* `full_matching_reversal`: suppose H has UniqueTriangleEdge. If p,q,r
  and a,b,c are two DISJOINT triangles of arcGraph H, and p--a, q--b,
  r--c are all arc-graph edges, then a=reverse p, b=reverse q,
  c=reverse r. Thus the full-matching partner of a triangle is determined.
* `second_arc_full_matching_reversal`: specializes the theorem to
  H=arcGraph G, whose edges have unique triangles for every G.

The proof is explicit coordinate analysis. The two directed cycle
orientations in each arc triangle give four cases. Same-direction matching
would make an arc shared by both triangles, contradicting disjointness.
Opposite-direction matching, with unique common neighbors through base
edges, forces reversal. The formerly unfinished `reverse_cycle` lemma
was fixed by reversing its final adjacency in one case.

IMPORTANT SCOPE: This is not a covering theorem. In particular it holds
for second arc graphs of COMPLETE graphs too, with no K4 hypothesis.
Therefore a matching bound on the full-pair index graph alone cannot
possibly establish second-right countable coverability. The full second
right target retains the complete original graph via unitTwice. No claim
that deleting/adding a global matching preserves second-right covers has
been proved, with or without an additional target K4 bound.

Further review in this pass considered the mixed-matching covering gap,
coherent finite bounds, higher mutual ultrafilter stages, countable-palette
partite constructions, rational collinearity assignments, and generic
models. It produced no additional main lemma. Existing barriers remain:
ordinary saturation does not control external colorings; arbitrary rational
coefficient choices have no compactness theorem here; finite bipartite
homogenization does not supply compatible infinitely many partite stages;
and countable-palette Hales--Jewett is explicitly false. No new large-cardinal
or universe-reflection assumption was introduced.

Spec.lean is still unchanged with its original sorry. No proof or disproof
of erdos_595 has been obtained or submitted. No job is pending.

## Every K4-free second single cone has TWO edge pieces (NEW, verified)

`Submission/SecondConeTwoCover.lean` compiles with an olean and no warnings.
Namespace `Erdos595SecondConeTwo`; log `/tmp/second-cone-two-cover.log`.
All printed audits contain only the permitted axioms (not_two_pure uses
just propext).

* `not_two_pure`: in right(cone G), an edge between two Pure bicliques
  lies in NO triangle. This holds for every G, with no clique hypothesis.
  If their singleton apex sides agree, they cannot be adjacent. If the
  singleton sides are opposite, a common neighbor would have the apex
  on both sides of its biclique, contradicting looplessness.
* `exact_pure`: under NoFive G, mark precisely the Pure bicliques. The
  existing pure_transversal lemma supplies at least one in each triangle;
  not_two_pure supplies at most one. Thus the marking is ExactTransversal.
* `two_cover`: NoFive G implies CoversWith (right^2(cone G)) 2, by the
  exact-one transversal theorem from ExactTransversalRightCover.
* `two_cover_of_cliqueFree`: the full second right target being K4-free
  already implies NoFive G, so its edge-cover bound is uniformly TWO.

This strengthens the older THREE-piece bound in FiniteTransversalRightCover.
It does NOT establish a bound at the third or any higher right-cone stage.
The Pure set need not be independent: its opposite-side edges can exist,
but those edges are not in triangles.

Further exploration this pass did not supply the needed higher-cone
chromatic lower bound. Large proper chromatic number of the cone base
still cannot be assumed to transfer to triangle-edge chromatic number.
A proposed bipartite-double-cover lifting analysis was only exploratory:
right-adjoint bicliques can have many lifts, and no finite lifted-color
bound or coherent triangle lifting theorem at higher stages was proved.

Also reviewed first-difference/stepping-up constructions, infinite-support
restricted tuple families, generic extension arguments, and graphical
hypergraph gluing. No concrete first-difference adjacency rule was obtained
with BOTH K4-freeness and non-coverability. No infinite-palette signal
sender, induced Ramsey host for arbitrary infinite bipartite targets, or
coherent infinite partite construction was proved. Ordinary uncolored
extension/saturation still supplies no color-preserving extension principle.

Important distinction in the geometric review: NegativeInner supplies a
COUNTABLE EDGE cover, not a countable PROPER VERTEX coloring. Symmetrized
arc graphs of arbitrarily large complete graphs illustrate why those
conclusions cannot be interchanged. No new edge-vector argument was proved.

Spec.lean remains unchanged with its original sorry. No proof or disproof
of erdos_595 has been obtained or submitted; no build/search is pending.

## Exact finite filter marginals do NOT supply a countable limit (NEW, verified)

`Submission/InverseFilterLimitObstruction.lean` compiles with an olean and
no warnings. Namespace `Erdos595InverseFilterLimit`; log
`/tmp/inverse-filter-limit-obstruction.log`. The printed audits for map_drop
and no_thread contain only propext, Classical.choice, and Quot.sound.

* X n consists of strictly increasing (n+1)-tuples of Ordinal.{0}.
* drop n deletes the FIRST coordinate.
* F n is the pullback of the ordinal tail filter by the first coordinate.
  It is proper and countably complete.
* map_drop: map (drop n) (F (n+1)) = F n, EXACTLY.
* no_thread: there is no coherent sequence x n with drop n (x(n+1))=x n.
  Such a sequence would give an infinite strictly descending ordinal chain.

This rules out a GENERAL inverse-limit inference from proper countably
complete finite-stage filters with exact marginals. It does not say that
all graph-specific couplings have empty limits, nor settle Erdos 595.
The ordinal carrier lives in Type 1; it is a legitimate auxiliary generic
counterexample and is not used as a universe shortcut for Spec.lean.

Spec.lean remains unchanged with its sorry. No completed main proof has
been submitted. No job is pending.

## Continuum-sized four-cycle common neighborhoods suffice (NEW, verified)

`Submission/ContinuumFourCommonCover.lean` compiles with an olean and no
warnings. Namespace `Erdos595ContinuumFourCommon`; log
`/tmp/continuum-four-common.log`. Both audits use only the permitted axioms.
The current file states the cardinal theorem for V : Type (universe zero).

* ContinuumFourCommon: each actual four-cycle has <= continuum common neighbors.
* countable_cover: this condition implies a countable triangle-free edge cover,
  WITHOUT a clique hypothesis.
* large_common4_of_no_cover: any non-covered graph has a four-cycle with
  STRICTLY MORE than continuum common neighbors.

Proof generalizes FourCycleCommonCover: use continuum many four-ary closure
operations, cardinal induction with base size <= continuum, and the SAME
rank argument giving at most one common neighbor for distinct pairs inside
strict earlier neighborhoods. These lower neighborhoods are countably
properly colorable. The base case uses binary encoding of vertices.

This is a strict strengthening of the countable-common4 criterion, but it
is not a settlement: in a K4-free graph such a large common4 set is independent
and does not itself force a K4 or a coloring contradiction.

Other reviews this pass did not give a main proof. The AP-labeling idea is
already conditionally obstructed even with freely selected triangle midpoints
by ArithmeticProgressionObstruction plus its ordered triangle Ramsey
hypothesis. That Ramsey existence hypothesis was not newly proved here.
Higher-cone lifting, arbitrary bipartite Ramsey, noncontinuous ultrafilter
towers, and non-Archimedean geometric arguments remain exploratory only.
Spec.lean is unchanged with its original sorry, and no main proof was submitted.

## Unrestricted finite-tower reflection fails (verified corollary)

`Submission/FiniteTowerReflectionFailure.lean` compiles with an olean and
no warnings. Namespace `Erdos595FiniteTowerReflectionFailure`; log
`/tmp/finite-tower-reflection-failure.log`. Both axiom audits are permitted.

This packages a consequence of the EXISTING finite-support example, rather
than a new counterexample construction:
* base_no_finite: K has no valid triangle-avoiding edge coloring by ANY finite
  palette. Pull back through oldEmbedding and apply no_common_finite_support
  to the entire old vertex set.
* reflection_failure: a countable infinite K4-free base has countably covered
  mutual-ultrafilter towers at EVERY finite stage, but no finite base palette.

Consequently, countable-to-finite reflection is false without an extra
hypothesis, even if it assumes covers at all finite stages simultaneously.
No reflection theorem for the particular countable generic base was obtained.

Further exploration of generic extension properties and saturated Henson-type
hosts did not produce a color-preserving step. The generic extension property
prescribes adjacencies, not the external colors of new edges. It is not claimed
that no such host could be a witness; the required obstruction is unproved.
Likewise no new stationary-set normalization of the canonical filter, finite
bound assignment, infinite-palette signal sender, or higher-cone lower bound
was established. The existing finite-tuple and full countable-tuple covering
results must not be extended to arbitrary restricted countable-tuple families.

Spec.lean remains unchanged with its original sorry. No complete proof or
disproof has been submitted, and no build/search is pending.

## Countably many REALIZED edge types suffice (NEW, verified corollary)

`Submission/CountableRealizedTypes.lean` compiles with an olean and no
warnings. Namespace `Erdos595CountableRealizedTypes`; log
`/tmp/countable-realized-types.log`. The audits use only the permitted axioms.

* EdgeTypes G v is the set of pairType values attained on actual directed
  edges; nonedge types need not be countable.
* countable_cover: RelativeInvariant G v, K4-freeness, and countability of
  EdgeTypes imply a countable TF edge cover. There is NO restriction on the
  number of coordinates I, and the tuple family is arbitrary.
* countable_cover_of_types: it suffices to contain all actual edge types in
  an explicitly specified countable set.

This uses the EXISTING four-cycle/Later-flag argument from RestrictedTupleCover;
its code_valid lemma never needed finiteness of the coordinate type. Only
countability of the resulting palette was previously supplied by finite I.
The new proof restricts to the subtype of realized edge types and uses an
Option default on nonedges.

Thus a restricted countable-tuple construction using only one, finitely many,
or countably many interlacing types is excluded. The genuinely uncountably
many-type restricted-family case remains unresolved. No full restricted-
countable-tuple covering theorem or witness construction was obtained.

Additional discussion of countable supports, common cofinal limits, Boolean
intersection patterns, and algebraic representations was exploratory only.
No general sunflower-coloring theorem, no field-representation theorem for
arbitrary graphs, and no new generic-tower obstruction was proved.
Spec.lean remains unchanged with its sorry; no main proof was submitted.

## Properly colored EDGE-hitting subgraphs are not necessary (verified corollary)

`Submission/ProperEdgeHittingObstruction.lean` compiles with an olean and
no warnings. Namespace `Erdos595ProperEdgeHitting`; log
`/tmp/proper-edge-hitting-obstruction.log`. Both audits use permitted axioms.

* Hits G H: every G-triangle has at least one edge in H.
* cover_of_proper_hitting: if H has a proper binary-sequence vertex coloring,
  G has a countable TF edge cover. H need not be a subgraph of G.
* no_proper_hitting: VertexTriangleRamsey G C forbids a proper C-coloring of
  EVERY H satisfying Hits G H.
* covered_no_proper_hitting: for any nonempty palette C, the EXISTING shift-
  square vertex-Ramsey example is K4-free and covered (in fact by two pieces),
  yet admits no such properly C-colored edge-hitting graph.

In particular selecting the edge on the two least vertices of each triangle
cannot universally give a properly continuum-colored graph, regardless of
how the vertex order is chosen. This is the GLOBAL hitting-graph criterion.
It does NOT refute choosing an order such that each strict earlier neighborhood
is separately countably properly colorable. The latter remains unproved in
general and is strictly different from the global hitting-graph proposal.

Further review of local-ordering criteria and color internalization in generic
hosts produced no main result. Encoding external color classes on a small
subgraph does not make the encoding cover newly realized edges; no definable
closed edge domain or color-preserving saturation step was constructed.
Spec.lean remains unchanged with its original sorry. No settlement submitted.

## Ordered triangle filter has exact ordered marginals (NEW, verified)

`Submission/OrderedTriangleFilter.lean` compiles with an olean and no
warnings. Namespace `Erdos595OrderedTriangleFilter`; build and axiom-audit
log `/tmp/ordered-triangle-filter.log`. All audited declarations use only
propext, Classical.choice, and Quot.sound.

* Edge G consists of ascending orientations of G-edges, for ANY linear
  order on V. edgeFilter is countably generated by complements of TF graphs.
* comap_inclusion identifies edgeFilter exactly with the comap of the old
  coveringFilter along inclusion of ascending orientations.
* Triangle G consists of increasing triples a<b<c with all three G-edges.
* map_side: the (a,b), (a,c), and (b,c) marginals of triangleFilter are ALL
  exactly edgeFilter. No K4 hypothesis is needed.
* edgeFilter_neBot_iff and triangleFilter_neBot_iff: properness is equivalent
  to failure of a countable TF edge cover, not asserted unconditionally.

The reverse marginal proof forms a residual graph R of edges avoiding all
countably many exclusions and whose ASCENDING orientation is outside S.
Any R-triangle can be sorted; every side is bad, so its designated ordered
side contradicts the marginal hypothesis. This does NOT permute a triangle
while pretending to retain its ordered-side roles. R is therefore TF and
can itself be excluded by one more generator.

Scope: this allows finite gluing along specified ordered sides using the
existing Fiber lemmas. It does NOT force the missing diagonal of a diamond,
provide a four-clique coupling, or imply a countable inverse-limit thread.
The verified inverse-filter-limit obstruction remains applicable to the
latter inference. No new K4-free non-covered graph has been constructed.

Further review of extension-rich graphs, coherent finite bounds, Hilbert
triangle-hitting assignments, and the sparse matching-bundle normal form
produced no main theorem. No external-color saturation principle, universal
finite-bound assignment, or generalized hypergraph Ramsey shortcut was
established. In particular, the previously verified maximal-deletion failure
already blocks an argument based solely on local Grundy/minimality witnesses.

Spec.lean remains unchanged with its original sorry. No proof/disproof has
been submitted, and no build or unfinished implementation is pending.

## Exact COUNTABLE neighborhood extension is compatible with a cover (NEW, verified)

`Submission/CountableUltrapowerExtension.lean` compiles with an olean and no
warnings. Namespace `Erdos595CountableUltrapower`; build/audit log
`/tmp/countable-ultrapower-extension.log`. All printed axiom dependencies are
propext, Classical.choice, and Quot.sound.

Construction: take U = Ultrafilter.of atTop on N, and quotient functions
N -> CountableExtension.Vertex by eventual equality modulo U. The graph is
pointwise-eventual adjacency, expressed using chosen representatives. This
is an ORDINARY ULTRAPOWER, not the mutual-Fubini ultrafilter graph.

Verified:
* graph_cliqueFree: the ultrapower graph is K4-free.
* graph_cover: its quotient carrier has cardinal at most continuum, so it
  has a countable TF edge cover (the old cardinal-bound theorem).
* constantEmbedding embeds the original countable generic graph, and gives
  Infinite Point.
* no_finite_coloring: the old generic finite-Folkman theorem pulls back
  along that embedding, so the same graph has NO finite edge palette.
* sequence_extension realizes every consistent countable sequence of
  positive/negative adjacency requests, with a vertex distinct from every
  requested vertex. The positive part must induce a triangle-free graph;
  opposite requests must name distinct quotient vertices.
* countable_extension packages this for arbitrary DISJOINT countable sets
  S,T, with the induced graph on S triangle-free. The result is fresh outside
  S union T, adjacent to all of S, and nonadjacent to all of T.
* covered_extension_graph combines all these properties in one existential
  theorem. It is explicitly a COVERED graph, not a witness to Erdős 595.

Diagonal proof: for each finite initial segment, ultrafilter logic makes its
positive coordinate set triangle-free and separates positive/negative
coordinate sets on a U-large set. At coordinate n choose the greatest good
initial-segment length <=n; these lengths tend to infinity modulo U. Apply
CountableExtension.finite_extension at that coordinate. The quotient is
necessary for consistent negative requests; distinct functions alone need
not be distinct modulo U.

Scope: the theorem establishes the exact countable ONE-POINT NEIGHBORHOOD
extension property stated above. No theorem identifying this with full
first-order saturation or transferring saturation to arbitrary external
edge colors was used. Positive common-neighbor existence alone would have
been much weaker (even complete tripartite graphs have that property).

This decisively excludes inferring non-coverability or countable-to-finite
reflection merely from countable neighborhood-extension richness plus finite
Folkman obstructions. It does NOT address extension properties over larger
sets, nor arbitrary large saturated graphs.

Further review of long apex iterations, infinitary partite coherence,
chromatic-ideal fusion, forcing absoluteness, and reduced powers produced no
main theorem. Positive sets cannot be assumed to retain positivity through
countable intersections; ordinary uncolored extension properties still do
not control external countable edge colors. No new universal covering
argument or K4-free non-covered graph was obtained.

Spec.lean is unchanged with its original sorry, and no proof/disproof was
submitted. No build or unfinished implementation is pending. The scratch
UltrapowerExtensionCheck.lean intentionally contains failed API checks and
is not part of the verified development.

## Uncountable-coordinate and algebraic construction review (no new theorem)

Reviewed CountableTupleTypeCover, CountableRealizedTypes, RestrictedTupleCover,
LocalTupleCover, and the already verified RootLattice reduction. No main proof
or new candidate with a non-coverability argument resulted.

Important scope observation (mathematical discussion, NOT a newly audited
Lean declaration): arbitrary uncountable-coordinate order-type invariance is
too broad by itself. On binary-valued tuples, the comparison type of a
DISTINCT pair identifies the pair: among its values both 0 and 1 occur, and
the order/equality pattern identifies which coordinates have which value.
Thus this broad setting can encode arbitrary graphs. One must specify a
substantive structured relation, not assume that uncountably many coordinate
labels by themselves provide Ramsey amplification or a covering theorem.

Also reconsidered finite-support group presentations, Cayley/root graphs,
non-Archimedean orthogonality in signature (3,3), and finite-support algebraic
representations. No new universal representation or countable edge-Ramsey
transfer was established. The existing RootLattice countable_cover_iff
already rules out treating its construction as amplification.

The long-apex diagonalization review still has the old palette obstruction:
capturing all globally used colors at an earlier stage does not imply the
restricted coloring has no adapted labeling. A globally normalized coloring
has a finite adapted labeling, and extends across every countably covered
new induced graph using a reserved finite cross-edge palette. No argument
that bypasses this was found.

No new Lean file was added in this review. Spec.lean remains unchanged with
its original sorry. No completed proof/disproof has been submitted.

## Induced-bipartite Ramsey review (no settlement)

The finite-target arbitrary-palette theorem and the arbitrary-cardinality
matching/half-graph theorems were rechecked. Arbitrary COUNTABLE induced
bipartite targets are still not supplied by those results. A huge asymmetric
complete bipartite host forces monochromatic infinite bicliques by a profile
pigeonhole argument, but does not supply prescribed nonedges. Those nonedges
matter in the K4-preserving partite amalgamation step.

Universal incidence hosts and repeated finite-pattern selection gave no
countable-limit realization argument. A countable pair-box theorem cannot be
assumed (InfiniteBoxObstruction already refutes it). No independence or
large-cardinal necessity result was proved. The proposed induced-ray route
was not implemented or fully verified. Even an additional special bipartite
Ramsey target would not supply infinitely many coherent partite stages.
The asymmetric TriangleArrow existence statement remains genuinely missing.

Further review of hypergraph roots, ordinary ultrapower reflection, finite
bounds, canonical filters, and mixed partial/full matching bundles produced
no main theorem. Do not infer countable-to-finite reflection for arbitrary
external colors from saturation. Full-matching and no-full-pair covering
arguments have not been combined for arbitrary mixed bundles.

## Residual triangle degree is canonically co-large (NEW, verified)

`Submission/ResidualTriangleDegree.lean` compiles with an olean. Namespace
Erdos595ResidualTriangleDegree; log `/tmp/residual-triangle-degree.log`.
Every printed axiom list contains only the permitted three axioms.

* lowDegree R keeps precisely the R-edges with at most continuum many
  common neighbors INSIDE R.
* lowDegree_cover: this subgraph has a countable TF edge cover. Its own
  common neighborhoods are subsets of the corresponding R-neighborhoods.
* eventually_not_lowDegree: the canonical filter of ANY G avoids these
  lowDegree R edges, even without assuming R is a subgraph of G.
* eventually_many_extensions: if the R-edge subset of Edge G is large for
  coveringFilter G, then almost every edge belongs to R and has MORE than
  continuum many common neighbors inside R.
* eventually_many_common_neighbors: the special case R=G.
* positive_residual_many_extensions: a canonically positive spanning
  subgraph has such an edge, using exact restriction and its proper filter.

No clique assumption is required for these lemmas. They do not assert
properness of coveringFilter G, positivity of individual common-neighbor
fibers, disintegration into positive fibers, a common neighbor for a whole
triangle, or a countable inverse-limit thread. The result alone does not
force K4 and does not settle the conjecture.

## Thin marked triangles lift through the first right adjoint (NEW, verified)

`Submission/ThinMarkedSecondRight.lean` compiles with an olean. Namespace
Erdos595ThinMarkedSecondRight; log `/tmp/thin-marked-second-right.log`.
All audited dependencies are propext, Classical.choice, and Quot.sound.

Assumptions on H and m : V -> Bool:
* ExactTransversal H m: every triangle has exactly one marked vertex.
* Thin H m: if marked a belongs to triangle abc, all neighbors of a
  are b or c. Only marked vertices lying in triangles are constrained.

Verified:
* MarkedSide p says one NONEMPTY side of biclique p is entirely marked.
* lift_exact: marking those bicliques gives an exact-one transversal of
  triangles of right H.
* second_right_two_cover: the FULL right^2 H has TWO TF edge pieces.

Proof: in a six-witness right triangle, suppose the forward marked vertex
is x. The opposite witness x' is adjacent to x, hence equals y or z.
In the first case one biclique side contains y and z; every vertex on its
opposite side must be marked by exactness. The other case is symmetric.
Conversely, two bicliques with marked sides would mark two vertices of
one of the two witness triangles. No unique-common-neighbor hypothesis,
independence of the marked set, or finite cardinal bound on H is used.

Lean detail: explicitly include the Six witness s when it does not occur
in the theorem statement; otherwise section-variable omission removes it.

## Arbitrary two-neighbor ears cannot amplify at the second right (NEW, verified)

`Submission/EdgeEarSecondRight.lean` compiles with an olean. Namespace
Erdos595EdgeEarSecondRight; log `/tmp/edge-ear-second-right.log`.
Audits use only permitted axioms (mark_thin uses only propext).

Given ANY triangle-free B on V, ANY ear index type E, and l,r : E -> V,
form H on V + E retaining B and adjoining independent ears e adjacent
exactly to l(e),r(e). Endpoints may coincide, need not be adjacent, and
arbitrarily many ears may have the same endpoint pair.

* mark_exact: marking the ears meets each H-triangle exactly once.
* mark_thin: a marked vertex in a triangle has just its two triangle
  neighbors.
* second_right_two_cover and second_right_cover: right^2 H has a TWO-piece
  TF edge cover, with no cardinality or proper vertex-coloring bound on B.

This includes the construction attaching a private triangle to each edge
of a triangle-free graph. It is excluded as a witness at the second right
stage, even when the base has arbitrarily large proper chromatic number.
No general third-stage assertion is made.

Exploratory SAT checks (NOT Lean certificates): /tmp/edge_ear_adjoint.py
found no map arc^2 K4 into edge-ear graphs over C3,C4,C5,C7,C9 or the
Groetzsch graph. These finite checks were superseded for candidate exclusion
by the universal two-cover theorem; no universal K4 assertion was inferred.

A separate DEGREE-THREE review remains only exploratory. Adding an apex for
every triple of C5 gives a SAT homomorphism arc^2 K4 -> H when both P3 and
one-edge-plus-isolated triple types are allowed. Individually, the P3 and
one-edge types gave UNSAT on C5, Groetzsch, and K3,3, but those are not
kernel certificates or universal theorems. One-edge-type tests on the
23-vertex Mycielski graph and Clebsch graph timed out after 30 seconds each.
Scripts: /tmp/triple_apex_adjoint.py, /tmp/triple_apex_more.py,
/tmp/triple_apex_large.py. No process remains active. No K4 bound or
non-coverability transfer for a degree-three family has been proved.

Spec.lean remains unchanged with its original sorry. No completed proof or
disproof has been submitted, and no main-proof build is pending.

## Dominating marked neighborhoods give a two-piece second-right cover (NEW, verified)

`Submission/DominatedMarkedSecondRight.lean` compiles with an olean.
Namespace Erdos595DominatedMarkedSecondRight; log
`/tmp/dominated-marked-second-right.log`. Audits use only the allowed axioms.

This genuinely strengthens ThinMarkedSecondRight:
* Dominated H m: for every triangle a,b,c with marked a, every neighbor d
  of a is adjacent to b OR c. In other words each edge of the marked
  neighborhood dominates that neighborhood.
* dominated_of_thin includes the earlier degree-two condition.
* lift_exact: the SAME MarkedSide/liftMark construction gives exactly one
  marked biclique in each triangle of right H.
* second_right_two_cover: the FULL second right adjoint has TWO TF pieces.

The proof is short and does not use a finite bound: in a six-witness right
triangle with forward marked vertex x, the opposite witness x' is adjacent
to x. Domination makes x' adjacent to y or z. In the first case y,x' are
unmarked adjacent vertices on one side of q; exactness forces its opposite
side to be entirely marked. The other case gives a marked side of p.
The old not_two_markedSides lemma supplies uniqueness. No maximal-biclique
completion, independence of the marked set, or K4 premise is needed.

## Complete-bipartite/star apex neighborhoods are excluded (NEW, verified)

`Submission/BipartiteNeighborhoodApexCover.lean` compiles with an olean.
Namespace Erdos595BipartiteNeighborhoodApex; log
`/tmp/bipartite-neighborhood-apex-cover.log`. All audits are permitted.

Start with ANY triangle-free B and ANY family N : E -> Set V. Form H on
V + E, retaining B, making E independent, and adjoining apex e with exactly
N(e) as its old neighborhood. Mark all new apices.

* mark_exact: every H-triangle contains exactly one new apex.
* DominatingEdges B N: for every e, an edge ab inside N(e) is adjacent,
  at one of its endpoints, to every d in N(e).
* mark_dominated, second_right_two_cover, second_right_cover transfer the
  preceding general theorem.
* dominating_of_complete_bipartite and two_cover_of_complete_bipartite:
  an explicit binary complete-bipartite labeling of each N(e) suffices.
* dominating_of_stars and two_cover_of_stars: each N(e) may be ANY subset
  of {center(e)} union N_B(center(e)). There is no cardinality/degree bound.

Thus the DEGREE-THREE PATH-neighborhood candidate is now universally ruled
out, and much more: arbitrary large star and complete-bipartite apex
neighborhoods also cannot produce a second-right witness. The degree-three
ONE-EDGE-PLUS-ISOLATED case is not covered by this theorem. The full problem
remains open in this development.

Additional finite exploration (NOT Lean-certified claims):
* /tmp/triple_apex_fixed.py fixes one source triangle and one target
  triangle in the Clebsch one-edge-neighborhood test. This restricted
  instance returned UNSAT. No universal orbit argument was certified.
* /tmp/triple_apex_blowup.py returned UNSAT for both separate triple types
  over the twofold independent blowup of C5.
* /tmp/oneedge_exact_mark.py found that the first right adjoints in the
  C5, Groetzsch, and C5-blowup ONE-EDGE examples have no exact-one triangle
  marking; the PATH examples did have such markings. This motivated the
  now-verified domination theorem but is not itself a Lean theorem.
* /tmp/oneedge_second_palette.py enumerated 312 completed bicliques at
  the second stage for the C5 one-edge example (10,125 edges, 2,130
  triangles) and found a valid TWO-color edge assignment. No universal
  coloring rule or infinite transfer follows, and no Lean certificate for
  this finite computation was generated.
* A simple proposed degree-three folding of second-arc normal forms was
  tested in /tmp/marked_neighbor_fold.py. Identifying all non-triangle
  neighbors of each selected vertex creates unwanted loops/triangles even
  for small K4-free sources. It supplies no new representation theorem.

Further review of bounded apex degrees, triangle-distance/tree colorings,
finite-support graph representations, and chromatic-profile lower bounds
produced no proof of the conjecture or its negation. None of the new results
asserts non-coverability of a K4-free graph. Spec.lean remains unchanged with
its original sorry. No completed proof/disproof was submitted. All temporary
SAT jobs have finished, and no main-proof build is pending.

## Bounded universal one-edge-apex experiment (exploratory; not a theorem)

The completed `/tmp/oneedge_universal_root.py 12 180` search returned UNSAT
(CaDiCaL exit 20; log `/tmp/oneedge-universal-12.log`). It searched for a
triangle-free base with twelve old vertices, independent apices whose
neighborhoods are an edge plus an isolated third point, and a homomorphism
arc^2(K4) into the resulting graph. The source triangle and target endpoint
labels were fixed, and a first-occurrence label symmetry restriction was used.
No Lean certificate or completeness proof was produced. In particular this
is NOT a universal K4-preservation result and provides no non-coverability
statement. All jobs from this experiment have finished. Spec.lean is unchanged.

Further bounded experiment: `/tmp/oneedge_universal_root.py 60 600` also
returned UNSAT (log `/tmp/oneedge-universal-60.log`; 30,390 variables and
1,731,230 clauses). This still has no Lean certificate. A finite-image
completeness argument and the source/target symmetry reductions would need
an explicit proof before treating it as a universal theorem.

`/tmp/oneedge_modthree.py` checked the weaker possibility of a vertex labeling
of the first right adjoint by F_3 with triangle sums constantly one. Gaussian
elimination found no such labeling for the C5 and Groetzsch one-edge bases.
These are exploratory finite computations, not Lean theorems.

An attempted second-right enumeration for the Groetzsch one-edge base found
15,958 completed bicliques. The naive Python adjacency construction was stopped
before completion to avoid its large memory use. No palette result was obtained
for this graph (log `/tmp/oneedge-second-grotzsch.log`). No SAT job remains active.

## Unrestricted local one-edge-apex obstruction (certificate verified; graph transfer pending)

The earlier size-bounded experiments have been replaced by a cleaner necessary-
condition test on the sixty source images themselves. `/tmp/oneedge_local_constraints.py`
uses equivalence and adjacency propositions on source images, marks, independent
marked vertices, a mark in every triangle, marked degree at most three on the
source neighbors, and matching marked neighborhoods. There is NO target size
bound and NO symmetry reduction. It returned UNSAT. The encoding has 3,600
variables and 372,230 clauses. A trimmed core has 5,990 clauses and 4,129 RUP
steps (25,440 hints).

`Submission/OneEdgeLocalSAT.lean` HAS compiled with an olean; its raw_unsat
axiom audit is [propext] only. It embeds a renamed version of the core and the
LRAT certificate as string literals. Mathlib.Tactic.Sat.fromLRATAux reconstructs
ordinary propositional proof terms, which the Lean kernel checks. This is NOT
native_decide or bv_decide. The tiny wrapper omits only the reification into
thousands of proposition binders. Log: `/tmp/oneedge-local-sat.log`.

`Submission/OneEdgeLRATCheck.lean` also compiles, using the stock lrat_proof
command on the earlier externally stored core files; its audit is the permitted
three axioms. It is an auxiliary check, not needed by the intended graph theorem.

Graph transfer is still being compiled in `Submission/OneEdgeLocalPattern.lean`.
It explicitly enumerates the second arcs of K4, realizes all 5,990 core clauses
from LocalConditions, and intends to prove no_second_arc_four and hence
second_right_cliqueFree. LocalConditions comprises independent marked vertices,
a triangle-hitting mark predicate, degree at most three at every marked vertex,
and matching neighborhoods at those marked vertices. The current 57k-line
version uses explicit balanced formula nodes to avoid slow unification. Do NOT
yet count these graph theorems as verified until its build has succeeded.

The associated `Submission/ThreePointMatchingApex.lean` is prepared but not yet
checked. It applies those LocalConditions to arbitrary independent apices over
a TF base, whose neighborhoods have at most three points and induce matchings.
It also includes the one-edge-plus-isolated-point specialization. This is a
K4-preservation claim, NOT a coverability or non-coverability claim.

Small auxiliary checks `OneEdgeLeafCheck.lean` (five instances of each clause
family) and `OneEdgeTreeBench.lean` (a 187-leaf subtree) compile without errors.
A failed older MetaCheck scratch file merely used the wrong namespace for the
LRAT meta functions; the correct namespace is Mathlib.Tactic.Sat. The finalized
SAT wrapper has already passed its axiom check.

## Larger finite palette experiment (exploratory, not Lean-certified)

The Groetzsch one-edge example was enumerated with compact bitsets rather than
Python sets. Its first completed right adjoint has 274 vertices; the second has
15,958 vertices and 11,374,844 edges. There are 15,509,660 triangles, involving
1,454,530 edges and 15,836 vertices. A full SAT search FOUND A TWO-EDGE-COLORING;
C++ then rechecked all triangles against the returned assignment. This rules out
that particular finite graph as a 2-palette obstruction, but proves no universal
covering theorem. Artifacts: `/tmp/oneedge-grotzsch-count.log`,
`/tmp/oneedge-grotzsch-palette.log`, `/tmp/oneedge_grotzsch_rows.bin`, and
`/tmp/oneedge_grotzsch_palette.{cnf,out}`. Scripts: oneedge_grotzsch_data.py,
oneedge_count.cpp, oneedge_palette.cpp, run_oneedge_palette.sh, all under /tmp.
The palette job has finished. Its CNF is about 745 MB.

A separate finite test of a proposed coarse mixed-orientation edge-color rule
also found counterpatterns for both possible marked-backtrack bits. Both live
over five-cycle old bases, with one-edge-plus-isolated apex neighborhoods.
Artifacts `/tmp/oneedge_tri_type_{0,1}.json`; script
`/tmp/oneedge_triangle_types.py`. The first extraction mistakenly merged marked
source images, which could inflate their degrees; the corrected extraction uses
one separate apex per marked source vertex and checks the actual conditions.
This is exploratory only and supplies neither a counterexample to the universal
K4 claim nor a non-coverability result.

The graph-transfer build was subsequently split again:
* `OneEdgeLocalDefinitions.lean` HAS now compiled (38 MB olean). It contains
  the explicit source enumeration, LocalConditions, valuation, the closed
  balanced formula nodes, and a checked equality with the certified core.
  Log: `/tmp/oneedge-local-definitions.log`.
* `OneEdgeLocalPattern.lean` now imports those definitions and checks the
  realization in 32 separate proof blocks, then combines them with raw_unsat.
  It remains a PENDING build at the time of this note. Progress is written
  to `/tmp/oneedge-block-progress.log`; final log is
  `/tmp/oneedge-local-pattern.log` (driver appends LEAN_EXIT).
* `/tmp/run_oneedge_pattern.sh` compiles ThreePointMatchingApex only after
  a successful Pattern build. The driver log is `/tmp/oneedge-build-driver.log`.

Further finite exploration: the C5 second-right graph admits a two-color
VERTEX labeling with no monochromatic triangle, but the Groetzsch second-right
graph does NOT: the latter vertex-palette SAT instance returned UNSAT. This is
not a Lean theorem, and it does not contradict its verified-in-C++ TWO-EDGE-
COLORING. It blocks an unqualified claim that all these second-right graphs
have a two-piece TF vertex cover. Artifacts: `/tmp/oneedge_C5_vertex_two.*`,
`/tmp/oneedge_grotzsch_vertex.{cnf,out}`, `/tmp/oneedge-grotzsch-vertex.log`;
script `/tmp/run_oneedge_vertex.sh` and C++ source oneedge_vertex_palette.cpp.
No SAT job remains active. Spec.lean is still unchanged with its original sorry.

## Possible simpler pair-graph subfamily (informal sketch; NOT formalized)

A potential way to use the new local obstruction without carrying all first-
right bicliques is the following. For a TF graph B, let P(B) have vertices
(S,eps), where S is a two-element independent old set and eps is Boolean.
* At equal eps, require both S intersect common_B(T) and T intersect common_B(S)
  to be nonempty (the old cross graph contains a dominating P4 or C4).
* At opposite eps, require S intersect T nonempty.

Informally, P(B) should map to right(H) for an instance of the three-point
matching-apex family: first extend B by independent old clones adjoining common
neighbors to each independent set of at most three original vertices, then add
all one-edge-plus-isolated marked triples. Send (S,eps) to (S,common_H(S)), or
its reversal. Equal-eps edges have old witnesses. For opposite eps, S union T
has at most three vertices and at most one old edge; its common neighbor is
an old clone in the independent case, or a new marked apex in the one-edge case.
This would make right(P(B)) K4-free by the now-being-finalized local theorem.
This mapping and resulting K4 theorem HAVE NOT been written in Lean.

No non-coverability transfer was found. In particular, one must not infer a
lower bound from proper chromatic number of B alone. Standard ordered shift
bases have positive equality-defined finite-coordinate relations, for which
Noetherian/finite-parameter covering arguments are a serious obstruction.
A high-chromatic base with genuinely unrestricted common-neighborhood structure
would need a separate argument controlling arbitrary external edge colors.

## Clean completion of one-edge local theorem

The clean builds of OneEdgeLocalPattern and ThreePointMatchingApex both finished
with LEAN_EXIT=0. no_second_arc_four, second_right_cliqueFree, local_conditions,
and second_right_cliqueFree_of_one_edge were audited and depend only on
propext, Classical.choice, Quot.sound. The universal K4-preservation theorem is
now verified, superseding all pending-build annotations above.
Spec.lean is unchanged; non-coverability remains unproved.

## Independent-pair right-adjoint family (NEW, verified)

`Submission/IndependentPairAdjoint.lean` compiles with an olean. Namespace
Erdos595IndependentPair; log `/tmp/independent-pair-adjoint.log`.
Audits: intoFirst uses [propext, Quot.sound]; right_cliqueFree uses only
[propext, Classical.choice, Quot.sound].

For arbitrary triangle-free B, Pair B is an ordered pair of nonadjacent
vertices (repetition is allowed). Its support is the associated one- or
two-point set. P(B) has vertices Pair B x Bool:
* equal bits: each support has a vertex adjacent in B to the entire other
  support (mutual domination);
* unequal bits: the supports intersect.

`near_disjoint` proves that mutually dominating independent supports are
disjoint. `intoFirst` maps P(B) into right(H), where H is B with independent
apices indexed by triples (d,l,r) with d nonadjacent to l and r, having
neighborhood {l,r,d}. No old clone extension is needed: if two independent
pairs overlap, their union has at most three points and at most one edge,
so an apex of this very family provides their common neighbor.

`rightMap` supplies covariance by images of biclique sides. Combining it
with the verified degree-three local theorem yields `right_cliqueFree`:

    B.CliqueFree 3 -> (right (graph B)).CliqueFree 4.

This simplifies the previously informal pair-graph candidate. It is ONLY
a K4 bound; neither coverability nor non-coverability of this family has
been established. In particular high proper chromatic number of B has
not been shown to give a triangle-edge coloring lower bound.

## New finite local tests (exploratory, NOT Lean certificates)

`/tmp/local_apex_variants.py` repeated the source-image local encoding for
second arc graphs of several small graphs. Degree-three maps were FOUND
for the diamond, five-wheel, and octahedron. Extracted old bases had,
respectively, 2, 32, and 2 vertices. These finite cases do NOT establish a
universal representation theorem for K4-free graphs.

For arc^2(K4), removing the degree bound gave SAT with maximum marked degree
six. Degree FOUR already gave SAT, with all triangle-bearing marked
neighborhoods consisting of one edge and at most two isolated points.
Thus the universal local K4 exclusion cannot simply be extended from degree
three to degree four, even with at most one edge in each marked neighborhood.
These are exploratory witnesses, not kernel-verified countertheorems.
Artifacts `/tmp/local_variant_K4_{0,4,5}.{cnf,out,json}`; logs
`/tmp/local-variant-K4-{0,4,5}.log`. All these solver jobs have finished.

A more rigid attempted representation used ordered edges of G as the
triangle-free shift base, with one apex over the three edges of each
G-triangle. `/tmp/triangle_incidence_hom.py` found homomorphisms from arc^2 G
for K3, the diamond, and the octahedron, but returned UNSAT for the five-wheel.
The initial support-only CNF did NOT enforce functionality; the script
correctly reran every SAT result with one-hot clauses, and the reported final
results are from those one-hot instances. This rigid representation therefore
does not cover all K4-free graphs. No Lean certificate was produced.
Logs `/tmp/triangle-incidence-{K3,diamond,wheel5,octahedron}.log`.

The final main file remains unchanged with its original sorry. No proof or
disproof of Erdős 595 has been obtained or submitted. The new pair graph has
not bridged the essential countable-cover gap.

## Independent-pair family is universally covered (NEW, verified)

This SUPERSEDES the earlier suggestion that right(P(B)) might be a witness.
`Submission/IndependentPairCover.lean` compiles with an olean; namespace
Erdos595IndependentPairCover, log `/tmp/independent-pair-cover.log`.
For EVERY triangle-free B, `countable_cover` proves a countable triangle-free
edge cover of right(P(B)), with no size or proper chromatic bound on B.
It uses finite profiles and equality/adjacency diagrams of selected anchors
AND intersection witnesses. The anchor-only diagram shortcut was false.

Supporting files `PairAnchorSAT.lean` and `PairAnchorPattern.lean` are verified.
The stock lrat_proof declaration embeds a 64-variable, 84-clause certificate
with 38 RUP steps (158 hints). The graph realization `no_pattern` rules out
an 18-coordinate old pattern. These are ordinary kernel-checked proofs, not
native_decide/bv_decide. All audited axioms are among the permitted three.

`RightCoverReduction.lean` supplies two verified reductions:
* delete_colored: delete a COUNTABLY PROPERLY VERTEX-COLORED subset S of H;
  coverability of right(H[S^c]) implies that of right(H).
* triangle_core: if S contains EVERY vertex of EVERY triangle of H, then
  coverability of right(H[S]) implies that of right(H).
The second hypothesis is stronger than just meeting every triangle.

## Small marked neighborhoods cannot yield a second-right witness (NEW, verified)

`Submission/SmallMarkedSecondRightCover.lean` now compiles cleanly with olean.
Namespace Erdos595SmallMarkedSecondRight; log `/tmp/small-marked-second-right.log`.
`second_right_cover` and all intermediate audited lemmas depend only on
propext, Classical.choice, Quot.sound.

Conditions H m: the marked vertices are independent and meet every triangle;
at any marked vertex lying in a triangle, every independent triple of its
neighbors has a repetition. Under these conditions right(right H) is covered.
No cardinality restriction on H or its unmarked triangle-free part is needed.
The conditions alone do NOT assert that right(right H) is K4-free.

Proof: bicliques with a nonempty entirely marked side are properly Boolean
colored. Delete them with delete_colored. Every remaining triangle vertex
has one independent unmarked side with one or two points. Encode that side
and its orientation into P(B), where B is the unmarked triangle-free graph.
Triangle-core restriction, covariance of right, and IndependentPairCover finish.

`conditions_of_degree_three` and `second_right_cover_of_degree_three` derive
this from degree at most three at marked vertices. No matching-neighborhood
condition is required for coverability. Therefore ALL the earlier
ThreePointMatchingApex and one-edge-plus-isolated-point candidates are ruled
out as witnesses, even though their K4-preservation theorem remains valid.

This does not cover arbitrary second-arc normal forms, which have unbounded
marked neighborhoods. No proof or disproof of erdos_595 has been obtained.
Spec.lean remains unchanged with its original sorry.

## Three-point support boundary (exploratory, NOT Lean-certified)

`/tmp/independent_support_K4.py` tests hom arc(K4) -> P_k(B), where P_k
uses independent supports of size at most k (repetition allowed), mutual
old domination at equal bits, and support intersection at opposite bits.
For k=3 it found a homomorphism even with B triangle-free and C4-free.
The extracted old graph has 9 vertices and 12 edges and is isomorphic to
the Petersen graph minus one vertex. Data `/tmp/supportK4_3_5.json`;
log `/tmp/supportK4_3_5.log`. Thus merely increasing girth from four to five
does NOT preserve the K4 bound for the three-point family. The test without
the C4 restriction was SAT too (`supportK4_3_4`).

Variants `/tmp/independent_support_K4_bip.py` and
`/tmp/independent_support_K4_odd.py` returned UNSAT under bipartiteness,
no closed five-walk, and no closed seven-walk respectively. These UNSAT
results have not been kernel-certified and are not needed for any Lean proof.

There is already a mathematical reason the no-five restriction is unhelpful:
for any family of old supports, map (S,bit) to (S,common_cone(S)) or its
reversal in right(cone B). Same-bit domination supplies old witnesses;
opposite-bit overlap supplies one witness and the single cone apex the other.
Thus right(P_k(B)) maps into right^2(cone B). Under NoFive B the latter
already has a VERIFIED two-piece edge cover (SecondConeTwoCover). This
argument needs no bound on support size; it is a projection, not a lower bound.
No unrestricted higher-support covering theorem or witness was obtained.

Web access to erdosproblems.com was attempted but DNS was unavailable.
No new source or externally established resolution was found. Subsequent
reviews of higher cones, saturated extensions, and countably complete
canonical filters supplied no new main lemma. Existing limitations on
external colors and inverse-filter-limit arguments still apply.

## Further finite higher-cone marking test (exploratory only)

Scripts `/tmp/second_cone_exact_test.py` and
`/tmp/second_cone_profile_test.py` enumerate completed bicliques of the first
and second right adjoints of a cone over a finite odd cycle.
* C7: first right has 32 vertices; second right 356 vertices, 11,575 edges,
  3,332 triangles. No exact-one triangle vertex marking; a weak Boolean
  non-monochromatic triangle vertex coloring exists; no rainbow 3-labeling.
* C9: first right 40 vertices; second right 456 vertices, 15,043 edges,
  4,248 triangles. An exact-one triangle vertex marking exists (hence also
  a weak Boolean marking); no rainbow 3-labeling.
These are SAT results, not Lean certificates or a general theorem.
Logs `/tmp/cone-second-C7.log`, `/tmp/cone-second-C9.log`; data and CNFs
`/tmp/cone_second_C{7,9}*`.

The coarse 4-bit profile records whether each biclique side contains a
first-right Pure biclique of each apex orientation. Both cycles have EXACTLY
the same triangle profile list:
 (0,6,9), (1,1,6), (2,2,9), (4,4,9), (6,8,8).
No exact-one marking depending only on that profile exists, even for C9.
Thus the positive C9 SAT assignment is not justified by this coarse rule.
No higher-cone non-coverability transfer or universal marking theorem was
obtained. All test jobs completed; no main-file change or proof submission.

## Submission attempt and continued boundary checks

A submit_proof call was made with Spec.lean still explicitly unresolved; the
verifier rejected it, and the user instructed continued work. No success or
settlement was claimed. The main file still has the original sorry.

The longer exact SAT search for arc^3(K4) -> cone(C7) returned UNSAT.
This supersedes the old 45-second timeout, but is NOT a Lean certificate.
Output `/tmp/arc3K4_coneC7_long.out`; original input
`/tmp/arc3K4_coneC7.cnf`. This suggests the third right adjoint of cone(C7)
is K4-free, but no kernel-checked theorem has been added for it.

`/tmp/cone_third_count.py` enumerated 110,528 completed bicliques at the
third right stage over cone(C7). Data `/tmp/cone_third_C7_concepts.json`;
log `/tmp/cone-third-C7-count.log`. A restricted subgraph on all 2,444
nonempty concepts with at least one side of size <=2 has 242,744 edges and
65,072 triangles. The triangles use 23,884 edges. Its two-edge-color SAT
instance is SAT (not a certificate for the FULL third right graph).
Scripts `/tmp/cone_third_small_data.py`, `/tmp/cone_third_small.cpp`;
artifacts `/tmp/cone_third_C7_small2.{bin,cnf,out}`. No job is running.

Further analysis revisited asymmetric Ramsey targets, ultrapower/color
saturation, finite-coordinate intersection constructions, and rational
collinearity assignments. It produced no new main theorem. In particular
small countable palettes are not made internal by uncolored saturation,
and the old AP/F3 representation obstructions have not been bypassed.

## Small-marked family has a UNIFORM FINITE palette (NEW, verified)

`Submission/SmallMarkedFinitePalette.lean` compiles with an olean and no warnings.
Namespace Erdos595SmallMarkedFinitePalette; log
`/tmp/small-marked-finite-palette.log`. All three printed audits use exactly
propext, Classical.choice, Quot.sound.

New declarations:
* `of_ordered_patterns`: retains the original palette in HasColoring,
  without passing through Nat.
* `independent_pair`: right(P(B)) has a SINGLE fixed finite palette for
  every triangle-free B, independent of its carrier size.
* `triangle_core`: finite-palette version, adding Option to the palette.
* `delete_colored`: palette-preserving version with target palette
  (Set D x Set D) x C, where D properly colors the deleted base vertices.
* `small_marked`: right^2 H has a fixed finite palette under the already
  verified SmallMarkedSecondRight.Conditions H m.
* `finite_representation_failure`: finite Folkman supplies a FINITE K4-free
  G such that arc^2 G has no homomorphism to ANY small-marked H (arbitrary
  target carrier size).

The palette is explicitly
  PairPalette = (Profile x Profile) x Option (Bool x Diagram)
  Palette = (Set Bool x Set Bool) x Option PairPalette,
where Profile = Bool -> Bool -> Bool and Diagram consists of two binary
relations on Fin 10. It is finite by ordinary typeclass inference. Thus the
flexible degree-three representation idea is now excluded, not just the
older rigid representation. The small finite SAT successes cannot extend
to all finite K4-free sources. No numerical Folkman witness is required.

A separate exploratory canonical quotient test, not used in the Lean proof,
collapses all nontriangle neighbors of each selected triangle-bearing vertex
of arc^2 G to a third point. It already creates triangles in the unmarked
quotient for G=K3. Script /tmp/canonical_degree3_quotient.py.

Reviewed the remaining higher cone, canonical filter, partite, saturation,
graphic-matroid, and transfinite recoloring routes. None supplied the missing
infinitary argument. Direct external DNS-over-HTTPS requests to 1.1.1.1 and
8.8.8.8 also timed out, so no updated online reference was obtained.

Spec.lean remains unchanged with its original sorry. This is an auxiliary
obstruction theorem, NOT a proof or disproof of the original existential.

## Further global certificate/exponential review (no settlement)

Rechecked TriangleHit, HilbertHitStrictness, RamseyVectorObstruction,
ExponentialCandidate, ExponentialChromaticFilter, ExponentialCompactness,
and ExponentialNeighborhoodTransfer. No new main lemma was obtained.

* Fixed uniform negative margins remain blocked as a universal certificate
  by the earlier finite Ramsey transfer. Nonuniform strict triangle hitting
  is still unproved for arbitrary K4-free graphs.
* Generic countable-target exponentials over arbitrary high-chromatic
  triangle-free domains remain outside the established shift exclusions.
  Neither evaluation nor the chromatic-filter transfer controls arbitrary
  external countable edge colorings. No lower-bound transfer was found.
* Speculation about finite-positive-index Gram completions, valuation
  reductions, algebraic supports, graphical matroids, and coherent partite
  limits supplied no universal representation or cover theorem. None of
  those speculative assertions was added to Lean.

No new proof submission was made. Spec.lean is still unchanged and unresolved.

## Robust fixed odd-wheel length (NEW, verified)

`Submission/RobustOddWheel.lean` compiles with an olean. Namespace
`Erdos595RobustOddWheel`; build and axiom audit log `/tmp/robust-odd-wheel.log`.
All three printed theorem audits use only propext, Classical.choice, Quot.sound.

Definitions and verified declarations:
* `WheelWalk G n`: a closed walk of length n in one induced neighborhood of G.
  This does NOT assert a simple or induced rim cycle.
* `wheelWalk_mono`: monotonicity under spanning-subgraph inclusion.
* `cover_of_no_odd_wheel`: if every neighborhood has only even closed walks,
  Mathlib's two_colorable_iff_forall_loop_even gives local two-colorings;
  LocalChromaticProduct.cover_of_neighborhood_colorings gives a countable
  triangle-free edge cover.
* `cover_diff`: coverable D and G\D imply coverable G.
* `fixed_odd_length`: if G is NOT countably TF-edge-covered, there is one odd
  n such that for EVERY countably TF-edge-covered D, G\D has WheelWalk n.
* `not_wheelWalk_one`: looplessness excludes length one.
* `not_wheelWalk_three`: K4-freeness excludes length three.
* `fixed_odd_length_ge_five`: the persistent odd n is at least five when G
  is K4-free.

Proof of the fixed-length step is only countable deletion: otherwise choose
one coverable D_n removing all n-wheel walks for each odd n. Their countable
union E is covered, and G\E is locally bipartite, hence covered. This would
cover G. No ultrafilter extension or infinite inverse-limit thread is used.

This is a NECESSARY CONDITION, not a witness or a contradiction. In particular
neither this lemma nor the existing diamond coupling makes opposite diamond
vertices adjacent in a K4-free graph. A wheel is not itself forbidden by K4
freeness. No statement eliminating all such persistent odd wheels was proved.

Further discussion rechecked uncountable neighborhood-extension properties,
finite-support versus full-product Ramsey constructions, indefinite Gram
representations, sparse normal forms, and high-chromatic exponential domains.
No new main lemma resulted. Do not infer a universal positive-index-three
Gram representation, a countably complete ultrafilter extension, a finite
palette from uncolored saturation, or a countable-limit partite embedding.

Spec.lean is unchanged and still contains its original sorry. No new
submission was attempted, and no build is pending.

## Minimal persistent odd-wheel residual (NEW, verified)

`Submission/MinimalRobustOddWheel.lean` compiles cleanly with an olean.
Namespace `Erdos595MinimalRobustOddWheel`; log
`/tmp/minimal-robust-odd-wheel.log`. Both printed axiom audits use only
propext, Classical.choice, and Quot.sound.

* `Persistent G n` means that every covered edge deletion leaves an n-step
  closed rim walk in some neighborhood.
* `cover_sup` combines two countable TF edge covers.
* `persistent_diff` shows that deleting a covered edge graph preserves
  persistence at each already persistent length.
* `minimal_residual`: given a hypothetical K4-free non-covered G, there are
  a covered edge graph E and an odd n>=5 such that R=G\E is K4-free and still
  non-covered, n is persistent in R, and R has NO odd rim walk of any length
  smaller than n.

Proof: minimize the persistent odd length using Nat.find. For each smaller
odd m, choose a covered deletion eliminating all m-wheel walks. Their union
is covered. Deleting it preserves non-coverability and persistence at n.
The statements remain about closed WALKS, not asserted simple/induced rims.
No extraction of an induced wheel or graph embedding was needed or claimed.

This remains an auxiliary normal form. No method eliminating the remaining
persistent odd wheel, and no construction satisfying non-coverability, was
obtained. It therefore does not settle the conjecture.

Further review in this continuation revisited edge-dependent finite-bound
compactness, closure under common neighborhoods, exponential domains beyond
the excluded shifts, higher arc/right towers, quadratic-form candidates in
other characteristics, and finite-support/algebraic graph encodings. None
supplied a main proof. In particular:
* Independent common-neighbor sets cannot simply be assembled over an
  arbitrarily large index set using the continuum vertex-union lemma.
  A general vertex-closure preservation claim is already as difficult as
  the negative main answer: attach a private triangle to each vertex of an
  arbitrary K4-free graph and start from the disjoint matching of its private
  edges. This explanatory observation was not added as a Lean theorem.
* Unbounded finite Ramsey palettes still do not give a coherent edge-bound
  function or an external-color saturation theorem.
* No universal positive-inertia/Gram representation or non-Archimedean
  geometric Ramsey assertion was established.
* A library search found no existing Folkman/countable-triangle-cover result
  resolving the main conjecture.

Spec.lean remains unchanged with its original sorry. No new proof submission
was made. No Lean build or solver is pending.

## Countable partial-coloring antichains on a covered graph (NEW, verified)

`Submission/CountablePartialAntichain.lean` compiles with an olean; log
`/tmp/countable-partial-antichain.log`. Namespace
`Erdos595CountablePartialAntichain`. All seven printed audits contain only
propext, Classical.choice, Quot.sound.

This formalizes the earlier informal forcing counterexample, and strengthens
it to show individual GLOBAL extendability of every condition.

For an arbitrary type I, vertices are N + (I x Bool). There are all root--
private edges; private pairs (i,s),(j,t) are adjacent iff i != j and s != t.
The graph has an explicit proper Fin 3 coloring, is K4-free, and is the union
of two bipartite (hence TF) spanning graphs: rootPiece and privatePiece.

`PartialColoring G` records a countable vertex domain, an ambient unordered-
pair coloring, and validity on domain triangles. `Extends q p` preserves
only colors of actual edges in p's domain and includes that domain.

`condition i` uses all roots and the two private vertices of fiber i.
Both spokes from root n have color n. Each domain is bipartite, so the
condition is valid. `domain_inter` proves the domains form a delta system
whose common root is precisely the independent set of roots. Moreover ALL
conditions use the SAME ambient color function, not merely root-agreeing
functions.

`incompatible`: for i != j there is no PartialColoring extending both
conditions. Given the color n on the required cross edge (i,false)--(j,true),
root n makes a monochromatic triangle. `condition_injective` exhibits
arbitrarily large pairwise incompatible families.

`condition_globally_extendable`: each condition separately extends to a
valid coloring of the ENTIRE graph. Keep spokes at fiber i colored n;
spokes to every other fiber receive n+1. All private edges receive 0.
A triangle whose private edge has color 0 either has two shifted spokes
(which are nonzero), or has two different spoke colors n,n+1. The two
private vertices cannot both be in fiber i because they would not be
adjacent. This is checked by `globalColor_valid` and `globalColor_agrees`.

Thus a naive chain-condition proof for countable partial colorings fails
even if conditions are restricted to those individually globally extendable,
and even when all delta-system root data agree. This is not an obstruction
to the existence of a cover: `ambient_covered` explicitly supplies one.
Finite-support partial-coloring forcing is a different issue; the large
antichain uses countably many roots and private vertices seeing all colors.

Rechecking fixed finite-factor reduced powers, third mutual-ultrafilter
towers, sparse second-arc full-pair patterns, and non-Archimedean geometry
produced no genuine main implication. In particular, a full-pair matching
bound without the target K4 condition also holds in second arcs of large
complete graphs, whose second-right targets contain the original complete
graphs. No universal covering theorem follows from that property alone.

The main conjecture remains unresolved. Spec.lean is unchanged; no new
proof submission was made. No builds or searches are pending.

## Minimal persistent wheels are INDUCED (NEW, verified)

`Submission/ShortestOddInducedCycle.lean` compiles with an olean; log
`/tmp/shortest-odd-induced-cycle.log`. Namespace
`Erdos595ShortestOddInducedCycle`. The four printed audits use only
propext, Classical.choice, Quot.sound.

General shortest-odd-walk results:
* `segment w i j` runs from w[i] to w[j], length j-i.
* `complement w i j` runs back around a closed w, length length(w)-j+i.
* `MinimalOdd G n`: every odd closed walk in G has length at least n.
* `distinct_of_minimal`: for an odd w with MinimalOdd G w.length,
  its vertices at distinct positions strictly below length(w) differ.
  Otherwise the two complementary segments are shorter loops, and their
  lengths sum to the odd number length(w).
* `no_chord_of_minimal`: a nonconsecutive edge between two rim positions
  closes both complementary segments. Both resulting loops are shorter,
  and their lengths sum to length(w)+2, again odd.
* `inducedCycle`, `inducedCycleLength`: these facts give an INDUCED graph
  embedding of cycleGraph n, using getVert at the positions in Fin n.
  This is stronger than merely proving IsCycle for the original walk.

Wheel lifting:
* `wheel n = coneGraph (cycleGraph n)`.
* `wheelEmbedding` adjoins the center to an induced cycle in its induced
  neighborhood. The neighbor property separates the center from every rim
  vertex and supplies all spokes.
* `minimal_neighbor` transfers absence of shorter ambient odd wheels to
  a minimal odd-walk bound in any subgraph neighborhood.
* `induced_wheel_in_subgraph`: if R has no odd wheel walk shorter than odd n,
  and H<=R has an n-wheel walk, there is an induced wheel n embedding into
  R whose edges all lie in H. The proof compares the same walk in the H
  and R neighborhoods. Its induced cycles use identical getVert labels.

Main strengthened reduction:
`minimal_induced_residual G hK hbad` gives covered E and odd n>=5 such that
R=G\E is K4-free and still non-covered, has no shorter odd wheel walks,
and EVERY covered D admits an induced wheel n embedding into R with
all wheel edges avoiding D. Crucially, the embedding is induced in the
SAME residual R before D is deleted, not just in R\D.

Scope: this is a necessary condition conditional on a non-covered graph.
It does not construct such a graph, and no contradiction from the robust
induced wheel was derived. The conjecture in Spec.lean remains unresolved.

The higher-cone review did not supply a lower bound for countable edge
colorings. HigherConeOddBound remains only a sufficient K4 exclusion,
not a transfer from high proper chromatic number to edge non-coverability.
Similarly, NegativeInner proves a countable TF EDGE cover, not a countable
proper VERTEX coloring; arbitrary-cardinality shift graphs prevent that
incorrect strengthening. No universal strict Hilbert triangle-hitting
assignment or new infinite-palette Ramsey construction was established.

Spec.lean is unchanged with its original sorry. No proof submission was
made in this continuation. No build or solver is pending.

## Four constraints suffice for arc common neighborhoods (verified)

FourDeterminedArcNeighborhoods.lean is complete; its olean and permitted-
axiom audits are recorded in /tmp/four-determined-arc.log. The general
four_constraints lemma handles intersections of two-coordinate equality
disjunctions. It yields arc_four_determined for every graph, and the bound
is sharp on the arc graph of K_{2,2} (Sharp.not_three_determined).

The exact universal_cover_iff_four_determined_rights reduction shows that
bounded finite determination of a right-adjoint BASE is not an easier
substitute for the original question. no_uniform_finite_palette supplies
finite Folkman obstructions even for finite bases with this bound and a
two-piece TF cover, while retaining K4-freeness of the full right adjoint.
These are reductions/limitations, not a proof or disproof of Erdos 595.
Spec.lean remains unchanged; no submission was attempted.

## Free-corner reduction added; no main solution

FreeCornerArrow.lean is verified (see ContinuationStatus.md for details).
Independent corner markings permit a three-colorable four-wheel as the blue
forcing target and a cone over a high-chromatic TF graph as the red target.
The necessary infinite corner-preserving K4-free asymmetric Ramsey host is
still missing. There is no proof or disproof in Spec.lean.

The same status file records three exploratory linear, Berge-triangle-free
ordered hypergraph templates on four-subsets and an unverified order-CSP
suggesting their shadow bases have K4-free rights. These are candidates only;
no countable edge-color lower bound or complete Lean construction exists.

## Verified no-prism finite-palette exclusion

NoPrismRightCover.lean proves that with unique triangles through edges and no
disjoint matched triangle pair, all right-adjoint triangles consist of stars.
Their centers map each such triangle to the base. NoPrismFinitePalette.lean
then transfers edge palettes unchanged and proves a UNIFORM Bool palette for
the right adjoint. Both files compile and have permitted-axiom audits.
See ContinuationStatus.md for the precise scope and for the unverified ordered
hypergraph applications. There is still no proof or disproof of Erdős 595.

## Simultaneous finite-tower compression obstruction (verified)

FiniteTowerCompressionObstruction.lean rules out a proposed general bridge
from finite-stage coverability to countable K4-free homomorphism targets.
Its `simultaneous_obstructions` example is initially countably properly
colorable, has no finite TF edge palette and no countable K4-free target,
but ALL finite mutual towers are countably TF edge-covered. It is a disjoint
union of a locally finite Folkman target and the earlier triangle-free
no-countable-target graph. `Split.every_tower_cover` supplies the preservation
argument, with only permitted axioms. See ContinuationStatus.md and
/tmp/finite-tower-compression.log. This leaves the generic third stage and
the original conjecture unresolved; Spec.lean is unchanged.

## Finite-rank folds and generic separation (verified)

FiniteRankUltrafilterFold.lean proves finite common-neighborhood determination
for exact finite-dimensional bilinear orthogonality representations, and upgrades
the fold to fix principal points. Its finite tower maps are actual retractions.
For signature (3,n) over arbitrary ordered fields, every finite mutual tower
has exactly the same countable-coverability status as its base. This does not
settle the base status for n>=3, including the unresolved (3,3) case.

GenericFiniteRankObstruction.lean proves that the countable generic K4-free
graph has no homomorphism into ANY K4-free finite-dimensional exact bilinear
orthogonality target. Restrict a hypothetical map to its countable image;
that image has finite common-neighborhood determination, so its UF extension
folds back into it. Functoriality would then map the first generic UF stage
into a countable K4-free target, contradicting NoCountableK4Target.

All five printed audits use only allowed axioms. Logs:
/tmp/finite-rank-ultrafilter-fold.log and
/tmp/generic-finite-rank-obstruction.log.
These are restrictions on a geometric route, not a settlement of Erdős 595.

## Palette localization (verified)

Submission/PaletteLocalization.lean now compiles; all three printed axiom
audits use only propext, Classical.choice, and Quot.sound.
`bijective_edge_coloring` gives a valid bijective coloring of an infinite
countable actual edge set. `in_supergraph` extends that coloring literally
along an induced embedding into any covered supergraph. Consequently the
fixed countable old graph can use every natural-number color.
`no_fresh_color_principle` makes the resulting obstruction to naive palette
exhaustion arguments explicit. This is not a solution of Erdős 595.
Log: /tmp/palette-localization.log. Spec.lean remains unchanged.

## Finite common neighborhoods plus independent extension (verified)

Submission/FiniteCommonIndependentExtension.lean compiles with an olean.
Namespace Erdos595FiniteCommonIndependent; log /tmp/finite-common-independent.log.
All five printed axiom audits use only propext, Classical.choice, and Quot.sound.

`finite_cover` proves, for arbitrary cardinality, that a K4-free graph has a
FINITE triangle-free edge cover if it satisfies BOTH:
* FiniteCommonNeighbors (every common neighborhood is finitely determined);
* FiniteIndependentExtension (every finite independent set has a common neighbor).
There is no asserted uniform finite bound.

`independent_extension` upgrades finite requests to arbitrary independent sets
using finite determination. `countable_finite_cover` applies the existing
no_countable_target theorem with the graph itself as source and target.
For arbitrary carriers, `countable_witness` reflects failure of finite covering
to a countable induced subgraph by FINITE-palette compactness.
`countable_extension_hull` closes a countable set under chosen witnesses for
finite independent requests. `finite_common_induce` preserves finite determination
under induced subgraphs, so the countable theorem applies to the hull.
Helpers: countable_closed_superset and finite_cover_of_coloring.

This completes the previously unformalized observation, even at arbitrary
cardinality. It does NOT give either extra hypothesis for arbitrary K4-free
graphs or establish a witness to the main conjecture. The signature (3,3)
base and generic third mutual-U stage remain unresolved.

Other reviews of infinite bipartite/partite Ramsey amplification, generic
exponentials, graphical hypergraph realization, and external-color saturation
gave no additional theorem. Web access still fails DNS. Spec.lean is unchanged
with its original sorry; no proof/disproof was submitted.

## Infinite interval incidence and whole-ray Ramsey hosts (verified)

Submission/IntervalBipartiteRamsey.lean compiles with an olean. Namespace
Erdos595IntervalBipartite; log /tmp/interval-bipartite-ramsey.log. All four
printed axiom audits use only propext, Classical.choice, and Quot.sound.

`ramsey` gives induced, side-preserving bipartite Ramsey hosts for arbitrary
palettes and point-interval incidence targets of arbitrary cardinality.
The target has left data lo,hi : L -> A and right data point : R -> A, with
Adj(l,r) iff lo(l) < point(r) < hi(l). A is well ordered; interval endpoint
pairs and right points are injective. The two-coordinate pair_box theorem
from InfiniteBipartiteRamsey supplies the host intervalGraph B D.
`step` transfers this to a K4-free free-amalgamation extension.

`ray_ramsey` specializes to the WHOLE one-way infinite path on N+N with
edges L_i--R_i and L_i--R_(i+1). Use intervals (4i,4i+7) and points 4j+2.
This is stronger than finding finite paths of every length. `ray_step`
homogenizes a designated induced infinite ray inside a K4-free extension.
The implementation reconstructs an embedding across interval_ray_eq; plain
simp does not rewrite the dependent embedding type in this existential.

Scope: this is a two-coordinate positive infinite-target theorem, not a
general finite-coordinate theorem for all representations and not an arbitrary
infinite bipartite Ramsey theorem. It does NOT solve the separate compatibility
problem at infinitely many partite stages. Continuous bipartite amalgamations
remain covered by the earlier theorem. The required infinite asymmetric
free-corner/ordered-triangle host is still missing.

Other review revisited canonical filters, external-color saturation, triangle
hypergraph developments, binary-cube amplification, and long apex towers.
No further mathematical implication was established. In particular the
arithmetic-progression labeling shortcut already has its earlier conditional
finite Ramsey obstruction; it was not assumed here. Spec.lean remains
unchanged with its original sorry. No proof/disproof was submitted.

## Boundary-based prescribed extension (verified)

BoundaryPrescribedExtension.lean is audited with permitted axioms; see
ContinuationStatus.md and /tmp/boundary-prescribed-extension.log.
Literal extension only requires a countable proper coloring of the old
boundary (indeed, only separation of old adjacent pairs sharing a new
neighbor). Its amalgamation corollary removes the triangle-free-base
assumption from the countably properly vertex-colorable base theorem.
No countable-palette obstruction or main solution follows. Spec.lean
remains unchanged with its original sorry.

## Transfinite boundary-amalgamation corollary (verified)

TransfiniteBoundaryAmalgamation.lean is complete and audited with permitted
axioms; /tmp/transfinite-boundary-amalgamation.log. It removes the
triangle-free-base field from the continuous well-ordered amalgamation
preservation theorem when each base is countably properly vertex-colorable.
Arbitrary attaching sets are allowed. This excludes that broader class of
presentations as a route to a witness; it does not show arbitrary K4-free
graphs have such a presentation. No main proof or disproof was obtained.

## Ordered-quadruple right adjoint: verified K4-free but finitely covered

The second matched-pair pattern ((0,2),(1,5),(3,4)) has now been fully checked.
OrderedQuadRight and OrderedQuadNoArc (with six generated certificate modules)
prove K4-freeness of its full biclique right adjoint over every linear order.
OrderedQuadProperties proves unique triangles through edges and an explicit
prism over Fin 8, so the older NoPrism criterion does not apply to this pattern.

Nevertheless OrderedQuadShapes and OrderedQuadFiniteCover give a UNIFORM
256-color triangle-avoiding edge palette for that full right adjoint. The key
FirstStar bit concerns an ENTIRE biclique side having constant first coordinate,
not only its selected witnesses. A sliding-pair common-neighbor lemma controls
all side vertices. The same theorem on OrderDual A covers the reversed third
matched-pair pattern. finite_representation_failure uses finite Folkman to show
that the family cannot be universal even for all finite K4-free sources.
All aggregate axiom audits are permitted. Details and logs are recorded in
ContinuationStatus.md. This is a verified candidate exclusion, not a settlement
of Erdős 595. Spec.lean remains unchanged with its original sorry, and no proof
submission was made. No build or solver is pending.

## Canonical edge and triangle completeness obstruction (NEW, verified)

CanonicalEdgeCompletenessObstruction.lean, namespace
Erdos595CanonicalEdgeCompleteness, compiles cleanly. All audited results use
only propext, Classical.choice, Quot.sound. Log:
/tmp/canonical-edge-completeness.log.

The complete graph on P(Nat -> Fin 2) has a proper canonical avoiding edge
filter. Both endpoint marginals have continuum-successor completeness, but
the edge filter does not: continuum many individual coordinate agreements
would identify the endpoints of an actual edge. The canonical triangle
coupling likewise has all three vertex marginals with stronger completeness,
yet cannot itself have that completeness, since its edge marginal is exactly
the preceding edge filter.

This example is explicitly proved NOT K4-free. It does not solve Erdos 595
or disprove a K4-free-specific completeness assertion. It shows that the known
marginal completeness, even together with the canonical edge/triangle coupling
identities and countable completeness, cannot alone justify the upgrade.

No new construction of the infinite asymmetric Ramsey host, no lower bound
for a remaining exponential or ultrafilter candidate, and no universal covering
theorem was obtained. Spec.lean remains unchanged with its original sorry.

## Arbitrary-field algebraic orthogonality route completed (verified exclusion)

See the latest ContinuationStatus.md entry. AllFieldOrthogonalityCover now
covers EVERY finite-dimensional nonisotropic bilinear representation over
EVERY field, using actual linear disjointness of private algebraic supports
and specialization into countable algebraically closed root extensions.
Thus earlier notes treating arbitrary-field signature (3,3) as open candidates
are superseded. DiagonalPositiveIndexCover also handles finitely many positive
coordinates and arbitrary finitely supported negative coordinates over ordered
fields. No universal representation or main proof/disproof was obtained.

## Finite Ramsey host for the Paley margin obstruction (NEW, verified)

FiniteInducedRamsey.lean proves a finite induced binary edge-Ramsey host
for EVERY finite K4-free target, by the existing finite partite construction.
The ordinary Ramsey input is Combinatorics.Diagonal.hasRamseyProperty_choose,
which is available via the original import. No infinite-target or
countable-palette inference is made.

PaleyRamseyMargin.lean uses this to provide the previously missing finite
red-Paley17 / blue-triangle Ramsey host. Consequently there exists a finite
K4-free graph with no unit-vector triangle-hitting assignment at uniform
threshold -1/3 in any real Hilbert space. This strengthens the earlier
conditional vector obstruction to an unconditional finite one, but it is
NOT a noncovered graph and does not settle Erdős 595. Strict variable
negative margins and smaller uniform negative margins remain separate.

Clean logs: /tmp/finite-induced-ramsey.log and /tmp/paley-ramsey-margin.log.
Axiom audits: propext, Classical.choice, Quot.sound only. Main conjecture
unchanged with sorry; /tmp/spec-finite-ramsey-margin-review.log.
