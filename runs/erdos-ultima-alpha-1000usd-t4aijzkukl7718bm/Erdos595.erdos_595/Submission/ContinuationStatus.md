# Current continuation status

The conjecture in Spec.lean is still unresolved. The original file and its
sorry are unchanged (SHA256 de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45).
One submit_proof call with this unresolved state was rejected; the user then
explicitly instructed continued work. Do not call it a successful submission.

## Verified completion this continuation

SmallMarkedSecondRightCover.lean now compiles with olean. The only pending
error was its local subtype annotation, now:
  let S : Set {p : P H // ¬Pure H m p} := {p | Good H m p.val}

Main theorem second_right_cover uses an independent marked triangle transversal,
with no three distinct independent neighbors at each marked vertex lying in a
triangle. It proves countable TF edge coverability of right(right H).

Added and audited:
* conditions_of_degree_three
* second_right_cover_of_degree_three
No matching-neighborhood hypothesis is needed for these covering results.
All axiom audits are permitted; log /tmp/small-marked-second-right.log.
This excludes the entire degree-three independent-apex family as witnesses.

Earlier verified IndependentPairCover, PairAnchorSAT, PairAnchorPattern and
RightCoverReduction remain intact. Their results and the new completion were
appended to UltrafilterNotes.md (now over 8300 lines).

## New exact computational tests, not Lean certificates

1. Independent supports of size at most 3:
   /tmp/independent_support_K4.py finds arc(K4) -> P_3(B), even with B
   triangle-free and C4-free. Extracted B is Petersen minus a vertex.
   /tmp/supportK4_3_5.json and log. No-five/No-seven and bipartite variants
   were UNSAT. Under NoFive this cannot yield a witness anyway: arbitrary
   support graphs map to right(cone B), and their rights to the already
   two-covered second cone right. No support-size restriction needed.

2. Second rights of finite cones:
   C7: R1=32, R2=356, 11575 edges, 3332 triangles. Exact-one triangle marking
   UNSAT; weak Boolean triangle marking SAT; rainbow 3-labeling UNSAT.
   C9: R1=40, R2=456, 15043 edges, 4248 triangles. Exact-one SAT; weak Boolean
   SAT; rainbow 3-labeling UNSAT.
   Scripts /tmp/second_cone_exact_test.py and second_cone_profile_test.py.
   Both have the same 4-bit Pure presence triangle profile list:
     (0,6,9), (1,1,6), (2,2,9), (4,4,9), (6,8,8).
   Thus a marking depending only on that coarse profile fails even for C9.

3. Longer arc^3(K4) -> cone(C7) search returned UNSAT, superseding the old
   timeout. /tmp/arc3K4_coneC7_long.out; original CNF same stem without _long.
   This is not yet a kernel certificate or a Lean K4 theorem.

4. Third right over cone(C7) has 110528 completed bicliques, enumerated in
   /tmp/cone_third_C7_concepts.json by /tmp/cone_third_count.py.
   Its small-side restriction (one side of size <=2, nonempty) has 2444
   vertices, 242744 edges, 65072 triangles, and 23884 triangle-bearing edges.
   A two-edge-coloring was found. This says nothing about the FULL third right.
   Artifacts /tmp/cone_third_C7_small2.{bin,cnf,out}; scripts
   /tmp/cone_third_small_data.py and /tmp/cone_third_small.cpp.

All jobs have finished. No active solver or Lean build is pending.

## Still missing

A genuine K4-free non-covered graph, or a universal covering theorem.
The many candidate exclusions are NOT a disproof of the existential.

The most recent mathematical review revisited infinite asymmetric triangle
Ramsey construction, saturation with external colors, canonical-filter fusion,
finite-template functors, collinearity labels, and well-order/local-neighborhood
covering. No new main lemma was proved.

Important observations not to promote to theorems:
* A well-order with all earlier neighborhoods countably properly colorable
  would suffice for a universal negative answer; no such order was constructed.
* Rich uncolored saturation does not make an arbitrary edge coloring internal.
* Large chromatic profile fibers can be selected, but their countable nested
  intersection need not retain chromatic size.
* A focusing pair A*B with A independent, B TF high-chromatic, and common
  edge-color profiles on A makes B's edges avoid the profile colors. Adding a
  new common apex over B does NOT force a fresh color: it may reuse an old
  profile color, and connecting it to the old A would create K4s.
* Simply connected flag two-complexes need not have triangle-free distance
  spheres. Subdividing two incident edges of an octahedron yields a finite
  counterexample to that shortcut.
* Universal fixed-positive-index orthogonality representation was not proved;
  neither finite clique number nor finite feasibility justifies it.

Web DNS was unavailable. /opt contains only Pantograph docs. No relevant
preexisting Mathlib theorem was found by the latest search.

## Later verified improvement

SmallMarkedFinitePalette.lean now compiles and is audited (log
/tmp/small-marked-finite-palette.log). The whole independent-pair family,
and then the small-marked second-right family, have one UNIFORM FINITE
edge palette, not merely a countable one. Finite Folkman therefore proves
finite_representation_failure: some finite K4-free G has no hom
arc^2 G -> H for ANY H satisfying the small-marked Conditions.
This excludes the flexible degree-three universal representation approach.
The previous few finite SAT successes do not generalize.
No change to Spec.lean and no main solution was obtained.

## Latest continuation: robust fixed odd-wheel length

RobustOddWheel.lean now compiles with olean and permitted axiom audits:
  /tmp/robust-odd-wheel.log
Namespace Erdos595RobustOddWheel.

Main auxiliary theorem fixed_odd_length_ge_five says: for a K4-free graph G
without a countable TF edge cover, there is an odd n>=5 such that G\D has a
closed n-step walk in a vertex neighborhood for EVERY coverable edge graph D.
This is a wheel WALK, not necessarily a simple or induced wheel.
Proof uses countable deletion and the local bipartite covering criterion.
It does not rely on infinite filter coupling. No contradiction from the
persistent wheel, or K4-free example satisfying it, has been proved.

The main conjecture is still unresolved; Spec.lean remains unchanged.
No proof submission was made in this continuation. No builds are pending.

## Latest continuation: minimal persistent residual

MinimalRobustOddWheel.lean compiles cleanly with olean and permitted axioms;
log /tmp/minimal-robust-odd-wheel.log.
Namespace Erdos595MinimalRobustOddWheel.

minimal_residual: a hypothetical K4-free non-covered G has a covered deletion
E and an odd n>=5 such that R=G\E is still K4-free/non-covered, every covered
deletion from R leaves an n-step rim walk in some neighborhood, and R has no
shorter odd rim walks. The proof minimizes the previous persistence result
and deletes the countable family of smaller-length obstructions. It is still
conditional, and still uses walks rather than simple/induced rim cycles.

No genuine witness or universal cover theorem was obtained. Further finite-
bound, closure, exponential, arc/right-tower and algebraic discussions yielded
no main lemma. Spec.lean is unchanged; no new submission was attempted.
No build is pending.

## Latest continuation: countable partial-coloring antichains

CountablePartialAntichain.lean is complete and audited, with olean and log
/tmp/countable-partial-antichain.log. All printed audits use only permitted
axioms. Namespace Erdos595CountablePartialAntichain.

For ANY index type I, graph I has roots r_n and private pairs a_i,b_i.
Roots are independent and adjacent to every private vertex. The private
edges a_i--b_j occur precisely when i != j. This is three-colorable and has
an explicit TWO-piece triangle-free edge cover.

condition i is a valid countable partial coloring on all roots plus a_i,b_i;
both spokes at root r_n receive n. The domains form a delta system with
common root exactly the independent set of all r_n. All conditions use the
SAME ambient color function, so agreement on overlaps is literal.

incompatible: distinct conditions have no common extension (not just no
extension on their union). The color of a_i--b_j chooses the obstructing
root. condition_injective gives an arbitrarily large family of such
conditions. condition_globally_extendable: EACH individual condition has
a valid coloring of the ENTIRE ambient graph extending it. Explicitly,
shift all spokes outside the selected pair from n to n+1 and color private
edges 0. Thus restricting to globally extendable conditions does not repair
the failed chain-condition argument.

This formalizes the previous informal forcing obstruction, with the new
individual global-extendability strengthening. It is NOT a disproof of
Erdos 595: ambient_covered proves the graph is already covered.

Further review of reduced powers, third mutual ultrafilter extensions,
geometric representations and sparse second-arc full-pair normal forms
found no missing main implication. The graph full-pair matching property
also holds for arc^2 of complete graphs and cannot alone imply coverage.
Spec.lean remains unchanged with its original sorry; no proof or disproof
has been obtained. No proof submission was made in this continuation.

## Latest continuation: persistent INDUCED odd wheels

ShortestOddInducedCycle.lean is complete and audited, with olean and log
/tmp/shortest-odd-induced-cycle.log. Namespace
Erdos595ShortestOddInducedCycle. All four printed audits use only the
permitted axioms.

New general lemmas construct the two complementary segments of a closed
walk. distinct_of_minimal and no_chord_of_minimal show that a globally
shortest odd closed walk has neither repeated rim vertices nor chords:
cutting at a repetition/chord produces two shorter closed walks whose
length sum is odd, hence one is odd. inducedCycle and inducedCycleLength
package this as an induced embedding of cycleGraph n.

wheel n is coneGraph (cycleGraph n). induced_wheel_in_subgraph says that
if R has no shorter odd wheel walks, an n-wheel walk in ANY H <= R yields
an induced wheel embedding INTO R with all wheel edges in H. In particular,
inducedness is in R BEFORE the additional edge deletion, not merely in H.

minimal_induced_residual strengthens the existing minimal_residual:
there exist covered E and odd n>=5, R=G\E still K4-free and non-covered,
with no shorter odd wheel walks, and for EVERY covered D an induced
wheel n embedding into R whose every edge avoids D.

This is a conditional necessary condition, NOT a contradiction and NOT a
construction of a non-covered graph. The original conjecture remains
unresolved and Spec.lean is unchanged with its original sorry.

Other review in this continuation: fixed-stage higher cones have the
verified finite odd-walk sufficient K4 bound, but no countable edge-color
lower bound was obtained. Do not infer one from high proper chromatic
number of the cone base. Hilbert negative-inner-product graphs are known
here to have countable TF EDGE covers, not countable proper VERTEX colors;
ordered shift graphs show why the latter would be false. No new universal
Hilbert representation, Ramsey host, or coherent bound assignment was proved.
No proof submission was made and no build or solver is pending.

## Further review after the induced-wheel continuation

No new proof of the main implication was obtained, and no new auxiliary Lean
result was added in this review. Spec.lean remains unchanged.

Revisited persistent induced wheels, the canonical ordered-triangle filter,
finite and infinite bipartite Ramsey steps, higher cone rights, and
countable-target exponentials. The precise gaps in these routes remain:
* persistence of an induced odd wheel is not contradictory to K4-freeness;
* finite-stage homogenization does not supply a simultaneous infinite host;
* exact finite filter marginals do not supply an infinite thread;
* high chromatic number of a cone base has not been transferred to triangle
  edge non-coverability of its higher right adjoints.

The non-Archimedean geometric idea was checked against existing files rather
than asserted as new. IndefiniteUnitOrthogonality already proves the positive-
index clique bound over arbitrary ordered fields. IndefiniteFiveCover already
excludes signature (3,2), also over arbitrary ordered fields. No lower-bound
argument for larger negative index or universal representation was found.

No proof submission was made. The main-file check is recorded in
/tmp/spec-continuation-review.log and retains the original sorry warning.

## New verified continuation: four-determined arc neighborhoods

Submission/FourDeterminedArcNeighborhoods.lean compiles with olean; log
/tmp/four-determined-arc.log. Namespace Erdos595FourDeterminedArc. All seven
printed axiom audits use only propext, Classical.choice, Quot.sound.

four_constraints: for arbitrary f : I -> A and g : I -> B, every family
of clauses f(x)=a OR g(x)=b is determined by at most four members of the
family. If two constraints differ in both coordinates, their conjunction
leaves at most two candidate pairs, each requiring at most one further
constraint. Otherwise the family is a star in one coordinate, and at most
two constraints suffice.

BoundedCommonNeighbors G n retains the determining finite set inside the
original defining set. arc_four_determined proves this property with n=4
for arcGraph G, for EVERY G. arc_finiteCommonNeighbors supplies the existing
unbounded finite-determination property as a consequence.

Sharp.not_three_determined proves that four cannot be replaced by three,
even for arcGraph of the four-vertex complete bipartite graph. Its four
rectangle constraints each have a witness satisfying exactly the other
three. Sharp.bipartite explicitly confirms that this example is covered,
not an Erdos 595 witness.

universal_cover_iff_four_determined_rights shows that restricting the BASE
of a full K4-free right adjoint to four-determined common neighborhoods
leaves a question equivalent to the original universal covering assertion.
It uses the existing exact arc/right cover and four-clique round trips.

no_uniform_finite_palette uses finite Folkman: for every finite palette C
there is a FINITE, four-determined base H, itself with a two-piece TF edge
cover, for which right H is K4-free and has no valid C edge coloring. Thus
one may not infer a uniform finite palette from the bound four.

No cover theorem for all finitely determined K4-free graphs, no countable
palette theorem for their right adjoints, and no genuine non-covered witness
was obtained. The original Spec.lean remains unchanged with its sorry.
No proof submission was made.

## New verified continuation: free-corner four-wheel reduction

`Submission/FreeCornerArrow.lean` compiles with olean; log
`/tmp/free-corner-arrow.log`. Namespace `Erdos595FreeCorner`, 170 lines.
All four printed axiom audits use only permitted axioms.

`Marking G` selects exactly one corner of every triangle (up to swapping the
other two vertices), with validity, symmetry, totality, and uniqueness.
`Different M col` requires the two edges incident at the selected corner to
have different colors.

`coneMarking B hB` selects the cone apex on every triangle when B is TF.
`cone_different_gives_coloring` turns a Different edge coloring into a proper
vertex coloring of B, using spoke colors. `exists_red_target C` therefore
gives, for ANY palette C, a marked K4-free graph with a TWO-piece TF edge
cover but no Different C edge coloring. This is simpler than the red target
needed for ordered middle corners.

`W` is the four-wheel with apex 0 and rim cycle 1--3--2--4--1. It is properly
three-colorable (`wheelColoring`) and K4-free (`wheel_cliqueFree`). Its four
triangles select corners as follows:
  (0,1,3) at 0; (0,1,4) at 0; (0,2,3) at 0; (0,2,4) at 2.
`wheel_forces_mono` proves, for any palette C, that equality at these four
selected corners forces the triangle (0,2,4) to be monochromatic.
This marking is NOT an ordered-middle marking; do not insert it into the
old ordered TriangleArrowReduction.

`MonoCopy` is induced and corner-preserving. `Arrow M N` quantifies over
Boolean corner colorings symmetric in the last two vertices, and asks for
a red copy of M or a blue copy of the marked four-wheel.
`no_cover_of_arrow` proves the genuine sufficient condition, but NO K4-FREE
HOST WITH THIS ARROW PROPERTY HAS BEEN CONSTRUCTED. The main conjecture is
still unresolved. Spec.lean is unchanged with its sorry. No proof submission
was made.

## Exploratory ordered hypergraphs — NOT Lean-verified

Three temporary Python scripts were used:
  /tmp/corner_patterns.py
  /tmp/arc_hypergraph_test.py          log /tmp/arc-hypergraph-test.log
  /tmp/order_arc_hypergraph.py         log /tmp/order-arc-hypergraph.log
All searches have finished; the background processes are defunct, not pending.

Construction: vertices are increasing FOUR-element subsets of a linear order.
Fix a partition P,Q,R of {0,...,5} into pairs. Each increasing six-tuple gives
a hyperedge consisting of the three four-subsets obtained by omitting one
of P,Q,R. Every pair of hypergraph vertices determines at most one hyperedge.
The following three partitions have no Berge triangles in the exact finite
check on 8 points:
  ((0,2),(1,4),(3,5))
  ((0,2),(1,5),(3,4))
  ((0,4),(1,2),(3,5)).
Eight points suffice for that check informally: a Berge triangle consists
of three four-subsets with pairwise intersection of size two, so their union
has size at most eight. There is NOT YET a Lean formalization of this bound
or of the finite enumeration.

Their shadow graphs F are consequently plausible locally-matching type
bases. Infinite ER on four-tuples would make their VERTEX triangle chromatic
numbers arbitrarily large; this has not been formalized for these patterns.
This is NOT edge non-coverability: each F has a finite edge cover by pair type.

A finite-order CSP for a hom arc(K4) -> F found NO hom for all three patterns.
The CSP assumes all shadow triangles are the designated hyperedges, assigns
one of six role permutations to each of the eight triangles of arc(K4),
then one of six pair types to each of its six reversal edges. Equalities
are merged and cycles of strict inequalities rejected. It explores roughly
1700--1800 states per pattern. This suggests right F is K4-free, but the
CSP and its reduction are NOT a Lean proof. No lower bound for edge colorings
of right F was obtained.

Further limitation: the first pattern has no disjoint matched triangle pair
in the finite check up to 10 points. The second and third do have triangular
prisms. For the second pattern, one example is
  [(1,3,4,7),(0,2,3,4),(0,1,2,7)]
matched in that order to
  [(1,4,5,6),(0,1,2,6),(0,2,4,5)].
There can be arbitrarily many matching partners in finite samples. A typical
six-tuple (a,b,c,d,e,f) has partners (a,b,c,e,u,v) with e<u<v<f, suggesting
an anchored shift/interval structure rather than immediate non-coverability.
A possible finite-cut/finite-parameter covering argument for these rights
was discussed but NOT proved.

Do NOT assert the tempting unproved transfer
  right F countably TF-edge-coverable => F has bounded vertex-triangle colors.
Even if the new bases have unbounded vertex-triangle chromatic number, that
alone provides no obstruction to edge covering of their right adjoints.

## New verified continuation: prism-free right adjoints have TWO edge colors

`Submission/NoPrismRightCover.lean` and `Submission/NoPrismFinitePalette.lean`
compile with oleans. Logs:
  /tmp/no-prism-right.log
  /tmp/no-prism-finite.log
Namespaces:
  Erdos595NoPrismRight
  Erdos595NoPrismFinitePalette
All eight printed axiom audits use only propext, Classical.choice, Quot.sound.

`NoPrism H` excludes two DISJOINT triangles joined by three matching edges;
the prism need not be induced. `UniqueTriangleEdge H` is the existing property
that adjacent vertices have at most one common neighbor.

`matched_equal_of_overlap`: under UniqueTriangleEdge, two matched triangles
that overlap have the same vertex set. The proof checks the nine possible
shared vertices, using common-neighbor uniqueness twice in each nontrivial
case. Therefore `matched_equal` says every matched triangle pair is identical
when NoPrism also holds.

A non-star biclique then has independent sides. `triangle_star` uses the six
witnesses of a right-adjoint triangle to show every one of its vertices is a
star: otherwise the equal witness triangle sets force a loop on a matching
edge. `centers_adj` shows that centers of stars on a right triangle form a
triangle in H. This need not hold for edges outside triangles, and no global
homomorphism from the star subgraph to H is claimed.

`cover_of_star_triangles` transfers a countable edge palette from H when all
right triangles consist of stars. `right_cover` combines this with the
countable-common-neighbor criterion for UniqueTriangleEdge bases.

The companion finite-palette file strengthens this to a UNIFORM TWO-color
result. `base_two` colors each edge by whether its unique triangle completion
is earlier than both endpoints in an arbitrary vertex order. For a sorted
triangle, its first edge is false and its last edge is true.
`star_palette` transfers ANY nonempty palette unchanged, not just N.
`right_two` proves HasColoring (right H) Bool from UniqueTriangleEdge + NoPrism.
`finite_representation_failure` uses finite Folkman to exhibit a finite
K4-free G whose arc graph cannot map to ANY such base H (of any size).
Thus this class is not a universal replacement for the main problem.

## Further exploratory computations (not Lean proofs)

`/tmp/prism_order_patterns.py` uses the finite-order CSP to test matching
between two designated six-tuple triangles in the ordered hypergraph bases.
It found no DISTINCT prism for the FIRST pattern
  ((0,2),(1,4),(3,5))
(412 explored states), and a prism for the SECOND. The new Lean theorem would
exclude the first pattern's right adjoint IF its unique-triangle and no-prism
properties are formalized. No Lean file defining these ordered bases has
been written, so do not claim that application as verified.

`/tmp/right_hypergraph.py`, log `/tmp/right-hypergraph.log`, enumerates maximal
ordered bicliques using common-neighbor closure and tests arc(K4) homomorphisms
into the finite right adjoints. For the first two patterns, it found none for
index orders of size 6 through 10. At size 10 the right carriers have 1030 and
876 vertices, respectively. This is only a finite sample. In particular it
does NOT establish K4-freeness of their full SECOND right adjoints, much less
non-coverability. All searches are finished; no solver is pending.

An informal possible explanation for the second pattern's first-right
coverability: its observed prisms match the two triangle triples using only
the pair type with equal first coordinate. One of the resulting bicliques
may be forced to stay entirely in that type. This has NOT been proved and
must not be used as a covering theorem.

The public problem page was retried via curl, but DNS is still unavailable.
No external result was obtained. The conjecture in Spec.lean remains unresolved
and unchanged with its sorry. No proof submission was made.

## Further second-right and prescribed-extension review

No new proof or disproof of the conjecture was obtained in this review.
The exact sparse second-right normal form was rechecked, including the
independent marking and unique reversal partners. None of these properties
supplies the missing cover of the full second right under its K4 hypothesis.
The previously proved bounded-internal-fiber criteria require extra hypotheses.

The one-vertex prescribed-color extension route was also rechecked against
AdaptedLimitObstruction and AdaptedReflectionObstruction. The former already
provides a triangle-free graph with a fixed countable edge coloring having no
adapted labeling. A valid literal extension of that coloring to its cone would
supply such a labeling via the spoke colors, so universal literal one-vertex
extension is unavailable. This is not non-coverability: the cone has a two-piece
cover after recoloring. The latter file separately prevents assuming that
failure of global adapted labeling reflects to a triangle-free induced subset.

No new Lean result was asserted, no proof submission was made, and Spec.lean
remains unchanged with its original sorry. The latest main-file check is
/tmp/spec-second-right-extension-review.log.

## New verified continuation: exponential target distinction

Two new files compile with oleans, and all eight printed axiom audits use
only propext, Classical.choice, and Quot.sound:

* Submission/LocallyFiniteFolkmanTarget.lean
  Namespace Erdos595LocallyFiniteFolkmanTarget.
  Log /tmp/locally-finite-folkman-target.log.
  H is the disjoint union of the existing finite universal K4-free targets.
  It is countable, locally finite, and K4-free. `finite_universal` embeds
  every finite K4-free graph into H. `no_finite_palette` uses finite Folkman
  to rule out every finite triangle-free edge palette of H.
  Nevertheless `all_exponentials_covered` proves that exponential H B is
  countably triangle-free edge-coverable for EVERY domain B satisfying
  the uncountable proper-chromatic hypothesis, by the existing locally
  finite target criterion. Thus full finite age and unbounded finite edge
  palettes alone cannot yield the desired exponential lower bound.

* Submission/GenericTargetLocalObstruction.lean
  Namespace Erdos595GenericTargetLocal.
  Log /tmp/generic-target-local-obstruction.log.
  The ordered shift on N has no finite proper vertex palette, by the
  existing injection into the power set of a proposed palette.
  Its cone embeds in the countable generic K4-free graph. Consequently
  `generic_neighborhood_unbounded` gives a generic vertex whose neighborhood
  has no finite proper vertex coloring.
  `no_hom_locally_finitely_colorable` rules out a homomorphism from the
  generic graph to ANY target whose neighborhoods all have finite proper
  colorings, regardless of cardinality. In particular `no_hom_locally_finite_target`
  rules out compression to the new locally finite target with the same
  finite K4-free age.

These are target restrictions, NOT an exponential non-coverability proof.
Generic-target exponentials with general triangle-free uncountably chromatic
domains remain unresolved. No new theorem about all such exponentials, no
asymmetric infinite Ramsey host, and no settlement of Erdős 595 was obtained.
Spec.lean is unchanged with its original sorry, and no proof was submitted.

## Finite-tower compression implication disproved (verified auxiliary result)

Submission/FiniteTowerCompressionObstruction.lean compiles with olean.
Log: /tmp/finite-tower-compression.log. Both printed axiom audits use only
propext, Classical.choice, and Quot.sound.

Namespace Erdos595FiniteTowerCompression.
`simultaneous_obstructions` constructs a K4-free graph G such that:
* G has a proper countable vertex coloring;
* G has no finite triangle-free edge palette;
* G has no homomorphism into ANY countable K4-free graph;
* EVERY finite mutual-ultrafilter tower over G is countably triangle-free
  edge-coverable.

The construction is the disjoint union of the countable locally finite
Folkman target and the previously verified triangle-free, countably properly
colorable graph with no countable K4-free target. The helper Split structure
records a closed triangle-free vertex part and a complementary part mapping
into a fixed locally finite target. `Split.next` transports this structure
through a mutual ultrafilter extension: supported points retain triangle-
freeness, while nonsupported points map to the locally finite target via
principal collapse. `Split.every_tower_cover` iterates it.

Consequently the absence of finite edge palettes and countable K4-free
homomorphism targets does NOT, even together with initial countable proper
colorability, force a finite ultrafilter-stage obstruction. A successful
argument for the particular generic base must use more of its structure.
This theorem is NOT a proof or disproof of Erdős 595.

Other discussion of saturation, higher cones, generic exponentials,
infinitary Ramsey constructions, algebraic hypergraph realizations, and
recoloring produced no additional theorem settling the conjecture. The
public reference page remains unreachable (DNS failure). Spec.lean remains
unchanged with its original sorry. No proof submission was attempted.

## Finite-rank orthogonality and generic-target obstruction (verified)

Two new files compile with oleans; all five printed axiom audits use only
propext, Classical.choice, and Quot.sound.

1. Submission/FiniteRankUltrafilterFold.lean
   Namespace Erdos595FiniteRankFold.
   Log /tmp/finite-rank-ultrafilter-fold.log.
   `finite_common`: any exact finite-dimensional bilinear orthogonality
   representation gives FiniteCommonNeighbors. Neither nondegeneracy nor
   injectivity of the vector map is required. A finite generating subset of
   the span of the requested vectors determines all the orthogonality equations.
   `foldHom` refines the existing finite-common-neighborhood fold to FIX all
   principal ultrafilters. `retract` proves that towerFold is a genuine
   retraction along the iterated principal embedding.
   `tower_cover_iff` gives equality of the covering status of every finite
   mutual tower and its base. `unit_tower_cover_iff` applies to signature
   (3,n) over every ordered field, regardless of cardinality or Archimedeanness.
   IMPORTANT: neither side is proved for n>=3. In particular this is NOT a
   covering theorem or a non-coverability theorem for signature (3,3).

2. Submission/GenericFiniteRankObstruction.lean
   Namespace Erdos595GenericFiniteRank.
   Log /tmp/generic-finite-rank-obstruction.log.
   `no_hom`: the countable generic K4-free graph cannot map into ANY K4-free
   graph with an exact finite-dimensional bilinear orthogonality representation,
   even over an arbitrarily large field. Restrict a proposed map to its countable
   image, fold the ultrafilter extension of that image, and contradict the known
   no-countable-K4-target theorem for the first generic mutual extension.
   `no_hom_unit`: applies to every signature (3,n) over any ordered field.
   Thus these finite-dimensional targets cannot receive the countable generic
   graph even non-inducedly. Do not infer that they themselves are covered.

No new countable-palette Ramsey obstruction was obtained from signature (3,3).
Speculation about ordered-field valuation/building arguments, stable or algebraic
relations, binary Ramsey cubes, and group or matroid constructions supplied no
additional theorem. None may be treated as established. The original conjecture
is unresolved; Spec.lean retains its original sorry and imports unchanged.
No proof submission was made in this continuation.

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

BoundaryPrescribedExtension.lean compiles with olean; all four printed
axiom audits use only propext, Classical.choice, Quot.sound. Log:
/tmp/boundary-prescribed-extension.log. Namespace Erdos595BoundaryExtension.

exists_extension and along_embedding require only a natural-number labeling
of old vertices that separates adjacent old pairs with a common neighbor
outside the old copy. along_boundary derives this from a countable proper
vertex coloring of the induced old boundary. The rest of the old graph need
not be countably properly colorable. Existing old colors are preserved
literally, including on nonedge unordered pairs.

amalgamation extends every valid coloring of a distinguished copy across
any free amalgam with a countably properly vertex-colorable base. Unlike
the older BipartiteAmalgamationExtension result, the base need NOT be
triangle-free. All neighbors of a private distinguished vertex remain in
that copy, so only the attaching set belongs to the old boundary.

This is a preservation/exclusion theorem, not a settlement of Erdős 595.
The main Spec.lean is unchanged, with its original sorry. No submission
was made in this continuation.

## Transfinite boundary-amalgamation corollary (verified)

TransfiniteBoundaryAmalgamation.lean compiles with olean and permitted-axiom
audits; log /tmp/transfinite-boundary-amalgamation.log. Namespace
Erdos595TransfiniteBoundaryAmalgamation.

The new AmalgamationStage omits the old triangleFree field entirely.
countably_colorable_extension uses BoundaryPrescribedExtension.amalgamation;
cover then applies the existing well-founded literal-extension recursion.
Thus a continuous well-ordered free-amalgamation presentation with countably
properly vertex-colorable bases is countably triangle-free edge-coverable,
without requiring triangle-free bases or finite attaching sets. Its initial
stage may be any covered graph. No assertion that arbitrary K4-free graphs
admit such a presentation has been proved.

Further review of the generic third mutual-U stage, saturated apex towers,
graphic triangle closure, type-graph constructions, and the free-corner
asymmetric Ramsey reduction yielded no missing main implication. In
particular, uncolored universality and finite-palette obstructions were not
mistaken for an obstruction to arbitrary external countable edge colors.
Spec.lean remains unchanged with its original sorry. No proof submission
was made in this continuation.

## Ordered-quadruple right-adjoint candidate (new verified exclusion)

Namespace Erdos595OrderedQuadRight. The base is on functions Fin 4 -> A
for an arbitrary linearly ordered A. Its nonisolated vertices are increasing
quadruples. The canonical triangle for a<b<c<d<e<f is
  (b,d,e,f), (a,c,d,e), (a,b,c,f).
This is the matched-pair partition ((0,2),(1,5),(3,4)) from the earlier
exploratory notes. Its order reversal is the other remaining partition
((0,4),(1,2),(3,5)).

Verified files with oleans and permitted-axiom audits:
* OrderedQuadRight.lean: triangle_options proves that every triangle has one
  of the six canonical role permutations. Log /tmp/ordered-quad-right.log.
* OrderedQuadProperties.lean: unique_triangle, base_two, and has_prism. The
  last gives an actual disjoint matched triangle pair over Fin 8, so the
  earlier NoPrism hypothesis does not apply. Log /tmp/ordered-quad-properties.log.
* OrderedQuadShapes.lean: slide_common_first and mono_shape. A Slide is a
  pair (a,c,d,e), (a,c,d',d) with a<c<d'<d<e; every common neighbor has first
  coordinate a. mono_shape classifies the four residual diagrams when the
  three opposite witness pairs in a right triangle have equal order type.
  Log /tmp/ordered-quad-shapes.log.
* OrderedQuadFiniteCover.lean: right_finite_cover uses one UNIFORM palette
  of cardinality 256 over EVERY linearly ordered carrier, not just finite
  test instances. right_countable_cover follows. finite_representation_failure
  applies finite Folkman to rule out universality of the entire template
  family. Log /tmp/ordered-quad-finite-cover.log.

Finite-cover proof: use the six-bit directed order-type code of the two
opposite intersection witnesses, together with two endpoint FirstStar bits.
FirstStar means that ONE ENTIRE biclique side has constant first coordinate.
In a putative monochromatic triangle, mono_shape forces FirstStar at p or r,
but not q. The Slide lemma controls all extra vertices of the relevant side,
not merely the six chosen witnesses. This avoids the old anchor-only gap.
The theorem also applies to OrderDual A, excluding the reversed template.

Exact small checks (not Lean certificates) on A=Fin 8 and Fin 10 found
2-edge-colorings of the completed-biclique graphs:
  n=8: 110 concepts, 398 edges, 58 triangles;
  n=10: 878 concepts, 10432 edges, 540 triangles.
Artifacts /tmp/ordered_quad_right_{8,10}.{json,cnf,out}, logs
/tmp/ordered-quad-right-test.log and /tmp/ordered-quad-right-test-10.log.
The verified uniform 256-color theorem supersedes these finite tests for
assessing the candidate; it does not assert a uniform two-color theorem.

The main conjecture in Spec.lean is still unresolved, and Spec.lean retains
its original sorry and unchanged imports/statement. No proof was submitted.

The separate K4-freeness certificate is now also fully VERIFIED:
* OrderedQuadNoArcCase0.lean through OrderedQuadNoArcCase5.lean;
* OrderedQuadNoArcCases.lean imports the six cases;
* OrderedQuadNoArc.lean proves no_arc_four and right_cliqueFree.
Aggregate audit log /tmp/ordered-quad-no-arc.log contains only the three
permitted axioms. The exact order-constraint search was converted into
ordinary Lean proofs using equality, strict transitivity, and irreflexivity;
there is no reliance on trusting the Python search. The certificate has
1700 branching states and 8501 contradictory leaves. Cases were compiled
in batches of three to remain below the 10 GB memory limit.

Thus this particular candidate is now verified both K4-free and uniformly
finitely edge-coverable. K4-freeness was not used to infer the covering result.
The preceding finite proper-coloring/boundary exclusions remain unchanged.
No main proof or disproof has been obtained. No Lean build or solver is pending.

Useful implementation details:
* ![a,b,...] is a FUNCTION; apply it with `(vector : Fin n -> T) i`, not `[i]`.
* A local DecidableRel instance was supplied for arcGraph(top : Fin 4).
* Explicit coordinate equality paths were used after fin_cases in the unique
  triangle lemma; generic `order` did not normalize all of those goals.
* The large no_arc proof was split into six declarations/modules for practical
  compilation. Scratch OrderedQuadCheck.lean is incomplete and not imported.
* Direct Lean builds can reuse LEAN_PATH from /tmp/erdos595-lean-path, avoiding
  a Lake parent while running parallel certificate checks. No change to imports
  in Spec.lean was made.

## Latest continuation: exponential and abstract-hypergraph review

No new Lean theorem or main solution was obtained in this review. The original
Spec.lean is unchanged. Reviewed the fixed generic exponential, its chromatic
filter and reduced-power representation, third mutual-ultrafilter stages,
adapted one-point extensions, and abstract triangle hypergraphs.

The proposed domain-homomorphism transfer is ALREADY present as
ShiftExponentialCover.precomposeHom / cover_of_shift_hom and
LargeSecondShiftExponential.cover_of_domain_hom. Do not duplicate it or report
it as new. Consequently a candidate exponential domain must avoid receiving
these excluded high-chromatic shift homomorphisms, not merely differ from a
shift as an abstract graph.

No theorem turning linearity plus absence of Berge triangles into countable
hypergraph colorability was established. Graphical realization imposes extra
endpoint/closure restrictions; the previously verified root obstructions
remain relevant. Pure-graph saturation still supplies no control of arbitrary
external edge colorings. No submission was made, and no build remains pending
after the main-file check in /tmp/spec-exponential-review.log.

## New verified continuation: canonical joint completeness obstruction

Submission/CanonicalEdgeCompletenessObstruction.lean compiles cleanly with an
olean and permitted-axiom audits; log /tmp/canonical-edge-completeness.log.
Namespace Erdos595CanonicalEdgeCompleteness.

For the complete graph on Set (Nat -> Fin 2):
* the canonical avoiding edge filter is proper and countably complete;
* both endpoint marginals are continuum-successor-complete;
* the edge filter is NOT continuum-successor-complete;
* the canonical triangle coupling is proper and countably complete, and all
  three vertex marginals are continuum-successor-complete, but the triangle
  coupling is NOT continuum-successor-complete either.

Proof of failure: each binary-sequence coordinate cut is eventually avoided.
Intersecting all continuum many agreement sets would identify the two endpoints
of an edge, contradicting looplessness. Properness uses the already proved
large_complete_no_cover. The file explicitly proves not_cliqueFree: this graph
contains K4. Thus the result blocks an ABSTRACT marginal-to-joint completeness
upgrade; it does not refute such an upgrade under an additional K4-free
hypothesis and does not settle Erdos 595.

The infinite asymmetric host in FreeCornerArrow remains unconstructed. Reviews
of higher cone rights, ordered ultrafilter stages, algebraic graphical closure,
and countable-palette compactness did not give a main implication. Spec.lean is
unchanged with its original sorry; no main proof or disproof was submitted.

## Finite-exponent root Cayley graphs and finite local bounds (verified)

Newly completed and axiom-audited:
* FiniteRootCayley.lean, namespace Erdos595FiniteRootCayley.
  All root identities, K4/K3 preservation, exact countable-cover transfer,
  and translation-invariant replacement of covers work over ZMod 5.
  The finite coefficient group makes the graph finite when the base is finite.
  Log /tmp/finite-root-cayley.log. Earlier ZMod arithmetic errors are fixed.
* FiniteEarlierNeighborhoodObstruction.lean, namespace
  Erdos595FiniteEarlierNeighborhood. Log /tmp/finite-earlier-neighborhood.log.
  `no_uniform_finite_bound n` supplies a finite K4-free graph with TWO TF edge
  pieces such that EVERY linear order has an earlier neighborhood that is
  not properly n-colorable. Use the finite shift graph on Fin(2^n+1), take
  its cone, and take the finite root Cayley graph. Every neighborhood contains
  the shift graph; a largest vertex of any order has its full neighborhood
  earlier. All audits use only propext, Classical.choice, Quot.sound.

Scope: this defeats only a UNIFORM FINITE local bound. It does not refute
vertex-dependent finite bounds, countable local bounds, or prove/disprove
Erdos 595. The main Spec.lean is unchanged with its original sorry.

Further review of the asymmetric Ramsey host, countable-palette extension,
finite-support/group models, and canonical avoiding-filter route did not
supply the missing main implication. No proof/disproof was submitted.

## Reduced-power review after the finite local obstruction

No new theorem or settlement in this review. Rechecked the main-equivalent
countably complete reduced-power route rather than extending the finite local
obstruction. CountableCoordinateRepresentation supplies varying countable
coordinates; countable generic universality permits a fixed countable K4-free
target. The positive-fiber lemma still gives only positivity, not membership
in the filter. Natural-valued eventual-order ranks and minimum positive
coordinate colors do not overcome the incompatible-fiber issue. A triangle
can realize the same selected pair/color on three different positive sets.
No arbitrary intersection of these positive sets was assumed.

The existing finite global/local chromatic and finite-per-triangle-component
transfer theorems do not apply to the generic countable target. Reviewing
Boolean-valued partitions, the asymmetric Ramsey construction, and
prescribed-color extension did not establish a missing main implication.
Spec.lean remains unchanged with its original sorry. No proof was submitted.

## Further graph-realization and generic-extension review

No main proof or new verified theorem in this review. Rechecked the abstract
ordered hypergraph route and the exact sparse second-arc normal form. The
RootCases obstruction already permits noninjective edge-label maps, so dropping
injectivity does not rescue that matched-pair pattern. A coloring of a Cayley
or group-presentation graph still cannot be assumed translation-invariant.

Revisited full triangle-free apex extensions and the generic third mutual
ultrafilter stage. Positive common-neighbor extension alone is insufficient:
a complete tripartite graph has common neighbors for every triangle-free
vertex subset while remaining finitely edge-covered. No assertion that a
saturated uncolored graph controls an arbitrary external countable coloring
was established. The finite-edge-unsupported third-stage subgraph remains
unresolved in the generality discussed in the older notes; the existing
one-unsupported-point triangle theorem was not promoted to an all-unsupported
or non-coverability conclusion.

Spec.lean retains its original statement/import and sorry. No proof submission.

## Finite-dimensional geometric review

No new Lean theorem or main solution. Reviewed the unresolved signature (3,3)
unit-orthogonality family and the existing finite-dimensional results.
IndefiniteFiveCover covers negative index <3, not >=3. The real-Hilbert
negative-inner-product proof cannot be applied to an indefinite form or to
an arbitrary non-Archimedean ordered field. ArcIndefiniteEmbedding already
rules out treating finite-dimensional orthogonality as necessarily properly
countably colorable over arbitrary large fields.

Explorations of finite-rank neighborhood geometry, algebraic representations,
and valuation-based decompositions did not produce a verified countable edge
cover or a non-coverability proof. No general finite-rank or stable-graph
covering assertion was assumed. Spec.lean remains unchanged with its sorry.

## Higher-shift and graphical-realization review (no settlement)

No new Lean theorem or main implication was obtained in this continuation.
Rechecked ExponentialCandidate, ExponentialCompactness,
ExponentialChromaticFilter, AllSecondShiftCover, DirectedOrRightCover,
SecondArcNormalForm, and the recorded ThirdRightProfileObstruction result.
The third unrestricted right target can be non-coverable, but its proved K4
prevents treating it as a witness or transferring its lower bound to a
K4-free exponential subgraph. No countable-palette lower bound for higher
shift exponentials was established.

Further mathematical review of mixed-sign Cayley presentations, asymmetric
Ramsey hosts, and canonical edge-filter completeness did not close their
existing gaps. In particular, no translation-invariance of arbitrary edge
colorings, compatibility of positive filter fibers, or infinite partite
coherence was assumed. Spec.lean is unchanged with its original sorry.
No proof/disproof was submitted.

## Fixed finite-bound review (no settlement)

Reviewed FiniteEdgeBounds, RankEdgeCover, and FiniteAdaptedExtension as a
potential universal covering route. No assignment b : Sym2 V -> Nat was
constructed that works simultaneously on every finite induced subgraph of
an arbitrary K4-free graph. Bounds chosen separately for each finite set
cannot be interchanged with the existential quantifier in countable_cover_iff.
The boundary/earlier-neighborhood coloring hypotheses in the existing
extension and rank theorems remain additional assumptions.

Further exploration of finite-support representations, natural-valued
reduced-power ranks, and graph realization did not yield a new theorem or
close a main gap. In particular, no compatibility of positive fibers was
asserted, and no universal Hilbert representation was established.
Spec.lean remains unchanged with its original sorry. No proof was submitted.

## Asymmetric Ramsey and partite-construction review (no settlement)

Revisited the free-corner asymmetric Ramsey reduction and the verified
finite/infinite designated bipartite Ramsey steps. No coherent infinite
partite host was constructed. The continuous amalgamation theorem with
countably properly colorable old boundaries preserves countable TF edge
coverability, so constructions covered by that theorem cannot supply the
missing host. One-piece homogenization was not treated as simultaneous
homogenization of infinitely many pieces.

Further informal exploration of equality-based corner constraints,
triangle-hypergraph realization, and forcing/mixing did not establish a
new theorem. In particular, no forcing-extension witness was promoted to
a ground-model witness, and no compatibility of locally chosen edge
representatives was assumed. Spec.lean still has its original sorry, and
no proof/disproof was submitted.

## Point-countable edge-cover localization (NEW, verified)

Submission/PointCountableEdgeCover.lean compiles with an olean. Namespace
Erdos595PointCountableEdgeCover; log /tmp/point-countable-edge-cover.log.
All six printed audits contain only propext, Classical.choice, Quot.sound.
No sorry or pending repair remains in this new file.

* countable_cover: an arbitrarily indexed union of covered spanning graphs
  is covered if each vertex is incident to at most countably many pieces.
  No K4-freeness hypothesis is required.
* cover_of_le_iSup: corresponding subgraph version.
* spanning_cover: turns a covered induced subgraph into a covered spanning
  graph with all other vertices isolated.
* localization: one covered core graph plus point-countably many covered
  induced pieces suffices if every remaining edge lies in one piece.
* cover_of_countable_supports: vertices may carry arbitrary countable sets
  of coordinates; if adjacent supports intersect and all coordinate stars
  are covered, then the graph is covered.
* finite_intersection_reduction: with finite supports, project each edge
  to a covered target indexed by the intersection of its endpoint supports.
  This suffices globally since only finitely many intersections are incident
  to a fixed vertex. Has an explicit [DecidableEq I] argument.

Proof mechanism: choose local natural-number indices for the pieces incident
to each vertex. An ordered edge records its two local indices and the color
within its chosen piece. In an increasing monochromatic triangle, the first
vertex identifies the first two pieces and the last vertex identifies the
last two; all three edges are consequently in one piece with the same color.

Scope: this is a closure theorem, not a universal decomposition of K4-free
G. No point-countable covered family was constructed for the third generic
mutual-ultrafilter tower, and no countable edge-color lower bound for that
tower was obtained. The finite-intersection result does not itself establish
coverability of finite-dimensional indefinite orthogonality targets (signature
(3,3) and above remains unresolved), nor does it establish a universal
orthogonality representation of K4-free graphs.

Spec.lean is unchanged with its original sorry. No main proof was submitted.

## Point-countable closure versus cardinal decomposition (no settlement)

Rechecked CriticalCardinality and the canonical endpoint marginals after
PointCountableEdgeCover. The new closure result requires edge coverage by
a family whose incident-index set is countable at EVERY vertex. A family
of individually covered vertex sets does not provide coverage of crossing
edges. The family of all K4-free vertex neighborhoods consists of TF pieces,
but need not be point-countable; no suitable point-countable selection was
constructed. No cofinality improvement or universal decomposition theorem
was obtained.

Further exploration of right-adjoint templates and finite-support/common-
neighbor selection did not produce a new main implication. Spec.lean remains
unchanged with its original sorry. No proof or disproof was submitted.

## Further construction and transfer review (no settlement)

Rechecked TupleTypeCover and CountableTupleTypeCover: homogeneous pair order
patterns on three full tuples extend to four, so the proposed finite-tuple
ordinal-pattern Ramsey construction is already excluded by verified results.
No restricted-domain construction evading those results was obtained.

Rechecked NoCountableK4Target, FiniteCliqueUltrafilterColoring, and
FiniteTowerCompressionObstruction. The last file explicitly blocks a general
inference from covered finite mutual-ultrafilter towers to a countable K4-free
target, even when the original graph is properly countably colorable and has
no finite triangle-edge palette. No version using additional generic-graph
hypotheses was proved. The generic third-stage problem is still open here.

Informal examination of mixed-sign group presentations, finite-dimensional
algebraic representations, elementary-model decompositions, and Boolean-valued
forcing descent yielded no main implication and no new Lean theorem. In
particular, no translation invariance of an arbitrary edge coloring, compatible
specialization of field elements, point-countable neighborhood selection, or
locality of a coloring on Boolean names was established.

Spec.lean is unchanged with its original sorry. No proof/disproof was submitted.

## Polynomial and rational-function orthogonality covers (NEW, verified)

Submission/PolynomialOrthogonalityCover.lean compiles with an olean, with seven
printed axiom audits containing only propext, Classical.choice, Quot.sound.
Namespace Erdos595PolynomialOrthogonality; build/audit logs:
  /tmp/polynomial-orthogonality-cover.log
  /tmp/polynomial-result-audit.log
No sorry, warning, or pending repair remains in this new result file.

For a finite coordinate type J and an arbitrary variable type I:
* countable_cover: the nonisotropic polynomial-vector graph is covered over a
  countable infinite integral domain. Adjacency is orthogonality in BOTH
  directions, allowing nonsymmetric matrices.
* cover_of_representation: only preservation of edges and nonzero diagonal
  values is required; representations need not be injective or exact.
* countable_cover_domain / cover_of_representation_domain: adjoining one
  coefficient variable removes the infinitude restriction on the countable
  domain. In particular finite coefficient fields are allowed.
* cover_of_polynomial_matrix: coefficients of the finite matrix may themselves
  be polynomials in I. Move their finitely many variables into a countable
  coefficient domain, using an explicitly split injective polynomial map.
* cover_of_fraction_representation: clear a common denominator per vector.
* cover_of_fraction_matrix: also clear a denominator for the matrix. The final
  theorem works with ANY finite matrix over ANY fraction field F of
  MvPolynomial I R, where R is a countable integral domain and I is unrestricted.

Mechanism: each polynomial vector has finite variable support and an evaluation
that keeps its diagonal value nonzero. For a finite F, specialize private
variables using that evaluation, while retaining F as polynomial variables.
For an edge whose endpoint supports intersect exactly in F, the endpoint maps
are restrictions of ONE substitution. Orthogonality is therefore preserved.
Targets over finite F are countable. PointCountableEdgeCover's verified
finite_intersection_reduction then supplies the global countable edge cover.
No K4-freeness hypothesis is needed for these covering results.

Scope limitations: this does NOT prove coverability for arbitrary field
extensions, including arbitrary algebraic extensions of rational-function
fields. Compatible algebraic specializations were considered informally but
not established. It does not give a finite-dimensional representation of an
arbitrary K4-free graph; GenericFiniteRankObstruction already excludes such
a universal representation. No result about the generic third ultrafilter
stage or main asymmetric Ramsey host was obtained.

Spec.lean remains unchanged with its original sorry. No main proof/disproof
was submitted. The external reference page was still unreachable (DNS failure).

## Countable-dimensional field-extension transfer (NEW, verified)

Submission/AlgebraicOrthogonalityCover.lean is complete and compiles with an
olean. Namespace Erdos595AlgebraicOrthogonality. Its five printed audits use
only propext, Classical.choice, Quot.sound. No warning or pending repair in
the result file. Logs:
  /tmp/algebraic-orthogonality-cover.log
  /tmp/algebraic-extension-audit.log

Definitions/results:
* graph B: nonisotropic points of an arbitrary bilinear form, with mutual
  orthogonality as adjacency (no symmetry/nondegeneracy assumption required).
* FiniteFormsCover K: all such graphs in finite dimensions over K are covered.
* cover_of_finite_representation: transports this field property to arbitrary
  finite-dimensional K-vector spaces and edge-preserving representations.
* rational_field: fraction fields of MvPolynomial I R satisfy FiniteFormsCover
  when R is a countable integral domain; I has arbitrary cardinality.
* finite_extension: FiniteFormsCover passes from K to a finite-dimensional
  extension F/K. Separate points according to a nonzero coordinate of their
  diagonal value in a K-basis of F, then restrict scalars on each fiber.
* cover_of_countable_representation: a countable basis of the represented
  K-vector space suffices. Partition by finite basis support and apply the
  finite-dimensional result on each subspace.
* countable_extension: the field-extension transfer consequently works for
  ANY extension with a countable K-basis. Algebraicity is not assumed.

Scope: arbitrary algebraic extensions of uncountable rational-function fields
can have uncountable vector-space degree, so they are NOT covered by this
transfer. An informal route using algebraic closures of finite transcendence
supports would still require a rigorous independent-specialization theorem;
that has not been proved. No universal finite-dimensional bilinear
representation of arbitrary K4-free graphs (even allowing a target with K4s)
was established. GenericFiniteRankObstruction specifically excludes universal
finite-dimensional K4-FREE exact orthogonality targets; do not silently remove
that target hypothesis from its statement.

No main implication was obtained. Spec.lean is unchanged with its original
sorry, and no proof/disproof was submitted.

## New verified continuation: finite domination and K5-free targets

`Submission/NoetherianTriangleExtension.lean` compiles with olean.
Log: `/tmp/noetherian-triangle-extension.log`.
All six printed audits use only propext, Classical.choice, Quot.sound.
Namespace `Erdos595NoetherianTriangleExtension`.

* `finite_dominating`: a countable graph with FiniteCommonNeighbors and
  FiniteIndependentExtension has a finite OPEN-neighborhood dominating set.
  No clique hypothesis is required. If finite domination fails, an independent
  sequence can simultaneously escape an enumeration of all neighborhoods;
  finite determination and finite independent extension supply a forbidden
  common neighbor of the whole sequence.
* `k4_vertex_cover`: for a K4-free graph these hypotheses imply a finite cover
  of VERTICES by triangle-free induced sets, stronger than the earlier finite
  EDGE cover conclusion.
* `finite_edge_detectors`: with finite triangle-free extension, each vertex
  has two adjacent detectors from one fixed finite list, both adjacent to it.
* `k5_vertex_cover`: a countable K5-free graph with FiniteCommonNeighbors and
  finite triangle-free extension has a finite vertex triangle-free cover.
* `generic_no_noetherian_k5`: the countable generic K4-free graph has no hom
  into ANY K5-free graph with FiniteCommonNeighbors. Restrict to the countable
  homomorphic image; finite triangle-free extension transfers to that image.
* `generic_no_finite_rank_k5`: applies the preceding obstruction to exact
  finite-dimensional bilinear orthogonality targets over arbitrary fields.

This extends the earlier target obstruction from K4-free to K5-free targets.
It DOES NOT remove the target clique bound, and does not prove a universal
representation or any non-coverability theorem. The original conjecture in
Spec.lean remains unchanged with its sorry.

The same file now additionally proves `finite_common_mutual` and
`generic_no_rank_four`. The latter rules out even a WEAK bilinear representation
of the countable generic graph in dimension <=4 over ANY field: diagonal values
must be nonzero and edges must map to zeros. No symmetry, exactness, or
injectivity hypothesis is required. Mutual orthogonality defines the target;
five nonisotropic orthogonal vectors would be linearly independent. All SEVEN
printed audits in the updated log use only the permitted axioms.

No new general target obstruction for clique bounds >4 was proved. Discussions
of arbitrary finite rank, OR-ultrafilter towers, saturation, exponential
color-fiber selection, and iterated color elimination remain informal and do
not supply a main implication. In particular the finite triangle-free extension
property cannot simply be inherited through common neighborhoods of an
arbitrary clique: the corresponding request can already contain a triangle.

Latest main-file check: /tmp/spec-noetherian-k5-review.log; only the original
sorry warning. No build or solver is pending, and no proof submission was made
in this continuation.

## New verified continuation: bipartite label classes and failed apex-swap gluing

`Submission/AdaptedBipartiteSwapObstruction.lean` compiles with olean.
Log: `/tmp/adapted-bipartite-swap-obstruction.log`.
All five printed axiom audits use only the permitted axioms.
Namespace `Erdos595AdaptedBipartiteSwap`.

* `exists_bipartite_pieces_no_adapted` strengthens the fixed-coloring
  obstruction: the graph is triangle-free, has a proper vertex coloring by
  binary sequences, and EVERY natural-number edge-color class has a proper
  two-color vertex coloring, but the fixed edge coloring has no adapted
  vertex labeling. Construct B x (N -> Fin 2), keeping B-edges only when the
  binary coordinates differ, and color by first difference. The high-chromatic
  B/profile argument still works because the diagonal witness is unequal.
* `square_swap_impossible`: four homomorphic copies of a graph, glued along
  two overlapping triangles by the alternating apex swaps (a b) and (a c),
  force the adjacent vertices a,b of one copy to have equal images. This fails
  in EVERY simple target graph, not merely K4-free targets.
* `alternating_square`: any square in B produces a 0,1,0,1-labeled square in
  the first-difference index graph, using four explicit binary sequences.
* `square_of_no_countable_coloring`: uncountable chromatic number forces a
  four-cycle, via the existing countable-common-neighbor coloring theorem.
* `no_simultaneous_swap_realization`: combines the preceding three facts to
  rule out the proposed first-difference indexed apex-swap gluing construction.

This review tested a DIRECT positive construction idea: each cone copy must
have an equal-spoke corner, and two identically colored copies glued with
exchanged apices would force a monochromatic triangle. The ordinary
first-difference index family cannot realize the required simultaneous
identifications. No replacement gluing scheme has been constructed.

Revisiting infinite asymmetric triangle Ramsey, generic third mutual-U,
colored saturation, fusion, and hypergraph block amalgamation did not yield
an additional main implication. Spec.lean remains unchanged with its original
sorry, and no proof/disproof was submitted.

Latest main-file check for this continuation: /tmp/spec-adapted-swap-review.log;
only the original sorry warning. The new auxiliary file has no incomplete
proofs, and no build or solver is pending. Informal discussion of local finite
palettes and countable vertex partitions into finite edge-palette pieces did
not establish either a normalization theorem or a counterexample to one.
Do not use those discussions as a main implication.

## Further exponential/product and structural review (no new main result)

Rechecked ExponentialNeighborhoodTransfer, LocalChromaticProduct,
SecondArcNormalForm, SecondArcTargetCharacterization, DirectedOrRightCover,
ThirdRightProfileObstruction, and the critical-cardinality/filter reductions.
No new theorem connecting these reductions to a main witness was obtained.
In particular:
* no infinite-product chromatic lower bound for the generic-target exponential
  was proved;
* countable/continuum vertex palettes and countable triangle-free EDGE palettes
  must not be interchanged;
* the countable-base directed second-right coloring does not cover an arbitrary
  higher profile target or an arbitrary K4-free induced subgraph of one;
* the canonical edge filter's stronger completeness under K4-freeness remains
  unproved; its stronger vertex-marginal completeness is not sufficient alone;
* no universal finite-positive-index or countably dimensional representation
  was established;
* topological/cohomological and transfinite color-normalization discussions
  yielded no applicable universal covering theorem.

No new auxiliary Lean file was added in this pass. Spec.lean is unchanged,
with its original sorry, and no proof submission was made.

## Latest direct-construction review (no settlement)

Revisited the apex-swap gluing obstruction, free-corner asymmetric Ramsey
reduction, higher single-cone right adjoints, saturation/one-point extensions,
triangle-hypergraph realizations, and canonical-filter coupling. No replacement
gluing scheme, infinite Ramsey host, or universal covering argument was proved.
In particular, HigherConeOddBound supplies K4 exclusion but no edge-color
lower bound; third_right_countable_cover already rules out the countable-base
third-right route. Prescribed adapted-labeling obstructions still do not apply
to every coloring of a fixed graph.

A possible stronger finite-rank target exclusion using finite vertex
indivisibility of the generic graph was discussed only informally. Neither
that indivisibility lemma nor the proposed stronger exclusion was formalized,
and neither would settle the main conjecture by itself.

No new Lean theorem or candidate witness was established in this pass.
Spec.lean remains unchanged with its original sorry; the final review log is
/tmp/spec-latest-construction-review.log. No proof/disproof submission was made.

## Additive and full-word Ramsey review (no settlement)

Rechecked RootLattice and FiniteRootCayley: both preserve coverability exactly;
neither gives an independent additive coloring theorem for the K4-free case.
Leading-coordinate, support-size, and norm discussions did not supply one.

Rechecked CountableHalesJewettObstruction and BinaryInfiniteHalesJewett.
The three-letter obstruction `cube_countable_coloring` applies to the FULL
function space (I -> Fin 3), for EVERY index type I. It is not restricted to
finite-support words: a Hamel basis is applied to the entire rational vector
space I -> Q. Thus passing to full infinite words does not repair the
countable-palette partite step. The positive binary result does not provide
arbitrary finite or infinite edge alphabets.

Also revisited the fixed generic reduced-power normal form, countably complete
filters, cone-swap gluing, and linear/matroid representations. No new coloring
transfer, Ramsey host, generic saturation implication, or universal algebraic
representation was established. These discussions remain informal; no new
Lean theorem was added. Spec.lean is unchanged, with its original sorry.

## Canonical-filter compatibility review (no settlement)

Rechecked TriangleFilterCoupling, ResidualTriangleDegree,
CanonicalPositiveRestriction, EdgeVertexFilterMarginal, and CriticalCardinality.
The exact triangle marginals permit gluing two triangles along an edge, but
`opposite_nonadjacent` shows that K4-freeness forbids the missing opposite edge.
Residual common-neighbor abundance gives cardinal size, not a compatible
positive conditional fiber. Neither endpoint completeness nor the critical
cofinality bound supplies the missing cyclic compatibility or a cardinal
reflection theorem. No stronger completeness result under K4-freeness was
proved.

Further discussion of saturation, local odd-wheel deletion, and infinitary
coloring compactness yielded no applicable implication. No new Lean theorem
was established, no change was made to Spec.lean, and no proof/disproof was
submitted. The original sorry remains.

## Finite-fiber odd bounds and second-right exclusions (verified auxiliary results)

Three new files compile with oleans. Every printed axiom audit uses only
propext, Classical.choice, and Quot.sound. No main proof/disproof was obtained.

1. Submission/FiniteFiberOddBound.lean
   Namespace Erdos595FiniteFiberOddBound.
   Log: /tmp/finite-fiber-prism.log.
   * bundle F P hP B has vertex type I × S, fiber adjacency F, and cross
     adjacency B.Adj i j ∧ P a b.
   * Template consists of two proper three-colorings c₀,c₁ of F with
     P a b → c₀ a ≠ c₁ b. Symmetry gives the reverse cross condition.
   * three_of_two gives a three-coloring when the index graph is bipartite.
   * three_of_finite_hom correctly uses the FINITE IMAGE in I of the source
     homomorphism, not a potentially inconsistent coloring of source copies.
   * cliqueFree extends HigherConeOddBound to all such templates: for each
     fixed n, NoShortOdd B (bound n) ensures K4-freeness at right stage n.
   * Prism defines the concrete 6-vertex triangular prism, label classes
     {0,4},{1,3},{2},{5}, the equality cross relation, and its two-coloring
     template. Kernel checks establish cross_independent, no_three_fold,
     and cross_refl. No non-coverability conclusion is asserted.

2. Submission/CrossClassSecondRightCover.lean
   Namespace Erdos595CrossClassSecondRight.
   Log: /tmp/crossclass-second.log.
   * A finite fiber glued over any triangle-free index graph by equality of
     a proper countable label has a countably covered SECOND right adjoint.
   * Uniform bicliques have one unordered label pair on all within-fiber
     edges. Two internal fibers imply uniformity. Nonuniform bicliques
     have a unique internal fiber and are labeled by the finite local
     biclique there. The combined label is rainbow on triangles of the
     first right adjoint (code_ne).
   * Prism.second_right_cover explicitly transfers this theorem to the
     concrete prism bundle from the previous file, using Prod.swap.
   * Thus the proposed prism is EXCLUDED AT STAGE TWO, even for arbitrarily
     large/high-chromatic triangle-free B. Higher stages are NOT excluded
     by this theorem.

3. Submission/FiniteFiberSecondRightCover.lean
   Namespace Erdos595FiniteFiberSecondRight.
   Log: /tmp/finite-fiber-second.log.
   * Stronger and simpler criterion: finite F, triangles confined to index
     fibers, and P disjoint from F.Adj imply a covered second right stage.
   * code p a b means that (i,a) lies on the left and (i,b) on the right of
     p for SOME i. This is a finite relation when S is finite.
   * For a first-right triangle, one witness base triangle has coordinates
     x,y,z in one fiber. If p and q have equal codes, p contains both z→x
     at that fiber and x→y at some fiber j. If the fibers agree, p contains
     x on both sides, impossible. If they differ, biclique completeness
     forces P z y, contradicting the fiber edge F.Adj z y.
     Hence code_ne supplies a finite rainbow-on-triangles label.
   * triangle_fibers derives confinement from independent P-neighborhoods
     and triangle-free B.
   * second_right_cover_of_reflexive: if P is reflexive and each P-neighborhood
     is F-independent, then P is automatically disjoint from F.Adj; the
     second right stage is covered for every triangle-free B. P need NOT
     be an equivalence relation.

Informal explorations NOT established:
* An alternative finite 9-vertex fiber F = complement of the square of C9,
  with P = loops plus cycle adjacency, has plausible two-fiber 3-colorings,
  but its second stage is already excluded by the reflexive criterion above.
  No Lean definition or numerical test of this alternative was added.
* Arbitrary nonreflexive P can meet F.Adj on coordinates without loops. The
  raw-relation proof then need not work. No general second-right cover for
  all such P was proved. Full-matching cases have earlier separate covers.
* No non-coverability result for higher finite-fiber right towers, generic
  third mutual-ultrafilter stages, or transfinite extension towers was proved.
* No new saturation, infinite Ramsey-host, or universal-cover implication
  was obtained in the other discussions.

Spec.lean remains unchanged, SHA256
  de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45
with the original sorry. No proof/disproof was submitted. No build or solver
is pending after the final checks of this continuation.

## Universal nine-point template (verified reduction, still no settlement)

Submission/FiniteFiberUniversal.lean compiles with an olean.
Namespace: Erdos595FiniteFiberUniversal.
Log: /tmp/finite-fiber-universal.log.
All eight printed axiom audits use only propext, Classical.choice, Quot.sound.

Nine := ULift (Fin 3 × Fin 3).
The universal fiber graph and symmetric cross relation are:
  fiber.Adj a b := a.1 ≠ b.1 ∧ a.2 ≠ b.2
  cross a b := a.1 ≠ b.2 ∧ a.2 ≠ b.1.
Its two three-colorings are the two coordinate projections.

Verified results:
* fold maps ANY fiber template (even an infinite fiber) with two compatible
  proper three-colorings into this nine-point template over the SAME index
  graph B, using a ↦ (c₀ a,c₁ a).
* iterRightHom transports a homomorphism through every finite right tower.
* cover_of_universal transfers a cover at stage n back to any such template.
* universal_no_cover transfers a genuine obstruction in any such template
  to the universal one. No such obstruction has been established.
* universal_cliqueFree supplies the existing NoShortOdd B (bound n) K4 bound.
* base_cover: for triangle-free B the universal bundle at STAGE ZERO is
  countably triangle-free edge-covered, by its finite coordinate partition.
* mixed_triangle: every B-edge i--j gives the triangle
    (i,(0,1)), (j,(0,1)), (i,(2,2)).
  Thus triangle confinement to index fibers fails in this universal family.
* rainbow_transfer: a vertex label rainbow on every triangle of the
  universal base properly colors B. This is a statement about RAINBOW
  VERTEX LABELS, NOT countable triangle-free EDGE covering. It supplies
  no non-coverability result for the first or subsequent right stages.

Other review in this continuation:
* Considered a nonreflexive prism cross relation with loops at 0,3 and
  the square edges 1--2--5--4--1. It has two compatible three-colorings,
  but informally identifies with SplitTriangleRightCover: use top triangle
  (A,B,C)=(1,2,0), bottom (A,B,C)=(5,4,3); the C-index graph is B □ K2
  and all additional edges are A--B edges. The existing five-cover theorem
  therefore excludes its second stage. No separate Lean definition or
  transfer lemma for this variant was added.
* Revisited finite/infinite partite Ramsey, profile signal gadgets, generic
  mutual-ultrafilter towers, saturation, and countable palette localization.
  No main bridge or chromatic lower bound was obtained.
* A possible general FIRST-right cover for arbitrary finite-fiber graphs
  projecting to equality-or-a-triangle-free-index relation was discussed
  informally only. The proposed classification of projected bicliques is:
  disjoint index sides (maps to right B), one singleton index side, or both
  index sides supported on the same two adjacent indices. Finite local
  patterns might give triangle-free vertex fibers. THIS HAS NOT BEEN
  FORMALIZED, and no claim about the universal first-right stage follows
  from the current new file.
* The opposite-order version of SecondArcTransversal informally gives a
  second disjoint independent triangle transversal. No new general second-
  right covering theorem follows; any uniform finite bound in that general
  normal form would contradict the already verified finite Folkman results.

Spec.lean remains unchanged with the original sorry. Latest main check:
  /tmp/spec-universal-template-review.log
No proof/disproof was submitted. No pending build or solver remains.

## Countable-fiber first-right cover (new verified result, no settlement)

Submission/CountableFiberFirstRightCover.lean compiles with an olean.
Namespace: Erdos595CountableFiberFirstRight.
Log: /tmp/countable-fiber-first.log.
All three printed axiom audits use only propext, Classical.choice, Quot.sound.

Main theorem first_right_cover:
  H : SimpleGraph (I × S), Countable S,
  B : SimpleGraph I, B.CliqueFree 3,
  H.Adj x y -> x.1 = y.1 or B.Adj x.1 y.1
  imply a countable triangle-free edge cover of right H.
No fixed fiber graph or cross relation is required. No K4 hypothesis is used.

Proof details:
* Separated bicliques have disjoint left/right index projections. Any triangle
  among them projects its three cyclic witnesses to a B triangle.
* Bicliques with a singleton left index projection are coded by the set of
  left fiber coordinates. A monochromatic triangle again gives a B triangle.
  Empty left sides cause no difficulty. Right-singleton sides follow by swap.
* Every remaining biclique has both projections supported on the SAME TWO
  distinct indices. This classification is proved using triangle-freeness of B.
* Well-order the two indices. It suffices to code the TWO LEFT coordinate
  sets (not all four left/right sets). Equal-coded adjacent bicliques have
  concatenating increasing index pairs, hence map to an ordered shift graph.
* Shape tags and these sets form Code S = Fin 4 × (Set S × Set S).
  For countable S this embeds in the power set of a countable type and then
  in binary sequences. The codes have triangle-free vertex fibers.
* bundle_first_right_cover applies to all countable-fiber bundles.
* universal_first_right_cover explicitly applies to the universal nine-point
  template over every triangle-free B. Its FIRST RIGHT STAGE is now excluded.
  The general universal SECOND and higher stages are NOT settled.

Normal-form shortcut checked informally and rejected:
* Merging reversal-partner second-arc triangles into six-vertex prism bags
  does not yield a triangle-free index graph, even for K4-free sources.
* A book abc, abd, abe has three prism bags meeting the same first-arc vertex
  a->b, producing a quotient triangle (arbitrarily large clique for a big book).
* A nonstar vertex in right(arc^2 G) can likewise participate in triangles from
  many distinct full-matching pairs; the unit image of a->b in a book does so.
  No uniqueness of such a pair follows from K4-freeness.

Further discussion, NOT a proved bridge:
* Reviewed higher universal right stages, the third mutual-ultrafilter stage,
  infinite partite construction, and the triangle-edge hypergraph viewpoint.
  No non-coverability or general covering theorem was obtained.
* The universal fiber can be viewed as K3 × K3 with cross adjacency twisted
  by swapping the two coordinates. Its six off-diagonal points form a prism.
  Mixed triangles prevent applying the existing confined-fiber second-right
  theorem. No successful decomposition at the second stage was proved.
* A restricted two-coordinate shadow construction has an independent exact
  triangle marking with star neighborhoods, and is covered by the existing
  DominatedMarkedSecondRight criterion. This was only identified informally;
  no separate formal transfer was added.

Spec.lean remains unchanged with its original sorry. No main proof/disproof
was obtained or submitted. No build or solver is pending after final checks.

## Universal nine-point second-right cover (NEW, verified)

UniversalProfileSAT, UniversalProfileDefinitions, UniversalProfilePattern,
NoOppositeTriangleCover and UniversalSecondRightCover all compile with oleans.
The final logs are /tmp/universal-profile-pattern.log and
/tmp/universal-second-right.log. All printed axiom audits are permitted.

The first right of the universal nine-point bundle has a finite vertex profile
(the global fiber-coordinate set on each biclique side) with no simultaneous
triangle profiles AAB and BBA. UniversalProfilePattern.no_pattern verifies the
finite obstruction via a kernel-checked LRAT certificate: 497 variables, 1483
input clauses and 539 retained proof steps. The semantic graph bridge uses 120
sample points (108 profile representatives and 12 intersection witnesses).
The clause bridge uses separate global lemmas; the old generator at
/tmp/generate_universal_profile_pattern.py does NOT reproduce all final fixes.

NoOppositeTriangleCover.right_cover proves that any countable vertex labeling
with this no-opposite property gives a countable TF edge cover of its right
adjoint, by coloring edges with unordered pairs of witness labels.
UniversalSecondRightCover.second_right_cover therefore covers the SECOND right
of the universal bundle over EVERY triangle-free index graph.
template_second_right_cover pulls this back to all compatible two-three-
coloring templates, even with infinite original fibers.

This is another candidate exclusion, NOT a proof or disproof of Erdős 595.
The auxiliary files do not modify the main conjecture. Spec.lean remains
unchanged with its original sorry. There is no pending build.

External SAT observations, NOT Lean theorems: arc^2 K4 has no hom to the
universal bundle over any triangle-free B (arbitrary-index SAT, 6.89s),
including C5/C7. The arc^3 K4 to universal bundle over C5 test timed out.
Scripts and artifacts: /tmp/universal_arbitrary_tf.py,
/tmp/arc2K4_universal_arbitraryTF.*, /tmp/universal_arc_hom.py,
/tmp/universal_opposite_profiles_nosym{,_core}.{cnf,lrat} and core JSON.

## Algebraically closed tensor-domain auxiliaries (verified; no main solution)

AlgClosedSpecialization.lean and AlgClosedTensorDomain.lean compile with oleans.
Their printed axiom audits use only propext, Classical.choice, Quot.sound.
Logs: /tmp/algclosed-specialization.log and /tmp/algclosed-tensor-domain.log.

Erdos595AlgClosedSpecialization.exists_hom proves that a nontrivial finite-type
commutative algebra C over an algebraically closed field F has an F-algebra
homomorphism to F, using a maximal-ideal quotient and the finite-type field
extension theorem.

Erdos595AlgClosedTensorDomain.tensor_isDomain proves that A tensor_F K is a
domain for arbitrary field extensions A,K of an algebraically closed F.
The proof uses finite basis support, a finite-type coefficient subalgebra
containing inverses of selected nonzero coefficients, and specialization to F.
Supporting lemmas include coeff_map, map_right_injective, coord_rid and
restrictCoeffs_apply. NoZeroDivisors and mul_ne_zero are also exported.

IMPORTANT: this is about the ABSTRACT tensor product. It does not prove
injectivity of multiplication into an arbitrary common overfield. For the
independent-transcendence-support plan that additional step remains unproved.
A proposed localization/base-change route was recorded in the conversation;
no implementation of that step exists. Even the full algebraic cover plan
would only exclude geometric candidates, not settle the original conjecture.
TensorDomainCheck.lean is a disposable scratch file with #check errors and is
not a dependency of the completed files.

Subsequent review of finite ordered-type graphs, generic saturation, adapted
labelings, stationary/ladder constructions and finite-positive-index Gram
representations produced no new main bridge. Existing counterexamples to
adapted-labeling reflection and finite-type amplification still apply. No
universal finite-positive-index representation was established.

Spec.lean remains unchanged with its original sorry. No solution was obtained.

## Arbitrary-field finite-dimensional bilinear cover (NEW, verified)

The earlier algebraic-support gap is now CLOSED. AllFieldOrthogonalityCover.lean
proves cover_of_finite_representation: over ANY field, a graph whose edges map
to orthogonal pairs in a finite-dimensional bilinear space, with every vertex
image nonisotropic, has a countable triangle-free edge cover. Only the forward
edge implication is needed; no K4-free hypothesis is used. Its finiteFormsCover
also completes the existing countable-dimensional field-extension transfer.

New compiled dependencies: AlgClosedTensorInjection, AlgClosedLinearDisjoint,
AlgebraicSupportFields, CountableFieldUniversal, AlgebraicBilinearTransfer,
AlgebraicRootSpecialization, AlgebraicSupportCover. Actual multiplication
injectivity is proved from disjoint transcendence supports, not merely from
abstract tensor-domain. Finite-support algebraic closures are rebased over
the relative algebraic closure of the support intersection; two embeddings
into a common countable algebraically closed field transfer cross-equations.
The existing finite_intersection_reduction supplies the graph cover.
Logs include /tmp/all-field-orthogonality.log. Audited axioms are permitted.

DiagonalPositiveIndexCover.lean additionally covers orthogonality graphs of
positive vectors with finitely many positive coordinates and arbitrarily many
FINITELY SUPPORTED negative coordinates, over every ordered field. Projection
to the shared negative support preserves edge products and increases the
positive diagonal. Log /tmp/diagonal-positive-index-cover.log. Permitted axioms.
This does NOT cover arbitrary non-diagonal infinite-dimensional bilinear forms:
such forms need not possess an orthogonal Hamel basis.

These results are candidate exclusions, NOT a settlement. No universal weak
representation of arbitrary K4-free graphs in these classes is established.
GenericFiniteRankObstruction.no_hom rules out the generic graph mapping into
K4-free exact finite-rank orthogonality targets (including signatures (3,n));
it does not itself exclude weak representations into targets with K4s.
Spec.lean remains unchanged with its sorry. No pending build or solver.

## Latest main-bridge review (no settlement)

Recorded the completed arbitrary-field algebraic results above and reviewed
weak/non-diagonal bilinear representations, higher single-cone rights, generic
mutual-ultrafilter towers, and prescribed-color focusing. No universal
representation, non-coverability lower bound for a K4-free higher cone, or
new canonical-filter amalgamation theorem was obtained. HigherConeOddBound
supplies only clique exclusion; ThirdRightProfileObstruction's non-covered
target contains K4. These cannot be combined as if they concerned one graph.
External reference page still fails DNS resolution.

Direct check /tmp/spec-current-review.log reports only the original sorry.
Spec.lean SHA256 remains
  de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45
No main proof/disproof was obtained, no new proof submitted, no build pending.

## Infinite shift-graph Ramsey (verified; main problem unresolved)

InfiniteShiftRamsey.lean compiles with an olean. All six printed audits use
only propext, Classical.choice and Quot.sound. Log:
/tmp/infinite-shift-ramsey.log. Namespace Erdos595InfiniteShiftRamsey.

ramsey gives an induced monochromatic copy of orderedShiftGraph A inside a
larger ordered shift graph for an arbitrary nonempty palette C and an arbitrary
well-ordered A. It follows by coloring increasing triples and applying the
previous arbitrary-palette triple Ramsey theorem. graph_ramsey and
ramsey_of_embedding package this as a graph Ramsey property. step combines it
with free amalgamation to homogenize an induced shift subgraph of a K4-free H.
cycle_five_ramsey supplies an induced monochromatic C5 in a triangle-free host
for arbitrary palettes. None of these results produces a monochromatic triangle.

Unfinished mathematical sketch, NOT a Lean theorem: countable coverability of
right H may transfer to right(H square K2). Restrict each biclique to either
Boolean layer; these restrictions detect two covered edge families. A triangle
among remaining edges forces both sides of every biclique to meet both layers.
Such mixed bicliques are four-point rectangles indexed by oriented edges of H;
the rectangle graph is arcGraph H and has a two-piece triangle-free edge cover.
If verified, this would extend some no-prism second-right candidate exclusions,
not give a universal covering theorem or settle the conjecture. No corresponding
Lean file exists yet.

Spec.lean remains unchanged with its original sorry. No proof/disproof obtained.

## Cartesian prism and no-prism second-right covers (NEW, verified)

CartesianBoolRightCover.lean and NoPrismSecondRightCover.lean compile with
oleans. Logs: /tmp/cartesian-bool-right.log, /tmp/no-prism-second-right.log.
All printed axiom audits use only propext, Classical.choice and Quot.sound.

Erdos595CartesianBoolRight.right_cover proves the formerly sketched transfer:
  right H covered => right (H square K2) covered.
No clique hypothesis is used. Prism triangles lie in one Boolean layer.
Restricting bicliques to layers detects two covered edge families. Any triangle
of the remaining graph consists of bicliques mixed on both sides; mixed_rect
classifies these exactly as four-point rectangles indexed by Arc H. Rectangle
adjacency maps to arcGraph H, whose two-piece cover covers that triangle core.

Erdos595NoPrismSecondRight.cover_of_star_triangles then proves:
  all triangles of right H consist of stars, and H covered
  => right(right H) covered.
Its starHom maps the full induced graph of stars of right H into H square K2,
using the chosen singleton-side center and the side bit. Right functoriality,
the prism transfer, and RightCoverReduction.triangle_core finish the proof.
second_right_cover applies this under UniqueTriangleEdge H and NoPrism H.
Triangles of H are allowed to share vertices; this extends the previous
vertex-disjoint-triangle criterion.

These are candidate exclusions, NOT a settlement of the conjecture. The
second-arc normal form has genuine prism pairs, so the no-prism hypothesis
cannot be dropped by that reduction. Spec.lean is still unchanged with sorry.

## Subsequent amplification and incidence review (no settlement)

Reviewed generalized Mycielski/apex amplification, large generic or saturated
hosts, exponential targets, and the triangle-incidence hypergraph. No new
palette-amplification theorem or universal covering theorem was obtained.
Important distinctions remain: a construction killing one prescribed coloring
is not a construction killing all countable colorings; an arbitrary external
coloring does not inherit saturation from the uncolored graph. Normalizing a
color on a star and localizing the palette in a countable old graph still defeat
simple fresh-color arguments.

A new finite, EXTERNAL check in /tmp/ordered_trade_grid.py found no 3-by-3 grid
hypergraph in the three previously studied matched-pair ordered patterns on
nine indices. This is not a Lean certificate. The proposed grid consists of
nine distinct labels with three row triples and three column triples. A possible
informal support bound uses parity in each row/column: every index occurs on an
even subgraph of K3,3, hence at least four times, so the 36 total occurrences
in nine four-subsets use at most nine indices. Combined with the earlier
symbolic anti-Pasch test, this obstructs another tempting abstract-hypergraph
shortcut; no general implication from these forbidden configurations was proved.

External access remains unavailable: DNS resolution failed, and a direct
HTTPS DNS request to 1.1.1.1 timed out. No new external result was obtained.
Spec.lean is unchanged with the original sorry; there is still no valid proof
or disproof to submit. No Lean build or solver is pending.

## Copositive/quadratic-form review (no new main theorem)

Reviewed a Motzkin--Straus-type formulation of the clique bound. Informally,
for finite-support nonnegative weights x, K4-freeness gives copositivity of
(sum x)^2 - 3 sum_{unordered G-edges ab} x_a x_b. This is not positive
semidefiniteness on arbitrary signed vectors and does not supply a finite
positive-index representation. Even natural forms for simple disjoint unions
have unbounded positive and negative indices. No theorem converting this
copositivity condition to a countable triangle-free cover was obtained.
No new Lean declaration for this discussion was added.

The existing NegativeInner.lean already includes Hilbert-space approximation
results; treating an infinite-dimensional real Hilbert extension as a new
missing lemma would duplicate completed work. Finite-dimensional and
finite-positive-index covering theorems still do not apply to arbitrary
K4-free graphs without an additional representation theorem.

Spec.lean remains unchanged with its original sorry. There is no main proof
or disproof and no pending build or solver.

## Reversal-invariant arc coloring (new, verified)

Submission/ReversalInvariantArcColoring.lean compiles with olean and only the
permitted axioms. Log: /tmp/reversal-invariant-arc.log.
Namespace: Erdos595ReversalInvariantArcColoring.

* rev reverses a directed edge; rev_rev proves involutivity.
* Valid is weak vertex triangle-color validity on arcGraph G.
* cover_iff: G has a countable triangle-free edge cover iff there is
  c : Arc G -> Nat with c(rev e)=c(e) and Valid G c.
* no_unrestricted_symmetry_refinement: some source G has a K4-free arc graph
  with a two-piece triangle-free EDGE cover, but has no countable reversal-
  invariant weak VERTEX triangle coloring of its arcs. The source is the
  complete graph on Set (Nat -> Fin 2), using large_complete_no_cover.

This is not a solution: source G in the counterexample is not K4-free. The
arc graph's own K4 bound is automatic for all sources and cannot substitute
for the original conjecture's source K4 hypothesis. A generic symmetrization
of the order-sign coloring therefore does not supply the needed cover.

Further review of right-adjoint amplification did not establish a countable-
palette obstruction in a K4-free full target. The third-right countable-base
cover theorem remains the precise verified bound, not a result for all higher
stages. ThirdRightProfileObstruction's non-covered target contains K4.

Spec.lean is unchanged (SHA256 de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45).
Latest check /tmp/spec-reversal-review.log reports its original sorry warning.
There is still no valid main proof or disproof; no solver or build is pending.

## Reversal-invariant finite/countable palette gap (new, verified)

ReversalInvariantArcColoring.lean now additionally imports
Submission.FinitePaletteCompactness (no change to Spec.lean imports).
Its new palette_iff works for ANY nonempty palette C, identifying
HasColoring G C with reversal-invariant Valid colorings of Arc G.
The old cover_iff is a corollary with the same statement as before.
anti_invariant_two_coloring explicitly supplies the opposite-symmetry weak
Boolean vertex coloring for every source graph using order signs.
All four printed audits are permitted; refreshed olean and log
/tmp/reversal-invariant-arc.log.

New file ReversalInvariantFiniteGap.lean imports the preceding file and
LocallyFiniteFolkmanTarget. It compiles with olean and permitted axiom audits;
log /tmp/reversal-invariant-finite-gap.log.
Namespace Erdos595ReversalInvariantFiniteGap.

finite_countable_gap gives ONE countably infinite K4-free source G with:
* an anti-invariant weak two-coloring of Arc G;
* no reversal-invariant Valid coloring by Fin(n+1), for EVERY n;
* a reversal-invariant Valid coloring by Nat.
The source is the already verified countable locally finite target containing
all finite K4-free graphs. Finite Folkman supplies the finite obstructions;
injective coloring of unordered pairs supplies the countable coloring.
This explicitly separates failure of every finite refinement from failure
of countable refinement, even with the actual SOURCE K4 bound.

Additional review of arbitrary-palette Ramsey amalgamation, larger
neighborhood-extension constructions, and adapted-coloring obstructions did
not produce a genuine amplification theorem. Continuous bipartite
amalgamation is already covered by the literal-extension results. Shift
boundaries are not subject to that countable-proper-boundary argument, but
no compatible construction forcing a monochromatic triangle was obtained.

Spec.lean is still unchanged with the original sorry. No proof or disproof
of erdos_595 has been established. No build or solver is pending.

## Finite positive-index representation obstruction (NEW, verified)

Four new files compile with oleans and permitted axiom audits:
* MycielskiFiveOrderObstruction.lean -- /tmp/mycielski-five-order.log
* PositiveIndexTwoOrder.lean -- /tmp/positive-index-two-order.log
* PositiveIndexTwoObstruction.lean -- /tmp/positive-index-two-obstruction.log
* PositiveIndexThreeConeObstruction.lean -- /tmp/positive-index-three-cone-obstruction.log

Namespaces are Erdos595 plus the corresponding filename without .lean.
There are no pending builds. All four files are free of sorry.

### Combinatorial ingredient

MycielskiFiveOrderObstruction defines the 11-vertex Mycielski graph of C5 on
Option (Fin 5 x Bool). old i = some(i,false), copy i = some(i,true), apex=none.
Old-old and old-copy adjacency follows C5; copies are independent and the
apex sees exactly the copies. triangleFree is kernel-verified.

no_balanced_signs: no antisymmetric +/-1 edge labeling balances every C4.
Write a_i for old i -> old(i+1), b_i for old i -> copy(i+1), c_i for
copy i -> old(i+1), and d_i for apex -> copy i. Ten four-cycles imply
  a_i+a_(i+1)-c_(i+1)-b_i=0,
  c_i+b_(i+1)-d_(i+2)+d_i=0.
Summing gives 2 sum a_i=0, contradicting that five +/-1 signs sum oddly.
The Lean proof uses these ten equations, not an exponential search.

increasing_shortcut: for ANY linear-order-valued t separating adjacent
vertices, there are a,b,c,d with edges ab,bc,cd,da and t(a)<t(b)<t(c)<t(d).
square_balance proves this from the preceding sign obstruction, using an
explicit sixteen-case sign analysis. Injectivity of t on all vertices is
NOT required, only separation of edges.

### Positive-index TWO obstruction -- arbitrary ordered fields

PositiveIndexTwoOrder works with ANY ordered field K, ANY K-vector space E,
and ANY symmetric positive semidefinite bilinear form Q on E. Its normalized
representation is 1+t(a)t(b)-Q(q(a),q(b)), positive on the diagonal.
energy_pair and energy_three prove weighted quadratic-energy inequalities.
no_shortcut rules out an increasing three-edge path with an endpoint edge:
the energy inequality contradicts the four strictly positive diagonal norms.
no_mycielski_normalized combines this with the combinatorial obstruction.

PositiveIndexTwoObstruction removes the normalized-chart hypothesis.
no_representation says that the Mycielski graph of C5 has no representation
  p0(a)p0(b)+p1(a)p1(b)-Q(q(a),q(b))
positive on the diagonal and zero on graph edges. Q need not be definite or
finite-dimensional. This is over EVERY ordered field, not just the reals.
exists_rotation chooses alpha avoiding finitely many forbidden slopes;
  p0' = p0+alpha*p1, p1' = p1-alpha*p0, Q'=(1+alpha^2)Q
has p0' nowhere zero. Dividing each vector by its first coordinate gives
the normalized representation and the contradiction.

### Positive-index THREE finite K4-free obstruction -- REAL field

PositiveIndexThreeConeObstruction uses the cone on that Mycielski graph.
cone_card=12, cone_cliqueFree, and cone_covered are all verified.
no_representation rules out
  inner(p(a),p(b))-Q(q(a),q(b))
positive on the diagonal and zero on edges, where the positive real inner
product space P has finrank 3, and the negative real bilinear space E is
arbitrary with Q symmetric positive semidefinite.

For the apex, put u=q(apex), a=p(apex), r=inner(a,a)>Q(u,u).
reduced Q u r is Q(x,y)-Q(u,x)Q(u,y)/r and remains PSD.
Project the positive components to a's orthogonal plane and take an
orthonormal basis. Apex orthogonality makes the corrected form on the
neighbors exactly the original one. The index-two obstruction applies.

IMPORTANT SCOPE: the index-two theorem is field-independent; the index-three
cone theorem currently uses REAL inner products and an orthonormal basis.
Do not claim it has been formalized for arbitrary ordered fields.
The finite cone is already covered, so this is NOT an Erdos 595 witness or
disproof. It definitively blocks the proposed UNIVERSAL REAL positive-index-
three representation bridge, even for finite K4-free graphs and even with
arbitrarily large/degenerate negative spaces. It does not block every finite
positive-index bound or establish an arbitrary-field universal statement.

### Lean details

* Explicitly `include hs hp in` for theorems using the PSD/symmetry hypotheses;
  section variables absent from the theorem statement are otherwise dropped.
* A docstring must follow `include ... in`, not precede it.
* With `open scoped RealInnerProductSpace`, use `inner` notation without the
  `_Real` suffix. Mixing the suffix with this scope caused parser errors.
* In a simp list outside its namespace, fully qualify
  Erdos595PositiveIndexTwoOrder.radius: unqualified radius selected the
  unrelated SimpleGraph.radius.
* `OrthonormalBasis.fromOrthogonalSpanSingleton 2 ha` supplies the plane basis
  from Fact(finrank P=3); no extra FiniteDimensional assumption is required.

Spec.lean is still unchanged with its original sorry. Latest main-file check:
/tmp/spec-positive-index-obstruction-review.log. No main proof or disproof
has been established, and no proof submission was made.

## Incidence shift Ramsey and proper attaching-boundary extension (verified)

IncidenceShiftRamsey.lean embeds the whole incidence graph of all pairs of an
arbitrary well-ordered set into an ordered shift graph over its lexicographic
double. Original vertices map to (low a, high a); a<b pairs map to
(high a, low b). The whole incidence graph has a triangle-free induced
edge-Ramsey host for any nonempty palette. The host need not be bipartite.
The step theorem gives a single K4-free induced free-amalgamation step.
It does not provide a coherent infinite iteration or a color-elimination
operator. Adding edges between the original vertices invalidates the
induced-attaching-subgraph hypothesis.

ProperAttachmentExtension.lean now compiles with permitted axiom audits:
/tmp/proper-attachment-extension.log. The amalgamation theorem literally
extends a prescribed valid Nat edge coloring on a selected old copy if the
attaching induced subgraph has a proper Nat vertex coloring and the host has
a countable triangle-free edge cover. Proper vertex colorability of the
host is NOT needed. incidence_amalgamation specializes this using the
explicit two-coloring of the incidence target. This is an obstruction to
naive prescribed-color iteration, not a main witness or universal covering
proof. Spec.lean remains unchanged with its original sorry.

## Mixed-star triangle split and exact nonstar reduction (NEW, verified)

MixedStarTriangle.lean and SecondArcNonstarReduction.lean compile with oleans
and permitted axiom audits only (propext, Classical.choice, Quot.sound).
Logs: /tmp/mixed-star-triangle.log and /tmp/second-arc-nonstar-reduction.log.

Namespaces: Erdos595MixedStarTriangle, Erdos595SecondArcNonstarReduction.

MixedStarTriangle.disjoint_of_nonstar: for H with UniqueTriangleEdge, the two
Six witness triangles of a triangle in right H are disjoint if one of its
vertices is a nonstar biclique. Uses the already verified matched-equality
lemma when the witnesses overlap. No no-prism assumption is made.
star_iff: all three vertices of a right-H triangle have the same Star status.
triangles_in_kinds: the Boolean Star flag confines triangles to fibers.
second_cover_iff: assuming right H is covered and H has unique triangle edges,
  covered(right(right H)) iff covered(right(nonstars H)),
where nonstars H is the induced subgraph of right H on bicliques with neither
side a singleton. The star fiber maps to H square K2, and the existing
CartesianBoolRight preservation theorem covers its right adjoint.

SecondArcNonstarReduction specializes to base G = arcGraph(arcGraph G),
core G = nonstars(base G), target G = right(core G).
first_cover proves covered(right(base G)) using its independent transversal.
cover_iff proves covered G iff covered(target G), WITHOUT a clique hypothesis.
cliqueFree proves G.CliqueFree 4 -> (target G).CliqueFree 4.
This isolates the remaining case, but DOES NOT cover the nonstar target or
settle either answer to Erdos 595.

## Latest exact external checks -- NOT Lean certificates

/tmp/prism_quotient_check.py computed the prism quotient of the triangle core
of second arc graphs for K3, diamond, K4, K222, K333, and cone(Mycielski C5).
In each case every triangle had one prism mate, so the prism quotient was a
matching. This was true even for K4. It does not imply a triangle-free quotient
for ALL cross-fiber edges or a second-right cover.

/tmp/prism_triangle_hom.py used exact finite graph-homomorphism backtracking
on a nine-vertex graph: three K3 fibers, identity matchings on 01 and 12, and
a cyclic shift matching on 02. It found no arc(K4) or arc^2(K4) homomorphism
into this graph. The graph is in fact 3-colorable: coordinate colors on fiber
0, shifted by +2 on fiber 1 and by +1 on fiber 2. Thus a prism-quotient triangle
does not by itself force a second-right K4. No Lean file for this example.

The ordered quadruple base is the second matched-pair pattern already used
in OrderedQuadRight. An external Z3 query found UNSAT for arc^2(K4) mapping
into this ordered template, suggesting that its second right is K4-free.
This is NOT a kernel-checked theorem. Also UNSAT for arc^2(cone C5), so this
family misses even that four-chromatic K4-free source at stage two.
The arc^3(K4) query returned UNKNOWN after the 180-second timeout; no claim
at stage three is justified.

Files/logs:
* /tmp/order_second_arc_hypergraph.py: custom order-DAG backtracker, timed out
  after 240 sec and 3784 calls; /tmp/order-second-arc-hypergraph.log.
* /tmp/order_second_arc_z3.py: UNSAT for second arc K4, followed by the expected
  error from asking for a model of an unsatisfiable problem;
  /tmp/order_second_arc.smt2, /tmp/order-second-arc-z3.log.
* /tmp/ordered_quad_iterated_check.py and /tmp/ordered-quad-iterated-check.log:
  wheel5 arc2 UNSAT in 44.8 sec, K4 arc3 UNKNOWN after 180 sec.
  /tmp/oq-wheel5-arc2.smt2, /tmp/oq-K4-arc3.smt2.
* Python z3 module is absent, but /usr/lib/x86_64-linux-gnu/libz3.so.4 exists;
  ctypes calls to Z3_mk_config, Z3_mk_context, Z3_eval_smtlib2_string suffice.
  Solver results remain external and were not used as axioms in Lean.

All these jobs have finished. No solver or build is pending. Spec.lean is
unchanged with its original sorry; no genuine proof or disproof was obtained.

## Rank/local-neighborhood and filter review (no new proof)

The continuation beginning at resource time 79h54m rechecked the rank,
local-neighborhood, critical-cardinality, and canonical filter results.
No new Lean theorem or mathematical settlement was obtained. Spec.lean
was not edited.

* RankEdgeCover.cover_of_rank still needs proper countable colorings of
  strict lower neighborhoods; K4-freeness only supplies triangle-freeness.
* Whether proper continuum-sized neighborhood colorings suffice for a
  countable triangle-free edge cover remains unproved here. The prescribed
  adapted-labeling obstructions prevent simply extending arbitrary old
  colorings, even on triangle-free graphs with continuum vertex palettes.
* TriangleFilterCoupling already proves that gluing two triangles with a
  common edge preserves the canonical marginals. Its opposite_nonadjacent
  theorem explicitly forbids the missing opposite edge under K4-freeness.
  Neither that gluing identity nor ResidualTriangleDegree's abundance
  theorem provides a K4 or a contradiction.
* The existing closure and transfinite-amalgamation exclusions were
  rechecked; no new implication bypassing them was found.
* An attempted external status check could not resolve
  www.erdosproblems.com; no current external result was retrieved.

Latest main-file compilation log: /tmp/spec-rank-filter-review.log.
The original sorry remains; no valid proof submission was made.

## Five-state function-power normal form (NEW, verified)

Submission/FiveStatePower.lean compiles to an olean. Log:
/tmp/five-state-power.log. Namespace Erdos595FiveStatePower. All printed
axiom audits use only propext, Classical.choice, Quot.sound.

Allowed is a fixed symmetric relation on Fin 5. States 0,1,2 form a
loopless triangle; 3 and 4 have loops and are mutually related. State 3
sees 0 and 2 but not 1; state 4 sees 1 and 2 but not 0. The only common
Allowed-neighbor of 0 and 1 is 2, and Allowed 2 2 is false.

For any index type I, graph I has carrier I -> Fin 5. Its adjacency is:
  (forall i, Allowed (f i) (g i)) and
  (exists i, (f i=0 and g i=1) or (f i=1 and g i=0)).
cliqueFree proves the FULL graph I is K4-free. An edge's tight coordinate
forces the other two vertices of a hypothetical K4 both to have state 2.

embedding G hG is an INDUCED embedding of every K4-free G into
  graph ((V x V) + V).
At a coordinate anchored by an actual edge a-b, a gets 0, b gets 1,
common neighbors get 2, neighbors of b not a get 4, and other vertices
get 3. Nonedge anchors are constant 3. Additional coordinates in the
right summand use only loop states 3 and 4 to separate isolated vertices.
state_allowed verifies compatibility using K4-freeness exactly in the
common-neighbor/common-neighbor case. A tight coordinate conversely
recovers an actual source edge, proving inducedness.

all_cover_iff proves (in each universe):
  all K4-free graphs have countable TF edge covers
  iff forall I, graph I has such a cover.
NEITHER SIDE is established. This is a new exact normal form, NOT a witness
or a universal covering proof. Spec.lean is still unchanged with its sorry.

Also rechecked the infinite shift Ramsey attachment route. A single shift
amalgamation cannot itself produce a witness: AmalgamationCover already
preserves countable coverability for arbitrary covered input graphs,
regardless of the size or proper chromatic number of the attaching graph.
No color-elimination theorem for a coherent uncountable iteration was found.

## Five-state follow-up review (no settlement)

Rechecked the countable Hales--Jewett obstruction, countable tuple-type
covering theorem, rational midpoint obstruction, local-neighborhood criteria,
and canonical edge/vertex filter distinction against their actual Lean
statements. No new covering theorem or non-covered K4-free witness resulted.
In particular, the five-state normal form still has no proved countable-edge-
coloring conclusion for arbitrary index types. The rational-vector sphere
argument does not itself color these edges; endpoint completeness does not
supply completeness or disintegration of the edge/triangle filters.

No auxiliary theorem was added in this review, and no final-file edits were
made. The original conjecture remains unresolved. Latest final-file check:
/tmp/spec-five-state-followup.log. No valid proof submission was made.

## Further filter and construction review (no settlement)

Re-examined the canonical triangle coupling, residual common-neighbor bound,
and inverse-filter-limit obstruction. No new implication from these results to
K4 existence was obtained. Equal edge marginals do not supply a four-clique
coupling; the existing `opposite_nonadjacent` theorem forbids the opposite edge
in the glued diamond. The residual abundance result remains an eventual
statement, not a stable residual of uniformly large codegree or a simultaneous
extension theorem for several edges.

The external status retry failed: DNS could not resolve erdosproblems.com, and
a direct HTTPS connection to 1.1.1.1 timed out. No external mathematical result
was retrieved. Further consideration of transfinite apex extensions, root
Cayley graphs, and finite-state coordinate constructions produced no new main
lemma. No Lean theorem was added, no edit was made to Spec.lean, and no valid
proof submission was made.

## Mutual-ultrafilter follow-up (no settlement)

Reviewed Work's first/second mutual covering results, finite maximal-clique
codes, OrAfterMutualCover, and the third-stage support obstructions. The first
mutual extension of a countable finite-clique base is properly countably
colorable by the later FiniteCliqueUltrafilterColoring theorem; the second is
countably TF edge-covered. The third generic extension remains unresolved.

No argument was obtained that converts a countable external edge coloring of
the third stage into a finite palette on the original generic graph. Failure
of original finite-edge-cover support is insufficient: the existing
FiniteEdgeSupportTowerCover examples retain countable covers at every finite
stage. No new Lean theorem or final-file edit was made in this review.

## Ramsey and prescribed-extension follow-up (no settlement)

Reviewed the binary infinite Hales--Jewett lemma against the stronger existing
finite-bipartite infinite-palette Ramsey step. Neither supplies simultaneous
homogenization of infinitely many attachments. The special infinite shift
Ramsey targets still lack a coherent countable-color elimination argument.

Rechecked AdaptedReflectionObstruction and DetectorExtensionReduction. Failure
of one prescribed adapted labeling, even for a valid edge coloring of a
covered K4-free graph, does not obstruct all countable edge colorings of an
extension. In particular, an independent family of new apices can always use
a fresh color on its spokes when the old coloring is allowed to be relabeled.
No argument forcing a palette obstruction at an uncountable limit was found.

No new Lean theorem or final-file edit was made. Spec.lean still contains its
original sorry. Latest compilation log: /tmp/spec-ramsey-extension-followup.log.
No valid proof submission was made.

## Five-state finite/countable palette boundary (NEW, verified)

Submission/FiveStatePaletteBoundary.lean compiles to an olean. Log:
/tmp/five-state-palette-boundary.log. All four printed axiom audits use only
propext, Classical.choice, and Quot.sound.

* coordinateEmbedding extends functions along any coordinate injection using
  the loop state 3 outside its image. It is an induced graph embedding.
* no_finite_palette proves that the full five-state graph on ANY infinite
  coordinate type has no valid finite edge palette, using finite Folkman and
  the existing induced representation of finite K4-free graphs.
* countable_coordinate_cover proves that countably many coordinates give a
  countable bipartite (hence triangle-free) edge cover, indexed by a tight
  coordinate separating states 0 and 1.
* fixed_palette_boundary combines these facts for the single graph on
  Nat -> Fin 5: it is K4-free, countably covered, and defeats every finite
  palette. This is NOT a witness for Erdos 595.

The full graph for arbitrary uncountable coordinate sets remains unresolved.
No edit was made to Spec.lean; its original sorry remains. No valid main proof
submission was made.

## Nonstar-target neighborhood obstruction (NEW, verified)

Submission/NonstarNeighborhoodObstruction.lean compiles to an olean. Log:
/tmp/nonstar-neighborhood-obstruction.log. All printed audits use only the
permitted axioms; unit_nonstar and reducedUnit use no axioms at all.

* unit_nonstar: two distinct neighbors of v make both sides of unit H v
  nonsingletons, so it is a nonstar biclique.
* arcUnitNonstar/reducedUnit: if every vertex of arcGraph G has two distinct
  neighbors, the first arc unit lands in core G, and currying gives
  G ->g target G for the exact SecondArcNonstarReduction target.
* cone_arc_neighbors: coneGraph H has the required arc-degree condition
  whenever the base vertex type is nontrivial. Isolated base vertices cause
  no problem because the apex supplies the other endpoint's alternatives.
* neighborhoodHom: H maps into the neighborhood of the apex image in
  target (coneGraph H).
* arbitrarily_large_neighborhoods: for EVERY nonempty palette C there is
  a K4-free, COUNTABLY COVERED target (coneGraph H) with a neighborhood
  admitting no proper C-coloring. The base H is an existing triangle-free
  high-chromatic graph, and coverability follows from the cone cover and
  the exact nonstar cover equivalence.

Consequently a uniform countable or continuum proper-neighborhood palette
cannot be inferred from the nonstar normal form. This is a method obstruction,
NOT a witness for Erdos 595 or a universal covering theorem. Spec.lean remains
unchanged with its original sorry; no valid main proof submission was made.

## Canonical-filter strengthening review (no settlement)

Revisited exact triangle coupling, canonical positive restriction, ordered
triangle marginals, and critical-cardinality reduction. No K4-free-specific
edge-filter completeness, primeness, or simultaneous-extension theorem was
obtained. Gluing along one edge still yields a diamond with nonadjacent
opposite vertices, not the missing four-clique. Low-degree residual pruning
also did not produce a justified stable residual or a cover of all discarded
stages. No new Lean theorem was added in this review.

Further review of finite-cover right-adjoint bases and their finite parameter
representations yielded no countable-cover theorem. Existing exact round-trip
reductions must not be treated as an amplification or as a solution.

Spec.lean remains unchanged with the original sorry. No valid proof or
disproof submission was made during this review.

## Unconditional Paley AP obstruction (NEW, fully verified)

The earlier active modular-rank development is now complete. These files
compile to oleans and all printed axiom audits contain only propext,
Classical.choice, and Quot.sound:

* Submission/APModularTransfer.lean
  Log: /tmp/ap-modular-transfer.log
  vector_constant transfers a full-rank reduced triangle incidence matrix
  over F3 to constancy of rational-vector AP labels, for ALL independently
  chosen midpoint rules. Coefficients -2,1,1 become 1,1,1 modulo 3.
* Submission/PaleyAPObstruction.lean
  Log: /tmp/paley-ap-obstruction-clean.log (exit 0)
  certificate is a kernel-checked 67-by-67 left inverse over ZMod 3 for the
  incidence matrix of the first 67 Paley17 triangles, omitting edge zero.
  Each column has at most three nonzero entries. No native_decide or external
  solver result is trusted. The inverse rows are packed in base three.
* Submission/PaleyAPApplication.lean
  Log: /tmp/paley-ap-application.log (successful fresh rebuild)
  triEdges_correct and triangles_correct connect the certificate tables to
  the existing Paley graph. all_edges_constant proves that every labeling
  of its edges in ANY rational vector space making every triangle an AP is
  constant, regardless of midpoint choices. no_nondegenerate_AP_labeling
  rules out nonconstant AP labels on every triangle unconditionally.

This strengthens ArithmeticProgressionObstruction's fixed-midpoint and
conditional finite-Ramsey obstruction. It closes that sufficient labeling
route, NOT the original conjecture. Paley17 is finite and already has a
verified three-piece TF cover in PaleyObstruction.lean.

Build engineering notes: direct matrix multiplication and whole quantified
finite checks caused OOM (137). Sparse row checks on explicit lists worked.
The final symbolic padded_sum uses Fin.lastCases on its column index. The
older proof via Fin.sum_univ_castSucc followed by unrestricted simp hung;
do not restore it. Temporary profiling and progress commands have been
removed from PaleyAPObstruction.lean. Its clean build takes about 2 minutes.
The disposable PaleyAP*Check/Profile files are not imported by the result.

Further mathematical review of saturation, asymmetric infinite triangle
Ramsey, ultrafilter towers, finite-state powers, and residual-degree pruning
produced no new main lemma. Spec.lean is unchanged at the original SHA256
and still contains its sorry. Latest check: /tmp/spec-paley-ap-followup.log.
No valid main proof or disproof, and no new submission, was made. All active
Lean builds from this continuation have finished.

## Free-corner and reduced-power review (no settlement)

Rechecked the free-corner asymmetric Ramsey reduction against the actual
infinite shift, incidence, and finite-bipartite Ramsey theorems. None provides
the required corner-preserving K4-free infinite-red / finite-blue host.
Finite-stage homogenization and separate compatible attachments do not give
coherent countable-color elimination at an uncountable limit.

Also re-examined generic countable-target exponentials and countably complete
reduced powers. The positive-fiber argument for a countable color partition
does not make three separately positive fibers jointly positive. No valid
filter primeness, disintegration, or simultaneous-extension step was found.

Reminder: AllFieldOrthogonalityCover.lean ALREADY excludes every finite-
dimensional nonisotropic bilinear candidate over arbitrary fields, including
all finite signatures (3,n). Older UltrafilterNotes sections calling (3,3)
unresolved are superseded by that theorem. No universal finite-positive-index
representation of arbitrary K4-free graphs has been proved.

No auxiliary theorem was added in this review, no final-file edit was made,
and no valid proof submission was made. Spec.lean retains its original sorry.
Latest main-file check: /tmp/spec-corner-power-review.log.

## Maximal-extension review (no settlement)

Reviewed free-amalgamation preservation, well-ordered literal-color extension,
nonedge diamond witnesses, and possible Hilbert/finite-rank homomorphism
representations. No theorem converting maximal K4-freeness into countable
non-coverability, or a universal covering theorem, was obtained. Adding
nonedge witnesses must not be treated as a color-elimination argument.
No new maximal-completion theorem was formalized in this review.

No proof file was added or changed. Spec.lean remains unchanged with its
original sorry. Latest check: /tmp/spec-maximal-extension-review.log.
No valid proof/disproof submission was made.

## Third-stage generic and reduced-power re-review (no settlement)

Rechecked GenericUltrafilterUniversality, FiniteCliqueUltrafilterColoring,
OneSidedSupport, FixedGenericReducedPower, FixedFiniteReducedPower, and
FixedPowerSupportObstruction. No new mathematical implication was established.
In particular, generic finite extension does not justify compression of the
ultrafilter-indexed third-stage cone supports, and no reflection theorem for
arbitrary external countable edge colorings of the reduced powers was proved.
The countable-index finite-factor powers are already covered despite having
no finite palette, so finite Folkman obstructions do not close this gap.

No Lean proof code or the main statement was changed. Spec.lean still contains
its original sorry. Check log: /tmp/spec-third-stage-reduced-power-review.log.
There is still no valid proof/disproof submission.

## Verified diamond maximal completion

Submission/DiamondCompletion.lean is complete, with olean and clean log
/tmp/diamond-completion.log. Namespace Erdos595DiamondCompletion. Every printed
axiom audit uses only propext, Classical.choice, Quot.sound.

The graph uses finite Node trees: leaves are original vertices; a pair of
opposite-tag forks over each nonadjacent pair forms a diamond. Validity requires
nonadjacent children. Every nonedge in the resulting graph has an adjacent pair
of common neighbors, giving maximality among K4-free graphs on its carrier.
The original graph embeds inducedly, and cliqueFree proves K4-freeness whenever
the original is K4-free.

color_valid and color_old prove literal extension of EVERY prescribed valid
Nat edge coloring. All new edges use only 0 and 1: equal-height fork-mate edges
use 1 and parent-child edges use 0. At a maximum-height fork in a triangle,
one neighbor must be its mate and the other a child. Thus the incident colors
differ, regardless of the original colors.

countable_cover_iff and maximal_extension prove exact preservation of countable
TF edge coverability under this completion. This is NOT a noncovered witness
or a universal cover theorem. It does not rule out a proof using maximality;
it shows that adding all these nonedge witnesses does not change the covering
status, and does not ensure witnesses survive covered-edge deletions.

Spec.lean is unchanged with its original sorry. The main conjecture remains
unresolved. No valid proof/disproof has been submitted.

## Corner-host and higher-clique review after diamond completion

Revisited FreeCornerArrow, AdaptedReflectionObstruction, FiniteAdaptedExtension,
MiddleCornerObstruction, MiddleEqualityThreeColor, and OrderedTriangleFilter.
No new proof code or main mathematical implication was obtained. The infinite
asymmetric marked-corner host remains unconstructed. No known larger-clique-bound
noncovered graph plus covered K4-hitting deletion was found in this development.
A hypothetical such deletion argument was not asserted as a theorem.

Also re-examined selector graphs of triangle hypergraphs, neighborhood/model
closure arguments, reduced powers, and external-color saturation. None supplied
the missing countable-palette step. Earlier no-middle-coloring counterexamples
remain applicable, including freedom to choose the vertex order. The verified
diamond completion does not give robust witnesses after covered-edge deletions.

Spec.lean remains unchanged with its original sorry. Check log:
/tmp/spec-corner-host-followup.log. No valid proof/disproof has been obtained.

## Finite induced Ramsey host and unconditional -1/3 margin obstruction

New completed files:
* Submission/FiniteInducedRamsey.lean
  namespace Erdos595FiniteInducedRamsey
  log /tmp/finite-induced-ramsey.log
* Submission/PaleyRamseyMargin.lean
  namespace Erdos595PaleyRamseyMargin
  log /tmp/paley-ramsey-margin.log

Both oleans are in .lake/build/lib/lean/Submission. All printed axiom audits
contain only propext, Classical.choice, Quot.sound.

finite_binary_clique uses the existing
Combinatorics.Diagonal.hasRamseyProperty_choose from
FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean (already
transitively imported by FormalConjecturesUtil). Thus the project did have
an ordinary finite binary Ramsey theorem for arbitrary clique sizes.

finite_induced_ramsey: every finite K4-free graph H has a finite K4-free
host G such that every binary edge coloring of G has an INDUCED copy of H
with all H-edges monochromatic. The proof takes disjoint H-copies indexed
by injections into an ordinary finite Ramsey clique, then applies the
existing finite partite homogenization to all pairs of parts.

finite_ramsey_against_triangle and exists_paley_ramsey_host remove the
previous conditional Ramsey hypothesis from the Paley vector obstruction.
exists_no_third_triangle_hit gives ONE finite K4-free host having no
UnitTriangleHit assignment at threshold -(1/3) in ANY real Hilbert space,
including arbitrary nonseparable spaces. The finite graph is of course
countably edge-covered, so this is only a uniform-margin method obstruction.
It does NOT exclude every possible negative margin, nor variable margins.

Further review of triangle-hypergraph roots, full ultrafilter flattening,
and reduced powers yielded no settlement. Keep the finite-factor and
countably-complete cases separate: FixedFiniteReducedPower uses the fine
filter on FINITE subsets, which is not countably complete; the exact
countably-complete representation uses COUNTABLE factors instead.
CompleteFilterProduct already proves the finite-factor / countably-complete
case is finitely vertex-colorable.

Spec.lean is unchanged (SHA256
 de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45)
and still contains the original sorry. Main-file check:
/tmp/spec-finite-ramsey-margin-review.log. No valid proof/disproof submission.
No active build is pending. Submission/FiniteRamseyCheck.lean was only a
scratch #check file and has been removed.

## Higher-right-cone and direct-construction review (no settlement)

Rechecked HigherConeOddBound, RightTowerCountableCover, ThirdConeObstruction,
ThirdRightProfileObstruction, SecondArcNormalForm, and the finite/infinite
partite boundaries. No new mathematical implication or proof code was obtained.

Important existing bound: RightTowerCountableCover.third_right_countable_cover
already rules out EVERY K4-free third right adjoint of a COUNTABLE base, not
just single cones. Any new countable-base candidate in that family must be
at a higher stage. HigherConeOddBound gives K4-freeness at each fixed stage
from a finite odd-walk exclusion on the cone base; it gives no edge-coloring
lower bound. No such lower bound was established in this review.

Further consideration of graphical hypergraph roots, marked-corner forcing,
transfinite clone constructions, countably complete reduced powers, and
external-color compactness yielded no new proof. No finite-palette theorem
was promoted to a countable-palette assertion. No new submission was made.

Spec.lean remains unchanged with its original sorry. Latest check:
/tmp/spec-higher-right-cone-review.log. The verified finite Paley Ramsey-margin
obstruction from the previous continuation remains auxiliary only.

## Imported utility audit (no overlooked settlement)

Audited FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean,
Hypergraph/ThreeUniform.lean, SetTheory/Cardinal/SimpleGraph.lean, and the
Mathlib graph-partition references. The relevant utilities define
HasFiniteRamseyProperty, HasCountableRamseyEscape, IsErdosHajnalExceptional,
and IsObligatory; they do not prove the needed partition or obligatory
hypergraph theorems. No overlooked universal cover theorem or K4-free
noncovered witness was found. The ordinary finite binary Ramsey theorem
already used in FiniteInducedRamsey remains available and correctly audited.

No proof code or conjecture statement was changed in this continuation.
Further consideration of triangle closure, graphical/binary hypergraphs,
model-theoretic compactness, and edge ideals did not yield a new implication.
Spec.lean retains its original sorry. Latest check:
/tmp/spec-imported-utility-audit.log. No valid proof or disproof submitted.

## Algebraic and group-construction re-review (no settlement)

Rechecked RootLattice.lean and FiniteRootCayley.lean. Both are already exact
cover-preserving normal forms; their translation-invariant-cover conclusions
use the root-specific countable_cover_iff theorem, not a general averaging
argument for arbitrary Cayley graphs. These results do not construct a
noncovered input.

Further consideration of mixed-sign group presentations, exponent-three
root graphs, and finite-support algebraic labels produced no new proved
implication. In particular arbitrary external countable edge colorings were
not made translation-invariant or measurable. No proof code was added.

Spec.lean remains unchanged with the original sorry. Latest check:
/tmp/spec-algebraic-group-review.log. No valid proof/disproof submission.

## Earlier-neighborhood ordering review (no settlement)

Re-examined the sufficient condition that some vertex order makes every
strict earlier neighborhood countably properly colorable. This condition
would give the requested countable triangle-free edge cover, but no universal
ordering theorem was established. FiniteEarlierNeighborhoodObstruction only
rules out a uniform finite bound; PrescribedOrderObstruction concerns an
already prescribed coloring. Neither excludes choosing a new countable
coloring and a new order together.

No compatible transfinite ordering/coloring construction, or counterexample
to the countable ordering criterion, was proved. No proof code changed.
Spec.lean retains the original sorry; latest check:
/tmp/spec-earlier-neighborhood-review.log. No valid proof/disproof submission.

## Latest continuation: residual-wheel and external-color reflection review

Reviewed MinimalRobustOddWheel, RobustOddWheel, NoCountableK4Target,
ThirdBadTriangle, the higher cone/right-adjoint criteria, and the adapted
coloring reductions. No new main implication or Lean theorem was obtained.

The fixed induced odd wheel in every covered-edge residual does not itself
force K4: the common-neighborhood sets can remain independent. The avoiding
ultrafilter theorem detects failure of finite covering, not countable
covering. No theorem reflecting an arbitrary external Nat edge coloring
through the generic mutual-ultrafilter tower was established. Likewise no
higher-cone lower bound or universal earlier-neighborhood ordering was proved.

Spec.lean remains unchanged with its original sorry. No valid proof/disproof
is ready and no new proof submission was made. No solver or build is pending.

## Latest continuation: infinite asymmetric Ramsey / shift-amalgamation review

Ordinary continuous partite constructions over countably properly
vertex-colorable bases are already excluded by TransfiniteAmalgamationCover.
InfiniteShiftRamsey supplies a whole-shift-graph Ramsey step with arbitrary
palette and potentially uncountably chromatic TF base, so this is a genuine
step outside that exclusion. However AmalgamationCover still preserves
coverability at each single step, and no coherent uncountable iteration or
palette-growth theorem was obtained. Finite/countable iteration cannot
suffice because covered edge graphs form a sigma-ideal.

No new Lean theorem, proof, or disproof was produced. Spec.lean is unchanged;
no valid submission is ready and no build or solver is pending.

## Further continuation: construction and residual review (no settlement)

Revisited shift-Ramsey amalgamation, prescribed adapted-color obstructions,
triangle-copy identifications, and persistent minimal odd wheels. No fixed
K4-free new-color forcing host or residual wheel-shortening implication was
found. Single induced amalgamations still preserve coverability; failure to
extend a prescribed coloring does not exclude a different coloring.

Further consideration of saturation, group presentations, and earlier-neighbor
orders yielded no proved missing implication. No Lean theorem was added and
Spec.lean remains unchanged with its original sorry. Latest compilation log:
/tmp/spec-current-continuation-check.log. No valid proof/disproof is ready.

## Continued bilinear and arc/right review (no settlement)

PositiveIndexThreeConeObstruction already rules out universal real
positive-index-three representations by a finite K4-free cone. No higher-index
universal representation was proved. The reference site remains inaccessible
(DNS failure; a direct HTTPS DNS request also timed out).

ArcRoundTrip supplies BOTH right_arc_cover_iff and right_arc_cliqueFree_iff.
Consequently the proposed use of the two-covered arc base is an exact
reformulation, not a universal covering theorem: proving coverability of its
K4-free right adjoint still requires the missing original implication.

Further consideration of labeled triangle-copy amalgamations, group
presentations and transfinite apex closure yielded no valid construction.
No Lean source was changed. Spec.lean still contains its original sorry;
no complete proof/disproof is ready.

## Completed Mycielski margin amplification (auxiliary, not a settlement)

Submission/MycielskiMargin.lean is complete and verified. Its theorem
exists_no_uniform_triangle_hit strengthens the earlier Paley obstruction to
EVERY fixed positive real margin delta. For each delta > 0 there is one finite
K4-free graph that has no unit-vector triangle-hitting assignment with threshold
-delta in any real inner-product space (arbitrary dimension, no completeness or
separability requirement). All eight printed axiom audits use only propext,
Classical.choice, and Quot.sound. Build log: /tmp/mycielski-margin.log.

The finite reflection step uses a Mycielski graph and a finite Bool x Bool
induced Ramsey host. It improves a universal all-edge margin delta to
 delta + delta^6 / 512
when 0 < delta <= 1/2. Iterating contradicts the triangle bound delta <= 1/2.
The all-edge obstruction transfers to triangle-hitting via the existing finite
asymmetric Ramsey theorem. This does NOT exclude variable strict negative
margins. Each resulting graph is finite and therefore countably edge-covered.
It is NOT an Erdos 595 witness.

## Subsequent external-color and construction review (no settlement)

Reviewed the higher right-adjoint candidates, generic/saturated apex extensions,
triangle-hypergraph roots, and possible transfinite Mycielski analogues. No new
main implication was established. In particular, an arbitrary external coloring
still cannot be assumed saturated or internal, and palette exhaustion on a
countable old subgraph is not a fresh-color obstruction. The ordinary Mycielski
construction creates no triangles at its apex; its triangles descend through
parent maps, so vertex-chromatic amplification is not triangle-edge-color
amplification. No alternative K4-free countable-color forcing construction was
proved.

Spec.lean remains unchanged with its original sorry. No valid proof or disproof
is ready for submission. Latest main-file check for this review is recorded in
/tmp/spec-external-color-review.log. No background build is pending.

## New verified continuation: countable clone-history preservation

New auxiliary file: Submission/CloneHistoryCover.lean (140 lines).
Build log: /tmp/clone-history-cover.log. Both printed axiom audits use only
propext, Classical.choice, and Quot.sound; the final build is clean.

Definitions ValidHistory and Inherited describe root : V -> B + I and
history : V -> Set I. An apex root cannot belong to its own history. Each
edge either projects to an edge between two base roots, or joins an apex
root i to a vertex whose history contains i. Each history is countable;
the stage type I and the vertex type V have arbitrary cardinality.

cover proves countable triangle-free edge covering when the base has a
countable proper vertex coloring, via a locally countable conflict cover.
cover_of_covered_base strengthens this to a base that merely has a countable
triangle-free edge cover. It separates base-root and apex-root vertices;
the former pull their cover back from the base, while the latter have the
countable-history conflict cover. Edges across the two classes are harmless.
No clique bound is needed for either theorem.

This excludes constructions ADMITTING THE SPECIFIED ROOT/HISTORY DATA,
including the proposed finite-ancestry clone/apex scheme when its inherited
edges have that form. A universal root/history representation for arbitrary
K4-free graphs was NOT established, and no blanket theorem about all possible
transfinite amalgamations is asserted. Direct apex attachment over old large
sets need not have countable histories and is not ruled out by this result.

The main conjecture remains unresolved. Spec.lean is unchanged, SHA256:
de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45
No valid main proof/disproof is ready for submission.

## New verified continuation: existing-hub clone extension

New auxiliary file: Submission/HubCloneExtension.lean.
Build log: /tmp/hub-clone-extension.log. The final build is clean; all four
printed audits use only propext, Classical.choice, and Quot.sound.
An olean was generated under .lake/build/lib/lean/Submission/.

Construction: given an old graph G, an induced triangle-free subset D, and
an old vertex r, add a clone copy of D. Old--clone edges inherit G-adjacency
within D, with additional edges from every clone to r; clone--clone edges
are those of G.induce D. The hub r is allowed to belong to D.

triangle_at_clone: every triangle involving a clone contains the old hub.
cliqueFree: K4-freeness of G is preserved.
color_valid and color_old: EVERY valid old Nat edge coloring extends
LITERALLY. Hub--clone edges get 0 and all other new edges get 1. Every new
triangle has both colors, regardless of the old colors. countable_cover
records the covering consequence. The literal extension is suitable for
coherent stage-extension arguments; no theorem about arbitrary unmodeled
transfinite graph operations is claimed.

This removes the proposed existing-hub clone modification as a color-forcing
step. Direct apex attachment over an arbitrary old TF set is different and
is not covered by this lemma. Further review of residual odd wheels,
filter coupling, and full apex saturation did not yield a settlement.
In particular persistent wheels still do not force a fourth common vertex.

Spec.lean is unchanged with its original sorry. Latest main-file check:
/tmp/spec-hub-clone-review.log. No complete main proof or disproof is ready.

## Continued external-color, apex, and higher-right review (no settlement)

Reviewed the fixed finite and fixed generic reduced-power normal forms and the
exponential exclusions. No bridge from an arbitrary EXTERNAL natural-number
edge coloring to an internal coloring, a countably complete ultrafilter, or a
finite palette was established. Finite-factor/countably-complete products are
already covered by the existing CompleteFilterEdgeCover result; a countable
fixed target without a finite palette remains different.

Revisited adapted apex extension and the infinite asymmetric marked-corner
Ramsey host. The explicit triangle-free prescribed-color obstruction does not
obstruct recoloring. A finite or countable sequence of extensions does not
force exhaustion of the palette, and backward homogenization through an
uncountable partite sequence still has no justified compatibility argument.

Reviewed RightTowerCountableCover and HigherConeOddBound, particularly the
fourth-right possibility. The third-right countable-base exclusion is already
proved; higher finite-stage clique bounds alone supply no noncoverability.
The general claim that coverability transfers through a K4-free right adjoint
would, via the exact arc/right round trip, itself imply the universal negative
answer. It was NOT proved. Further consideration of graphical triangle closure,
countable support, and canonical triangle-filter couplings yielded no new main
implication.

No Lean theorem was added in this review. Spec.lean remains unchanged with its
original sorry; no complete proof/disproof is ready. Main-file check for this
review: /tmp/spec-higher-right-external-review.log. No background job is pending.

## Subsequent exponential-reflection review (no settlement)

The proposed implication from a countably covered exponential to a finite
palette on its countable target is not valid without additional hypotheses:
the existing locally-finite target transfer already gives covered exponentials
for targets with unbounded finite triangle-edge palettes. No argument supplying
the needed extra hypothesis for the fixed countable generic target was found.

Revisited the universal nine-point finite-fiber bundle and higher right stages.
The existing first/second-stage covering results and finite odd-walk clique
bounds remain the only applicable conclusions; no higher-stage countable-color
lower bound was obtained. The finite/binary infinite Hales--Jewett results do
not overcome the separately proved countable-palette or infinite-alphabet
obstructions.

Informal additional avenues considered, NOT promoted to theorems:
* Countable-condition coloring forcing does not give downward absoluteness.
  In particular, merging two prescribed countable colorings can fail: their
  stars on a common countable independent root can exhaust all colors on a
  required new edge, even in a K4-free book of triangles.
* Arbitrary positive-semidefinite negative spaces over non-Archimedean fields
  go beyond the diagonal finite-support result. No noncovered example, universal
  representation theorem, or general covering theorem for that extension was
  proved. The finite positive-index-two/three representation obstructions still
  apply where their hypotheses hold.
* Neither greedy neighborhood/pivot removal nor graphic-matroid triangle
  closure supplied a decreasing rank proving countable termination.

No new Lean theorem was added. Spec.lean still has its original sorry and
unchanged conjecture/import. Main-file log: /tmp/spec-exponential-reflection-review.log.
No valid proof/disproof is ready and no background job is pending.

## Further canonical-filter and amplification review (no settlement)

The reference-site request again failed at DNS resolution. No new external
result was obtained.

Reviewed exact triangle/edge filter marginals, their diamond fiber product,
canonical joint-completeness failure, and avoidance-marginal isolation. The
existing gluing does not supply a K4: opposite vertices of the diamond are
necessarily nonadjacent. Countable completeness was not upgraded to an
ultrafilter, precipitousness, a coherent inverse-limit thread, or a fourth
clique coupling. These remain genuinely missing implications.

Reviewed possible edge-addition/Zykov-type amplification, higher right towers
of odd-girth cones, and mutual-ultrafilter towers of the countable generic
base. No operation was proved to force a fresh color for arbitrary countable
palettes while preserving K4-freeness. In particular selecting individual old
edges of different colors does not permit identifying their endpoints while
retaining all prescribed old copies and colors. The finite-palette and
complete-graph Ramsey theorems still do not provide the requested witness.

No larger-clique-bound infinite Ramsey witness was found among the verified
files that could simply be sharpened to K4-freeness. No new Lean theorem or
main proof/disproof was added. Spec.lean remains unchanged with its original
sorry. Latest check: /tmp/spec-canonical-amplification-review.log. No job pending.

## Further continuation: hypergraph realization and asymmetric Ramsey review

No new Lean theorem or source modification was made in this review, and the
conjecture remains unresolved. Spec.lean retains its original statement and
sorry.

Reviewed the graphical-realization route, arc/right palette comparisons,
Cartesian prism amplification, and the infinite-red/finite-blue corner-Ramsey
reduction. The proposed Cartesian H x K2 right-adjoint step is already covered
by CartesianBoolRightCover.lean's cover-transfer result; it supplies no new
lower bound. TupleTypeCover.lean and RestrictedTupleCover.lean were checked
for their exact scope: even arbitrary restricted families of finite tuples
with relatively order-type-invariant adjacency have the verified cover. Thus
an asymmetric corner-Ramsey host within that scope cannot be a witness.

The missing asymmetric Ramsey host was not constructed. No theorem about
arbitrary graphical triangle hypergraphs, abstract non-Archimedean PSD
representations, universally extendable colorings, or external colors of
reduced products was established. These discussions are exploratory only.

Main-file review log: /tmp/spec-hypergraph-asymmetric-review.log.
No proof submission was made and no background build or solver is pending.

## Further continuation: edge gluing and palette forcing

The conjecture remains unresolved; no new Lean result or source edit was made.
Reviewed AmalgamationCover, ProperAttachmentExtension, and the continuous
transfinite extension results against a proposed edge-gluing construction.
Free amalgamation preserves countable TF edge covers, and countably properly
colorable attachments (in particular individual edges) permit literal
extension of prescribed valid colorings under the stated host hypotheses.
No cyclic-identification construction was established that both preserves
K4-freeness and defeats every Nat edge coloring.

Additional discussions of mixed-sign group presentations, saturated generic
models, neighborhood orderings, and the generic-target exponential remained
informal. No new theorem from those discussions may be used as a result.
In particular no arbitrary-color transfer, countably complete ultrafilter
extension, or universal earlier-neighborhood ordering was proved.
Spec.lean is unchanged. No proof submission was made, and no job is pending.

## Further continuation: higher-right lower-bound review

No proof or disproof was obtained, and no Lean source file was changed.
Rechecked HigherConeOddBound, FiniteFiberOddBound, RightTowerCountableCover,
ArcRoundTrip, RightCoverReduction, and ThirdRightProfileObstruction. The
higher-cone result is a finite odd-walk sufficient condition for K4-freeness,
not an edge-palette lower bound. No transfer from a hypothetical countable
edge coloring of a fourth or higher right stage to a contradiction in its
base was proved. Those stages have not been ruled out in general.

The third right stage of a countable base is already covered when K4-free.
The unrestricted third-stage non-coverability example in
ThirdRightProfileObstruction contains a large complete graph and is expressly
not a witness. Arc/right round-trip equivalences give no independent lower
bound without first establishing one for the original graph.

A new request to the public problem page failed at DNS resolution; a direct
request to Google's public DNS HTTPS endpoint timed out. No external source
was obtained and no published result is being asserted on that basis.
Spec.lean remains unchanged with its original sorry. No submission or
background job is pending.

## Further continuation: local chromatic and geometric review

No settlement or new Lean theorem was obtained. Rechecked RankEdgeCover,
LocalChromaticProduct, FiniteEarlierNeighborhoodObstruction,
ArcIndefiniteEmbedding, and the positive-index representation obstructions.
Countably properly colorable full neighborhoods suffice for an edge cover;
this does not prove such a local property for arbitrary K4-free graphs or
for the unresolved non-diagonal, non-Archimedean PSD candidates.
FiniteEarlierNeighborhoodObstruction already shows that two TF edge pieces
do not impose any uniform finite bound on earlier-neighborhood proper
chromatic numbers, even when the order can be chosen freely. No lower bound
against countable EDGE colorings follows merely from large local vertex
chromatic numbers. The additional geometric discussions remain informal.
Spec.lean is unchanged with its original sorry; no submission or job is pending.

## Further continuation: simultaneous diagonalization and structural review

No settlement or new Lean theorem was obtained. Spec.lean was not modified.

Revisited simultaneous triangle-hitting requirements, independent-apex
extensions, and the possibility of a finite hypergraph obstruction forced
by uncountable chromatic number. No construction meeting all the coloring
requirements while preserving K4-freeness was proved. The existing
matched-pair root obstructions exclude that particular realization; no
unavoidability theorem for arbitrary non-countably-colorable triangle
hypergraphs was established.

Also reconsidered infinitary partite constructions, graphical lifts of
hypergraphs, and generic-target exponentials. These discussions remained
informal and supplied no new lower bound against arbitrary external Nat
edge colorings. Countable-index reduced products are already excluded by
CountableEdgeProduct.lean and are not a new candidate.

Main-file check: /tmp/spec-diagonal-structural-review.log. The original sorry
remains. No valid proof submission was made, and no background job is pending.

## Further continuation: cone profile omission (new, verified)

New file: Submission/ConeProfileOmission.lean, namespace
Erdos595ConeProfileOmission. It compiles cleanly and has a built olean.
All five printed axiom audits use only propext, Classical.choice, Quot.sound.
Log: /tmp/cone-profile-omission.log.

For an independent root set R joined completely to a triangle-free base H,
a valid edge coloring c gives each base vertex b the full function
r -> c(r,b). If H has no proper coloring by R -> C, some adjacent a,b have
identical profiles. The color of ab is absent from their common profile.

Verified declarations include edge_color_omitted, exists_omission,
not_all_profiles_surjective, two_cover, cliqueFree, and exists_base.
The latter uses the existing arbitrary-palette high-chromatic triangle-free
construction to supply bases for every root set and palette.

Crucial scope: every graph constructed in this file has a TWO-piece TF edge
cover. An omitted profile color is not a color omitted from the entire old
graph or from the entire global coloring. No K4-preserving mechanism linking
these local omissions into a contradiction for an arbitrary Nat coloring
was proved. The additional discussions of transfinite profile systems,
exponentials, and hypergraph lifts remain informal.

Spec.lean is unchanged, with its original sorry. Main-file check:
/tmp/spec-cone-profile-review.log. No valid proof submission was made.
No background job is pending.

## Further continuation: recoloring and algebraic review

No settlement or new Lean theorem was obtained. Spec.lean was not modified.

Reviewed the single-vertex recoloring/extension route. Arbitrary labeled
triangle-free neighborhoods need not admit adapted Nat vertex labelings;
AdaptedLimitObstruction and AdaptedBipartiteSwapObstruction already supply
verified counterexamples. Thus neither unrestricted greedy extension nor
its compatibility at limits was established.

The proposed F3 triangle-relation quotient shortcut is already refuted by
F3Obstruction.lean; arbitrary rational midpoint choices are already refuted
by PaleyAPObstruction.lean and APModularTransfer.lean. An independent exact
mod-3 finite-graph exploration in /tmp/test_triangle_linear.py also found a
collapsed triangle on a 16-vertex K4-free graph, but this is not a new Lean
result and is not a counterexample to the conjecture.

Further informal review of generic graphs, reduced products, triangle
closures, and bounded-positive-index geometry supplied no missing universal
representation theorem or external-color lower bound. In particular the
non-diagonal non-Archimedean PSD cases were not settled.

Main-file check: /tmp/spec-recolor-algebra-review.log. The original sorry
remains. No valid proof submission was made, and no job is pending.

## Further continuation: higher-stage review after recoloring

No settlement or new Lean theorem was obtained; Spec.lean is unchanged.
Rechecked HigherConeOddBound, FiniteFiberOddBound,
RightTowerCountableCover, ThirdRightProfileObstruction,
ExactTransversalRightCover, and SecondConeTwoCover. The fixed-stage odd-walk
bounds establish clique exclusion, not a lower bound on the number of
triangle-free edge pieces. No transfer from a countable coloring of a
fourth or higher right target to a contradiction in its base was proved.
The unrestricted third-stage non-covered example contains K4 explicitly.

Also considered countable-core/reflection properties for right towers,
nonuniform Hilbert triangle-hitting assignments, and maximal K4-free
graphs. These remained informal and yielded no universal cover theorem or
new witness. No such property may be treated as established.
No valid proof submission was made, and no job is pending.

## Further continuation: unrestricted apex-tower hypotheses

No settlement or new Lean theorem was obtained. Spec.lean is unchanged.
Reviewed ExtensionObstruction, ProperAttachmentExtension,
WellOrderedColorExtension, and CloneHistoryCover. The proper-attachment
hypothesis concerns the attaching induced subgraph, not merely the new
independent vertex set. Thus arbitrary large triangle-free neighborhoods
cannot be substituted into its literal-extension theorem. CloneHistoryCover
requires each vertex's history to be countable; arbitrary later apex
incidences need not have that property.

Conversely, at most continuum many independent stages are covered by the
existing vertex-fiber closure theorem, irrespective of the sizes of the
stages. No lower bound against countable edge colorings of a longer
unrestricted apex tower was obtained. The informal observation that such
towers can realize successive allowable neighborhoods is not an edge-color
obstruction. No valid proof submission was made; no job is pending.

## Further continuation: adjoint and infinitary-partite transfer review

No settlement or new Lean theorem was obtained. Spec.lean was not changed.
Reviewed the potential transfer from a countable edge coloring of higher
right targets to a coloring obstruction at an earlier stage. The cone
profile omission and fixed-stage odd-walk bound still do not supply such
a transfer. The round-trip reductions retain the original difficulty;
they are not universal covering theorems.

Also reviewed the asymmetric marked-corner reduction and infinite partite
construction. FreeCornerArrow.no_cover_of_arrow continues to require an
unproved infinite-red/finite-blue host. Finite Ramsey hosts, binary infinite
Hales--Jewett, and available bipartite results do not establish compatible
copies through infinitely many partite stages. No compactness or saturation
claim for arbitrary external countable colorings was proved.

Main-file check: /tmp/spec-final-adjoint-partite-review.log. The original
sorry remains. This continuation has no valid proof to submit, and no
background job is pending.

## Verification rejection and adaptive-apex review

The submission tool was called with Spec.lean unchanged; verification rejected
it, as the original sorry remains. There is no accepted submission.

After that rejection, reviewed whether an adaptive apex-extension strategy
could force exhaustion of the countable palette. No winning strategy was
proved. A single independent-apex extension of a covered graph remains
covered by shifting old colors and reserving a new color. A prescribed
nonextendible coloring (as in the adapted-labeling obstructions) does not
show that EVERY valid old coloring is nonextendible. PaletteLocalization
also prevents treating global surjectivity of colors as the missing step.
The necessary persistent obstruction over a longer iteration remains
unproved. No Lean theorem or change to Spec.lean resulted from this review.

## Further continuation: non-diagonal geometry and larger finite fields

No main proof or disproof was obtained; no Lean source was modified.

Reviewed non-diagonal positive-semidefinite negative spaces with finite
positive index. The clique bound does not establish an edge-color lower
bound, and no such lower bound or universal representation theorem was
proved. The existing finite positive-index representation obstructions
remain in force.

Investigated a possible affine-labeling reduction over a fixed finite field:
three distinct collinear edge labels on every triangle would permit a
countable triangle-avoiding coloring of the label space. The missing step is
existence of such a representation for every finite K4-free graph (with one
fixed field), followed by an appropriate compactness argument. Neither step
was proved here. Arbitrary scalar colorings without bichromatic triangles
are only a necessary condition, not an affine representation.

Exact exploratory SAT checks:
* /tmp/paley_no_bichromatic.py: for Paley-17, three colors with triangle
  (0,1,2) rainbow is UNSAT, as expected from F3Obstruction; four colors SAT.
* /tmp/paley_affine_f4.py: Paley-17 has a four-color scalar labeling with
  EVERY triangle rainbow, checked directly after solving. Consequently
  Paley-17 does not obstruct the four-element-field affine route.
* /tmp/test_no_bichromatic.py tested finite K4-free process graphs for the
  necessary scalar condition. Results were SAT or TIMEOUT, never a proof
  of a universal statement. No main-conjecture inference is justified.

These experiments were not formalized and are not a solution. No new
submission was made after the earlier rejection. No background job remains.

## Further continuation: closure-growth and adaptive-profile review

No proof or disproof was obtained, and Spec.lean remains unchanged.

Considered a possible structural route through the triangle hypergraph:
completion from k seed graph edges introduces no new endpoints, hence at
most binomial(2k,2) distinct edges can be generated. RootObstruction already
formalizes the relevant endpoint-counting bound for finite traces. No theorem
was proved saying that this quadratic bound plus absence of Berge triangles
implies countable hypergraph colorability. Such an implication must not be
assumed or reported as a solution.

Also reconsidered palette-profile amplification in long apex towers. A
profile omission at one cone does not persist as an omitted color on the
spokes of later cones. Connecting two roots that share an old base edge
creates K4, so the proposed palette-extension step is not available. No
persistent obstruction for all global countable colorings was established.
No Lean source was changed, no valid submission was made, and no job is
pending.

## Further continuation: longer scalar four-color check

No settlement or new Lean theorem was obtained. Spec.lean is unchanged.

Retried the exact necessary scalar condition on the previously timed-out
60-vertex K4-free-process graph (seed 0). The longer run returned SAT after
about 24 seconds; log /tmp/refine_no_bichromatic.log and assignment
/tmp/no_bichromatic_60_0_long.out. The graph has 636 edges; the color class
sizes are 130, 257, 121, 128. The exceptional edges relative to any one
color are not covered by two vertex stars, so this assignment is not of
the simple localized type seen in the Paley-17 test. This is only a scalar
necessary-condition experiment, not a vector representation or a universal
claim. No counterexample to the conjecture was found.

Further reasoning about quadratic triangle-closure growth, triangle-closed
color classes, and profile propagation did not establish a new implication
to the main theorem. The one background SAT run has finished. No job is
pending and no further proof submission was made.

## Further continuation: persistent induced-wheel review

No settlement or new Lean result was obtained. Revisited RobustOddWheel,
MinimalRobustOddWheel, and ShortestOddInducedCycle. The fixed minimal odd
length supplies persistent induced wheels after covered deletions, not a
four-clique or a covered transversal meeting all those wheels. No rule for
selecting wheel edges with a countable TF cover was proved.

Also reconsidered whether this finite-pattern persistence supplies stronger
joint filter completeness or an external-color transfer for a saturated
generic graph. Neither implication was established. The previous warnings
about marginal versus joint completeness and arbitrary external Nat colors
still apply. Spec.lean retains the original sorry; no new submission or
background job was started.

## New verified continuation: finite-field affine compactness reduction

The main conjecture is still unresolved, and Spec.lean is unchanged.
Two new scratch files compile with only propext, Classical.choice, Quot.sound:

* AffineLineColoring.lean (namespace Erdos595AffineLine): `coloring` gives a
  countable coloring of any vector space over a countable field, in any
  dimension, avoiding monochromatic triples of distinct collinear points.
  The proof colors a vector by its ordered list of nonzero Hamel-basis
  coefficients. `rigid` proves the key three-term affine rigidity by erasing
  the least coordinate of the union of the three finite supports.
* AffineCompactnessReduction.lean (namespace Erdos595AffineCompactness):
  `cover_of_represents`, `cover_of_finite_representations`, and
  `universal_cover_of_finite_field` prove the precise conditional bridge.
  For ONE FIXED FINITE FIELD, representations of every finite induced graph
  in finite-dimensional vector spaces (without a uniform dimension bound)
  imply a countable TF edge cover of the entire graph. The compactness proof
  quotients the dependent product of the local vector spaces by its submodule
  of eventually-zero vectors over a fine ultrafilter. Finiteness of the field
  selects one constant affine ratio for each global triangle.

Build logs: /tmp/affine-line-coloring.log and /tmp/affine-compactness.log.
Both oleans are built in .lake/build/lib/lean/Submission/.

CRITICAL MISSING PREMISE: no fixed finite field has been shown to represent
all finite K4-free graphs. These theorems are not a disproof. The F3 finite
obstruction remains valid; a scalar no-bichromatic-triangle coloring over
four colors still does not establish vector affine realizability.

### Affine F4 exploratory check after the verified reduction

/tmp/affine_f4_bit.py now encodes actual vector collinearity over F4 with a
single orientation/ratio shared by all coordinates of each triangle. Unlike
the earlier scalar no-bichromatic condition, a SAT assignment is a genuine
finite vector representation, checked directly by the script. This remains
an external experiment, not a Lean theorem or a universal existence proof.

For the same deterministic K4-free-process generator (seed 0):
* 17 vertices: a two-dimensional F4 representation was found and validated.
* 20 vertices: a two-dimensional F4 representation was found and validated.
* 60 vertices: both dimension 2 and dimension 3 timed out at 180 seconds.
  Neither timeout is evidence of nonrepresentability.

An initial encoding had the first triangle's orientation unit clause reversed;
its immediate UNSAT was an encoding error and was discarded. The corrected
encoding was checked on a single triangle and validates every returned SAT
assignment. All solver runs have ended; no job is pending.

Spec.lean was checked again; /tmp/spec-affine-reduction.log still reports the
original sorry at line 34. Its SHA256 remains
  de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45.
No proof submission was made in this continuation.

## Further continuation: verified constant-F4-ratio obstruction

The main conjecture is unresolved. Spec.lean is unchanged, including its sorry.

Added Submission/UniformF4Obstruction.lean (namespace
Erdos595UniformF4Obstruction), with a built olean and permitted axiom audits.
Log: /tmp/uniform-f4-obstruction.log.

It defines an explicit nine-vertex, 23-edge, 18-triangle graph G and proves:
* cliqueFree: G.CliqueFree 4.
* collapse: an exact linear combination of all 18 triangle relations over
  any characteristic-two field K, for w satisfying w^2+w+1=0, forces
  f 1 2 = f 1 3 in every K-vector space.
* collapse_affine: the same conclusion for the direct equations
    f a c = w • f a b + (1-w) • f b c
  on all increasing triangles a<b<c of G.
* no_uniform_affine: these equations conflict with noncollapse on triangle 123.

IMPORTANT: this is a UNIFORM ordered-triangle-ratio obstruction. It is NOT
an obstruction to arbitrary varying-ratio representations of this nine-vertex
graph, and is not a proof/disproof of Erdős 595.

New INFORMAL implication using the standard finite ordered-graph Ramsey theorem:
The class of finite ordered K4-free graphs is Ramsey for copies of K3. A finite
ordered triangle-Ramsey host for this nine-vertex G, with two triangle colors,
cannot have a noncollapsed affine F4 representation in ANY dimension. Color each
increasing triangle by its affine ratio (one of w and w+1); a monochromatic
order-preserving copy of G contradicts collapse_affine. The lemma covers both
roots because w+1 also satisfies x^2+x+1=0 in characteristic two. Thus the
fixed-F4 universal representation premise is mathematically ruled out by this
standard Ramsey theorem. HOWEVER: the ordered TRIANGLE-color Ramsey theorem is
NOT currently formalized in the scratch files; FiniteInducedRamsey and
FiniteFolkman only concern EDGE colors and cannot be substituted without proof.
This is not yet a Lean theorem excluding all F4 representations universally.
No conclusion for every other fixed finite field was proved here.

Exact exploratory software added:
* /tmp/affine_f4_orientation.py checks one full triangle-orientation assignment
  in ALL dimensions by GF4 row-space elimination, retaining and directly
  verifying coefficient certificates for each collapsed triangle. Its conflict
  clauses exclude orientation subsets that force such collapses.
* It was cross-checked against the genuine 17- and 20-vertex representations:
  ranks 67 and 98 respectively, zero collapsed triangles, as required.
* All 512 orientations of K5 modulo global conjugation were checked: none is
  representable. K5 is not K4-free, so this is not the desired obstruction.
* 300 conflict-clause iterations each on the 20- and 30-vertex process graphs
  did not solve representability; not even the known 20-vertex example was
  recovered. Logs /tmp/f4_orient_20_0.log and /tmp/f4_orient_30_0.log. These
  incomplete searches supply no negative conclusion.
* /tmp/uniform_affine_obstruction.py and /tmp/uniform_tripartite_search.py
  investigate constant ratios on ordered complete tripartite graphs. In
  particular the ordered K333 with parts given by 0,1,2,0,1,2,0,1,2 has all
  triangle labels forced equal at the F4 ratio. Over sampled odd prime fields
  its central triangle (3,4,5) collapses except at characteristic 3, ratio 2.
  No universal-field theorem or polynomial certificate for this was proved;
  do not promote the samples to one.

Further review of countably closed coloring forcings and order-type graphs
produced no new implication. TupleTypeCover/RestrictedTupleCover already exclude
the finite-tuple order-type construction revisited here; do not reopen it.

No proof submission was made. No solver or build is pending. Main-file check:
/tmp/spec-uniform-f4-review.log, still the original sorry warning.

## New verified continuation: ALL fixed finite fields ruled out

The main conjecture is still unresolved, and Spec.lean is unchanged.
This section supersedes the earlier suggestion to prove the universal
fixed-finite-field representation premise: that premise is now DISPROVED
in Lean for every fixed finite field, not just F4.

New verified files (all with oleans and only permitted axiom audits):

1. FiniteTrianglePartite.lean, namespace Erdos595FiniteTrianglePartite:
   `partite` is the finite-palette tripartite lemma for ordered triangle
   colorings, using Mathlib Hales--Jewett and coordinatewise product graphs.
2. FiniteTriangleStep.lean, namespace Erdos595FiniteTriangleStep:
   `step` and `homogenize` extend the partite lemma by induced free
   amalgamation and finitely many iterations, retaining K4-freeness.
3. FiniteOrderedTripleRamsey.lean, namespace
   Erdos595FiniteOrderedTripleRamsey:
   `finite_ramsey` is ordinary finite ordered triple Ramsey for an arbitrary
   finite palette. It reflects the already verified infinite triple-Ramsey
   theorem through finite-palette ultrafilter compactness.
4. FiniteTriangleRamsey.lean, namespace Erdos595FiniteTriangleRamsey:
   `finite_triangle_ramsey` proves that every finite ordered K4-free target
   has a finite K4-free host for every fixed FINITE coloring of its ordered
   triangles. This is the previously missing Ramsey theorem; the older
   FiniteFolkman/FiniteInducedRamsey results only colored edges.
5. FiniteF4Obstruction.lean, namespace Erdos595FiniteF4Obstruction:
   `f4_obstruction` now rigorously combines the nine-vertex uniform-ratio
   certificate with triangle Ramsey. There is a finite K4-free graph not
   affinely representable over GaloisField 2 2, in ANY dimension.
6. UniformAffineObstruction.lean, namespace Erdos595UniformAffineObstruction:
   An explicit 12-vertex, 38-edge, 32-triangle K4-free graph G has NO
   noncollapsed uniform proper affine ratio over ANY field. `certificate`
   is a checked integer-polynomial linear combination of 24 triangle
   relations, showing
     (t*(1-t)) • (f 1 6 - f 1 10) = sum of those relations.
   All coefficient polynomials have degree at most three and integer
   coefficients. `collapse` cancels t*(1-t), given t != 0,1, and `no_uniform`
   contradicts noncollapse on triangle (1,6,10). No characteristic hypothesis.
7. FiniteRatioObstruction.lean, namespace Erdos595FiniteRatioObstruction:
   `RepresentsUsing r G f` specifies a palette of ratios r : C -> K.
   `finite_ratio_obstruction`: for ANY field K and ANY finite palette C of
   allowed ratios, there is a finite K4-free graph with no noncollapsed
   affine edge representation using those ratios, in ANY vector-space
   dimension. The graph is selected independently of the dimension.
   `finite_field_obstruction` specializes the palette to the entire finite
   field. Finally, `no_universal_finite_field` proves the literal negation of
   the finite-field existence premise of
   AffineCompactnessReduction.universal_cover_of_finite_field (Type 0 form).

Logs (all successful):
 /tmp/finite-triangle-partite.log
 /tmp/finite-triangle-step.log
 /tmp/finite-ordered-triple.log
 /tmp/finite-triangle-ramsey.log
 /tmp/finite-f4-obstruction.log
 /tmp/uniform-affine-obstruction.log
 /tmp/finite-ratio-obstruction.log

CRITICAL LIMITATIONS:
* None of these is a proof or disproof of Erdős 595. The obstructing graphs
  are FINITE, hence themselves trivially countably TF-edge-covered.
* Affine representation implies covering, not conversely. Nonrepresentability
  is not a countable edge-color obstruction.
* The new triangle-Ramsey theorem has a FINITE palette. It cannot be applied
  with Nat; the infinite-color coherence/Hales--Jewett obstruction remains.
* Countable-field affine representations with genuinely infinitely many
  ratios are not excluded by the finite-ratio theorem, but no universal
  existence theorem or applicable countable-field compactness was proved.

Exploratory artifacts leading to the verified certificate:
 /tmp/uniform_char3_small.sage and /tmp/uniform_char3_small.json found the
 12-vertex process graph, seed 98, and collapsed triangle (1,6,10).
 /tmp/uniform_small_ansatz.sage and /tmp/uniform_small_ansatz_0.json obtained
 the degree-three integer-polynomial certificate, with multiplier t*(1-t).
 /tmp/gen_uniform_affine_obstruction.py generated the Lean certificate.
 These computations are not trusted axioms: the resulting polynomial identity
 and K4-freeness were independently checked by Lean.

Other experiments, NOT promoted to theorems:
 /tmp/uniform_tripartite_smith.sage attempted polynomial Smith form; it was
 killed/timed out and supplied no result. No such solver remains running.
 /tmp/uniform_tripartite_ansatz.sage found a characteristic-zero certificate
 with multiplier 3*t*(1-t) for an ordered K333. Attempts to get a useful
 characteristic-three version failed; F9/F27 checks showed that K333 does
 admit noncollapsed uniform ratios there. This was superseded by the valid
 12-vertex all-characteristic certificate, so do not assume K333 works in
 characteristic three.

The renewed web check failed DNS and direct-IP HTTPS timed out. Reviews of
fourth right adjoints, long apex towers, polynomial triangle-closure growth,
and saturation/forcing yielded no additional main implication. Lower-stage
right-adjoint exclusions and all earlier guardrails remain in force.

Spec.lean was not modified. No valid proof submission was made; no solver or
build is pending. The task remains unresolved despite this completed exclusion.

## Further direct-construction review (no new result)

Continued after the all-finite-field exclusion. Reviewed profile omission,
adapted extension, transfinite cone towers, mutual-Fubini extensions, reduced
products, polynomial triangle closure, and minimal persistent odd wheels.
No new implication to the main conjecture was proved and no Lean source was
modified in this review.

In particular:
* ConeProfileOmission is still only local. No construction was found forcing
  a genuinely new global palette color for EVERY countable edge coloring.
* AdaptedReflectionObstruction explicitly blocks reflecting failure of a
  global adapted labeling to a triangle-free induced neighborhood.
* The countably complete reduced-product proposal was already fully excluded
  by CompleteFilterProduct and CompleteFilterEdgeCover. Positive-fiber
  selection plus an ordinary ultrafilter suffices there; no new construction.
* Large residual common-neighbor sets are independent in a K4-free graph;
  they do not give the missing fourth-clique coupling. Selecting countably
  many wheel spokes per vertex only deletes a covered edge graph and does
  not prove termination of the wheel-removal process.
* No statement transferring arbitrary external colorings to a saturated
  structure or an ultrafilter extension was established.

Spec.lean still has its original sorry and unchanged statement/import.
No proof submission was made, and no background solver or build is pending.

## Prescribed affine cone extension obstruction (completed)

AffineConeExtensionObstruction.lean now compiles with an olean. Log:
/tmp/affine-cone-extension.log. Namespace Erdos595AffineConeExtension.
All printed axiom audits contain only propext, Classical.choice, Quot.sound.

* base is two four-cycles sharing one vertex (7 vertices, 8 edges), and
  base_triangleFree proves it triangle-free.
* baseLabels assigns the eight old edges independent basis vectors in K^8.
  baseLabels_edge and baseLabels_represents verify this prescribed labeling.
* cone is obtained by adding one universal vertex; cone_cliqueFree proves
  it K4-free.
* no_vector_solution proves that no proper affine ratios on the eight cone
  triangles can extend the old labels. The sum of the first four coordinates
  of the shared spoke is forced to be both 1 and 0 by the two cycles.
* no_enlarged_solution applies a linear left inverse, showing that any
  injective linear enlargement of K^8 retains the obstruction.
* no_cone_extension packages this as failure of a Represents labeling of
  the cone preserving the independent labels, over EVERY field K.

The unfinished normalization issue was fixed using simp +decide, not plain
norm_num or just listing Fin.reduceAdd/Fin.reduceEq. Pi.single required the
explicit K-valued-function type annotation.

IMPORTANT: This is only a PRESCRIBED-extension obstruction. It does NOT show
that the cone has no other affine representation, and the finite cone is
certainly countably TF-edge-covered. No implication to Erdős 595 was proved.
Spec.lean remains unchanged with its original sorry.

## Minimal odd-cycle neighbor profiles (new, verified)

MinimalOddCycleNeighbors.lean compiles with an olean. Namespace
Erdos595MinimalOddCycleNeighbors; log /tmp/minimal-odd-cycle-neighbors.log.
All printed axiom audits use only propext, Classical.choice, Quot.sound.

* neighbor_gap: for a shortest odd closed walk of length n>=5, if a vertex
  is adjacent to two distinct rim positions i<j, then j-i is 2 or n-2.
  Proof closes each of the complementary rim segments through that vertex;
  one resulting loop is odd and cannot be shorter than n.
* not_three_neighbors and neighbor_positions_card_le_two: no vertex has
  more than two rim neighbors. The latter is phrased using Nat.card to
  avoid dependent Finset-filter decidability-instance transport problems.
* wheel_in_subgraph_sparse_profiles: when H<=R contains a shortest odd
  wheel of the ambient R, the profile bound applies to ALL R-neighbors of
  its center, not merely to H-neighbors.
* persistent_sparse_rims combines this with minimal_residual: a fixed odd
  rim length with these sparse ambient profiles survives every covered
  deletion in a hypothetical non-covered K4-free graph.

LIMITATION: These are still necessary conditions, not a contradiction or
construction. In particular neighbors of the center may have EMPTY rim
profile. No covered transversal of the persistent wheels was constructed.

Also reviewed ordered/OR ultrafilter extensions, saturation with external
colors, and finite-pattern/triangle-radius arguments. No new main implication
was obtained. The first OR/ordered stage of a countable finite-clique base is
already countably PROPERLY colorable (FiniteCliqueUltrafilterColoring); do
not treat it as an open candidate. Higher-stage coverability remains open.

Spec.lean is unchanged with its original sorry. No proof submission was
attempted in this continuation. No build or solver is pending.

## Full-OR locally finite folding (new, verified)

LocallyFiniteOrFold.lean is complete, with an olean and permitted axiom audits.
Namespace Erdos595LocallyFiniteOrFold; log /tmp/locally-finite-or-fold.log.

* principal_pair: one Fubini direction over a LOCALLY FINITE graph already
  forces both ultrafilters to be principal.
* collapse_adj_one: therefore one-sided adjacency folds to the original
  target. This is stronger than the earlier mutual-only collapse for targets
  having finitely many infinite-degree exceptional vertices.
* nextGraph/nextHom implement the FULL symmetric OR extension for any graph
  mapping to the locally finite target, and fold it to that same target.
* stage/intoStage/retract iterate this construction, fixing original vertices.
* stage_cliqueFree preserves K4-freeness via the fold.
* palette_iff and cover_iff preserve exactly every palette and countable
  covering status through all finite OR stages.
* folkman_stages instantiates the countable locally finite Folkman target:
  every finite full-OR stage is K4-free and countably covered, but admits NO
  finite triangle-free edge palette. Thus unbounded finite palette demand
  alone still does not yield countable non-coverability after these stronger
  extensions.

The exploratory finite CSP /tmp/arcK4_moser_hom.py found no homomorphism from
arc(K4) to the seven-vertex Moser spindle. This was NOT formalized and supplies
no implication for the main conjecture. No other numerical search was used.
Further reviews of infinitary partite Ramsey, graphical hypergraph roots,
countable-color compactness, and saturation did not produce a main lemma.

Spec.lean remains unchanged with its original sorry. No proof submission was
made; there is no pending build or solver.

## Further continuation: direct extension and higher-adjoint review

No proof or disproof of the main conjecture was obtained. Spec.lean was not
modified. Rechecked WellOrderedColorExtension, RankEdgeCover,
BoundaryPrescribedExtension, the adapted-reflection obstruction,
RightTowerCountableCover, and the higher right-adjoint candidates.

* The well-order extension result retains its explicit literal-preservation
  hypothesis. No universal construction satisfying that hypothesis was found.
* The higher right-adjoint route still has no lower bound against arbitrary
  countable triangle-free edge colorings. The known noncovered third-stage
  example contains K4 and is not a witness.
* Further discussion of local proper colorings, triangle-completion orders,
  canonical edge filters, and geometric representations remained exploratory;
  no missing main implication was established.

There is no new Lean helper or unfinished implementation. No valid proof was
submitted, and no solver or build is pending after the main-file check.

## Ordinary Mycielski edge-palette preservation (new, verified)

Submission/MycielskiEdgePalette.lean compiles with an olean. Namespace
Erdos595MycielskiEdgePalette; log /tmp/mycielski-edge-palette.log.
All printed axiom audits contain only permitted axioms.

* oldEmbedding embeds the base graph inducedly into the ordinary Mycielski graph.
* triangle_no_apex proves that the new apex lies on no triangle.
* extend_valid preserves an arbitrary prescribed valid edge coloring literally,
  using exactly the same nonempty palette, by assigning parent-edge colors to
  old/shadow edges and an arbitrary palette color to apex edges.
* palette_iff preserves exactly every nonempty finite or infinite palette.
* countable_cover_iff preserves countable triangle-free edge coverability.

This formalizes the previous informal warning: ordinary Mycielski vertex-
chromatic amplification is not triangle-free edge-palette amplification. It
is not a proof or disproof of Erdős 595.

Also revisited finite/infinite partite Ramsey, non-diagonal non-Archimedean
positive-index forms, and ultraproduct/external-color arguments. No universal
covering theorem or genuine countable-color obstruction was obtained.
Spec.lean remains unchanged with its original sorry; no proof was submitted.

## Countable-field noncompactness (new, verified)

Submission/CountableFieldNoncompactness.lean compiles cleanly with an olean.
Namespace Erdos595CountableFieldNoncompactness.
Log: /tmp/countable-field-noncompactness.log.
All printed axiom audits contain only propext, Classical.choice, Quot.sound.

* represents_of_injective: injective scalar edge labels give noncollapsed
  affine triangle representations over any field.
* countable_rational_representation: every countable graph, with no clique
  restriction, has such a one-dimensional representation over Q.
* finite_subgraphs_rational: consequently every finite induced subgraph of
  EVERY graph has a representation over that same countable field.
* large_complete_not_representable: the complete graph on the power set of
  binary sequences has no such representation over any countable field, in
  any vector-space dimension, by the countable-cover implication and Cantor.
* noncompactness: explicit failure of unrestricted finite-subgraph affine
  representability compactness over Q.

SCOPE: the counterexample contains K4. This does NOT disprove compactness
restricted to K4-free graphs, and is NOT a proof/disproof of Erdos 595.
It clarifies why the finite-field compactness argument cannot just be changed
into a countable-field argument; finite rational representability is automatic.

Also reviewed prescribed extension, persistent wheel packing, arbitrary
external colors in reduced products, and higher right-cone stages. No new
main implication was established. No universal representation or coherent
transfinite prescribed-color extension theorem was found.

Spec.lean is unchanged, with its original sorry. Latest check log:
/tmp/spec-countable-field-review.log. SHA256 remains
  de0befb4abb4140a841c0ae58b8972db851af054de2ba75b8ebab02805abef45
No proof was submitted; no solver or unfinished build is pending.

## Further extension and ultrafilter review (no settlement)

Revisited literal prescribed-color extension, earlier-neighborhood orders,
triangle closure, elementary-model-style finite cone requests, and the
third generic mutual-ultrafilter stage. No universal extension invariant
or lower bound for arbitrary external countable edge colorings was proved.

The finite maximal-clique code remains a first-stage proper-coloring result;
the common triangle-free support argument handles the second mutual stage.
Neither was extended to settle the third generic stage. Existing finite-tower
compression obstructions must still be respected.

Also considered using whole branches of a countably branching partition tree
to avoid invalid nested-large-fiber fusion. This does not repair the separate
fresh-color gap: successive independent apices over a triangle-free set can
reuse the same spoke color. No claim of color consumption or infinite partite
compatibility was established.

No new proof code was added in this review. Spec.lean remains unchanged with
its original sorry. Check log: /tmp/spec-extension-ultrafilter-review.log.
No proof submission was made, and no solver/build is pending.

## Edge-filter / correlation review (no settlement)

Reviewed BadEdgeUltrafilter, TriangleFilterCoupling, OrderedTriangleFilter,
and EdgeVertexFilterMarginal. The direct finite-palette obstruction does
not turn into a new edge by taking its endpoint ultrafilters: their marginals
coincide, and the common marginal is isolated for K4-free graphs. Keeping
correlations via a shared reduced-product index does not itself yield a lower
bound against arbitrary external countable colorings. No new coupling or
compactness theorem was proved.

Also revisited the ordered middle-corner graph. The existing
MiddleCornerObstruction already supplies exactly the one-/two-step triple
shift counterexample: the stronger middle-corner coloring rule can require
arbitrarily large palettes although the graph has a two-piece TF edge cover.
Do not reintroduce that stronger rule as a universal necessary condition.

No new Lean proof was added in this continuation. Spec.lean is unchanged
with its original sorry. No proof was submitted; no build or solver is pending.

## Shift-base Ramsey/amalgamation review (no settlement)

Rechecked InfiniteShiftRamsey.step, IntervalBipartiteRamsey.step,
FreeCornerArrow, and TransfiniteAmalgamationCover. Whole induced shift bases
have arbitrary-palette Ramsey hosts, but their one-step embeddings do not
supply coherent selections at later stages.

Important scope: AmalgamationCover preserves countable coverability for a
single free amalgam of covered pieces, even if its TF base has uncountable
proper chromatic number. Thus finite iterations cannot supply a witness.
The countably-proper-boundary condition is needed for the stronger literal
prescribed-color extension theorem and its unrestricted transfinite use.
No sufficiently long limit construction with a countable-color lower bound
was established, nor was a universal transfinite preservation theorem.

No new Lean code or main implication resulted. Spec.lean is unchanged with
sorry; no proof was submitted and no build/solver is pending.

## Further reduced-power / structural review (no settlement)

Re-read FixedGenericReducedPower and CountableCoordinateRepresentation: the
fixed countable generic target reduction is already universal, and does not
supply control of arbitrary external countable edge colors. Rechecked graphical
triangle hypergraphs, finite-palette amplification, mutual ultrafilter towers,
and the minimal persistent odd-wheel reduction. No missing implication was
proved. In particular, countable completeness was not upgraded to ultrafilter
completeness; finite Ramsey constructions were not treated as countable-color
Ramsey constructions; and sparse rim profiles may still be empty.

Local library/documentation search found no overlooked Folkman or Erdős 595
result. Web DNS remains unavailable. No Lean theorem was added in this review.
Spec.lean is unchanged with its original sorry. No valid proof or disproof was
submitted, and no solver or unfinished implementation is pending.

## Locally finite cone fourth-right exclusion (new, verified)

Submission/LocallyFiniteConeRightFold.lean compiles cleanly with an olean.
Namespace: Erdos595LocallyFiniteConeRight.
Log: /tmp/locally-finite-cone-right-fold.log.
Axiom audits for fold and fourth_cover list only propext, Classical.choice,
and Quot.sound.

* A biclique in the cone of a locally finite graph either has two finite
  sides or one side contained in the singleton apex.
* Nonempty bicliques with an apex-only side enlarge to one of two canonical
  apex bicliques; the remaining nonempty bicliques are represented by finite
  pairs of vertex sets. Empty-side vertices are isolated.
* fold maps the first right adjoint to an explicit target on
  (Finset (Option V) x Finset (Option V)) + Bool. The target is countable
  when V is countable, and realize gives a reverse homomorphism.
* fourth_cover uses the reverse homomorphism to transfer K4-freeness to
  the third right of the countable target, applies the existing third-stage
  theorem, and pulls its cover back.

No clique restriction on the locally finite base is needed beyond the
stated K4-free FOURTH-stage hypothesis. This is an exclusion of a candidate
family, NOT a proof/disproof of Erdős 595. No theorem for arbitrary countable
cone bases, arbitrary fourth right stages, or all finite iterations was proved.

Also rechecked prescribed-color limits, reflection, and higher-right bounds.
No stable universal extension invariant or arbitrary-color lower bound was
found. Spec.lean is unchanged and still contains its original sorry.

## Further corner-Ramsey / exponential review (no settlement)

Revisited the actual finite triangle-partite lemma, FreeCornerArrow, the
whole-shift and interval Ramsey steps, and fixed-generic-target exponentials.
An infinite monochromatic cone over a shift base alone does not supply the
mixed-marking finite wheel required by FreeCornerArrow. No coherent long
partite construction or arbitrary-external-color lower bound was proved.
Finite-palette Hales--Jewett and finite-subgraph compactness were not extended
to infinite alphabets/palettes without justification.

No new Lean result in this review. The latest verified new result remains
LocallyFiniteConeRightFold.fourth_cover; its scope is only the stated locally
finite cone family. Spec.lean remains unchanged with its original sorry.

## Third mutual-ultrafilter review (no settlement)

Re-read GenericUltrafilterUniversality, ThirdBadTriangle,
ThirdTriangleFiniteEdgeSupportFailure, and CountableUltrapowerExtension.
The proved fixed-generic universality is for COUNTABLE source graphs; the
unsupported third-stage part is not thereby non-coverable. Neither unsupported
vertices on triangles nor failure of finite-edge supports yields a lower bound
for arbitrary external countable edge colors. The covered ordinary ultrapower
already has countable extension and no finite palette, so that implication
must not be used.

No new Lean theorem or main implication was obtained. No countably complete
ultrafilter extension, coherence theorem, or cardinal-unrestricted universality
was assumed. Spec.lean remains unchanged with its original sorry. No proof
submission was made and no unfinished implementation/build is pending.

## Further algebraic representation review (no settlement)

Re-read AllFieldOrthogonalityCover, DiagonalPositiveIndexCover,
PositiveIndexTwoOrder, PositiveIndexTwoObstruction, and
PositiveIndexThreeConeObstruction. No universal representation of K4-free
graphs, nor a lower bound for a non-diagonal infinite-dimensional candidate,
was established. Finite-dimensional covers and finite negative-support
intersection arguments were not applied outside their stated scopes.

The index-two obstruction is over arbitrary ordered fields. The existing
index-three cone obstruction remains the REAL inner-product theorem; this
review did not formalize its generalization. No new Lean source was added.
Spec.lean remains unchanged with its original sorry; no submission was made.

## Cardinal ideal and coupling review (no settlement)

Rechecked VertexCoverFilter, EdgeVertexFilterMarginal, CountableBadEdgeFilter,
and TriangleFilterCoupling. The previously established critical-cofinality
bound is already recorded in UltrafilterNotes: a cardinal-minimal witness has
cofinality above continuum. No new cardinal restriction was proved here.

The continuum-successor completeness belongs to the induced vertex-cover
ideal's dual filter, not to an arbitrarily extended ultrafilter. Equal triangle
marginals permit the proved fiber-product gluing but not identification of two
coordinates within one sample or a K4 coupling. No such extra implication was
assumed. No new Lean theorem, proof, or disproof resulted from this review.
Spec.lean is unchanged with its original sorry.

## Final rank / higher-right review (no settlement)

Rechecked RankEdgeCover, WellOrderedColorExtension, CountableRealizedTypes,
HigherConeOddBound, and RightTowerCountableCover. The rank theorem still needs
proper countable colorings of lower neighborhoods; K4-freeness supplies only
triangle-freeness there. The well-ordered assembly still needs its literal
prescribed-color extension hypothesis. No removal of either hypothesis was
proved.

For higher right adjoints, the finite odd-walk bound proves only K4-freeness.
No lower bound against arbitrary external countable edge colorings, and no
universal covering theorem, was obtained. Spec.lean remains unchanged with
its original sorry. No new Lean theorem or proof submission was made.

## Non-locally-finite higher-right continuation (no settlement)

Reviewed the adjunction and the countable rectangle-cover detector in detail.
No implication from the higher-right K4 exclusion to non-coverability was
proved. In particular, a vertex-chromatic lower bound would not by itself
suffice: triangle-free graphs can already have large vertex chromatic number.
No arbitrary-color Ramsey step for the non-locally-finite countable-base
candidate was constructed, and no extension of the locally finite cone fold
was proved. The main file is unchanged; no valid submission is available.

## Triangle-hypergraph realization review (no settlement)

Considered constructing a witness from a countably uncolorable linear
3-uniform hypergraph. Its ordinary graph shadow does not transfer weak
vertex non-colorability to triangle-free edge non-coverability: distinct
hyperedges in a linear hypergraph give edge-disjoint designated triangles.
The required edge-triangle realization, preserving the coloring obstruction
and K4 exclusion, was not constructed. No new Lean theorem was claimed.
Spec.lean is unchanged and the conjecture remains unresolved in this work.
