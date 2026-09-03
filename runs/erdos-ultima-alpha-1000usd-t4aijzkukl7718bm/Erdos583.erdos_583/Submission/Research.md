# Work status for Erdős 583

The conjecture is the full Gallai path-decomposition conjecture. The definitions appear faithful; no counterexample or complete proof has been found.

## Checked Lean progress

`Spec.lean` now contains all verified helpers, with its original import and theorem statement preserved. The original theorem splits on `Nat.card G.edgeSet ≤ Nat.card V`. The sparse branch is proved; **the other branch still has `sorry`**. This is NOT a completed submission.

`Work.lean` contains the same helpers in namespace `Erdos583Work` and has no proof gaps. `lake env lean Submission/Work.lean` succeeds. Audited main helper axioms: only `propext`, `Classical.choice`, `Quot.sound`.

Key lemmas:
- `exists_edge_decomposition`: singleton-edge paths give an edge partition.
- `exists_min_decomposition`: minimum-cardinality path partition exists.
- `GoodDecomposition.erase_empty`, `.merge`, `min_decomposition_cannot_merge`.
- `forest_endpoint_system`: for a forest, a minimal decomposition has pairwise distinct endpoints.
- `forest_decomposition`: `2 * D.card ≤ Fintype.card V` for forests.
- `forest_decomposition_odd`: exact equality `2 * D.card = card {v // Odd (G.degree v)}` for forests.
- `IsDecomposition.degree_eq_sum`: sum of subgraph neighbor-set cardinalities equals ambient degree.
- `restore_edge`: restore one deleted edge using at most one additional path.
- `cycle_nonbridge_avoiding`: any cycle supplies a non-bridge edge avoiding a prescribed vertex.
- `exists_delete_tree_even`: a connected unicyclic graph has a spanning tree with an even-degree vertex.
- `erdos_583_of_card_edges_le_card_vertices`: the requested bound for connected graphs with `|E| ≤ |V|` (trees and unicyclic graphs).

The unicyclic proof chooses a non-bridge edge whose deletion produces a tree with an even-degree vertex. Its forest path count is strictly less than n/2; restoring the edge then meets ceil(n/2).

## Failed approaches / concrete obstructions

A pairwise length-maximal decomposition need not meet the conjectured bound. In K5, these four paths partition the edges:
- 0-2
- 0-3-4-1-2
- 1-3
- 1-0-4-2-3
Every pair is already length-maximal, and no pair can be merged, but the desired bound is 3. A three-path exchange can fix this; this is NOT a counterexample to the conjecture.

Even replacing at most three paths by fewer paths can get stuck. In K8 minus edges 0-5 and 1-5, take:
- 0-7-5-3-4-6-1-2 (length 7)
- 0-3-6-5-2-4-7-1 (length 7)
- 5-4-1-3-2-6-7 (length 6)
- 1-0-6 (length 2)
- 4-0-2-7-3 (length 4)
This has five paths although the target is four. Every triple either has more than 14 edges, has six odd-degree vertices, or (the second, fourth, fifth paths) has degree 5 at vertex 0, so cannot be repartitioned into two paths. No pair can merge either. Exchanges preserving path count could still help. This is only an obstruction to strictly count-decreasing local moves, NOT to Gallai's conjecture.

`path_exchange.py` in the project root implements the targeted local-move test used to find these strategy obstructions. It was not a numerical search for a counterexample to the original conjecture.

Other explored but unproved routes: endpoint-pair transfer/augmenting fans; splitting even vertices to reduce to all-odd graphs; adding a matching to an all-odd graph. These each still require substantive unresolved combinatorics. No assumption asserting any of these has been added to Lean.

## Further obstruction: even the cycle-only conversion lemma fails

The proposed lemma “a connected union of k edge-disjoint cycles has a decomposition
into at most k+1 paths” is false. Take three disjoint copies of K5 minus edge 01,
with vertices (i,0),...,(i,4), and add the three edges (i,1)(i+1 mod 3,0).
The resulting connected 4-regular graph has 15 vertices. In each block take the
5-cycle 0-2-1-3-4-0. The remaining internal edges form the path 0-3-2-4-1;
the three such paths and the three interblock edges form a spanning cycle.
Thus the graph is a union of four edge-disjoint cycles.

However, restricting any simple-path edge partition to a block gives path pieces
of at most four edges, so its nine internal edges require at least three pieces.
There are at least nine pieces altogether. Deleting three interblock edges from
p paths creates at most p+3 nonempty path pieces, so p >= 6. In particular p > 4+1.
This is NOT a counterexample to Gallai: ceil(15/2) = 8.

The newest verified helper, `odd_vertices_le_twice_path_count`, proves the usual
parity lower bound for arbitrary path decompositions, not just forests. The general
upper bound remains unproved, and the dense branch in `Spec.lean` still has `sorry`.

## Endpoint exchange: an additional obstruction

The unrestricted claim that two intersecting edge-disjoint paths with four distinct
endpoints can be repartitioned into two paths with a different endpoint pairing is
false. Take triangles 0-1-4-0 and 2-3-5-2, together with edges 0-3 and 1-2.
There is a two-path partition
    0-1-2-3
    1-4-0-3-5-2.
The four odd-degree vertices are 0,1,2,3; in any two-path partition these are
exactly the endpoints. Each triangle must be divided into its two attachment-to-
attachment arcs, lying in different paths. Both paths must cross the cut between
the triangles, hence each uses exactly one of the two cut edges. The resulting
endpoint pairing is forced: (0,3) and (1,2).

This is not a counterexample to the conjecture, whose bound here is three paths.
The example specifically invalidates endpoint flexibility at a fixed optimal
path count. `endpoint_exchange.py` tests a narrower Hamilton-path version, where
no obstruction was found through nine vertices; that computational observation
is neither a proof of that lemma nor a proof of the conjecture.

## General path-restoration criterion (verified)

`restore_path_subgraph` generalizes `restore_edge`: if K is any path subgraph,
a path decomposition of G.deleteEdges K.edgeSet lifts to one of G with at most
one additional member. `restore_edge` is now a corollary, rather than a separate
proof.

`erdos_583_of_delete_path_acyclic` proves the requested bound whenever deleting
a path leaves a forest with an even-degree vertex. Connectivity is not required
for this criterion. The proof uses the exact forest formula: 2 * D.card is the
number of odd-degree vertices, which is strictly less than n when an even-degree
vertex exists. Restoring one path then meets ceil(n/2).

Both new lemmas, and the refactored `restore_edge`, were audited: their only axioms
are propext, Classical.choice, and Quot.sound. The main theorem now also closes
this certificate case; there remains one `sorry` for graphs not covered by either
this criterion or the previous sparse-graph theorem.

The criterion is sufficient, not necessary, even for a union of a tree and a path.
For example, on vertices 0,...,5 take edges
01,02,03,04,05,12,13,14,15,23 (K2 joined to K2 plus two isolated vertices).
There is a three-path decomposition
4-0-5-1-2; 4-1-0-3; 0-2-3-1.
There is also a tree-plus-Hamilton-path partition, but no path deletion leaving
a forest with an even-degree vertex: with ten edges on six vertices, the deleted
path must be Hamiltonian and the remaining forest a spanning tree. Vertices 4
and 5 have degree two in the graph, so each must be an endpoint of the deleted
Hamilton path (otherwise it would be isolated in the spanning tree). All other
vertices have odd degree in the graph and are internal in the Hamilton path;
therefore every remaining tree degree is odd. This is an obstruction to making
the new certificate universally applicable, not a counterexample to Gallai.

## General even-order reduction (verified)

New gap-free lemmas in both Lean files:
- `ncard_neighbor_delete_subgraph_add`: degree-cardinality splitting for a deleted subgraph.
- `cycle_neighbor_ncard_even`: every local degree of a cycle subgraph is even.
- `delete_cycle_preserves_degree_parity`.
- `exists_odd_supergraph_forest_difference`: if |V| is even, every G has a supergraph
  H with every degree odd and with H \\ G acyclic. Minimize |E(H)| among all odd
  supergraphs (the complete graph is one). A cycle in H \\ G could be deleted,
  preserving odd degrees and G <= H, contradicting minimality.
- `erdos_583_even_of_odd_forest_deletion`: a conditional reduction of the even-order
  conjecture to connected graphs H \\ F with H all-odd and F a forest contained in H.
  This lemma does NOT assume its hypothesis globally or use it to close the main gap.

The odd-completion theorem and parity lemma passed their axiom audit with exactly
propext, Classical.choice, and Quot.sound. The main theorem still has one `sorry`.

A possible route to the remaining forest-deletion statement is to find an n/2-path
partition of H for which, on every member, the surviving G-edges form at most one
contiguous segment. Trimming would then preserve the path count. This stronger
compatibility assertion remains UNPROVED. `forest_trim_test.py` checked all connected
all-odd graphs through six vertices and all forest deletions leaving them connected,
without finding an obstruction. Further scratch tests checked K8 with each of the
22 non-star unlabelled spanning trees deleted, also without an obstruction. These
finite tests are not a proof of the compatibility assertion or the conjecture.

## Structure of a minimum odd completion (verified)

The completion result now also has a minimality-preserving version,
`exists_min_odd_supergraph_forest_difference`. Its witness H minimizes the edge
count among all-odd supergraphs of G.

`min_odd_supergraph_component_complete` proves that whenever distinct u,v are
connected in H \\ G, they are adjacent in H. If that edge were absent, choose a
simple u-v path in H \\ G (necessarily of length at least two), delete its edges
from H, and add uv. The endpoint parity changes cancel, all other local parity
changes are even, G remains a subgraph, and the edge count strictly decreases.
This contradicts minimality.

`exists_odd_supergraph_complete_added_components` packages the general reduction:
for every even-order G there is H >= G, all degrees of H odd, added edges forming
a forest F, and each component of F inducing a clique in H. Equivalently, within
each such component G induces the complement of its added tree. The new helper
`path_neighbor_ncard_mod_two` and `path_edgeSet_ncard` support the exchange proof.
All new structural lemmas compile and have only the permitted axioms.

This is a stronger structural reduction, not a solution. The main theorem still
has one `sorry`. In particular, the forest-trimming compatibility assertion has
not been proved, and the stronger completion properties have not yet yielded the
required path-count bound.

## General path-exchange and star-forest reduction (verified)

`min_odd_supergraph_path_exchange_bound` generalizes the missing-chord exchange.
For a minimum odd completion H of G, a simple u-v path p in H \\ G cannot be longer
than a simple u-v path r in the complement of H. Removing p and adding r preserves
G and all degree parities, so a shorter r would contradict minimality. The earlier
component-completeness lemma is now a short corollary of this bound.

`min_odd_supergraph_long_path_dominating_edge` proves: if a simple path p in H \\ G
has length at least three, its endpoints u,v form a dominating edge in G, i.e.
G.Adj u v and every vertex is adjacent to u or v. Proof: acyclicity excludes a
one-edge or two-edge added-forest path between the endpoints. A vertex w adjacent
to neither endpoint in G would either lie in the same added-forest component,
forcing such a two-edge path by component completeness, or lie outside it,
providing a two-edge path in the complement of H and contradicting the exchange
bound.

`exists_odd_supergraph_short_added_paths` packages the consequence: for even-order
G with no dominating edge, there is an all-odd supergraph H with H \\ G acyclic
and every simple path in H \\ G of length at most two. Thus its components are
stars. This is a reduction only: neither the dominating-edge case nor deletion
of a star forest from an odd graph has been proved in full. Matching deletions
are already part of the unresolved star-forest case.

All three new lemmas passed the permitted-axiom audit. The main theorem still
has one `sorry`.

## Strict two-path trimming improvement can get stuck

`trim_local_exchange.py` found the following obstruction to a *strictly* improving
local-move claim (not to Gallai). Let H consist of K4 on 0,1,2,3 together with edges
04 and 05. H is all-odd. Delete the forest F={01,02}; G is connected and unicyclic.
Take the H-path partition
  3-0-5; 0-2-1; 2-3-1-0-4.
Deleting F leaves four nonempty path pieces. No replacement of just two H-paths
by two paths decreases that number. An equal-cost move followed by an improving
move does work:
  0-2-1; 3-1-0-5; 2-3-0-4              (four G-pieces)
  0-2;   3-1-0-5; 1-2-3-0-4            (three G-pieces).
In the last partition the F-only path 0-2 disappears on deletion and compensates
for the split of 3-1-0-5. Thus requiring every H-path to have a contiguous G-part
is stronger than needed: it suffices that the *total* number of G-pieces is at
most |V|/2. Scratch plateau tests found no obstruction to non-increasing two-path
moves for all connected odd graphs through six vertices, but this is not a proof
of a general exchange theorem.

## Strict matching-trimming obstruction, including the no-dominating-edge case

An exact test rules out strict two-path descent even for a *matching* in a
minimum odd completion. Take H=K6, F={01,25,34}, and the Hamilton path partition
  P0 = 0-5-1-4-2-3
  P1 = 1-0-2-5-3-4
  P2 = 2-1-3-0-4-5.
Trimming costs are respectively 1,2,1, so the total is four rather than three.
Every pair has ten edges on six vertices, so any replacement by two simple
paths must again consist of two Hamilton paths. Exhaustive exact enumeration
has eight replacements for each pair. Minimum trimming costs are 3,2,3 for
pairs (P0,P1), (P0,P2), (P1,P2), respectively: no strict improvement is possible.
`matching_trim_exchange.py` reproduces the finite check and also finds analogous
obstructions in Walecki decompositions of K8, K10, K12. This is a local-strategy
obstruction, NOT a counterexample to Gallai or to global forest compatibility.

It also persists with no dominating edge. Add vertices 6,7 adjacent only to 0,
and vertices 8,9 adjacent only to 1, in both H and G=H-F. Add paths 6-0-7 and
8-1-9 to the displayed partition. H is still all-odd; F is still a matching
and a minimum odd completion, since the six core vertices are even in G and
any completion must add at least three edges. The connected graph G has no
dominating edge: an edge dominating leaves 6 and 8 would have to be 01, which
is absent. There are five H-paths and six trimmed G-pieces.

For a pair involving P1 and either new leaf path, the odd vertices of its union
are 1,4 and the two new leaves. Hence neither 2 nor 5 can be an endpoint in
any two-path replacement, so the deleted edge 25 must remain internal. Neither
replacement path can be F-only, since F is a matching and none of its edges has
both endpoints among those four odd vertices. The pair therefore still costs
at least three. All other new pairs contain no F-edges and cannot improve.
Thus the verified star-forest/no-dominating-edge reduction does not eliminate
strict two-path obstructions. Equal-cost intermediate moves are still possible.

A candidate obstruction using a partial star deleted from K6 was also examined
and rejected: two star edges can lie together in a terminal prefix of a Hamilton
path, so the proposed counting obstruction was invalid. No claim that this was
a counterexample has been retained.

The Lean files were recompiled after this research. `Work.lean` remains gap-free;
`Spec.lean` still has the single original unresolved `sorry`. No new conjectural
exchange principle has been inserted into either file.

## Full reduction to matching deletion (verified in Lean)

The new theorem `erdos_583_of_odd_matching_deletion` reduces the **entire**
conjecture (all orders, including graphs with dominating edges) to this case:
H is all-odd, F <= H is a matching (isolated vertices allowed), and H \\ F is
connected. If the requested bound is proved for all such differences, then it
holds for every connected graph. This is a conditional theorem; its hypothesis
has NOT been proved or assumed globally.

Construction: if G has an even-degree vertex u, take two copies of G, and add
vertical edges between the copies of every even-degree vertex. This graph H is
all-odd. Delete all vertical edges except the one at u; the deleted edges form
a matching. The remaining K is two copies of G joined by one bridge. A bound
of |V(G)| paths for K, after deleting its bridge, gives at most |V(G)|+1 paths
for the disjoint copies. One copy therefore has at most ceil(|V(G)|/2) paths.
If G has no even-degree vertex, it is itself an instance with empty F.

New gap-free lemmas include:
- `pairedCopies`, its inclusion maps, degree formula, connectivity, and matching difference.
- `exists_odd_matching_completion_of_double_bridge` (constructive completion of the double).
- `walk_split_at_edge`, `split_path_delete_edge`.
- `refine_decomposition` (combine edge-disjoint refinements).
- `delete_edge_decomposition`: deleting one edge costs at most one extra path.
- `project_unpaired_path`, `decompose_one_of_two_copies`.
- `erdos_583_of_double_bridge`.
- `erdos_583_of_odd_matching_deletion`.

The original conjecture statement and import are unchanged. The main theorem
still has its one unresolved `sorry`; no proof of the matching-deletion case
has been inserted.

## Global endpoint-basis exchange is false

Another proposed global shortcut was that the minimum feasible sets of even
vertices supporting pairs of path endpoints form matroid bases. This is false.
Here "normal" means each odd vertex has exactly one endpoint and every even
vertex has either zero or two. Exact tests passed for all connected graphs
through eight vertices (995 through seven and 11,117 on eight), but failed on
this nine-vertex Eulerian graph:
  05,07,15,18,26,27,36,37,46,48,57,58,68.
Vertices 0,...,4 have degree two; 5,...,8 have degree four. Its minimum path
number is two. The feasible sets of the two common path endpoints are exactly
  {0,1}, {0,2}, {0,3}, {1,4}, {2,3}, {2,4}, {3,4}.
For bases X={0,1}, Y={2,3}, exchanging x=0 fails: neither {1,2} nor {1,3}
is feasible. This is NOT a counterexample to Gallai.

There is a structural explanation independent of numerical optimization.
Suppress the degree-two vertices: the graph becomes the doubled four-cycle
5-7-6-8-5. The five possible endpoints lie on these base edges:
  0 on 57; 1 on 58; 2 and 3 on 67; 4 on 68.
Two paths must each contain all four degree-four vertices. Their core traces
are Hamilton paths of the four-cycle. A pair of selected subdivision vertices
is feasible precisely when its two base edges are equal or adjacent, not
opposite. If the two base edges are opposite, the two core Hamilton paths would
have to omit those two edges respectively; the resulting endpoint locations
cannot each attach to one selected vertex on each opposite edge. Equal or
adjacent base edges give the required paths directly. This yields the displayed
seven pairs and the exchange failure.

Scripts: `endpoint_basis_test.py`, `/tmp/endpoint_bases8.py`, and
`/tmp/endpoint_bases9.py`. This obstruction rules out a matroid argument of that
form, and illustrates why passing small cases cannot establish an exchange law.

Separately, `matching_compatibility.py` tested the stronger assertion that an
|V(H)|/2-path partition of H can be chosen with every deleted matching edge
terminal (or a whole path). It passed all 28,981 eligible matching deletions
from the 224 connected all-odd graphs on eight vertices. This is finite evidence
only, not a proof of compatibility or Gallai.

## Complementary normal endpoint sets (unproved)

A stronger possible route is to find two normal decompositions of any connected
**even-order** graph, whose active even-vertex sets are complementary. Their
path counts would sum to |V|, proving the even-order bound. Odd vertices have
one endpoint in each decomposition; an even vertex has two endpoints in one
and none in the other. This is equivalent to a perfect path partition of the
canonical odd double with all vertical edges terminal. No proof is known here.

The exact diagnostic `complementary_endpoints.py` passed all 11,117 connected
graphs on eight vertices, and all 1,254 connected Eulerian graphs on ten
vertices with degrees 2 or 4. These are finite checks of an auxiliary assertion,
not a proof. Logs: `/tmp/complementary_endpoints8.log` and
`/tmp/complementary_endpoints10.log`.

The stronger requirement that two *minimum* normal decompositions have disjoint
active sets is false. Take K4 on 1,2,3,4, add 01,02 and the leaf edge 35. Its
unique minimum active set is {0}: there is a two-path partition
  0-1-2-3-4; 0-2-4-1-3-5,
while the other even vertices 1,2,3 have degree four and cannot be endpoints in
only two paths. This does not contradict complementary nonminimum sets.

Terminal-edge flexibility for two arbitrary paths is false as well. In the
two-triangle graph on {0,1,4} and {2,3,5}, joined by 03 and 12, the endpoint
pairing in a two-path partition is forced to (0,3),(1,2). Therefore 03 cannot
be terminal unless it is a singleton path, whose remainder is not a path.
Adding 45 makes the graph all-odd and permits three-path/global exchanges;
the two-path example alone does not refute matching compatibility.

## Three-path strict matching exchange is also false (structural obstruction)

The tempting extension to three-path improving exchanges fails as well. This
is a structural cut argument, not an inference from finite searches.

On each side of a cut, take nine vertices and the three Hamilton paths
  A = 0-2-3-4-5-6-7-8-1,
  B = 0-1-3-6-4-7-5-8-2,
  C = 3-5-1-6-2-7-0-8-4,
and the three unused matching edges 25,37,68 as singleton paths. Make two
copies, the second labeled 9,...,17. Join the Hamilton paths across the cut as
  P = reverse(A_left) + A_right, using cut edge (0,9),
  Q = B_left + C_right, using (2,12),
  R = reverse(C_left) + reverse(B_right), using (3,11).
Together with the six singleton paths, these form a nine-path partition D of
an all-odd simple graph H on eighteen vertices. H minus F={(0,9)} is connected.
F is internal to P, while its endpoints are endpoints of Q and R respectively.
Trimming D costs ten paths, exceeding the target nine.
`cut_matching_obstruction.py` checks all the displayed combinatorial data.

No replacement of at most three D-paths by the same number of paths strictly
improves the trimming cost:
* A replacement not including P cannot change the deleted edge. To make it
  terminal, the replacement must also include Q or R, since endpoint parity
  forces the endpoint set of any same-count replacement to stay unchanged.
* Replacing P,Q,R: the 51 edges force three Hamilton paths. There are just three
  cut edges, so each Hamilton path crosses exactly once. A cut edge cannot be
  terminal in a Hamilton path visiting all nine vertices on each side.
* Replacing two global Hamilton paths and one singleton: say the singleton is
  on the left. The union has seventeen left-internal edges, sixteen right-
  internal edges, and two cut edges. A simple path contains at most eight
  internal edges on either side. Thus all three replacement paths have a left
  edge and at least two have right edges. Those two paths must cross the cut;
  with only two cut edges, each crosses exactly once, and the third is wholly
  left. A terminal cut edge at its left endpoint would give its path no left
  edge, impossible. A terminal cut edge at its right endpoint would leave only
  the other crossing path covering the sixteen right edges, also impossible.
  The case of a right singleton is symmetric.
* The two-global-path case follows from the same count with sixteen internal
  edges on each side and two cut edges. One global path with up to two singleton
  paths has neither available endpoint of F and cannot make F terminal.
* F cannot become a singleton except in a replacement containing P,Q,R; in
  that case the other two paths cannot cover the remaining fifty edges.

Nor can a replacement reduce the number of H-paths: every chosen original path
has two distinct endpoints, and all chosen endpoints are distinct, forcing at
least the original number of paths by parity. With a one-edge matching, strict
trimming improvement therefore would require making that edge terminal or a
singleton, which the cases above exclude.

This is not a counterexample to the general conjecture or to global matching
compatibility. It rules out another bounded local descent strategy, even for
one deleted matching edge. The simpler three-Hamilton-path cut obstruction
already disproves the matching-preserving three-path switching lemma proposed
in this research turn.

By contrast, finite tests passed for the Walecki decompositions of K8 and K10,
and for 500 independently generated three-Hamilton-path unions on ten vertices
with one marked internal edge and disjoint marked terminal edges. The cut
construction explains why those small positive tests were not conclusive.

Additional status after this research turn:
- The Walecki three-path diagnostic also passed K12 (all 20 triples), without
  affecting the structural eighteen-vertex obstruction above.
- Complementary normal endpoint sets were found for three twelve-vertex graphs
  formed by gluing two copies of K3 joined to an independent four-set along two
  vertices (two clique vertices, one of each kind, or two independent vertices).
  These are further finite diagnostics only (`/tmp/split_gadgets.log`).
- `complementary_endpoints.py` now prunes an exact-cover state whenever a vertex
  has remaining degree d and endpoint quota c with d+c>2k for k remaining paths,
  or c>d. These are necessary conditions for simple paths, not approximations.
- A weaker sufficient global assertion would allow the two normal active sets
  to overlap at one prescribed root only. Their path counts would sum to at most
  |V|+1, which still yields ceil(|V|/2) for one copy. This assertion is UNPROVED;
  it is closely related to the already verified double-bridge reduction.
- No Lean source changes were made in this turn. `Work.lean` was recompiled
  successfully; `Spec.lean` was recompiled with its one expected sorry warning.
  No proof or counterexample to the original conjecture has been obtained.

## All-odd maximum-degree-three case (verified in Lean)

The conjectured bound is now proved for every graph with all degrees odd and
at most three (connectivity is not needed). This includes all cubic graphs.
New helpers in Work.lean and Spec.lean:
- `decompositionEnergy`, the sum of squared path edge counts.
- `exists_optimal_decomposition`: minimize path count, then maximize energy.
- `GoodDecomposition.replace_two`, `optimal_two_path_replacement_bound`.
- `optimal_endpoint_neighbor_mem`: if two distinct paths start at u, the first
  is no longer than the second, then its first neighbor lies on the second.
  Otherwise transfer that first edge to the second path; the resulting valid
  partition has at most the same size and strictly greater energy.
- The exact local degree formula for a nonempty path, endpoint representations,
  and lower bounds from the sum of two or three members' local degrees.
- `optimal_subcubic_parallel_paths`, `optimal_subcubic_no_three`.
- `optimal_subcubic_odd_endpoint_unique`.
- `subcubic_odd_decomposition`, `subcubic_odd_erdos_583`.

Proof of the key subcubic obstruction: order three paths starting at u by
length. The first neighbor of the shortest must lie on both other paths. If
this shortest path has length at least two, that neighbor has total degree at
least four. Hence it is a singleton u-v, and degree at most three forces both
other paths to end at v. Apply the same neighbor-transfer argument to those
two paths, ordered by length. If the shorter has length at least two, its first
neighbor is internal to both, again forcing degree at least four. If its length
is one, it duplicates the original singleton, impossible in a set partition.
Thus no three distinct paths end at one vertex. At an odd-degree vertex, two
endpoints would force a third by parity; so all endpoints are pairwise distinct,
and twice the number of paths is at most the vertex count.

All new helpers compile without gaps. Axiom audit:
`/tmp/Erdos583SubcubicAudit.lean` reports only propext, Classical.choice, Quot.sound.
Spec.lean now closes this additional case; the original theorem still has one
sorry. No general proof or disproof has been found.

## Strict two-path trimming fails even in the subcubic class

The all-odd subcubic endpoint theorem above is proved using path length energy;
it does not prove a matching-trimming descent rule. In fact, strict two-path
trimming descent fails already on eight vertices, even for one deleted edge.
Take H with edges
  04,06,07,14,25,26,27,35,46,57,
F={26}, and the four-path partition
  A=1-4; P=0-6-2-5-3; Q=6-4-0-7; R=2-7-5.
H is all-odd and subcubic; H-F is connected. Trimming costs five, not four.
`subcubic_trim_exchange.py` found and exhaustively checked this example.

A direct explanation: only a replacement of P with Q or R could make 26
terminal, since its endpoint tokens occur in Q and R. For P+Q, making it
terminal at 6 forces the path 6-2-5-3, leaving the triangle 0-4-6-0 with the
edge 0-7, which is not one path. The other endpoint 2 is unavailable. For P+R,
terminality at 2 forces 2-6-0, leaving triangle 2-5-7-2 and edge 5-3, again not
one path; endpoint 6 is unavailable. The pair P+A has neither endpoint token.
Singleton 26 is impossible for every pair because it needs both endpoint tokens.
No other pair contains the deleted edge. Thus no same-count two-path replacement
strictly improves trimming. This is NOT a counterexample to Gallai.

## Possible route from the proved cubic case to general subcubic graphs

A classical structural route, not yet formalized here, is to suppress all
vertices of degree two. The resulting connected multigraph has degrees one or
three. Loop blocks correspond to end cycles of the original simple graph,
each containing at least two suppressed vertices; such a cycle can be restored
with one additional path. A loopless all-odd subcubic multigraph can be reduced
to the simple case by removing a double-edge pair uv:
- If their other neighbors a,b differ, remove u,v and replace ua,vb by an edge
  ab. Restore a path through ab by a-u-v-b, using one uv edge, and restore the
  other uv edge as a singleton. This costs one path for two removed vertices.
- If a=b=w, delete u,v, making w degree one. Extend the endpoint path at w along
  w-u-v, and add the other u-v-w path. Again the cost is one.
The isolated triple-edge multigraph is an exceptional base case, corresponding
to a theta graph; simplicity before suppression ensures at least two degree-two
vertices, which pay for its extra path. Pure cycles are another base case.
This suggests a proof of the full subcubic case, but no multigraph lifting or
suppression argument has been formalized or used in Spec.lean.

Further verified subcubic additions in the same turn:
- `endpointMultiplicity D v` counts members with local degree one at v.
- `GoodDecomposition.odd_endpointMultiplicity_iff` proves that this count has
  the same parity as the ambient degree (for every path partition).
- `optimal_subcubic_endpointMultiplicity_le_two` and
  `exists_subcubic_normal_decomposition` prove that a minimum-cardinality
  subcubic path partition can be chosen normal: one endpoint at odd vertices,
  and zero or two at even vertices.
- `GoodDecomposition.sum_endpointMultiplicity` proves the exact double count
  sum_v endpointMultiplicity D v = 2*|D| for partitions with no empty members.
- `subcubic_one_even_erdos_583` proves the target whenever maximum degree is at
  most three and all vertices except possibly one have odd degree. The double
  count is at most |V|+1, which gives the required integer ceiling bound.
Spec.lean now closes this further case as well, with one unresolved sorry left.
The additional audit is `/tmp/Erdos583SubcubicNormalAudit.lean`; only the three
permitted axioms occur.

## Full subcubic case verified (latest continuation)

The maximum-degree-three restriction no longer needs an odd-degree hypothesis.
`subcubic_support_decomposition` proves, for a finite graph whose nonisolated
part is connected and whose maximum degree is at most three,

    exists D, GoodDecomposition G D and 2*D.card <= G.support.ncard + 1.

`subcubic_erdos_583` consequently proves the exact target for every connected
subcubic graph. Spec.lean now invokes this theorem in its subcubic branch. The
general branch STILL HAS ONE SORRY; no general proof or disproof was obtained.

The new proof avoids multigraphs. It inducts on support cardinality, with the
already verified all-odd subcubic theorem as the base when every nonisolated
vertex is odd. Otherwise a nonisolated even vertex x has degree two, with
neighbors u,v.

1. If uv is absent, suppress x by replacing u-x-v with uv. One support vertex
   is removed and every decomposition lifts with no increase in its size.
2. If xuv is a triangle and u also has degree two:
   - If v has no outside neighbor, connectedness of support implies the graph
     is just the triangle plus isolated vertices. An explicit two-path
     partition proves the required bound.
   - Otherwise let a be v's outside neighbor. Delete x,u,v, but reuse x as a
     leaf attached to a. Expand a-x to a-v-u-x and restore edge v-x. At least
     two support vertices disappear, and lifting costs at most one path.
3. If u,v each have an outside neighbor a,b:
   - If a,b are distinct and nonadjacent, delete x,u,v and add ab. Expand ab
     to a-u-x-v-b and restore edge uv. At least two support vertices disappear
     (in fact three), and lifting costs at most one path.
   - If a=b or ab is already present, delete x,u,v, but reuse v as a leaf
     attached to a. Expand a-v to a-u-x-v and restore path u-v-b. Again at
     least two support vertices disappear and the cost is at most one path.

Connectivity in the last case uses the existing edge ab (or a=b). All degree
bounds and support-cardinality inequalities are formalized. No new theorem
hypotheses are being assumed globally.

New general-purpose helpers include:
- `GoodDecomposition.expand_edge`: replace an edge by an internally fresh
  simple path without increasing a path-partition's size.
- `GoodDecomposition.map_of_edge_surjective`, `.lift_induce_support`.
- `SupportConnected` (nonisolated-part connectivity), and reachability
  mapping/closed-set helpers.
- `puncture G T`: remove edges incident with T on the same ambient type.
- `subcubic_puncture_add_edge`, `SupportConnected.puncture_add_edge`.
- `support_card_bound_of_removed`, `support_card_puncture_add_edge`.
- `GoodDecomposition.expand_edge_restore_path`, `.puncture_expand_restore`.
- `puncture_two_walks_cover`, `puncture_disjoint_walk`.
- `smooth_degree_two`, `reduce_triangle_two_degree_two`,
  `reduce_triangle_separate_attachments`, `reduce_triangle_near_attachments`.

Work.lean and Spec.lean are synchronized. Work.lean has no sorry and compiles;
Spec.lean has one unresolved sorry in its main theorem. Both have harmless
simp-linter warnings. The original import and main conjecture statement have
not changed. The proof is entirely in Spec.lean, not dependent on Work.lean.
Audit `/tmp/Erdos583FullSubcubicAudit.lean` printed exactly
`[propext, Classical.choice, Quot.sound]` for the new reduction lemmas,
edge expansion, and both full subcubic theorems. Audit output:
`/tmp/subcubic_full_audit.log`.

## Pendant-cycle extensions and an unrestricted triangle reduction

Latest continuation (all new helpers compiled and axiom-audited):

### Pendant-cycle attachment

`GoodDecomposition.attach_cycle` is now proved for arbitrary finite graphs,
with no degree bound. If H <= G, a simple cycle C meets H's support only at v,
v is nonisolated in H, and E(G)=E(H) union E(C), any path partition D of H
lifts to a path partition of G with at most |D|+1 members.

It is important that this does NOT assume that v is an endpoint in D. Choose
any member P containing v, split P at v, and extend the two pieces along the
two v-to-w arcs of C. Those two simple paths replace P. The internal freshness
of C gives simplicity and edge-disjointness.

The support count grows by at least two vertices (`support_card_attach_cycle`),
so `support_bound_attach_cycle` preserves the bound 2*|D| <= |support|+1.
`SubcubicCycleExtension` is an inductively defined sufficient class: a graph
with connected subcubic support, followed by finitely many such pendant-cycle
attachments. `SubcubicCycleExtension.support_bound` and `.erdos_583` prove the
requested bound for this class, which allows arbitrarily large degrees.
Spec.lean's former subcubic branch now invokes this stronger sufficient class.
This is not a classification of all connected graphs, nor a proof for all
cactus graphs.

Additional reusable lemmas:
- `GoodDecomposition.path_through_support`
- `GoodDecomposition.extend_replace_one`
- `attach_two_paths_to_path`
- `walk_disjoint_of_fresh_support`
- `walk_support_subset_support`
- `cycle_support_ncard`
- `erdos_583_of_support_bound`

### Unrestricted degree-two/degree-three triangle

`reduce_triangle_degree_two_three` removes two vertices x,u from a triangle
x-u-v, assuming deg(x)=2 and deg(u)=3 (encoded as explicit neighbor lists).
There is NO bound on the other degrees. Let a be u's third neighbor. On the
same ambient vertex type, set

    H = puncture G {x,u} union edge(v,a).

H has connected support and at least two fewer support vertices. Every H
path partition lifts with at most one extra path:
- If va is absent in G, expand va to v-x-u-a and restore uv.
- If va is already present, expand it to v-x-u-a and restore the two-edge
  path u-v-a, restoring both uv and the original va.

This observation avoids the need to split into cases on deg(v). The prior
subcubic induction is unchanged, but this new reduction is available for a
future general minimal-counterexample or larger-degree argument. It is not
used to assert the general conjecture.

### Current files and audits

Work.lean has no gaps and compiles with no warnings after removal of unused
simp arguments. Spec.lean contains all these helpers and still has exactly
one `sorry`, in the general branch of `erdos_583`. The original statement and
single import are unchanged. No complete submission was made.

Audit: `/tmp/Erdos583CycleAttachmentAudit.lean`, output
`/tmp/cycle_attachment_audit.log`. The seven audited declarations (including
the new closure theorem, unrestricted triangle reduction, and old subcubic
theorem after cleanup) use exactly propext, Classical.choice, Quot.sound.
Compile logs: `/tmp/clean_work_compile.log`,
`/tmp/spec_cycle_attachment_compile.log`.

Simp cleanup utility `/tmp/clean_simp_args.py` removes arguments identified by
the linter at their source locations. Lean diagnostic line numbers are 1-based
but the printed column numbers are 0-based. It expects the compile log at
`/tmp/clean_work_compile.log`. A pre-cleanup backup is
`/tmp/Work.before_simp_cleanup.lean`.

### Remaining mathematical difficulty

The unrestricted odd-graph theorem (Lovasz) and the connected matching-deletion
case remain unproved in this development. Mathlib has no path-decomposition
version of Lovasz's theorem. The existing cut obstructions still rule out the
bounded strict matching exchanges tried earlier. No new global rearrangement
argument or counterexample was found in this continuation.

One possible local strengthening, not yet formalized: in
`optimal_subcubic_no_three_ordered`, the degree bounds are only used at neighbors
of the common endpoint u (the first vertices of the two shorter paths). Thus
that lemma should generalize to the hypothesis that all neighbors of u have
degree at most three, without bounding deg(u) or nonneighbors. This would bound
endpoint multiplicity at an isolated high-degree vertex, but does not itself
bound excess endpoints at its degree-three neighbors and does not prove the
all-odd case.

## Localized endpoint lemma, cut bound, and a false odd-cycle deletion strategy

Latest continuation: the full conjecture is STILL unresolved. Spec.lean now
has 4053 lines and one sorry at line 4051. Work.lean has 4028 lines, no gaps,
and compiles without warnings. Spec.lean preserves its import and conjecture
statement. No incomplete proof was submitted.

### Verified localization of the endpoint argument

The previous suggested localization is now proved:
- `optimal_parallel_paths_of_neighbor_degrees`
- `optimal_no_three_ordered_of_neighbor_degrees`
- `optimal_no_three_of_neighbor_degrees`
- `optimal_endpointMultiplicity_le_two_of_neighbor_degrees`
- `optimal_endpointMultiplicity_eq_one_of_odd_neighbor_degrees`

The hypothesis is only `forall y, G.Adj x y -> G.degree y <= 3`. It imposes
no bound on x itself or on nonneighbors. For an optimal (minimum cardinality,
maximum squared-length energy) partition, endpointMultiplicity at x is <=2;
if x has odd degree, it is exactly one. The original subcubic declarations
are retained unchanged in interface.

This does NOT yet prove the almost-subcubic all-odd case: at a degree-three
vertex adjacent to a high-degree vertex the hypothesis need not hold, and
excess endpoints there remain uncontrolled.

### General degree/endpoint cut bounds (verified)

`boundaryGraph G S` consists of the G-edges crossing S. For any path partition
D with nonempty members and any v outside a finite vertex set S:

  degree(v) + endpointMultiplicity(D,v)
    + sum_{w in S} endpointMultiplicity(D,w)
  <= 2*|D| + |boundary(S)|.

This is `GoodDecomposition.degree_endpoint_cut_bound`. A path containing v
must cross the boundary once for each of its endpoints in S; a path not
containing v has at most two such endpoints. Splitting a path at v proves the
per-path inequality; summation uses the edge partition.

The parity corollary `GoodDecomposition.degree_odd_cut_bound` is

  degree(v) + 1_{degree(v) odd} + #{w in S : degree(w) odd}
  <= 2*|D| + |boundary(S)|.

Other new helpers:
- `GoodDecomposition.degree_add_endpointMultiplicity_le`
- `walk_boundary_nonempty`, `path_endpoint_boundary_bound`
- `path_sum_endpoints_on_set`
- `IsDecomposition.ncard_inter_eq_sum`

### Odd-vertex cycle deletion need not preserve consistency

A proposed shortcut toward Lovasz was that deleting a cycle consisting of
odd vertices from a consistent graph (one path endpoint at each odd vertex,
none at even vertices) preserves consistency. This is false EVEN if the
remaining graph is connected. The counterexample and proof are formalized
in namespace `OddCycleDeletionObstruction` in both Lean files.

On vertices 0,...,7, let H have edges
  05,06,07,15,17,25,27,36,46,56,57,67.
There is a three-path partition:
  0-5-1-7-6-3;
  4-6-0-7-2-5;
  6-5-7.
Its six endpoints are distinct and are precisely H's odd vertices
{0,3,4,5,6,7}; vertices 1 and 2 have even degree two.

Delete the triangle C=0-5-6-0. All three cycle vertices are odd in H. The
remaining connected G has edges
  07,15,17,25,27,36,46,57,67.
Choose v=7 and S={3,4,6}. Vertex 7 has odd degree five, all three vertices
of S have odd degree, and boundary(S) consists only of edge 67. The cut bound
therefore gives 5+1+3 <= 2*|D|+1, so every G path partition has at least four
members. This is a structural proof, not merely a search result.

G has the following four-path partition, also formalized:
  0-7-1-5-2;
  2-7-5;
  3-6-4;
  6-7.
Thus its path number is exactly four, equal to Gallai's bound for eight
vertices. This is NOT a counterexample to the original conjecture.

Key declarations in the namespace:
- `G_connected`, `G_boundary`, `G_no_three_paths`, `G_four_paths`
- `H_three_paths`, `c_isCycle`, `c_odd_vertices`, `delete_c`
- `witness` packages the failed auxiliary assertion's data.

The weaker version allowing disconnection also failed on eight vertices:
  H=05,06,07,15,26,27,36,37,47,56,67; C=0-5-6-0.
After deletion edge 15 is an isolated component, while another component
has degree-five vertex 7 and only four odd vertices, so it needs >=3 paths
in addition to the isolated edge. No Lean certificate was needed for this
weaker example once the connected example was found.

Diagnostic `odd_cycle_deletion.py` checked exact path partitions, not numerical
approximations. It passed 2026 eligible deletions through seven vertices and
then found the eight-vertex obstruction. The connected variant is
`/tmp/odd_cycle_deletion_connected.py`. Logs:
`/tmp/odd_cycle_deletion7.log`, `/tmp/odd_cycle_deletion8.log`,
`/tmp/odd_cycle_deletion_connected8.log`. No diagnostic is still running.

### Audits and Lean lessons

Latest audit `/tmp/Erdos583OddCycleObstructionAudit.lean`, output
`/tmp/odd_cycle_obstruction_audit.log`, reports only
[propext, Classical.choice, Quot.sound] for all seven audited results,
including the concrete witness, exact four-path partition, cut bound, and
the previously verified cycle-extension upper bound. Concrete finite checks
used kernel `decide`, not `native_decide`.

- In explicit walks, annotate each adjacency, e.g.
  `.cons (by decide : H.Adj 0 5) ...`; otherwise intermediate vertices remain
  metavariables and `decide` cannot run.
- `by decide` for a Walk.IsPath may get stuck on its instance's Eq.rec;
  `by apply Walk.IsPath.mk'; decide` checks the support list directly.
- Closed finite graph connectivity was decidable for this example.
- IsAcyclic had no synthesized Decidable instance, so the four-path upper
  bound was proved by the explicit partition instead.
- To compute a finite graph edge-set identity, use Sym2 induction, rewrite
  membership into decidable adjacency/list membership, then `revert a b;
  decide`. This was much cheaper than 64 `fin_cases`/simp branches.
- `Set.union_inter_distrib_right`, not `Set.union_inter_distrib`.
- `Set.Finite.ncard_biUnion` plus `finsum_mem_coe_finset` gives cardinal sums
  over a finite disjoint set union.

The all-odd Lovasz theorem itself and connected matching deletion remain the
core unproved mathematics. The cycle-deletion obstruction has two even vertices
and does not refute the all-odd theorem. There is still no valid global
rearrangement argument establishing that theorem or Gallai's conjecture.

## Two further false reductions and an explicit complete-graph construction

### Minimum decompositions need not be normal

Let G be K6 on 0,...,5 plus edges 60,61,62. Its eighteen edges have the
three-Hamilton-path partition
  6-0-5-1-4-2-3;
  6-1-0-2-5-3-4;
  6-2-1-3-0-4-5.
Three is minimum, by edge count. Vertices 0,1,2 have degree six and cannot be
endpoints in any three-path decomposition. Vertices 3,4,5 have degree five and
exactly one endpoint each; all three remaining endpoints must be at vertex 6.
Thus every minimum decomposition is non-normal. In particular, the verified
subcubic normality theorem cannot be generalized while retaining minimum
cardinality. A normal four-path partition exists:
  0-6-1;
  0-5-1-4-2-3;
  1-0-2-5-3-4;
  6-2-1-3-0-4-5.
Gallai's bound is four, so this is not a conjecture counterexample.

### Smoothing can increase path number

K5 minus edge 01 has nine edges and needs at least three paths. Subdivide
edge 23 with a new vertex 5. Its ten edges partition into two Hamilton paths:
  5-2-0-3-4-1;
  5-3-1-2-4-0.
Thus smoothing the degree-two vertex can increase path number, even with
nonadjacent neighbors. The verified edge-expansion lemma is only one-way.

### Walecki construction outline (not yet formalized)

For K_(2k), k>0, use ZMod (2*k). For i=0,...,k-1 take
  i, i-1, i+1, i-2, ..., i+(k-1), i-k.
Its edge sums alternate between 2i-1 and 2i modulo 2k, and its vertices are
all distinct. The odd sum class has k edges, the even class k-1. These k paths
partition the complete graph. For K_(2k+1), add infinity, close each such path
through infinity, and remove edge {i-1,i} from cycle i. The removed k edges
form the path -1,0,...,k-1. Together with the k broken cycles this gives k+1
paths. Handle k=0 separately: ZMod 0 is not finite. This would be an
unbounded-degree special case, not a proof of the general conjecture.

## Odd-vertex cycle addition also needs a global hypothesis

The converse of the earlier false cycle-deletion shortcut is false too, if
only the cycle vertices are required to be odd. Let G be the tree
  01,12,13,24,35.
It has two paths 4-2-1-0 and 1-3-5, with distinct endpoints exactly its odd
vertices {0,1,4,5}. Add the previously absent cycle 0-4-1-5-0. Its four
vertices were all odd. In the resulting H, vertex 1 has degree five, so any
path decomposition has at least three members. Thus adding an odd-vertex
cycle to a consistent graph need not preserve consistency either.

This is NOT a counterexample to Gallai: H has six vertices and the forced
three paths agree with its bound. It also does NOT refute cycle addition
when every vertex of the graph is odd; G has even vertices 2 and 3. That
restricted assertion would follow from the known all-odd theorem, but no
independent proof of it has been found here.

Exact diagnostic: /tmp/odd_cycle_addition.py. The degree-five obstruction is
a direct mathematical certificate, independent of the diagnostic's solver.
The Lean files were not changed in this continuation. Work still compiles
without warnings or gaps; the original general theorem in Spec remains
unfinished. Do not submit it as a complete proof.

## Complete graphs: Walecki construction now formally proved

The full even- and odd-order Walecki constructions are now gap-free in Lean,
including transfer to arbitrary finite vertex types. The main new theorem is
`complete_erdos_583`; no connectivity assumption is needed for this case, so
orders zero and one are included. The original theorem closes the G=top case
as well as its previous cases. The unrestricted branch still has one sorry.

Development file: Submission/Walecki.lean (imports the previously compiled
Work module during development). Its declarations have been incorporated
into Work and Spec without adding any import to the submission file.

Construction details:
- `zig (2*k) j` is j/2 at even positions and 2*k-(j+1)/2 at odd positions.
- `vertex i j` is i + zig(2*k,j) in ZMod(2*k). These vertex sequences are
  injective. For every consecutive pair x,y, `(x+y+1).val/2 = i`.
- `complete_even_decomposition`: k edge-disjoint Hamilton paths. Distinct
  modular edge-sum classes prove disjointness; cardinality proves coverage.
- `exists_tail` removes the first edge {i,i-1} from each zigzag path.
- For odd order, the path through the new vertex is
      i, infinity, i+k, ..., i-1,
  using the reversed tail. Its two spokes end at i and i+k. These pairs
  partition all finite vertices, so spokes of different paths are disjoint.
- The removed first edges form the extra path -1,0,...,k-1.
- `complete_odd_decomposition`: the k modified Hamilton paths and the extra
  k-edge path partition the complete graph on Option (ZMod (2*k)).
- `complete_transfer` maps decompositions across vertex equivalences.
- `complete_decomposition` yields 2*|D| <= |V|+1, including the small cases.
- `complete_erdos_583` converts this to the exact rational-ceiling bound.

Useful generic infrastructure added in namespace Walecki:
`exists_walk_support`, `exists_path_support`, `mem_edges_index`,
`getVert_of_support_eq_ofFn`, `decomposition_of_family_of_card`.
The last lemma establishes a finite path partition from pairwise-disjoint
path edge sets and the correct total edge count.

This is a genuine arbitrary-degree special case, not a proof of the general
conjecture. The all-odd theorem and matching-deletion reduction remain open
within this formalization.

## Two-path length optimization fails even for all-odd K6

An exact local-exchange diagnostic found this partition of K6 into five paths:
  2-4;
  0-1;
  1-4-0-3-2-5;
  0-2-1-5-4-3;
  0-5-3-1.
Every pair is length-maximal and cannot merge. This has a short structural
certificate: a pair containing either Hamilton path already has a path of
maximum possible length five and has more than five total edges. Among the
three other paths, 2-4 is disjoint from both others, while 0-1 together with
0-5-3-1 is a four-cycle, whose longest simple path has length three.

Thus two-path maximality alone cannot prove the all-odd result. This does NOT
contradict the globally minimum-cardinality optimal-decomposition lemmas:
the five-path partition is not globally minimum. Walecki gives three paths.
Diagnostic: /tmp/odd_pairwise_exchange.py and its corresponding .log file.

Walecki checkpoint verification:
- Spec has 4540 lines and one remaining sorry at line 4538.
- Work has 4511 lines and compiles without warnings or errors.
- Walecki.lean now uses namespace Erdos583WaleckiDevelopment with `open
  Erdos583Work`, so it still compiles after the integrated Work module is rebuilt.
- /tmp/spec_walecki_compile.log: only the expected original-theorem sorry warning.
- /tmp/work_walecki_compile.log: empty (both Work and development file passed).
- /tmp/Erdos583WaleckiAudit.lean and /tmp/walecki_axiom_audit.log: all six audited
  declarations, including complete_erdos_583, use exactly propext,
  Classical.choice, and Quot.sound. No extra axiom or native_decide was used.
- Spec retains exactly `import FormalConjecturesUtil` and the original theorem
  type. The file is not a completed submission; do not submit it as one.

## Terminal deletion and complete graphs with a matching removed (verified)

New development file Submission/Terminal.lean contains a gap-free general
trimming argument and a new use of Walecki's construction. These declarations
are now incorporated into Work and Spec, with no new import in Spec.

### General trimming theorem

`exists_trim_last` restricts a simple path to another graph if all edges except
possibly its last edge survive. It returns a path with support contained in
the original support, and exactly the surviving edge set. Induction on the
walk handles the case where its only edge is removed by returning a nil path.

`exists_trim_ends` permits deletion of the first and/or last edges. Its exact
hypothesis is that every edge in p.edges.tail.dropLast survives. No matching
assumption is needed.

`GoodDecomposition.restrict_terminal_edges` applies this to every member of a
path decomposition. If every missing edge is terminal in its member, restricting
the partition does not increase the number of paths. This theorem is conditional
on compatibility; it does NOT claim every odd graph has a compatible partition.

### A whole spanning cycle can be terminal in the even Walecki construction

For the i-th zigzag Hamilton path, the cyclic difference between consecutive
vertices at positions j,j+1 is plus or minus (j+1) modulo 2*k. Consequently an
edge between consecutive cyclic labels can occur only at the first or last
position. This is proved by `zig_succ_difference`,
`cyclic_adj_vertex_indices`, and `inner_edges_avoid_cycle` in namespace
WaleckiTerminal. `mem_inner_edges_index` is a general walk/list helper.

`WaleckiTerminal.complete_even_cycle_deletion` therefore proves the k-path
bound for ANY subgraph of K_(2k) containing every edge except possibly some of
  {0,1}, {1,2}, ..., {2k-2,2k-1}, {2k-1,0}.
No connectivity assumption is required. For k=1 the same definition is harmless
and the trimming lemma still applies.

`cyclic_complement_decomposition` and `erdos_583_of_cyclic_complement` transfer
this result along arbitrary vertex equivalences. The main theorem now closes
this certificate case, which includes deletion of a full spanning cycle as well
as partial cycles. This is an arbitrary-degree sufficient condition, not a
classification of all graphs.

### Arbitrary matchings can be placed on that cycle

`matching_vertex_order_aux` inducts on the number of vertices. Choose an edge
xy of the matching, remove its two vertices, order the remaining matching,
and prepend x,y. If there is no edge, use any ordering. The matching property
ensures there is no edge from x or y to a remaining vertex. The resulting
list is duplicate-free, contains all vertices, and contains every matching
edge as a consecutive pair in one orientation.

`matching_cyclic_order` turns that list into an equivalence from ZMod n to
any nonempty finite vertex type, placing every matching edge on the standard
spanning cycle.

`complete_even_matching_deletion` now proves:
  Even |V| -> (forall x, (G-complement).neighborSet x is subsingleton) ->
  exists D, GoodDecomposition G D and 2*|D| <= |V|.
The empty vertex type is handled separately. Its ceiling-bound corollary is
`erdos_583_of_even_complement_matching`.

Thus the earlier all-odd matching-deletion reduction is established in the
special case where the all-odd graph is complete. The reduction for arbitrary
all-odd graphs is STILL UNPROVED. No global endpoint rearrangement argument
was obtained in this continuation.

Terminal-deletion checkpoint audit:
- Work: 4989 lines, compiles without warnings or errors.
- Spec: 5023 lines, exactly one sorry at line 5021 in the original theorem.
- Terminal.lean also compiles against the rebuilt Work module.
- /tmp/spec_terminal_compile.log contains only the expected main-theorem sorry warning.
- /tmp/work_terminal_compile.log is empty.
- /tmp/Erdos583TerminalAudit.lean and /tmp/terminal_axiom_audit.log report only
  propext, Classical.choice, Quot.sound for all nine audited new declarations.
- The single original import and the original conjecture type are unchanged.

Possible next concrete extension (NOT PROVED): odd-order complete graphs minus
an arbitrary matching. In the odd Walecki Hamilton-cycle partition, the antipodal
finite matching {j,j+k}, j=0,...,k-1, is rainbow: its edge-sum class is
(j+ceil(k/2)) mod k. Relabel an arbitrary t-edge matching, leaving the new vertex
unmatched, so that its edges occupy classes 0,...,t-1. Break those t Hamilton
cycles at the deleted matching edges. Break each remaining cycle i at {i-1,i};
the latter removed edges form the single path t-1,t,...,k-1. This would give
k+1 paths, or k when t=k. A formal proof still needs a stronger exact ordering
of the matching pairs, and a generic simple-cycle-minus-one-edge path lemma.
This construction would be another special case, not a general Lovasz or Gallai
proof. Do not confuse the valid construction outline with an established Lean
result.

## Odd-order matching deletion and matching classification (verified)

The construction outlined above is now kernel-checked, and integrated in both
Work and Spec. `Submission/Cycles.lean` is the separate development copy.

Generic cycle cutting:
- `isCycle_append_comm`: rotating a cycle by commuting an append preserves
  simplicity, proved from edge and tail-support nodup.
- `exists_cycle_cut_edge`: deleting any edge from a simple cycle leaves one
  simple path, with precisely the edge-set difference and length one less.

Namespace `WaleckiCycles`:
- `closePath` closes a Walecki path through a new Option.none vertex; simplicity,
  exact length, finite-edge membership, and spoke membership are proved.
- `exists_cycle_family` gives k pairwise edge-disjoint Hamilton cycles in K_(2k+1).
- Each zigzag path's actual middle edge (between positions k-1 and k) is
  antipodal. The `middle_endpoint_index` and `middleEdge_injective` lemmas prove
  these edges form a matching, with one edge in each cycle.
- `prefixMatching k t` retains those middle edges in rows i<t; it is a matching
  with exactly t edges for t<=k.
- `canonical_matching_decomposition` cuts the t marked cycles at their deleted
  middle edges. Each unmarked cycle i is cut at {i-1,i}. The unmarked cut edges
  form the extra path t-1,t,...,k-1. All paths transfer to the complement of
  prefixMatching, are edge-disjoint, and their lengths sum to its edge count.
  Thus the complement has a decomposition into at most k+1 paths.

Coordinate-free transfer:
- `matching_edges_eq_of_mem`: matching edges sharing a vertex coincide.
- `matching_support_model`: matching support is equivalent to edgeSet x Bool,
  with adjacency precisely equality of the edge and inequality of the Boolean.
- `matching_support_card`: |support|=2*|edges|.
- `matching_equiv_of_card`: finite matchings with the same vertex and edge
  counts are isomorphic. Match the supports through the edge x Bool models,
  and separately match the isolated vertices by their cardinalities.
- `complete_odd_matching_deletion`: relabel any complement matching into the
  canonical prefix matching, and transport the construction. It proves
  2*|D|<=|V|+1 for odd order, including order one.
- `erdos_583_of_complement_matching`: combining with the previous even-order
  theorem gives the conjectured ceiling bound for ALL complement matchings.

Checkpoint:
- Spec: 5646 lines; exactly one remaining sorry at line 5644, in the original
  theorem's general branch. The new complement-matching branch is closed.
- Work: 5608 lines, gap-free and compiling with no warnings.
- Cycles: 626 lines, gap-free and compiling.
- Imports and original conjecture type unchanged.
- Audit `/tmp/Erdos583MatchingAudit.lean`, log `/tmp/matching_axiom_audit.log`:
  seven audited declarations use only propext, Classical.choice, Quot.sound.
- Compile logs `/tmp/work_cycles_compile.log` and `/tmp/spec_cycles_compile.log`.

This completes a genuine arbitrary-degree special case, NOT the full conjecture.
The general odd-graph theorem and connected deletion of a matching from an
arbitrary odd graph are still unproved. No original-conjecture counterexample
has been found. Do not submit the remaining sorry as a proof.

## Endpoint-pair slides alone can be completely blocked, even in K6

A further exact local-strategy obstruction (NOT a Gallai counterexample):
partition K6 into
  P0 = 0-1-2-3;
  P1 = 0-2-4-3-5-1;
  P2 = 0-3-1-4-5-2;
  Q  = 4-0-5.
These four edge-disjoint paths use all 15 edges. Vertex 0 has three path ends;
every other vertex has exactly one. Thus this is an all-odd graph with excess
endpoints concentrated at one vertex.

Consider the basic endpoint-pair slide: if P and R both end at x, transfer the
first edge xy of P to R, provided y is absent from R. This transfers two ends
from x to y, or merges the two paths if P was a single edge. In this example
all such moves are blocked. The three first neighbors at 0 are 1,2,3, and each
of P0,P1,P2 contains all three of those vertices. There are no two path ends at
any other vertex. Therefore even allowing arbitrary decreases of the length
objective does not make endpoint-pair slides alone sufficient.

More general two-path replacements are NOT ruled out: P0 and Q can be replaced
by 4-0-1-2-3 and 0-5. This subsequently permits endpoint slides. K6 itself has
its already-proved three-Hamilton-path decomposition. The obstruction only
invalidates an attempted restricted augmenting algorithm.

Diagnostic: /tmp/endpoint_slide_obstruction.py. It exactly enumerates paths for
the specified K6 configuration; no numerical conjecture search was used.

No new global rearrangement proof was obtained. The current conjecture remains
unresolved, with the single sorry documented at the matching checkpoint.

## Parity forest and normal path-and-cycle partition (verified)

New gap-free development file `Submission/Even.lean` contains 390 lines. Its
body is now incorporated into Work and Spec, with the original import unchanged.

- `exists_parity_forest`: minimize the number of edges among subgraphs of G
  with the same degree parity at every vertex. Deleting a simple cycle would
  preserve every parity and decrease the edge count, so the minimizer is acyclic.
- `neighbor_ncard_sdiff_add` and `sdiff_even_of_same_parity`: the complement of
  that forest within G has all degrees even.
- `acyclic_even_eq_bot`: the existing exact forest path formula implies an
  even forest has no edges.
- `IsCycleSubgraph`, `lift_cycle_subgraph`.
- Generic lifting helpers `IsDecomposition.lift_union`, `.lift_pairwise`, and
  `restore_subgraph_partition`. The latter restores an arbitrary subgraph to
  an edge partition; it does not assert that subgraph is a path.
- `even_cycle_decomposition`: induction on the number of edges gives a
  partition of any finite even graph into simple cycles. A nonempty even
  graph cannot be acyclic; remove a cycle, recurse, and lift the partition.
- `lift_subgraph_injective`, `neighborSet_lift`, `endpointMultiplicity_lift`.
- `GoodDecomposition.endpointMultiplicity_of_exact_card`: if a nonempty-member
  path partition attains the odd-vertex lower bound, its endpoint multiplicity
  is one at each odd vertex and zero at each even vertex. This follows by
  equality in a sum of pointwise lower bounds.
- `forest_normal_decomposition`: a forest admits such an exact endpoint partition.
- `normal_path_cycle_decomposition`: every finite G has disjoint finite families
  P and C of nonempty simple paths and simple cycles; P union C partitions all
  edges; the ends of P are exactly the odd vertices, each once; and
  2*|P| = number of odd vertices.

IMPORTANT: the last theorem imposes NO bound on the number of cycles. It is
NOT Lovasz's bounded path-and-cycle theorem and NOT the all-odd path theorem.
For an all-odd graph it yields |V|/2 paths PLUS an uncontrolled cycle family.
Absorbing those cycles without adding paths is still unproved.

## Maximum degree alone does not repair odd-vertex cycle addition (verified)

The proposed auxiliary lemma was: a consistent path partition into p paths
remains consistent after adding an edge-disjoint cycle on odd vertices,
provided the resulting maximum degree is at most 2p. This is false.

On vertices 0,...,7 take the tree G with edges
  01, 12, 13, 04, 46, 05, 57.
Its odd vertices are 0,1,2,3,6,7. A three-path partition is
  2-1-3; 1-0-4-6; 0-5-7.
Add triangle C=0-6-7-0, obtaining H. Every cycle vertex is odd in G and H,
and H has maximum degree five (below 2p=6). Nevertheless H needs at least
four paths. For S={1,2,3}, its boundary is just edge 01 and all three S
vertices are odd. Vertex 0 has degree five. The existing cut inequality gives
  5+1+3 <= 2*|D|+1,
hence |D|>=4.

Namespace `CycleAdditionDegreeObstruction` formalizes the tree, its three-path
partition, the added triangle, the exact deletion equality, the degree bound,
and the impossibility of three paths in H. `witness` packages these facts.
The tree proof uses connectedness and its exact edge count, followed by the
previously proved forest theorem. The impossibility proof uses the generic cut
bound, not a search or numerical approximation.

This does NOT refute the all-odd theorem: vertices 4 and 5 have degree two.
It does NOT refute Gallai: H has eight vertices, so four paths are allowed.

A preliminary exact check of the false auxiliary lemma passed 1462 eligible
cycle additions through seven vertices (`/tmp/cycle_addition_degree_test.py`).
The eight-vertex obstruction above was then constructed from a tight cut,
not from blind counterexample enumeration. A scratch feasibility check initially
misordered the NetworkX vertices; rebuilding the graph with nodes inserted in
range order corrected it. The Lean certificate is independent of that script.

Current checkpoint: Work has 5990 lines; Spec has 6029 lines and still exactly
one sorry at line 6027. The original conjecture is unchanged and unresolved.
Compile logs: /tmp/work_even_compile.log and /tmp/spec_even_compile.log.

Even-decomposition checkpoint audit:
- /tmp/Erdos583EvenAudit.lean and /tmp/even_axiom_audit.log report exactly
  propext, Classical.choice, Quot.sound for all eight audited declarations,
  including normal_path_cycle_decomposition and the new obstruction witness.
- Rebuilt Work and Spec oleans. Work and Even compile without warnings/errors.
  Spec has only the original theorem's sorry warning.
- No cycle-absorption assumption was added as an axiom or used to close the
  original theorem. No complete proof or original-conjecture disproof exists here.

## Two-choice ordered incident-edge pairing is too restrictive

A targeted exact diagnostic considered transition systems for all-odd graphs.
At each vertex, order the incident edges and choose either of the two alternating
pairings (leave the first or the last edge unpaired). This always gives one
trail end per vertex, but may yield repeated vertices or closed trail components.

With one common linear ordering of the vertices, ALL 64 such choices fail on
K6. By symmetry, relabeling the common linear order does not repair that example.
Script: /tmp/ordered_pairing_test.py. This invalidates this restricted construction,
not Lovasz's all-odd theorem, which allows many more transition choices.

Changing to the cyclic neighbor order beginning after each vertex repairs K6,
but the fixed cyclic-order two-choice rule fails on the eight-vertex graph
  04,05,07,15,16,17,25,26,27,37,46,47,56,57,67
(graph6 G?bb^{). Its degrees are all odd. Script:
/tmp/cyclic_pairing_test.py. This second check does NOT rule out choosing a
better cyclic order; no theorem asserting that such an order always exists
has been proved or assumed. Neither diagnostic has been integrated as a Lean
certificate, and neither is used by any submitted-file declaration.

## Edge capacity and exact complement-matching path counts (verified)

New development file `Submission/Bounds.lean` has 248 lines and is now integrated
in Work and Spec. This continuation did NOT obtain a general Gallai proof.

General lower bounds:
- `GoodDecomposition.card_edges_le`: |E(G)| <= |D|*(|V|-1), from the sum of
  member edge counts and the length bound for every simple path.
- `.card_gt_of_edge_capacity`: if k*(|V|-1)<|E(G)|, then |D|>k.
- `edge_ncard_add_compl`: |E(G)|+|E(complement G)|=choose(|V|,2).
- `odd_order_edge_ncard_add_compl`: the corresponding k*(2k+1) expression.
- `.exists_endpoint`: a nonempty graph partition has an actual path endpoint.
- `.min_degree_lower_bound`: if the graph is nonempty and has minimum degree
  at least d, then d+1<=2*|D|. At an endpoint the previous per-vertex capacity
  inequality is strict relative to the degree alone.

Sharp constructions:
- `WaleckiCycles.canonical_maximum_matching_decomposition`: when t=k, cut each
  of the k Hamilton cycles at its marked middle edge and use those k paths
  directly. Unlike the earlier general t<=k construction, there is no extra
  empty path. The sum of path lengths is exactly the remaining edge count.
- `complete_odd_maximum_matching_deletion`: transport this through the proved
  matching classification. On 2k+1 vertices, a complement matching of size k
  permits at most k paths, including k=0 (the edgeless one-vertex graph).
- `sharp_odd_complement_matching_decomposition`: for arbitrary complement
  matching on 2k+1 vertices, there is a minimum partition of size
    k + (if |E(complement G)|<k then 1 else 0).
  A smaller matching leaves too many edges for k simple paths; a maximum
  matching gives exactly k paths. The statement includes minimality against
  every competing GoodDecomposition, not just an upper bound.
- `sharp_even_complement_matching_decomposition`: for 2k vertices with k>=2,
  deleting any matching leaves path number exactly k. The existing construction
  supplies the upper bound. All degrees are at least 2k-2, and a nonempty path
  partition has an endpoint, so the lower bound forces at least k paths.
  The size restriction excludes the edgeless two-vertex exceptional case.

Work: 6230 lines, gap-free. Spec: 6270 lines, exactly one sorry at line 6268.
The conjecture and single original import are unchanged. Compile logs:
/tmp/work_bounds_compile.log and /tmp/spec_bounds_compile.log.

## An unproved stronger odd-order floor-bound route

A proposed strengthening was examined: for connected odd-order graphs, perhaps
failure of the floor(|V|/2) path bound always comes from the elementary edge
capacity obstruction |E|>floor(|V|/2)*(|V|-1). This is NOT proved or assumed.
It would be stronger than the original conjecture; finite positive tests do
not make it a valid reduction.

The exact diagnostic /tmp/floor_density_test.py passed all 869 eligible
connected odd-order graphs in the graph atlas (orders up to seven). It also
passed all 5621 graphs in /tmp/degree24_9.g6 with nine vertices and degrees
between two and four, including the 276 even-degree examples in
/tmp/even24_9.g6. The solver enumerates simple paths and uses exact edge masks;
it does not constrain endpoint multiplicities to be normal. The new sharp
complement-matching theorem verifies the proposed density boundary within that
family, but says nothing about arbitrary graphs outside it.

No original-conjecture counterexample was found. The all-odd cycle-absorption
step and the arbitrary all-odd matching-deletion case remain unproved.

Bounds checkpoint audit:
/tmp/Erdos583BoundsAudit.lean and /tmp/bounds_axiom_audit.log report only
propext, Classical.choice, Quot.sound for all nine audited new declarations.
Submission/Bounds.lean also compiles against the rebuilt Work module.
No incomplete proof was submitted. The single unresolved sorry is still in
Erdos583.erdos_583, not in any of the new helper declarations.


## Normal trail systems and the simplicity gap (verified)

New development: `Submission/Trails.lean` (481 lines), namespace
`Erdos583TrailDevelopment`; integrated into Work and Spec.

Verified lemmas:
- `trail_append_of_disjoint`, `splice_closed_trail`, `extend_trail_family`.
- `trail_neighbor_ncard_even_iff` and `trail_neighbor_ncard_odd_iff`.
  These use the Eulerian trail on the walk's own spanning subgraph. For an
  open trail, the odd local-degree vertices are exactly its two endpoints;
  their local degrees need not equal one.
- `absorb_cycle_family`: an edge-disjoint cycle remainder can be spliced into
  an indexed trail family when its endpoints cover all vertices. The index
  set and the two endpoint functions are preserved during this absorption.
- `all_odd_normal_trail_partition`: every finite all-odd graph has k open
  trails, 2*k = |V|, pairwise edge-disjoint and covering all edges, with
  the map from `Fin k × Bool` to their endpoints bijective.
  This is a TRAIL theorem, not the all-odd SIMPLE-PATH theorem.
- `all_odd_paths_of_bounded_path_cycle`: if an all-odd graph has a partition
  into path family P and cycle family C with 2*(|P|+|C|) <= |V|, then C is
  empty and P is a path partition of size |V|/2. The needed bounded
  path-and-cycle theorem is NOT proved by the earlier normal construction.
- `NormalTrailSystem` packages explicit endpoints, trails, endpoint
  bijectivity, disjointness, and coverage. `all_odd_normal_trail_system`
  supplies one. `endpoints_ne` and `twice_card` are checked.
- `NormalTrailSystem.score` is the sum of distinct vertex incidences.
  `exists_max_score` proves a maximum exists among ALL normal trail systems
  with k members, permitting the endpoint pairing to change.
- `NormalTrailSystem.sum_length` equals |E|.
  `score_le_edges_add` gives score <= |E|+k.
  `score_eq_edges_add_iff` proves equality iff every member is a simple path.
  `path_decomposition` converts such a simple system to a GoodDecomposition
  with exactly k members.
- `trail_endpoint_slide`: if a trail starts with v-w and revisits v, its
  first edge can move to an edge-disjoint trail starting at w. The two
  starting endpoints are exchanged; trail status, edge partition, and
  disjointness are preserved. Total distinct vertex incidence never
  decreases and strictly increases if the second trail avoids v.
  This is only a local move, NOT a global normalization argument.

### Remaining global issue

It is still unproved here that the maximum incidence score reaches |E|+k.
A local slide requires a repeated starting vertex, not merely an internal
repetition, and requires a second trail. Moving an internal loop to the
endpoint-owning trail can lose distinct vertex incidences elsewhere.
The earlier path endpoint-slide obstruction is not resolved by this lemma.

Do not require the original endpoint PAIRING to be preserved when trying
normalization. There is a concrete obstruction on eight vertices:

    triangles 0-1-4-0 and 2-3-5-2, edges 03,12,46,57.

Every degree is odd. A normal trail partition is

    4-6; 5-7; 0-4-1; 2-1-0-3-5-2-3.

There is no simple-path partition with exactly these endpoint pairs.
The leaf endpoints force the first two paths to be the edges 46 and 57.
In the remaining graph, each triangle's edges must belong to both remaining
paths (one simple path cannot contain an entire cycle). Thus both paths
must cross between the triangles. But each has its two prescribed ends in
one triangle, so each must use both cut edges 03,12, contradicting edge
disjointness. This is an obstruction to FIXED-PAIR normalization, not to
Gallai or the all-odd theorem. `NormalTrailSystem.exists_max_score` correctly
allows the two endpoint functions to change.

All ten declarations in `/tmp/Erdos583TrailAudit.lean` were audited; their
only axioms are propext, Classical.choice, and Quot.sound. Compile logs:
`/tmp/trails_compile.log`, `/tmp/work_trails_compile.log`, and
`/tmp/spec_trails_compile.log`. The original theorem statement and single
import are unchanged. There is still exactly one sorry, in the unrestricted
branch of the original conjecture. No new main-theorem special-case branch
was added in this development.

Final trail checkpoint: Work rebuild is warning-free; Spec rebuild has only the
original conjecture's sorry warning. The ten integrated Spec declarations also
passed an independent audit (`/tmp/Erdos583TrailSpecAudit.lean`,
`/tmp/trail_spec_axiom_audit.log`). An exact scratch enumeration checked the
fixed-pair example above: the four prescribed pairs have respectively 1, 1, 4,
and 4 simple paths, and no four-path choice partitions the edges. This diagnostic
was not used in any Lean proof. Current lengths: Work 6703, Spec 6744, Trails 481.

## Global incidence deficits and endpoint exchanges (verified)

New development: `Submission/Rearrangement.lean` (572 lines), namespace
`Erdos583RearrangementDevelopment`; its body is integrated into Work and Spec.
No new main-theorem case split was added.

In namespace `NormalTrailSystem`:
- `endpointEquiv`, `owner`, `endpoint_mem_support`, `owner_spec`,
  `endpoint_iff_owner` give explicit, orientation-independent endpoint ownership.
- `subgraph_injective`, `parts`, `parts_decomposition`, `degree_sum` work for
  trails, without assuming they are paths.
- `odd_degree`: any normal trail system has odd ambient degree at every vertex.
- `containing T v`: indices of trails containing v.
- `blockedVertices T v`: all endpoints of those trails. Its cardinality is
  exactly twice `containing.card`, and it contains v itself.
  `mem_blocked_iff` identifies membership with the owner's trail containing v.
- `escapeNeighbors T v`: neighbors w whose endpoint-owning trail avoids v.
  `mem_escape_iff` is the corresponding adjacency/avoidance equivalence.
- `escape_bound`:

      degree(v) + 1 <= 2*containing(T,v).card + escapeNeighbors(T,v).card.

  At most 2t-1 neighbors are blocked when t trails contain v: their 2t
  distinct endpoints include v, which cannot be its own neighbor.
- `sum_containing_card` equals the global incidence score.
- `exists_local_deficit`: any nonsimple normal system has some v with
  2*containing.card < degree(v)+1. Proof uses the degree-sum identity and
  `score_eq_edges_add_iff`, not a conjectural exchange argument.
- `exists_two_escape_neighbors`: any nonsimple normal system has at least
  two escape neighbors at some vertex. Odd degree upgrades the deficit
  to at least two. This gives targets, NOT a route to them.
- `permute_starts_bijective`, `sum_extract_two`, `replace_two_starts` lift a
  two-trail replacement to a full normal system and give its exact score change.
- `orient`: independently reverse any chosen members, preserving the score
  and every member's subgraph.
- `improve_of_start_slide`, `improve_of_escape_slide`: a repeated starting
  vertex whose first neighbor is an escape permits a strictly higher score.
  The latter handles either stored orientation of the receiving trail.
- `max_score_start_neighbor_blocked`: such a direct escape cannot occur in
  a maximum-score system. This alone does not address internal repetitions.

Other verified helpers:
- `trail_same_owner_rotation`: for h : Adj v w, p : Walk w v, q : Walk v w,
  if `cons h (p.append q)` is a trail, so is `(q.append p).concat h`, with
  exactly the same subgraph. This handles a same-owner configuration by
  cyclically reordering pieces rather than trying an illegal self-slide.
- `exists_first_exit_of_injective_successor`: if f is injective on finite S
  and x is not in f(S), iteration starting at x eventually leaves S; it
  supplies a first exit time. It does NOT assert that trail moves realize f.
- `tail_last_neighbor_injective`: edge-disjoint nonempty walks into a common
  root have distinct final neighbors.
- `closed_prefix_neighbor_not_tail_image`: the first neighbor of a nonempty
  closed prefix, edge-disjoint from such tails, is outside their final-neighbor image.

All eleven audited declarations use only propext, Classical.choice, Quot.sound.
Audits: `/tmp/Erdos583RearrangementAudit.lean`,
`/tmp/Erdos583RearrangementSpecAudit.lean`, and matching `*_axiom_audit.log` files.
Build logs: `/tmp/rearrangement_compile.log`,
`/tmp/work_rearrangement_compile.log`, `/tmp/spec_rearrangement_compile.log`.
Work and the development file compile without warnings. Spec has only the
original theorem's sorry warning. Current lengths: Work 7270, Spec 7312.
Original theorem line 7282, remaining sorry line 7310; one original import.

### Promising next argument: endpoint repetition via rooted tails — NOT YET PROVED

A more concrete alternating-chain outline emerged. It might prove that a
maximum-score normal system has no repeated *endpoint*. It has NOT been
formalized or packaged as a theorem, and must still be checked carefully.

Fix an endpoint v whose own trail revisits v. Write its oriented trail as

    C : v -> v, followed by reverse(R_b) : v -> b,

with C a nonempty closed prefix. For every other trail that contains v,
choose an arbitrary cut at v, writing it as

    R_a : a -> v, followed by reverse(R_c) : v -> c.

Thus, for every endpoint w other than v of a v-containing trail, there is
an endpoint-to-root tail R_w. All these tails and C are pairwise edge-disjoint.
They need not be simple and need not meet v for the first time at their ends.
This avoids the difficult first-visit/last-visit bookkeeping.

Let B be the endpoint set of the v-containing family, S = N(v) intersect B,
and define f(w) to be the final neighbor of R_w for w in S. The last two
verified helpers give injectivity of f and show that the first neighbor x
of C is not in f(S). Hence its successor chain eventually leaves S.
All successor values are neighbors of v, so an exit is an escape neighbor.

Proposed invariant for realizing that chain: only the tail of a processed
vertex changes; every unprocessed endpoint tail remains exactly the original
walk. The set B remains fixed, and all vertex-incidence contributions remain
unchanged until the final escape slide. If the current closed prefix starts
with v-w, there are two cases:

1. w is the endpoint of a DIFFERENT trail R_w + reverse(R_c).
   Write C = (v-w) + C_rest. Move edge v-w to that trail. The old active
   trail becomes C_rest + reverse(R_b), and the new active trail is
   (v-w) + R_w + reverse(R_c). Thus R_w is replaced by C_rest, and all other
   non-root tails are unchanged. Reverse its closed prefix (v-w)+R_w to
   expose f(w) as the next first neighbor. Removing v from the beginning
   of the old active walk does not remove it from its support, and adding
   it to the receiving trail does not add it to its support, so the score
   stays unchanged.

2. w is the OTHER ENDPOINT OF THE ACTIVE TRAIL. Then its form is
   (v-w) + C_rest + reverse(R_w). Use `trail_same_owner_rotation` to turn
   this into

       reverse(R_w) + C_rest + (v-w).

   The new closed prefix begins with f(w); the new tail R_w is the single
   edge w-v. Every other tail is unchanged, and the entire active subgraph
   is unchanged. This removes the apparent same-owner dead end.

Because the original successor chain has no repetitions before exiting,
the next tail has not been modified. At the exit, its endpoint-owner is
outside the v-containing family and avoids v, so the already proved escape
slide strictly raises the score.

Remaining work for this outline: define a rooted-cut normal-system data
structure, construct its cuts, implement both updates with the stated exact
walk-tail invariant, and induct along the first-exit chain. The current
`replace_two_starts` returns subgraph equalities, not exact walk equalities;
that alone is insufficient for preserving ordered tail data. Strengthen it
with ordered support/edge-list identities, or construct rooted updates with
explicit walk copies. Do not silently substitute arbitrary Euler traversals.

Even completion of this outline would NOT yet prove all-odd simplicity.
There can be internal repetitions while every endpoint is unrepeated. Example
on vertices 0,...,7, with edges

    01,02,03,04,05,45,46,57,

has the normal trails

    1-0-4-5-0-2; 0-3; 4-6; 5-7.

All degrees are odd and all endpoints are unrepeated, but vertex 0 is repeated
internally in the first trail. This particular system is not score-maximal.
A global argument must show that internal repetitions in a maximum-score
system can be removed or converted to endpoint repetitions without lowering
score. Simply moving an internal closed segment to the endpoint-owning trail
can lose incidences at other shared vertices.

### Targeted diagnostic for internal-to-endpoint conversion — NOT A PROOF

A proposed two-trail lemma is: when an internal repeated vertex of one trail
is an endpoint of a second edge-disjoint trail, repartition their union into
two trails with the same four distinct endpoints, at least the old incidence
score, and an endpoint repetition. Endpoint pairing may change.
This statement is still UNPROVED.

`/tmp/trail_repair_diagnostic.py` checked a concrete skeleton
P = 0-1-2-3-1-4, Q = 1-5-0-2-4-6. Its score is 11; there are 16 maximum-score
two-trail edge partitions, 12 with an endpoint repetition.
`/tmp/two_trail_conversion_test.py` checked all 172 simple receiving trails
on seven vertices for that fixed P, requiring them to contain both old ends
0 and 4, and found a score-preserving endpoint-repeat conversion in each.
These exact finite diagnostics are not used in Lean and do not establish the
lemma or the original conjecture. No new network or library theorem was found.

### Simplification of the proposed rooted-tail pivot (latest mathematical note)

The two cases above can probably be UNIFIED at the level of endpoint tails.
This is an unformalized construction outline, not another proved theorem.

Keep the set B of endpoints of v-containing members fixed. Represent each
such member a->b as R_a + reverse(R_b), where all R_x end at v, and R_v is
the active closed prefix C. Let C = (v-w) + C_rest and suppose w belongs to B.
Define the updated tail family by

    R'_v = reverse((v-w) + R_w),
    R'_w = C_rest,
    R'_x = R_x for x != v,w.

At the same time, apply the vertex transposition sigma=(v w) to BOTH endpoint
functions of every member. Reconstruct a v-containing member a->b as

    R'_(sigma a) + reverse(R'_(sigma b)).

Members avoiding v have neither endpoint v nor w, and are left unchanged.
This works even if w is the other endpoint of the same active member; no
self-merge is attempted. In that case the one reconstructed trail is simply
reoriented/reordered using its two updated tails. Thus explicit mate involutions
or separate same-owner graph updates are unnecessary.

Why it is promising:
- The updated tails partition the same edges as the original tails.
- They remain pairwise edge-disjoint trails.
- Their vertex sets are exchanged at v and w and unchanged elsewhere:
  prepending v to R_w adds no vertex (R_w already ends at v); deleting the
  first v from C adds/removes no vertex (C_rest still ends at v).
- Since the endpoint labels are transposed simultaneously, EVERY reconstructed
  indexed member has the same vertex set as its original member. Thus the
  entire score is unchanged, not merely its sum over a pair.
- The updated root tail starts with the old last neighbor of R_w, exposing
  f(w). Only the non-root tail R_w changes; unprocessed tails remain exact.
- A successor never equals v because it is adjacent to v. Thus the continually
  updated root tail does not interfere with the unprocessed-tail invariant.

Suggested Lean representation: a `RootedNormalTrailSystem` extending a normal
system, with fixed active indices I (members visiting v), fixed endpoint set
B, tails `R : (w : B) -> G.Walk w.val v`, pairwise tail disjointness and trail
proofs, exact decompositions of active walks into their two endpoint tails,
and `start(i) in B <-> i in I`, `finish(i) in B <-> i in I`. Outside I, walks
avoid v. Require v in B and R_v nonempty. Construct the initial cuts by
`takeUntil`/`dropUntil`, except at the repeated root endpoint: use a later
return to v, so R_v is a nonempty closed prefix rather than nil.

The pivot then changes both endpoint functions by `Equiv.swap v w`, preserves
I and B, and changes just two tails. Prove exact tail equalities away from v,w,
edge-union preservation, and per-index vertex-set preservation. Use the original
successor's first-exit time and distinctness of its iterates to induct the pivot.
At the exit w notin B, its owner is an outside member avoiding v, permitting
the verified strict-improvement slide (after orienting the root if needed).

This should target the theorem that an endpoint repetition precludes global
score maximality. The separate internal-repetition conversion remains unresolved.


## Rooted-tail checkpoint: global endpoint-repetition improvement proved

`Submission/Rooted.lean` now compiles without warnings or gaps. Its body has
been integrated into Work and Spec. The new structure `RootedTailSystem`
retains ordered endpoint-to-root tails, but member reconstruction requires
only subgraph equality. This is enough to use the exact ordered-tail
invariant while allowing subgraph-based replacement constructions.

The uniform transposition pivot, finite injective successor chain, escape
exposure, and final strict slide all compile. The initial cuts are built
using a later return at the repeated starting endpoint and ordinary
`takeUntil`/`dropUntil` elsewhere, with an equivalence between endpoint slots
and the blocked endpoint set. Main theorems:

- `RootedTailSystem.rebuild`
- `RootedTailSystem.pivot`
- `RootedTailSystem.expose_escape`
- `RootedTailSystem.improve`
- `RootedTailSystem.of_repeated_start`
- `RootedTailSystem.improve_of_repeated_start`
- `RootedTailSystem.max_score_no_repeated_start`

All seven were audited with `#print axioms` in `Submission/RootedAudit.lean`;
they depend only on propext, Classical.choice, and Quot.sound. This proves
a global necessary condition for maximum incidence score, not just a
restricted local exchange condition. Internal repetitions remain unresolved,
as does the original Gallai conjecture. Spec still has its one original
`sorry`; no submission has been made.


## Internal-repetition checkpoint: the full all-odd path theorem proved

`Submission/Internal.lean` (about 1310 lines) compiles without warnings or gaps.
Its body is integrated under `TrailNormalization` in Work and Spec, and the
original theorem now has a verified all-odd branch. It still has one unresolved
`sorry`, for general connected graphs with even-degree vertices.

The key new argument avoids the unproved two-trail conversion conjecture.
Among maximum-score systems, descend on the length of a prefix A before a
nonempty closed segment C of a member A+C+B. Move its first edge a-w to the
endpoint owner of w. The donor no longer contains a (endpoint repetition was
already ruled out). If the receiver avoids a, the move is score-neutral and
shortens A. Otherwise it loses exactly one incidence and makes a repeated
endpoint a. Represent that receiver using the REVERSE of its new closed prefix.
The removed edge a-w lies in that prefix, but is not its first edge.

A strengthened rooted successor exchange avoids w: neither its initial first
neighbor nor any original non-root tail's last neighbor can be w, since edge
a-w lies in the root tail and tails are edge-disjoint. The pivot chain preserves
every outside member's endpoints and subgraph. The final escape slide restores
exactly the lost incidence. The shortened donor stays unchanged unless it is
the receiving member, in which case the added edge attaches at its OTHER end
(because escape w was excluded). Thus it still has the shorter prefix before
C, followed by a possibly extended suffix. Structural induction on A closes
the descent, even though the normal system and endpoint pairing may change.

Verified and audited new theorems include:
- `expose_escape_tracked`: escape avoiding a specified subset of root-tail edges,
  with full outside-member tracking.
- `repair_protected`: strictly improves score while preserving a protected
  outside member as a prefix (possibly appending one edge at the far endpoint).
- `shorten_oriented`, `shorten_member`: advance a maximal-score member's start
  while preserving maximal score and a suffix extension.
- `no_closed_segment`: the descent on the prefix before a nonempty closed segment.
- `max_score_isPath`: every member of a global maximum-score normal system is simple.
- `all_odd_path_partition`: every all-odd finite graph has a GoodDecomposition D
  with exactly `2*D.card = Fintype.card V`.

`Submission/InternalAudit.lean` audited all seven key declarations. Each depends
only on propext, Classical.choice, and Quot.sound. No unproved exchange lemma
or conjecture was assumed. The general matching-deletion compatibility problem
remains open in this development and is the next blocker for erdos_583.


## Prescribed-edge checkpoint (verified)

`Submission/Force.lean` proves that any suffix of a member of a maximum-score
normal system can be retained as the prefix of a member of another maximum-score
system. This follows by iterating `shorten_member`, allowing suffix extensions.
Consequently any specified edge can be the FIRST edge of a member, at either
specified endpoint, in a normal simple-path partition of an all-odd graph.

New theorems, integrated into `TrailNormalization` in Work and Spec:
- `extend_suffix`
- `force_first_of_split`, `force_first_edge`
- `max_score_member_isPath`
- `all_odd_prescribed_first_edge`
- `all_odd_prescribed_leaf_edge`: any ONE specified leaf edge can be a whole member.
- `all_odd_delete_single_edge`: deleting any ONE edge of an all-odd finite graph
  leaves a GoodDecomposition with `2*card <= |V|`, without needing connectivity.

All five main results audited in `Submission/ForceAudit.lean` use only the three
permitted axioms. The full Gallai conjecture remains unresolved.

Another useful formulation of the remaining gap: attach a leaf to each even
vertex of a connected graph G. The resulting graph is all-odd. To recover
Gallai by deleting leaves, it would suffice to find an augmented normal path
partition with at least floor(number of even vertices / 2) leaf edges as WHOLE
members. The one-edge forcing result does NOT prove this simultaneous bound.
During a forcing operation other whole leaf-edge members can cease to be whole.
The earlier nine-vertex endpoint-basis exchange obstruction still rules out
assuming these feasible choices form matroid bases. No new exact search was
needed or run to repeat that already established obstruction.


## Truncated endpoint augmentation is also false (exact auxiliary obstruction)

The matroid-style augmentation law still fails when feasible inactive sets are
truncated to size floor(number of even vertices / 2), i.e. at the Gallai target.
This was NOT a numerical search for an original-conjecture counterexample.

The connected six-vertex Eulerian graph has edges
  01,02,04,05,12,23,25,34.
It is a theta graph with four 0-to-2 routes: edge 02 and paths 0-1-2,
0-5-2, and 0-4-3-2. All six vertices have even degree. The feasible inactive
sets A={1,5} and B={0,1,2} have sizes 2 and 3, but neither A+0 nor A+2 is
feasible. Suppressing the two inactive degree-two vertices 1 and 5 gives
three parallel routes between 0 and 2. If 0 is also inactive, its degree four
allows it to lie on only two paths; the three internally disjoint 0-to-2
routes must lie on three different simple paths. The same argument applies
at 2. Thus the failure has a direct structural explanation.

`/tmp/truncated_endpoint_exchange.py` found this obstruction in the graph atlas
and stopped; `/tmp/truncated_endpoint_exchange.log` has the complete finite
feasibility output. The earlier nine-vertex basis obstruction passes the new
truncation, so it did not by itself settle this stronger-looking shortcut.
This example does NOT rule out enlarging A by SOME vertex: A+3 and A+4 are
feasible. A separate exact diagnostic of that weaker extension assertion is
now being run. Neither assertion has been used as a Lean hypothesis.

## Pendant projection checkpoint (verified)

`Submission/Pendant.lean` now compiles without warnings or gaps, and its body is
integrated under `PendantCompletion` in Work and Spec. It proves:

- `leafCompletion_odd`, `leafCompletion_connected`: attaching one leaf at each
  even vertex gives an all-odd graph, preserving connectivity.
- `project_path_support`, `project_edges`: collapsing pendant edges projects
  simple paths to simple paths and preserves exactly the original graph edges.
- `project_system`: a normal all-odd simple-path system projects to a good
  decomposition D of nonempty paths. If Z indexes the empty projections, then
  `D.card + Z.card = k`; endpoint multiplicity is at most one off the attachment
  set and at most two on it.
- `exists_normal_decomposition`: every finite graph has a good nonempty path
  decomposition with endpoint multiplicity at most two, equal to one exactly
  at the odd-degree vertices. This theorem DOES NOT include a Gallai bound.
- `normal_count`: for any such normal decomposition,
  `2*D.card + 2*(inactive D).card = |V| + (#even vertices)`.
- `normal_gallai_iff`: for a FIXED normal decomposition, the Gallai cardinal bound
  is equivalent to `floor(#even vertices / 2) <= (inactive D).card`.
- `exists_max_inactive`: there exists a normal decomposition maximizing the
  number of inactive vertices, with no claimed numerical lower bound.
- `gallai_of_inactive_extension`: the unproved strict-extension premise would
  imply Gallai. This is an explicit conditional theorem, not an axiom.
- `project_even_system`: in the even-vertex completion, `Z.card` equals the
  number of inactive vertices of the projected decomposition.
- `gallai_of_purification`: an explicit augmented path-system witness with
  enough empty projections gives the desired bound.

The audit `Submission/PendantAudit.lean` reports only propext, Classical.choice,
and Quot.sound for all tested main lemmas. The original conjecture still has
exactly one sorry. The stronger bounded-normal-decomposition assertion has NOT
been deduced from unrestricted Gallai, nor assumed true.

## Finished weaker-extension diagnostics

The script `/tmp/endpoint_extension_threshold.py` checked the specific stronger
claim that a feasible inactive set below the Gallai threshold can be extended
by one vertex while keeping every old inactive vertex. No obstruction occurred:

- all 995 connected atlas graphs on 2--7 vertices;
- all 11,117 connected graphs on eight vertices;
- the degree-2/4 Eulerian nine-vertex file `/tmp/even24_9.g6`;
- all 1,254 connected degree-2/4 Eulerian ten-vertex graphs.

The logs are `/tmp/endpoint_extension_threshold.log`,
`/tmp/endpoint_extension_threshold9.log`, and
`/tmp/endpoint_extension_threshold10.log`. All jobs finished. These finite tests
are not proofs and are not used to discharge any Lean hypothesis.

A separate selection-rule diagnostic, `/tmp/balanced_cut_endpoint.py`, tested
balanced maximum cuts of the graph induced by the even vertices. It found
maximum cuts whose inactive side is infeasible, so an arbitrary maximum cut
cannot be used as a proof. Example: the six-vertex graph with edges
  04,05,13,14,23,24,34
has even vertices {0,1,2,4}. The inactive set {1,2} is a balanced maximum-cut side
but impossible. It forces the three distinct 3-to-4 routes through 1, through 2,
and along edge 34 to lie on different paths, whereas odd vertex 3 has exactly
one endpoint and degree three, so can occur on only two paths. Some OTHER
maximum cuts do work. Every atlas graph had at least one working maximum cut;
this weaker existential observation remains unproved and unassumed.

Network access is unavailable (curl cannot resolve arxiv.org); no external
new theorem has been retrieved or claimed.

## Exact endpoint activation and deactivation (verified)

`Submission/Activation.lean` compiles gap-free and warning-free. Its body is
integrated under `EndpointSelection` in Work and Spec. The pendant projection
now also has `project_system_tracked`, retaining a source index for each
projected member; the old `project_system` API remains as a wrapper.

New verified facts:
- `split_member`: exact cardinal and endpoint bookkeeping for replacing one
  path by two disjoint nonempty paths with the same edge union.
- `activate_vertex`: splitting a member at a supported inactive vertex creates
  exactly two endpoints there, changes no other endpoint multiplicity, increases
  path count by one, and erases precisely that vertex from the inactive set.
- `realize_subset`: if all vertices are supported, any subset A of a feasible
  inactive set is realizable EXACTLY. Its path-count increase is exact.
- `FeasibleInactive` and `feasible_downward_closed`: the exact feasible inactive
  sets form a downward-closed family for connected nontrivial graphs.
- `projection_inactive_of_owner_eq`: if a root and its pendant leaf have the
  same augmented endpoint owner, the root is inactive after projection.
- `exists_normal_inactive_at`: any ONE specified even vertex can be made
  inactive in a normal partition, without a Gallai cardinal bound.
- `feasible_singleton`: any even singleton is exactly realizable when G is
  connected and nontrivial.
- `deactivate_by_append`: if concatenating two endpoint paths at v is simple,
  it removes exactly two endpoints at v, preserves all other multiplicities,
  decreases path count by one, and inserts v into the inactive set.
- `max_inactive_pair_intersects`: in a maximum-inactive normal partition, the
  two endpoint paths at an active vertex must intersect away from that vertex.
  This is only a necessary LOCAL condition, not a global cardinal bound.

`ActivationAudit.lean` and the extended `IntegratedAudit.lean` report only the
three permitted axioms for all these main results. Spec still has exactly one
sorry, in the original conjecture. Neither the statement nor the import changed.

## Local endpoint obstructions must not be mistaken for the global proof

An explicit normal four-path partition of K5 is
  0-1-2-3-4;
  1-4-2-0-3;
  0-4;
  1-3.
Its inactive set is {2}, while the Gallai target requires two inactive vertices.
At every active vertex the two endpoint paths intersect elsewhere: the relevant
Hamilton path contains the other endpoint of the singleton edge. Thus no direct
endpoint merge works. The length-square energy is 34, maximal among ALL
four-path partitions of K5: for 1 <= l <= 4, l^2 <= 5l-4, and the four lengths
sum to 10. So maximizing energy at a fixed, excessive path count is insufficient.

Even arbitrary strict THREE-path cardinal reductions can fail for a normal
partition above the target. The following six paths partition K9, each with
six edges, and endpoints twice at {0,1,3,4,6,7} and zero at {2,5,8}:
  0-2-1-3-6-5-7;
  3-5-4-6-0-8-1;
  6-8-7-0-3-2-4;
  0-1-6-2-8-4-7;
  3-4-0-5-2-7-1;
  6-7-3-8-5-1-4.
Any three members have 18 distinct edges, but two simple paths on nine vertices
can contain at most 16 edges. Any two members likewise have 12 edges and cannot
be replaced by one path (maximum length 8). Thus no replacement involving at
most three members can strictly lower the path count. This is NOT a Gallai
counterexample: K9 has a five-path decomposition, already proved in the file.
The certificate was constructed using two base paths and translation by 3 in
Z/9Z; `/tmp/k9_local_exchange.py` verifies it exactly. A simpler attempted split
of a Walecki cycle partition did not produce this certificate and was abandoned.

Further verified additions in EndpointSelection:
- `walk_hits_boundary`, `path_endpoint_in_pendant_region`, and
  `no_inactive_pendant_region`: a supported vertex region with a single outside
  attachment cannot have no endpoints. These justify the articulation-component
  infeasibility pruning in the auxiliary diagnostic, rather than assuming it.
- `gallai_of_at_most_three_even`: the conjectured bound holds for ALL finite
  graphs with at most three even-degree vertices, without connectivity. The
  main conjecture now has this additional verified branch; the remaining sorry
  has at least four even vertices.

A new auxiliary diagnostic extends the earlier degree-2/4 tests to all 1,782
connected Eulerian graphs on nine vertices (including degrees six and eight).
The initial script `/tmp/endpoint_extension_threshold.py` completed indices
0--1700; log `/tmp/endpoint_extension_eulerian9.log`. The rescheduled script
`/tmp/endpoint_extension_scheduled.py` completed 1701--1730; log
`/tmp/endpoint_extension_eulerian9_tail.log`. It uses finite state budgets only
for scheduling: an exhausted query is UNKNOWN, never falsely declared infeasible.

The delay at index 1731 was explained structurally: this is K7 on
{0,2,4,5,6,7,8} with triangle {1,3,8} attached at 8. The tested A={0,1,3} is
itself infeasible, because the whole pendant region {1,3} has no endpoints.
Adding the necessary articulation-region test avoids that expensive dead search.
A third run starts at index 1731; log `/tmp/endpoint_extension_eulerian9_final.log`.
Its process was 39497 at launch. Check this final log/process for completion;
no failed extension had been found as of this checkpoint. These remain tests
of an auxiliary stronger assertion, not a proof or an original counterexample.

Completion update: `/tmp/endpoint_extension_eulerian9_final.log` ends with
`PASS RANGE 1731 1782`. Together the three logs verify the auxiliary extension
claim on all 1,782 connected Eulerian nine-vertex graphs. There is no live
background diagnostic left (the final process is only a defunct shell child).
No finite-test result has been substituted for a Lean proof.


## Two distinct rooted escapes (verified)

`Submission/DoubleEscape.lean` now compiles without gaps or warnings, and is
integrated under `DoubleEscape` in Work and Spec. The axiom audit uses only the
three permitted axioms. The main conjecture still has its one original sorry.

- `starts_eq_of_iterate_eq`: chains starting outside the image of an injective
  partial successor cannot meet before or at their first exits, unless the
  starting vertices agree. The proof is backward cancellation.
- `reverse_root_tracked`: reverse only the closed root tail. Its subgraph is
  unchanged, so the underlying normal trail system is literally unchanged.
- `realize_escape_orbit`: realize a specified first-exit successor chain using
  pivots, preserving score and every outside member.
- `successor_data`: nonroot penultimate neighbors define an injective partial
  successor, and both neighbors of the closed root tail are outside its image.
- `two_distinct_escapes`: the two root orientations expose different vertices.
- `expose_escape_avoiding`: an escape can avoid any one prescribed vertex.
- `repair_protected_any`: preserve any one outside member as a prefix during
  strict rooted repair; no special root-edge hypotheses are required.

Limitation: this does not give simultaneous avoidance of several vertices.
In the existing shortening construction, one of the two exits can be the new
start of the suffix being protected; choosing that exit can undo the shortening.
Thus the second escape alone does not preserve an arbitrary inactive set, and
no global lower bound on the number of inactive vertices follows yet.

A potential next abstraction is a permutation-indexed path partition for an
Eulerian graph: orient the degree-two endpoint-incidence graph of a normal
partition, and insert nil paths at inactive vertices. This does not strengthen
the proved cardinal bound, but could make exchanges and fixed-point counting
more transparent. No claim that sufficiently many fixed points exist is made.


## Eulerian permutation representation (verified)

`Submission/Permutation.lean` compiles warning-free. Its body is integrated under
`EulerianPermutation` in Work and Spec; `PermutationAudit.lean` reports only the
permitted axioms. It does not assert or assume the conjectural fixed-point bound.

- `regular_relation_matching`: Hall's theorem for a finite positive regular
  bipartite relation, with the cardinal condition proved by double counting.
- `two_regular_relation`: a finite two-regular bipartite relation is the disjoint
  union of two bijections.
- `orient_eulerian_normal`: orient the members of any normal Eulerian partition
  so every active vertex is a start once and a finish once.
- `PermutationPathSystem G`: a permutation sigma of V and simple walks
  `p_v : v -> sigma(v)`, whose edge sets partition G. Nil walks are allowed.
- `permutation_of_normal`: represents any normal Eulerian decomposition in this
  way, with fixed points EXACTLY its inactive vertices, and an exact image formula
  for its nonempty members.
- `exists_permutation_path_system`: every finite Eulerian graph admits such a
  system; it does not need connectivity and has no fixed-point lower bound.
- `nil_iff_fixed`, `parts_good`, `parts_nonempty`, `parts_card_add_fixed`:
  nonempty parts are a good partition, with `parts.card + fixed.card = |V|`.
- `gallai_iff_fixed`: for a fixed such system, the Gallai bound is equivalent to
  `floor(|V|/2) <= fixed.card`.

This makes the Eulerian case a concrete fixed-point optimization problem. The
main unproved assertion is still that a connected Eulerian graph has SOME such
system with enough fixed points. Arbitrary disjoint Eulerian graphs cannot obey
the same bound (two disjoint triangles have six vertices and require four paths),
so any prospective proof of the fixed-point bound must use connectivity.

Potential route requiring new proof: lift a permutation system to the all-leaf
completion, with exactly one leaf per indexed member. The existing rooted pivots
preserve each indexed vertex set; final escape slides move only core edges.
Tracking this invariant could expose the core endpoint permutation effected by
shortening. It would still be necessary to prove a global fixed-point increase,
not just that any one vertex can be fixed at the cost of other fixed vertices.


## Degree-controlled simultaneous protection (verified)

`Submission/ManyEscape.lean` compiles warning-free, and its body is integrated
under `MultipleEscape` in Work and Spec. All audited declarations use only the
three permitted axioms. The original conjecture remains unresolved.

- `closed_trail_first_at_neighbor`: rotate (and, if necessary, reverse) a closed
  trail to start along any of its edges incident to the root. The subgraph is
  unchanged.
- `replace_root_tracked`: replacing the root tail by a same-subgraph trail does
  not change the underlying normal system.
- `many_distinct_escapes`: if the root tail has d distinct neighbors at the root,
  there is a set E of d distinct escape vertices, each individually realizable
  by score-preserving pivots while retaining all outside members. The same
  nonroot successor map is used for every rotation; backward cancellation
  proves that their first exits are distinct.
- `expose_escape_avoiding_finset`: a forbidden set of size less than d can be
  avoided. This is a conditional degree bound, not arbitrary avoidance.
- `escape_slide_tracked`, `finish_exposed_tracked`: the final strict improvement
  changes only one outside member, namely the owner of the chosen escape vertex.
  Every other outside subgraph remains at the same index.
- `repair_protected_family`: an outside family L can all be retained as whole
  subgraphs when `2*L.card < d`.
- `repair_protected_adjacent_ends`: sharper version: only those protected
  endpoints adjacent to the root need to be included in the forbidden set.
  For pendant-leaf members there may be only one such endpoint per member.
- `protected_maximum_root_degree_le`: a score maximum under whole-subgraph
  preservation of L, with all L outside, must have `d <= 2*L.card`.

Limitation: the usual root tail in a one-edge shortening step is a simple cycle,
so d=2. The advanced suffix itself consumes a protected endpoint. Thus even the
sharper theorem does not automatically protect one pre-existing inactive vertex
AND the advanced suffix. A global exchange argument is still needed; no cardinal
bound has been inferred from these conditional local statements.


## One-leaf-per-member lift (verified)

`Submission/LeafPermutation.lean` compiles warning-free and is integrated under
`LeafPermutation` in Work and Spec. `LeafPermutationAudit.lean` is clean.

- `leafWalk` maps a core path into the all-leaf completion and appends the leaf
  edge at its destination. `leafWalk_isPath`, `leafWalk_leaf_support`, and
  `leafWalk_edges` give its exact path, leaf-support, and edge data.
- `leafWalk_project`: projecting the lifted walk returns the original walk exactly.
- `lift_permutation_system`: every permutation-path system lifts to a normal
  system on the all-leaf completion, with k=|V|, one core start and one leaf finish
  per member, exactly one leaf in every support, and exact projected walks.
  Because all its members are paths, its score reaches the universal edge-plus-k
  bound and is therefore a GLOBAL maximum among all normal trail systems.
- `same_owner_iff_fixed`: core v and its own leaf have the same owner exactly
  when the underlying core permutation fixes v.

Possible simplification for future work: explicit one-leaf invariance through
all previous exchanges may not be necessary. Any resulting augmented simple-path
system projects to a normal Eulerian decomposition; orienting its endpoint
incidence graph and re-lifting canonicalizes it to one-leaf-per-member while
preserving the inactive/fixed set. To retain ONE selected oriented nonempty
projected member, the two perfect matchings in the degree-two incidence graph
can be swapped globally if its orientation is wrong. This orientation-prescribed
canonicalization is mathematically plausible but not yet formalized. It does
not provide a fixed-point increase or prove the conjecture.

End-of-continuation status: all four new development files (DoubleEscape,
Permutation, ManyEscape, LeafPermutation) are gap-free and integrated; the main
conjecture still contains exactly one sorry. The import and original statement
are unchanged. No new numerical diagnostic or counterexample search was run,
and no submit_proof call has been made.

## Binary tail counting and pendant-defect transport (verified)

The pending BinaryEscape and DefectTransport developments are now integrated
under those names in Work and Spec. Both compile warning-free; their standalone
and integrated audits use only propext, Classical.choice, and Quot.sound.

BinaryEscape proves:
- `binary_tail_boundary_bound`: if a set S supplies TWO pairwise edge-disjoint
  endpoint-to-root tails per vertex, disjoint from a closed root trail C, and
  every final neighbor and root-trail neighbor lies in S union A, then
  `|S| + degree_C(root) <= |A|`.
- `exists_binary_tail_escape`: the contrapositive supplies a neighbor outside
  S union A. This is a counting escape, not a realized exchange.
- `binary_tail_boundary_add_two`: for a nonempty trail C, the bound implies
  `|S| + 2 <= |A|`.

The missing GLOBAL premise is still whether failed augmentation produces a
large enough closed family of two tails. Connectivity alone does not provide
edge-disjoint tails from all active vertices to one root.

DefectTransport proves:
- `replace_two_finishes_tracked`: the finish-label analogue of the existing
  start-label replacement, with exact indexed and incidence-score tracking.
- `leafWalk_isTrail`, `leafWalk_ncard`, `concat_ncard`.
- `pendant_transfer_data`, `transfer_pendant_defect`: transfer an unused short
  core edge b-c from its leaf-ended member to the member ending at leaf b,
  leaving the singleton leaf edge at b. This purifies b again. The exact loss
  in score is one iff c was already on the preceding core trail, otherwise zero.
- `leafWalk_concat_isPath_iff`: if the preceding core walk p is a path, the
  new lifted walk is a path iff c is NOT already on p.
- `concat_terminal_cycle`: when c is on p, the core walk p+(b-c) consists of
  the simple prefix to c followed by a simple cycle based at c.

IMPORTANT: the augmented walk ends at LEAF c, not core c. Its repetition is
therefore internal in the augmented graph. It is not automatically a rooted
endpoint defect to which the existing rooted repair theorem applies.

Two informal obstructions considered during this development (not counterexamples
to Gallai, and not asserted as Lean theorems):

1. Forcing an arbitrary new fixed vertex can require losing at least TWO old
   fixed vertices when the old set is above the half threshold. On six vertices
   take the union of the edge-disjoint Hamilton paths
     0-2-3-4-5-1,
     0-3-5-2-4-1.
   The normal two-path system has inactive A={2,3,4,5}. Vertices 0,1 have degree
   two and the other four vertices have degree four. If 0 becomes inactive,
   two paths are impossible: every degree-four vertex must be internal in both,
   leaving only vertex 1 to supply endpoints. Thus at least three paths and at
   most three inactive vertices remain. Adding 0 loses at least two old members
   of A. This does not refute below-threshold extension: |A|=4>floor(6/2)=3.

2. Adding an edge between odd vertices need not preserve path number, even in a
   connected non-path graph. Take the two Hamilton paths
     0-4-2-5-3-1,
     0-5-1-4-3-2.
   Their ten-edge union H has odd vertices 1 and 2. Adding edge 12 produces
   eleven edges on six vertices, requiring at least three paths by edge capacity.
   This G is K6 minus {01,02,03,45}; three is exactly Gallai's bound.

## Closed-cycle relocation: exact additional cost (verified)

`CycleRelocation.lean` is integrated under `CycleRelocation` in Work and Spec.
It and its audit compile cleanly with only allowed axioms.

- `relocate_cycle_data`: moving a closed segment C from r.append C to a trail q
  preserves the two-member edge partition and produces trails r and C.append q.
- `relocate_cycle_ncard`: the change in total distinct-vertex incidences is
  EXACTLY `|verts(r) inter verts(C)| - |verts(C) inter verts(q)|`, expressed
  without truncated subtraction.
- `path_split_verts_inter`, `terminal_cycle_prefix_inter`: the prefix and
  terminal cycle extracted from p+(b-c), with p simple and c on p, intersect
  only at c.
- `terminal_cycle_relocation_ncard`: in the leaf lift, the new two-member score
  plus `|verts(C) inter verts(q)|` equals the old two-member score plus one.
- `terminal_cycle_relocation_strict_loss`: any additional common vertex x!=c
  causes a strict loss for this relocation.

Thus moving an INTERNAL pendant defect to its core endpoint owner can create
additional incidence deficits. It cannot be treated as a score-preserving
endpoint exposure without proving the necessary overlap condition.

An informal concrete obstruction to an arbitrary same-score TWO-MEMBER root
exposure: let r=a-c, let C=c-x-y-c, and let q=c-z-x-d, on six distinct vertices.
The original two augmented trails are leafWalk(r.append C) and leafWalk(q).
Only c is repeated in the first. In their union, any simple path from a to
leaf c is forced to be a-c-leaf c, since a and leaf c are pendant at c.
The other trail must then carry C and q and repeats x as well as c. Hence
moving the unique deficit to an endpoint at core c while making the a-to-leaf-c
member simple cannot preserve the two-member incidence score. This does not
rule out exchanges using additional members of the full normal system.

Current checkpoint: Work and all new developments are gap-free. Spec still has
exactly ONE sorry in the original general theorem. The import and conjecture
statement are unchanged. No original-conjecture counterexample has been found,
no numerical diagnostic was run in this continuation, and no submit_proof call
has been made. The main missing step is still global inactive-set augmentation,
not the local edge/count identities established here.


## Singleton-token rotations (verified)

The 576-line SingletonRotation.lean development has been integrated into Work
and Spec under namespace SingletonRotation. Its standalone and integrated axiom
audits use only propext, Classical.choice and Quot.sound.

- escape_slide_receiver / finish_exposed_receiver track the exact exceptional
  receiver: it gains just the exposed root edge.
- shorten_oriented_one_exception preserves the entire suffix at its index when
  the discarded start is nonadjacent to the far endpoint. Among old members
  avoiding the discarded vertex, only one other indexed subgraph may change.
- purify_short_core_member turns a core b-a-leaf(a) member into leaf(a), preserving
  all other old leaf singletons except possibly one. If the exception was leaf(z),
  it becomes exactly b-z-leaf(z), for an actual edge b-z.
- singleton_neighbor_exchange: at a global purification maximum A, this gives
  precisely A -> (A-z)+a and a new short core edge b-z with z in old A.
- rooted_singleton_rotation additionally orients the new member from b and
  proves the new system still globally maximal, so the move can be repeated.
- singleton_augmentation_of_no_purified_neighbor: if b has no neighbor in old A,
  the local move strictly increases the purified set.

These lemmas use the all-leaf completion, hence their application is currently
Eulerian. They do not prove general augmentation or Gallai. For a fixed root b,
repeated rotations preserve A union {a} and can cycle. A global counting/closure
argument is still missing. Two-ended rotation would need a separate canonical
orientation of the projected core paths; merely reversing an augmented member
is not sufficient.

Exact auxiliary diagnostics from the singleton continuation (not Lean proofs
and not counterexamples to the original conjecture):
- Edge xy can be covered by a <=ceil(n/2) partition whose xy-member avoids v when
  v is nonadjacent to x and y: PASS all connected atlas graphs through 7 (995
  graphs, 10879 eligible triples) and all connected 8-vertex graphs (11117 graphs,
  223895 triples). /tmp/edge_avoidance{,8}.log.
- On all 224 connected all-odd 8-vertex graphs: prescribed first edge x-y with
  path avoiding v, for v nonadjacent to x only: PASS 10910 cases.
  /tmp/edge_one_sided_avoidance8.log.
- Stronger all-odd claim that a prescribed first edge x-y admits a path entirely
  in closed N[x]: PASS both orientations of all edges of those 224 graphs,
  6562 cases. /tmp/edge_neighborhood_full8.log. A preliminary weaker version
  also passed the 19 connected cubic graphs on 10 vertices.
These are unproved local assertions, not assumptions used in the formal file.

After integration Spec still has exactly one original-conjecture sorry.


## Canonical two-ended token exchanges and a cycle obstruction (verified)

CanonicalRotation.lean (427 lines) and TokenObstruction.lean (110 lines) have been
integrated into Work and Spec. Both standalone audits and IntegratedAudit pass
with only the three allowed axioms.

CanonicalRotation establishes the exact missing core bridge:
- projection_mem_iff: every nonempty projected indexed member belongs to the
  tracked core partition, and these are the only ones that do.
- own_leaf_purified: in an all-leaf normal PATH system, the core and leaf owners
  coincide iff their singleton pendant member exists.
- inactive_projection_eq_purified / project_normal_exact: the projected
  partition's inactive set equals the purified set POINTWISE.
- core_leaf_path_eq, lift_permutation_exact: reconstruct and track the entire
  lifted member, not just its projection or endpoint labels.
- reversed / reversed_fixed / reversed_parts: reverse the core permutation,
  preserving its fixed set and its path partition.
- permutation_of_normal_oriented / lift_normal_oriented: any prescribed
  singleton core edge can be oriented in either direction before leaf lifting.
- normal_single_edge_exchange: in a globally maximal normal Eulerian core
  partition containing singleton ab, there is another globally maximal normal
  partition with inactive set (A-z)+b and singleton az, where z was inactive
  and is adjacent to a. Apply at either endpoint. This is now a genuine
  TWO-ENDED rotation of an actual core decomposition.

TokenObstruction packages all maximal normal partitions with the same token
pool C=A union {a,b}. Its token graph has no dead ends: every directed edge
extends to another edge without immediately backtracking. Thus it has a cycle.
The verified singleton_token_cycle_obstruction states:
  if D is maximal normal and contains singleton ab in an Eulerian G,
  then G induced on A union {a,b} is NOT acyclic.
This is a structural obstruction, NOT a proof of the desired cardinal bound.
The existence of a cycle in this pool does not imply global augmentation.

### False stronger token assertion: arbitrary neighbors cannot be selected

The exact diagnostic /tmp/token_neighbor_test.py fails already on 7 vertices.
Graph edges:
  01,04,05,06,12,15,16,23,25,26,34,56.
A minimal normal (indeed minimal unrestricted) 3-path partition is:
  0-1,
  0-5-1-6-2-3,
  1-2-5-6-0-4-3.
Its inactive set is {2,4,5,6}. Rotating 01 at root 0 can select 5 or 6, but
CANNOT select 4 with exact inactive swap to {1,2,5,6}.
Analytic obstruction: then active vertices would be {0,3,4}. Vertex 4 has degree
2 and both incidences must be path ends; with token 04, its other edge 43 must
also be a whole path because 3 also has degree 2 and endpoint multiplicity 2.
The remaining ten edges cannot form the one remaining simple path on 7 vertices.
Minimality of the initial partition: a two-path normal partition would have
exactly two active vertices, both of degree <=2, hence 3 and 4. Then edge 34
would be singleton and the other 11 edges cannot form one path. No vertex can
have four endpoints in a two-path decomposition with nonzero degree, so the
same argument excludes an unrestricted two-path partition.
This is NOT a Gallai counterexample: 3 <= ceil(7/2)=4.
Log: /tmp/token_neighbor_atlas.log. Do not infer arbitrary-neighbor closure
from the existential rotation theorem.


## Indexed vertex preservation and a protected triangle-free edge (verified local results)

VertexTracking.lean (610 lines) and ProtectedEdge.lean (351 lines) are now
integrated in Work and Spec, under those namespace names. Standalone audits
pass with only allowed axioms.

VertexTracking exposes information previously proved only inside rebuild:
- SameVertices / sameVertices_trans.
- rebuild_vertices, pivot_vertices, expose_escape_vertices: ALL indexed
  vertex sets are preserved, alongside the old outside-member tracking.
- orient_root_start_vertices, escape_slide_vertices, finish_exposed_vertices.
- repair_active_vertices: a rooted repair gains exactly one incidence. There
  is one exceptional OUTSIDE member; all other indexed vertex sets are
  preserved, and all other outside whole subgraphs are preserved.
- chordless_three_verts_determine: a nonempty walk with exactly the vertices
  of an induced two-edge path has exactly that subgraph.
- repair_chordless_three_path: consequently a chordless a-root-b member that
  passes INTERNALLY through the defect root can be preserved as a WHOLE member
  during repair. It need not be outside the root's active set.

ProtectedEdge proves:
- trail_isPath_of_subgraph_eq: any trail with the same subgraph as a path is
  itself a path, via exact edge-length and vertex-incidence counts.
- repair_avoiding_single_edge: two exits suffice to preserve an outside
  singleton uv if the defect root is not adjacent to BOTH u and v.
- improve_repeated_start_protect_edge, protected_no_repeated_start: at a score
  maximum subject to keeping a triangle-free edge uv singleton at its index,
  no member (even an alternative traversal) repeats its starting endpoint.
- shorten_oriented_no_return: the earlier controlled-shortening lemma needs
  only that the discarded start is absent from the suffix, NOT full global
  score maximality. Nonadjacency to the far endpoint still preserves the
  entire suffix at its original index, at exactly equal score.
- strip_chordless_two_edge: a chordless a-u-v whole member can be replaced by
  the singleton uv at exactly the same score, without any maximality premise.
- protected_no_closed_after_first_marked: with uv singleton at l, oriented
  start u and finish v, at a protected score maximum no other member can have
  the form a-u followed immediately by a NONEMPTY closed u-segment and then
  a suffix. Proof: move a-u temporarily onto uv, creating the chordless
  a-u-v buffer; repair the new endpoint defect at u while preserving this
  INTERNAL buffer; strip the buffer at no score loss; contradict maximality.

IMPORTANT limits:
These results DO NOT prove that an arbitrary triangle-free edge in an all-odd
simple graph can be made singleton, and DO NOT prove full protected
normalization. The marked-endpoint closed-segment lemma handles only a
repetition immediately after the first edge of the other member.
A naive attempt to peel a longer prefix has to preserve both the marked edge
and the suffix start. A degree-two root supplies only two exits, and one may
hit the marked edge while the other returns the discarded first edge to the
suffix. The buffer can be stripped without score loss but may undo that
shortening, so no strict prefix decrease is established. Do not silently use
it as such a decrease.

Additional exact auxiliary diagnostic:
- nauty-geng -ct -d3 10 generated 209 connected triangle-free minimum-degree-3
  graphs; 19 have all degrees odd. The previously proposed closed-neighborhood
  first-edge assertion passes both orientations of all their edges: 658 cases.
  /tmp/trianglefree_odd10.g6 and /tmp/edge_neighborhood_trianglefree10.log.
  In triangle-free graphs this assertion would force the chosen edge singleton.
  The diagnostic is finite evidence only; the assertion remains UNPROVED.

Current state: the original import and conjecture statement are unchanged.
Spec still has exactly ONE sorry, in the original general theorem. All new
helpers are gap-free. No original-conjecture counterexample and no submission.
The global inactive-cardinality augmentation remains the main unresolved step.

## Induced buffers and local-leaf compression (verified)

InducedBuffer.lean (255 lines) and LocalLeaf.lean (about 265 lines) are integrated
under InducedBuffer and LocalLeaf in Work and Spec. Both developments compile
warning-free. LocalLeafAudit and the enlarged IntegratedAudit report only the
three permitted axioms. Spec builds with its one original-theorem sorry.

InducedBuffer proves:
- subgraph_coe_edge_card and path_vertex_ncard.
- induced_path_verts_determine: a walk spanning precisely the vertices of an
  induced path has the same subgraph (by connected edge count and inclusion).
- repair_induced_path: an active induced-path member survives rooted repair
  as a whole subgraph, using indexed vertex preservation.
- induced_tail, induced_nontrivial_tail_not_adj_ends.
- shorten_path_member_nonadj: a path member with nonadjacent endpoints can be
  shortened by one edge at exactly equal score, without maximality assumptions.
- strip_induced_prefix: strip any prefix of an induced path member while
  retaining a nonempty suffix and the total score.
- move_stem_to_singleton: transfer a path stem A onto a singleton uv, leaving
  the old suffix at its index. If A+uv is a path, score cannot decrease.
- protected_no_closed_after_induced_stem: at a score maximum preserving uv as
  a singleton, a closed u-segment cannot lie behind an induced A+uv buffer.

LocalLeaf proves:
- exists_lex_optimum: maximize incidence score subject to a predicate, then
  minimize any natural-valued secondary measure.
- local_leaf_neighborSet, local_leaf_endpoint: a vertex v with just one allowed
  neighbor u in the member's ambient set S has degree one in a nonempty member;
  trail parity makes v an endpoint.
- orient_finish and shorten_trail_member_no_return.
- constrained_no_repeated_start: at a score maximum among systems preserving
  one member's vertex set, that member cannot repeat its starting vertex.
- compress_local_leaf: if member l lies in S and contains v, and v has just
  the allowed neighbor u within S, it can be replaced by singleton uv at l
  without DECREASING total score. No assumption that the original member is a
  path, or that S is induced/chordless, is required.
  Proof: maximize score under the vertex-set inclusion and v-membership
  invariant; minimize l's vertex cardinality. Orient its degree-one endpoint
  v last. A nonempty proper suffix still contains v and u. The original start
  does not reappear, so it differs from u and is nonadjacent to v. The exact
  no-return shortening lemma preserves the suffix and score, contradicting
  minimality. Therefore the member is singleton uv.
- protected_no_closed_after_local_leaf_stem: the induced-buffer hypothesis in
  the preceding protected-stem theorem can be replaced by the local-leaf
  condition at the far marked endpoint. Transfer the stem, repair preserving
  its vertex set, and compress the possibly changed buffer.

Limitations: the buffer A+uv still must initially be a path, and the new local
condition fails if the stem meets another neighbor of v. No arbitrary protected
normalization, simultaneous purification theorem, or inactive cardinality bound
has been inferred. No original counterexample or settlement has been obtained.

Current main question remains global: can the maximum-purification exchange
system yield a closed two-tail family large enough for BinaryEscape, or another
injection/augmentation argument proving floor(even/2) inactive vertices? A root
repair alone and a token cycle alone do not establish that closure.

## Exact energy transport and a shortest-member obstruction (verified)

EnergyTransport.lean (353 lines) and EnergyPurification.lean (227 lines) are
integrated under EnergyTransport and EnergyPurification. Work is gap-free;
Spec is 15200 lines with its sole original-theorem sorry at 15198. Standalone
and integrated axiom audits are clean.

EnergyTransport strengthens shortening considerably:
- escape_slide_receiver_vertices and finish_exposed_receiver_vertices combine
  exact receiver-subgraph tracking with all-other-indexed-vertex preservation.
- shorten_oriented_vertex_transfer: remove the first edge from member i, with
  no repeated start and nonadjacent ends. At the same total score, i retains
  its suffix, one DISTINCT receiver r not previously containing the discarded
  start gains exactly a first edge, and EVERY OTHER indexed vertex set stays
  unchanged. This is stronger than preserving only outside whole subgraphs.
- vertexEnergy is sum of squares of indexed vertex cardinalities.
- vertexEnergy_transfer / shorten_oriented_energy give the exact identity
      E(U) + 2*|V(T_i)| = E(T) + 2*|V(T_r)| + 2.
- energy_maximum_recipient_smaller: at an energy maximum within a score level,
  the recipient is strictly smaller than the donor.
- vertexEnergy_le, exists_score_energy_maximum.

EnergyPurification:
- leafPart_isInduced, leafPart_vertex_rigid, leafPart_vertex_ncard.
- purified_subset_of_vertex_transfer: if both donor and receiver originally
  have at least three vertices, all old purified vertices survive the move.
- member_two_verts_leafPart: a member with at most two vertices and a pendant
  leaf is exactly that leaf's singleton edge.
- shortest_member_recipient_two_verts: maximize purification, then energy.
  Shortening a smallest >=3-vertex member can only use a <=2-vertex recipient.
- LeafCovered: every indexed member carries a pendant leaf.
- leafCovered_transfer: shortening at a CORE vertex preserves this property.
- shortest_member_purified_recipient: more directly, maximize energy among
  leaf-covered path systems preserving the old purified set. A smallest
  non-singleton donor's receiver is an old leaf singleton at some z in A,
  and the discarded core start a is adjacent to z.
- exists_constrained_energy_maximum proves the last optimization exists.
- exists_smallest_nonsingleton_member.

These are LOCAL optimality obstructions, not a Gallai bound. In particular,
DO NOT infer a root-degree/cardinality bound by counting all rooted tails:
only successor chains reached from the closed root tail are currently
realizable escapes. Other leaf-started chains can lie in separate components.
A bouquet of triangles illustrates why this missing reachability matters.

## New auxiliary matching idea — unproved, exact evidence only

Candidate: in an Eulerian simple graph, if I can be matched injectively along
actual graph EDGES into V\\I, then there is a normal path partition with every
vertex of I inactive. Equivalently, every matchable I is feasible. This would
in particular prove the Eulerian Gallai bound whenever G has a near-perfect
matching. No proof of this candidate has been found; it is not assumed in Lean.

Targeted exact diagnostics:
- /tmp/alternating_inactive.py: if P is a Hamilton path, taking a smaller
  alternating vertex class of P as I passed all Eulerian atlas graphs (51
  graphs, 607 sets) and all 184 Eulerian connected 8-vertex graphs (5832 sets).
- /tmp/two_matching_inactive.py: a stronger certificate (bipartite capacity-2
  matching saturating I twice, complement capacity two) passed 12573 sets in
  all 184 Eulerian connected 8-vertex graphs.
- /tmp/matching_inactive.py: ordinary bipartite matching saturating I passed
  22916 sets in the same 184 graphs.
- All 1782 connected Eulerian 9-vertex graphs also pass. The first run passed
  the first 1500 (329082 eligible sets), then the shell timeout killed it.
  The resumed last 282 passed 67795 eligible sets. Logs:
    /tmp/matching_inactive9.log
    /tmp/matching_inactive9_tail.log
  Their union covers all 1782 rows, with a possible small overlap after row1500.
- A new diagnostic is running on /tmp/even24_10.g6 (1254 Eulerian degree-2/4
  graphs on ten vertices), logging to /tmp/matching_inactive10.log.

A different, overly strong assertion is FALSE: even in a biconnected Eulerian
G, arbitrary I of size <=floor(n/2) need not be feasible. On six vertices:
  edges 01,02,04,05,12,23,25,34; I={0,1,5}.
Active vertices would be {2,3,4}. Degree-two active vertices 3 and4 force 34
as a singleton, while degree-four active vertex2 must lie in all three paths.
Contradiction. Subdividing edge34 twice gives an 8-vertex biconnected Eulerian
example with the SAME infeasible 3-set I, now strictly below half. The active
chain gives three singleton edges, leaving too few paths through vertex2.
I is NOT matchable into its complement (1 and5 both only neighbor2 there).
Diagnostic: /tmp/inactive_twoconnected.py.

Possible mathematical route to the matching candidate: remove the matching
M from Eulerian G and attach leaves to unmatched vertices. This is all-odd.
A normal path system can be extended along M at the selected I endpoints;
its only defects are repetitions of their matched partners. One needs a
normalization preserving endpoint multiplicity zero on I and two on the
complement. Standard rooted repair does not yet do this. Missing endpoint
vertices might be handled through their distinct matched partners using an
alternating-fan construction, but neither the construction nor its monotone
potential has been established. Do not claim it follows from single-edge
prescription or from the current energy lemma.

Matching diagnostic update: all 1254 graphs in /tmp/even24_10.g6 PASS, with
567769 eligible matchable inactive sets, in 192 seconds. No diagnostic process
from that run remains. This is still finite evidence only.

A STRONGER matching assertion is now being considered, not proved: given a
specific matching from I to its complement B, one can realize I as inactive
AND make each matched edge a-b terminal at its B endpoint b. Exact script
/tmp/matched_terminal_inactive.py passed all Eulerian atlas graphs (51 graphs,
12696 choices of I and matching). A separate dense 8-vertex test on K8 minus
a perfect matching is running, logging /tmp/matched_terminal_dense8.log.

Important setup for the matching approach:
- Delete the selected matching M from Eulerian G, and attach a leaf at every
  unmatched vertex. The resulting graph H is all-odd.
- An H normal path system projects after leaf removal to paths of G-M.
- Append M at each selected I endpoint. There are exactly |B| indexed trails,
  with two endpoint slots per b in B and none at I; nil trails are allowed.
  Every M edge is terminal at its B endpoint. Each member is a simple base
  path with at most two appended matching edges, so its only possible defects
  are repetitions of matched B partners. This construction is mathematical
  only so far, not yet a Lean helper.
- The missing theorem is normalization of these terminal-defect trails while
  retaining the endpoint budget. Simply generalizing the normal all-odd
  endpoint bijection is not enough: vertices in I have NO endpoint slots.
- If a root escape x-a reaches inactive a matched to b, and the b-ending
  receiver starts with b-a, a two-member switch can move the defect to b with
  no score loss (strict gain if b was absent from the donor). However keeping
  every other prescribed matching edge terminal during such a switch is NOT
  yet proved. The donor root's marked edge can become internal. A dynamically
  changed matching / alternating fan may be needed.

Analytic special-case observation (not formalized): if all B vertices have
exactly degree two, matching-inactive can be approached by cutting off B into
boundary ports. G[I] then has positive endpoint quotas equal to its numbers
of boundary edges. Positive quotas can be realized using the already proved
all-odd pendant construction, adding nil pieces for unused endpoint pairs.
The boundary-port pairing can avoid closed B-to-B pieces: a bad piece whose
both ports belong to the same B can have one port swapped with another piece
at either of its I endpoints. Since the two ports of that B were previously
on the bad piece, this creates no new bad piece. The sole obstruction is both
I endpoints having only one port, i.e. an isolated single edge in the port
multigraph; the matching-saturation hypothesis excludes that obstruction.
This does NOT normalize repeated B vertices when deg(B)>2, and has NOT been
used as a general proof.

Potential next target is the Hall-style sufficient statement itself:
  if I is infeasible in an Eulerian G, then I cannot be matched into V\\I.
It is enough to work with a minimal infeasible I, but no construction of the
necessary deficient neighbor set has been found. Even proving this statement
would not automatically settle arbitrary connected Eulerian graphs without a
near-perfect matching; a further matching-deficiency/block argument would be
needed, and the non-Eulerian case would still require its own reduction.

PORT PAIRING, POSITIVE QUOTAS, DEGREE-TWO BOUNDARY (completed)

Three new development files are compiled, audited, and integrated into Work/Spec:
- PortPairing.lean: common pairs of fixed-point-free involutions can be
  eliminated by label-preserving port swaps, provided each fixed pair has
  distinct labels and at least one label has another port. An incident
  matching from labels to boundary owners supplies this room condition.
- EndpointQuota.lean: PieceFamily allows indexed nil path pieces. Any positive
  endpoint quotas having the same parity as the degrees can be realized.
  Consequently endpoints can be assigned bijectively to prescribed labelled
  ports with positive parity-compatible label-fiber sizes. Also provides
  PieceFamily.parts_good and parts_card_le.
- DegreeTwoBoundary.lean: pairedExtension H label adds independent boundary B
  with two distinct labelled core neighbors per b. separate_endpoint_assignment
  reassigns path endpoints by same-label switches so no core piece has both
  boundary ports at the same b. lift_piece_family proves paths, disjointness,
  cover, boundary endpoints, and indexed cardinality |B|. The final theorem
  pairedExtension_path_partition yields <=|B| paths under quota parity and an
  injective incident matching A -> B. This confirms the matching criterion in
  this independent degree-two-boundary model, not for higher boundary degrees.
  The count meets the original Gallai bound when |A|=|B|; when |B|>|A| it need
  not. Do not claim this special case settles the original conjecture.

BoundaryAudit.lean and IntegratedAudit.lean show only the three permitted
axioms for all these helpers. Original erdos_583 still has its sole sorry.
The strong terminal-matching dense eight-vertex diagnostic also finished:
K8 minus a perfect matching, 3760 cases, PASS in 223 seconds. No diagnostic
process remains running from the matching tests.

MATCHING DELETION REVISITED

Important existing global reduction (not emphasized in the recent checkpoint):
`erdos_583_of_odd_matching_deletion` already reduces the ENTIRE conjecture to
connected H-F with H all-odd and F a matching, via the doubled-graph/one-bridge
construction. Thus simultaneous terminality for F in an H normal path system,
assuming H-F connected, would suffice for the original conjecture. It remains
unproved. The weaker sufficient trimming target is total internal F edges <=
total F-only singleton paths, not necessarily terminality of every F edge.

The connectivity hypothesis CANNOT be dropped from terminal matching. Exact
auxiliary diagnostic /tmp/terminal_matching_unrestricted.py found:
  H edges 03,05,06,14,16,17,24,26,27,35,37,45,46,47,67;
  F={06,37,45}.
H is all-odd, but H-F is the disjoint union of triangle {0,3,5} and K5 minus
one edge on {1,2,4,6,7}. Those components require >=2 and >=3 paths, respectively,
so H cannot have four paths all of whose F edges are terminal. This is not an
original-conjecture counterexample: the deletion graph is disconnected. The
previous 28981-case connected-deletion diagnostic is unaffected.

The stronger claim prescribing WHICH endpoint makes every F edge terminal is
FALSE even when H-F is connected. /tmp/terminal_matching_oriented.py found:
  H edges 05,06,07,15,16,17,27,37,47,57,67;
  F={05,16}, prescribe terminality at 5 and 1 respectively.
G=H-F consists of triangles 0-6-7 and 1-5-7 and leaves 2,3,4 at 7.
Both 1 and5 would be inactive after trimming, which is impossible for the
pendant triangle 1-5-7: a simple path containing edge15 cannot leave the triangle
at both ends through7. Thus choosing the terminal orientations is essential.
The unrestricted connected terminal-matching candidate is not disproved.
Both new diagnostics have finished; there are no ongoing processes.

Potential broader defect framework (not formalized yet): a k-path partition
with a singleton edge gives, after absorbing that edge into another path, a
(k-1)-trail partition with total path-score deficit one. There is just one
repeated vertex, at an endpoint of its member. Allowing endpoint multiplicity
four at the defect root permits moving the defect even to previously active
vertices; do not impose normal endpoint bounds during this search. With fixed
baseline quotas c_v (subtract two endpoints at the current root), each local
move preserves c_v, every indexed vertex set, and the deficit one. For Eulerian
normal starting data with inactive I and singleton ab, baseline c_v=0 on
C=I union {a,b}, and c_v=2 outside C. The defect root need not remain in C.

Elementary local move: defective P=(r-x).append p, where p is a path containing
r; another path Q starts at r and contains x. Remove first edge r-x from P,
prepend x-r to Q. Both indexed vertex sets stay fixed, P becomes a path and Q
has its unique repetition at x. Root moves r->x; endpoint counts lose two at
r and gain two at x. If Q avoids x instead, this immediately gives two paths
and repairs the only defect. Root degree four supplies additional receiver
choices. This differs from the old normal endpoint-bijection slide, which
swaps two DIFFERENT starting vertices and preserves endpoint counts.

Caveat: the defective member may be a closed simple cycle. Then both root
endpoints belong to that same member, so there may be no other root-ending
receiver. Such a cycle can be rotated to any of its vertices, changing the
root. Internal intersections with other paths are the remaining nontrivial
case: a path plus an intersecting cycle need not admit a two-path partition.
This framework has not supplied the missing global reachable-family bound.

MOBILE DEFECT LOCAL DATA (new verified development, not yet integrated)
`MobileDefect.lean` proves same_root_transfer_data, move_single_defect,
endpoint_quota_transfer, and single_defect_score. All compile without gaps.
These are local edge/vertex/endpoint identities, not a global defect-normalization
claim. No root-reachability cardinality theorem is established.

A possible cycle/path shortcut was checked and rejected before formalization.
It is FALSE that a cycle plus an intersecting simple path always decomposes
into two paths merely because some cycle vertex is absent from the path.
Exact counterexample: cycle C=(0,1,2,3,4,5,6,7,8,0), path
  P=(9,0,4,11,5,8,12,7,1,13,3,6,10).
The two are edge-disjoint; cycle vertex2 is absent from P. Exact enumeration
finds no two-path partition. There are 24 path-plus-cycle partitions, whose
cycle sizes are 9,10,11, so minimizing the cycle size does not fix the shortcut.
This is only an auxiliary lemma obstruction, not a Gallai counterexample:
there are 14 vertices and Gallai permits seven paths.
The tests /tmp/cycle_path_missing_vertex.py (12334 reduced cases) and
/tmp/cycle_path_general.py (185312 cases through cycle length8) had passed;
the cycle-length9 example was obtained by subdividing a cycle edge in the
obstruction found by /tmp/cycle_path_degree_two.py. Thus those finite passes
must not be treated as evidence of a proved general conversion lemma.
All of these diagnostics have finished.

MobileDefect.lean is now integrated and audited (contrary to the earlier
"not yet integrated" note above). Work has 15861 lines, Spec 15923 lines at
this checkpoint; the original theorem is still unresolved with one sorry.

Further limitation of purely vertex-preserving mobile-defect moves: they
cannot suffice globally. A closed-cycle member whose entire vertex set has
baseline endpoint quota zero must remain the closed defective member if every
indexed vertex set is held fixed; it cannot become a path with allowed ends.
For example take a triangle on c0,c1,c2 and four vertices s0..s3, each adjacent
to c0,c1. Partition its bipartite edges into the four two-edge paths
  s0-c0-s1, s1-c1-s2, s2-c0-s3, s3-c1-s0,
and retain the triangle as the closed member. Baseline quota is two on each
s and zero on each c. This one-defect system has five members on seven vertices,
but no repair preserving all five indexed vertex sets can turn the triangle
member into a path with the baseline-plus-root quota. Vertex-set-changing
exchanges are essential; in this particular graph a cycle/path exchange at a
single intersection immediately repairs the system. This does not refute any
unrestricted path-decomposition statement.

QUANTITATIVE MATCHING TRIMMING (completed, integrated, audited)

MatchingTrim.lean now proves:
- spanningCoe_acyclic_of_coe, path_spanningCoe_isAcyclic.
- restrict_path_partition: a path restricted to any spanning subgraph has a
  path partition with exact cardinality half the number of odd vertices of
  the resulting forest.
- terminalVertices K F: vertices of path subgraph K having local K-degree one
  and local (K intersect F)-degree one. This counts incidences, so an F-only
  singleton path contributes TWO, a terminal F edge contributes ONE, and an
  internal F edge contributes ZERO.
- trim_odd_card: exact parity sum for deleting a matching from one nonempty path.
- trim_path_partition: exact local count
    surviving_pieces.card + terminalVertices.card = 1 + |E(path) intersect E(F)|.
- terminalWeight D F: sum of these incidence counts over the path family D.
- trim_decomposition: for any nonempty-member good D of H, F<=H a matching,
  constructs good E of H-F with
    E.card + terminalWeight D F <= D.card + |E(F)|.
- trim_decomposition_of_terminal_weight: if terminalWeight >= |E(F)|, trimming
  does not increase path count. Thus simultaneous terminality is not necessary;
  internal F edges can be compensated by whole F-only singleton members.
- terminalWeight_le_twice_card.
- exists_terminal_weight_maximum: in an all-odd H, an n/2-path decomposition
  maximizing terminalWeight exists. NO sufficient lower bound is proved.
- gallai_of_matching_terminal_weight: the ENTIRE original conjecture follows
  if, whenever H is all-odd and H-F connected for a matching F, one can select
  an n/2-path decomposition of H with terminalWeight >= |E(F)|. This is a
  conditional reduction only. Its selection hypothesis remains open here.

MatchingTrimAudit and IntegratedAudit report only the three permitted axioms.
The original conjecture in Spec still has its one sorry.

Additional terminal matching diagnostic: all 19 connected cubic graphs on ten
vertices, all 5992 matchings whose deletion remains connected, PASS. Log
/tmp/terminal_matching_cubic10.log. No diagnostic is currently running.

Lean notes from this development:
- Finset.sum_coe_sort sometimes needs explicit s and f to match sums over s.
- Degree expressions from different Fintype neighbor instances may not be
  definitionally equal. Normalize using
    simp only [←card_neighborSet_eq_degree, ←Nat.card_eq_fintype_card]
  before rewriting graph equalities.
- Likewise normalize edgeFinset.card via coe_edgeFinset / Set.ncard_coe_finset;
  use conv_rhs when another Finset.card occurs earlier in the expression.

A new UNPROVED idea (not assumed in Lean) was checked only as a diagnostic:
for a fixed matching M in all-odd H, do the subsets of M that can all be made
terminal in some normal H path partition form a matroid? Script
/tmp/terminal_matching_matroid.py tested all 224 all-odd connected graphs on
eight vertices, 32562 matching subsets, and found no exchange-axiom failure.
However exactly ONE subset was infeasible (the previously recorded triangle
plus K5-minus-edge deletion), so this evidence is almost entirely vacuous and
must not be overinterpreted. It does not prove either a matroid assertion or
the connected terminal-weight bound. No test process remains running.

TRIANGLE-FREE MATCHING REDUCTION (new verified development)

The existing doubled-graph reduction's vertical edges have NO common neighbor
at their two ends: horizontal edges stay in their layer, and vertical edges
only join corresponding vertices. TriangleFreeMatching.lean formalizes this
and sharpens the full Gallai reductions accordingly. The matching-deletion
bound, or the terminalWeight >= |F| selection bound, is only required when all
marked matching edges are triangle-free in the original all-odd graph. The
selection bound is still NOT proved. Standalone audit uses only allowed axioms.
The helpers are integrated in Work and Spec as namespace TriangleFreeMatching.

Fixed prescribed terminal orientations remain impossible even in this subclass:
take two triangles joined by all three vertical edges (the triangular prism),
and mark two vertical edges. Deleting them leaves the two triangles joined by
one bridge. Prescribing both marked edges terminal at vertices in the same
copy makes those two vertices inactive after trimming; the pendant triangle
then has no endpoint off its sole attachment. Thus orientation exchange is
essential even for the special doubled construction.

The auxiliary singleton triangle-free-edge diagnostic /tmp/singleton_trianglefree.py
passed all 580 such edges in all-odd graphs on eight vertices. This duplicates
some earlier finite evidence and does not establish protected normalization.

TERMINAL-SUBSET MATROID SHORTCUT IS FALSE (structural derivation; not Lean-formalized)

The previous eight-vertex diagnostic was too small. A general encoding shows
that terminalizable subsets of a FIXED matching need not form a matroid,
even when all marked edges are triangle-free and the original all-odd graph
is connected. This is NOT a Gallai counterexample and NOT an obstruction to
the connected-deletion terminal-weight hypothesis.

Take the connected Eulerian theta graph G on {0,...,5} with edges
  01,02,04,05,12,23,25,34.
Build H on 24 vertices: retain G; for each i add a triangle (a_i,b_i,c_i),
the bridge-to-core edge i-a_i, and the ring edge b_i-c_(i+1 mod6).
Every vertex of H has odd degree. All the twelve external edges constitute
a perfect matching M, and each is triangle-free in H. Let A be the six ring
edges. For a subset I of core vertices, write B_I={i-a_i : i in I}.

Claim: A union B_I can all be terminal in a normal H path partition iff I is
contained in a feasible inactive set of a normal G path partition.

Necessity: in each added triangle at most ONE external incidence can be
terminal. If two vertices x,y had their external darts terminal, the two
triangle darts at each x,y would have to be paired in a single path. The edge
xy then forces all three triangle edges into that path, impossible for a
simple path. Terminality of all six A edges consumes at least six incidences
among the six triangles, hence exactly one in each. No i-a_i edge can be
terminal at a_i. If it is terminal, it must be terminal at core i. Restrict
all paths to G and split into path pieces: the local endpoint multiplicity
at core i is zero when i-a_i is terminal at i, and two otherwise. Therefore
this is a normal G partition with every i in I inactive.

Sufficiency: orient a normal Eulerian G partition so each active core vertex
is one start and one finish; add a nil arm at each inactive vertex. There are
six indexed arms, with starts and finishes each bijective onto the core.
For an arm ending at i append i-a_i-c_i. Add the six three-edge paths
  b_i-c_(i+1)-b_(i+1)-a_(i+1).
These twelve simple paths partition H and have one endpoint at every vertex.
All ring edges are terminal; i-a_i is terminal at i precisely for nil arms.

For X_core={1,5}, a normal G partition is
  4-0-1-2-3; 0-5-2; 0-2; 3-4.
For Y_core={0,1,2}, one is
  5-0-1-2-3; 5-2-0-4; 3-4.
But neither {0,1,5} nor {1,2,5} can be inactive: the three 0-to-2 routes
02, 0-1-2, 0-5-2 would have to lie in three different simple paths, while
an inactive degree-four vertex 0 (respectively 2) lies in only two paths.
Consequently X=A union B_{1,5} and Y=A union B_{0,1,2} are terminalizable,
|X|=8<9=|Y|, yet neither edge of Y\X augments X. The matroid axiom fails.

Crucial limitation: deleting A removes all ring connections, and deleting
any core bridge then isolates its triangle. Thus all the augmented deletions
above are disconnected. Connectivity still distinguishes the actual global
selection problem, which this obstruction does not resolve.

A preliminary structured diagnostic /tmp/terminal_matching_expanded.py had
expanded every K4 vertex into a triangle and tested its six external matching
edges. In that 12-vertex graph terminalizable subsets are exactly those of
size <=4 (U_(4,6)); all 64 subsets were checked in 0.23s. That finite pass did
not establish a general matroid theorem. The ring encoding above gives the
actual structural obstruction instead. No diagnostic process remains running.

CYCLE/PATH VERTEX-SET-CHANGING SURGERY (new verified development)

CycleDefect.lean proves last_hit_split, cycle_path_single_defect, and
cycle_path_single_defect_score. A cycle C and an edge-disjoint intersecting
simple path P can be repartitioned into a simple path B and a trail h::A
whose tail A is simple. Both new members start at the same vertex x. Thus
h::A is either a path or has only its starting vertex repeated. Total edge
length is unchanged, and total vertex-incidence score is unchanged in the
one-defect case, increased by one in the two-path case. The proof splits P
at its LAST intersection with C, rotates C there, and transfers its first
edge to the reversed prefix of P. This does not claim C+P always admits two
paths (the old 9-cycle counterexample remains valid). The new move changes
indexed vertex sets, unlike the previous same-root mobile-defect move.
All three new declarations compile and audit with only permitted axioms.
At this point the file has NOT yet been integrated into Work/Spec.

FIXED-BASELINE ONE-DEFECT NORMALIZATION IS FALSE (structural obstruction)

Candidate examined: if k>=ceil(n/2), a connected graph partitioned into one
simple cycle and k-1 paths with baseline endpoint quotas b_v in {0,1,2}
might admit k paths with quotas b_v+2*[v=root] for some freely chosen root.
This is false even for Eulerian graphs, with all initial paths nonempty.

Take K5 on core vertices {1,4,6,7,8}, remove edge 6-7, and replace it by
  7-3-0-5-2-6.
The graph has 9 vertices and 14 edges. Baseline quota is two on each of
B={0,2,3,5}, zero on the five core vertices. There is one cycle
  1-4-7-8-6-1
and four nonempty simple paths
  3-0; 0-5; 5-2; 2-6-4-8-1-7-3.
These partition all edges, and the four paths have exactly the stated
baseline. Thus k=5=ceil(9/2).

However the induced core K5-e has nine edges, so any simple-path partition
restricted to its five vertices needs at least THREE nonempty pieces
(each has at most four edges). There are only two boundary edges. With
baseline fixed outside the core, one extra endpoint pair contributes at
most two core endpoints. Hence restriction would have at most
(2 boundary incidences + 2 core endpoints)/2 = TWO pieces, a contradiction.
An extra root outside the core only makes this count smaller.

This does NOT refute Gallai. It proves that moving just one free endpoint
pair while holding all other endpoint quotas fixed is insufficient, even
at the target budget. Existing baseline endpoint pairs must also relocate.

Exact diagnostic /tmp/free_pair_defect.py passed all 994 connected atlas
graphs of orders 3--7 (5832 baselines, six with no free-root solution but
also no one-cycle witness), then found the above obstruction at row 180
of /tmp/even24_9.g6. The structural cut proof, not the finite search, explains
failure. A followup ten-vertex job is checking the same candidate; it is
not a search for an original-conjecture counterexample.

The ten-vertex followup also finished, finding the same dense-core type of
one-defect obstruction at row 391 (log /tmp/free_pair_defect10.log). No
process remains running. CycleDefect is now integrated under namespace
CycleDefect in Work and Spec; the earlier not-yet-integrated note is obsolete.
The original conjecture remains unresolved with its single sorry.

FOREST-ZERO ONE-FREE-PAIR HYPOTHESIS (unproved; diagnostics complete)

The rejected fixed-baseline normalization statement might hold if the subgraph
induced by vertices with baseline endpoint quota zero is acyclic. Precisely:
given one simple cycle and p simple paths with fixed baseline quotas c_v in
{0,1,2}, and acyclic G[{v | c_v=0}], can their union be partitioned into p+1
simple paths with quotas c_v+2*[v=root] for some root? Nil paths are permitted
in the auxiliary indexed formulation. No cardinal threshold is asserted.

/tmp/free_pair_forest_zero.py checked all baseline sizes with acyclic zero sets:
- atlas: 994 graphs, 15232 baselines; 148 lacked a free-root solution but none
  of those had the required initial one-cycle witness;
- /tmp/even24_9.g6: 276 graphs, 86198 baselines; 159 such no-solution baselines;
- /tmp/even24_10.g6: all 1254 graphs, 741198 baselines; 688 such baselines.
All checks pass, meaning no counterexample to this auxiliary hypothesis was
found. The ten-vertex run finished in 597.43 seconds. No job remains running.
These finite checks are not proofs of this statement or of Gallai's conjecture.

Local reasoning: at a zero-baseline root of an open lollipop defect there is
exactly one other root-ending path. If a first-edge transfer does not repair,
it moves the root to a cycle neighbor. Reversing the cycle prefix gives two
choices, so a nonbacktracking sequence wholly in the zero-induced forest
cannot continue forever. The unresolved step is the positive-baseline root:
extra receivers are available, but a terminating/global exchange argument has
not been established. A lollipop with nonempty tail cannot freely reroot its
cycle; its junction fixes the repeated endpoint. Pure closed cycles can rotate.

The earlier dense eight-vertex fixed-matching-terminal diagnostic also finished:
K8 minus a perfect matching passes all 3760 tested choices in 223.23 seconds.
This is evidence only. The matching-inactive and prescribed-terminal matching
claims remain unproved and are not used as assumptions in any Lean declaration.

MATCHED PROXY FIRST-EDGE SWITCH (new local Lean development)

Submission/MatchingProxy.lean compiles without warnings. It proves:
- common_neighbor_switch: for edge-disjoint trails r-x+p and b-x+q,
  exchanging their first edges gives edge-disjoint trails b-x+p and r-x+q
  with exactly the same union of edges;
- proxy_single_defect: if p is simple, b-x+q is simple, and r is absent from
  q, the second new member is simple and the first is simple iff b is absent
  from p. Otherwise its only possible repeat is its initial vertex b;
- proxy_endpoint_quota: all endpoint quotas are preserved exactly;
- proxy_single_defect_score: assuming r was repeated in the donor, the total
  vertex-incidence score increases by one iff b is absent from p, and is
  unchanged otherwise. The marked edge b-x stays terminal at b.

This is relevant when an inactive x has a distinct matched active partner b,
and that marked edge is already terminal. It is NOT matching normalization.
In particular, when the defective first edge itself is the marked r-x edge,
the proxy partner is r and this two-distinct-member switch is unavailable.
Reversing a lollipop's cycle can move that marked edge to an INTERNAL position
at its junction when the lollipop has a nonempty tail. Therefore the cycle
cannot freely be reversed while claiming preservation of every marked edge's
terminality. This remains a concrete blocker for the matching approach.

The new body has been integrated into Work and Spec under MatchingProxy.
Full rebuilds and standalone/integrated axiom audits are running at this note.
Spec has 16550 lines; its sole original-theorem sorry is at line 16548.

LOCAL-MOVE COMPLETENESS DIAGNOSTIC FOR THE FOREST-ZERO HYPOTHESIS

/tmp/mobile_forest_zero.py tests actual one-cycle-plus-path witnesses using
only cycle rotation, reversal of a lollipop's cycle prefix, and the verified
same-root first-edge transfer. Blocked transfers preserve the indexed vertex
sets; an unblocked transfer repairs the defect. Paths are canonically sorted,
and cycle-prefix reversal is canonicalized. This is a strategy test, NOT an
original-conjecture counterexample search. It allows at most four nonempty
baseline paths and at most 500 eligible witnesses per input graph, so it is
NOT exhaustive over witnesses. Baseline quotas are at most two, with acyclic
zero-induced graph. Search-cap exhaustion is UNKNOWN, not failure.

Completed:
- atlas: 994 graphs, 324480 eligible witnesses, no failed or unknown searches;
- /tmp/even24_9.g6: 276 graphs, 132003 witnesses, no failed or unknown searches.
A ten-vertex run on /tmp/even24_10.g6 is now running, logging to
/tmp/mobile_forest_zero10.log. These finite passes do not supply termination
or a proof of the forest-zero normalization statement. The positive-baseline
root case in a potential global exchange argument remains unresolved.

MatchingProxy checkpoint: Work and Spec full rebuilds succeeded. Work has no
warnings; Spec has only its original conjecture's sorry warning. Standalone
and integrated helper audits report only propext, Classical.choice, Quot.sound.
A missing audit-file docstring was fixed and that audit re-run cleanly.

Terminology clarification: for a defective TRAIL, the switched marked edge is
still the FIRST WALK EDGE at b. If b is repeated, its subgraph degree need not
be one. This is not yet the terminalVertices predicate used by MatchingTrim;
that implication becomes available only when the resulting member is a path.
The Lean lemma statements use Walk.cons explicitly and make no false claim
of degree-one terminality for a repeated endpoint.

NEW PROOF PLAN FOR FOREST-ZERO NORMALIZATION (not yet formalized)

A potentially valid way around the positive-root blocker is to generalize
rooted tail exposure to a DISTINCT SELECTED TAIL FAMILY, without requiring a
bijection between all endpoint slots and all vertices. The existing pivot
itself is purely tail algebra; only its packaging into NormalTrailSystem used
the endpoint bijection. This is NOT an assertion that the main conjecture is
proved. The following argument still needs a complete formal implementation.

Let k trails partition the edges, with total incidence deficit exactly one,
all endpoints having quotas c_v+2*[v=r], and with the unique repeated vertex
r at an endpoint of its member. Thus that member is a lollipop or a pure
cycle; every other member is a path. Baseline c may be any nonnegative quota,
not necessarily bounded by two. Assume no k-path solution with the same
baseline plus a freely placed pair exists.

At root r, split every member containing r into endpoint-to-r tails. There
is one nonempty closed root tail (the lollipop cycle). Other root-labeled
tails are nil. Let B be the SET of all endpoint vertices of these active
members. Select exactly ONE tail for each distinct b in B, choosing the
closed tail for r. Leave all duplicate-labeled tails unselected and fixed.
The selected nonroot tails are simple; all selected tails are edge-disjoint.

Pure tail pivot: if root tail is r-w+p with w in B, replace it by
(r-w+tail_w).reverse and replace tail_w by p, while transposing the selected
labels r,w. Each SELECTED SLOT keeps its vertex set under this relabeling;
unselected slots stay unchanged. Thus every original member keeps its
vertex set after rebuilding its two endpoint tails. Global endpoint quotas
are unchanged (one selected occurrence of each label is permuted), the edge
partition remains valid, and the incidence deficit remains exactly one.
Consequently the rebuilt family still has precisely one endpoint-rooted
lollipop/cycle at r and all other members are paths. This last conclusion
must be proved from the score identity, not silently assumed.

The existing injective penultimate-successor argument should apply to these
selected tails: the two distinct neighbors of the closed simple root cycle
start two disjoint successor orbits, each exiting B. For EACH exit x there
is a same-score realization exposing edge r-x on the root cycle.

If c_x>0, then x has an endpoint owner outside the active members (because
x is outside B), and that path avoids r. The ordinary different-start
first-edge slide repairs the defect, preserving all quotas. This contradicts
failure. Thus every obtained exit is a ZERO-baseline vertex.

If c_x=0, transfer r-x from the defective member to another root-ending
path. If the receiver avoids x this repairs; otherwise it moves the unique
root repetition and the free endpoint pair from r to x, with unchanged
baseline c and deficit. There is another root-ending member unless the
whole defect is a pure cycle with c_r=0. In that exceptional case simply
rotate the closed cycle to x, moving the free pair without changing edges.
A nil root-ending receiver, when present, immediately gives repair.

Therefore, if no repair exists, EVERY reachable root has two distinct ZERO
neighbors which are themselves reachable roots. In particular there is a
nonempty set of zero roots whose induced reachable-root graph has minimum
degree at least two. The finite no-dead-end lemma then gives a cycle in the
zero-induced graph, contradicting the forest assumption. This uses the
realized root-neighbor transitions, not an invalid assumption that all
nonroot tail chains are reachable from one root.

Implementation priority: first extract TailFamily (root_mem, tails, trails,
pairwise edge disjointness, nonempty root tail) and a rearrangement relation
recording a permutation of distinct labels, per-slot vertex-set preservation,
and total edge-union preservation. Port RootedTailSystem.pivot, successor_data,
realize_escape_orbit, and many_distinct_escapes to this smaller structure.
Then add a general indexed trail family WITHOUT endpoint_bijective, rebuild
its slots using a selected-tail rearrangement, and prove the deficit-one
normal form and the two-zero-root transition theorem. Finally use finite
acyclicity. The original Gallai statement will STILL need a separate global
step after any such auxiliary theorem is completed.

DISTINCT-TAIL / ARBITRARY-QUOTA ROOT EXPOSURE (verified new foundations)

Three new development modules compile warning-free and pass axiom audits:
- DistinctTails.lean (~430 lines), namespace Erdos583DistinctTailsDevelopment;
- QuotaTrails.lean (~163 lines), namespace Erdos583QuotaTrailsDevelopment;
- QuotaRooted.lean (~455 lines), namespace Erdos583QuotaRootedDevelopment.
All audited declarations use only propext, Classical.choice, Quot.sound.
They are NOT YET integrated into Work or Spec; their oleans are available.

DistinctTails proves the pure selected-label tail argument, independently of
any endpoint bijection: TailFamily, Rearranged (permutation of labels, fixed
slot vertex sets, total edge union), rearranged_trans, pivot, successor_data,
realize_escape_orbit, replace_root, many_distinct_escapes, and TWO distinct
neighboring exits for any nonempty closed root trail. The simple-cycle special
case is also available. cycle_of_two_zero_successors proves the final abstract
finite closure argument forcing a cycle inside Z.

QuotaTrails defines TrailFamily G k with indexed walks/trails, disjoint edges,
and full cover, but NO endpoint bijectivity condition. Nil members and repeated
endpoint labels are allowed. It proves endpoint quota invariance under a SLOT
permutation, the exact sum-of-lengths formula, score bounds, the path criterion
score=|E|+k, sum_defect_add_score, and one_defect_other_paths: if total deficit
is one and member i is nonsimple, its deficit is exactly one and every other
member is a path.

QuotaRooted defines RootedCut T r A, with tails indexed by active endpoint
SLOTS {s : Fin k x Bool // s.1 in A}. Rebuild permutes slots and preserves each
slot's tail vertex set, giving equal total score and equal endpoint quotas.
It explicitly permits a vertex label to have both active and outside owners.

- selected: choose one tail for each distinct label, fixing the closed root.
- rebuild_selected: apply a pure DistinctTails rearrangement through an
  embedding of selected labels into slots. Equiv.Perm.viaEmbedding extends
  the selected permutation and fixes all unselected slots. The entire active
  label set is proved unchanged, not assumed.
- of_repeated_start constructs all active endpoint-to-root cuts and a nonempty
  closed root tail from a repeated starting endpoint.
- select_labels chooses a right inverse including any prescribed root slot.
- outside_endpoint: a positive-quota vertex outside the active label set has
  an endpoint owner outside A, whose member avoids the root; no uniqueness of
  ownership is asserted or needed.
- two_root_exposures: TWO distinct adjacent vertices outside the active label
  set each have a same-score, same-quota realization, with a closed root tail
  containing the exposed root-neighbor edge. All rebuilt active labels remain
  exactly the original B. The result uses ExposedRoot to package this data.

Remaining steps for the FOREST-ZERO theorem (still unproved):
1. Turn an ExposedRoot into an oriented representative whose first edge is
   the exposed edge, with simple tail forced by the total deficit-one identity.
   One can rotate its closed root tail to that neighbor using
   MultipleEscape.closed_trail_first_at_neighbor, append the other endpoint
   tail reversed, and use per-member score. A root slot may be a finish slot;
   reverse the representative in that case. Root tail subgraphs are tracked,
   not literal walk equality, so do not assume the first edge already matches.
2. Port generic one/two-member replacement and orientation to QuotaTrails.
   Existing NormalTrailSystem.replace_two_starts_tracked and .orient use
   endpoint_bijective only in the construction of the old endpoint invariant;
   replace that with the quota-slot-permutation identity. A more general
   two-member replacement with arbitrary new starts and unchanged finishes
   should record the exact endpoint-quota balance. This also handles same-root
   MobileDefect transfers, which MOVE a pair rather than preserve quotas.
3. For positive outside-label exposure, orient an outside owner and apply the
   different-start first-edge slide. The root is absent from that receiver,
   so score increases one and all members become paths.
4. For zero exposure, use another root-ending member for MobileDefect. Unless
   repair occurs, the baseline stays fixed and the free pair/defect root moves
   to the exposed zero vertex. If no other root-ending member exists, prove
   the defect is a pure closed cycle and baseline at the old root is zero;
   rotate that cycle to move the free pair. Nil receivers repair immediately.
5. Under failure, two_root_exposures therefore gives two distinct ZERO-root
   successors for each reachable root. Apply cycle_of_two_zero_successors.

Do not conflate this proposed auxiliary completion with the original Gallai
statement. Even after it is proved, the unrestricted global cardinal bound
will still need an additional argument.

Latest local-move diagnostic finished: all 1254 rows of /tmp/even24_10.g6,
618820 sampled eligible witnesses, zero failures and zero unknown searches,
556.24 seconds. As before there are at most four baseline paths and at most
500 witnesses per input graph. This is NOT exhaustive over witnesses and is
not a proof. No diagnostic job remains running.

FOREST-ZERO NORMALIZATION COMPLETED

The preceding remaining-steps list is obsolete. QuotaSurgery now proves
exposedRoot_repair_of_positive and exposedRoot_move_pair_or_repair, including
the pure-closed-member rerooting case. ForestZeroNormalization proves
normalize_one_defect_forest and normalize_one_cycle_forest for arbitrary
baseline quotas with an acyclic zero-baseline induced graph. All five new
modules compile without warnings and their audits use only the permitted
axioms. They have now been inlined into Work and Spec. Both integration builds
passed, and the expanded IntegratedAudit passed with only permitted axioms. The original Gallai conjecture still has its one explicit sorry;
no unrestricted global endpoint-selection/cardinality bound is claimed.

NONEDGE MATCHING ADDITION (new conditional certificate and finite diagnostics)

New candidate, NOT proved: for an all-odd H and an oriented matching of
NONEDGES a--b, there is a normal H path partition such that the member ending
at each designated source a avoids its designated target b. Sources and targets
of different marked pairs are all distinct. This is stronger than merely
choosing one safe orientation per pair. Appending each marked edge at its source
would then yield paths without increasing member count. The endpoints at sources
would disappear and their targets would acquire a second endpoint.

Three exact finite diagnostics finished, with no failures:
- /tmp/nonedge_matching_append.py on all 224 connected all-odd 8-vertex graphs:
  25,607 nonempty nonedge matchings, 46.07 seconds. Both directions may be tested
  together: a pair is bad only if EACH endpoint's owner contains the other.
- /tmp/nonedge_matching_oriented_append.py on the same 224 graphs:
  all 153,574 prescribed source/target orientations, 163.76 seconds.
- /tmp/nonedge_matching_append.py on all 19 connected cubic 10-vertex graphs:
  46,918 nonedge matchings, 125.12 seconds.
These check auxiliary conditions, not Gallai itself, and are not proofs. All
three processes have finished. Logs have matching names under /tmp/.

MatchingAppend.lean (about 210 lines) now compiles warning-free. Its type
OrientedMatching G records source set, injective targets, disjoint source/target
sets, and matching edges in G. It proves the safe-extension CERTIFICATE:
- cap, moved, decorate append the chosen matching edge at either/both ends;
- decorate_isPath: if each source endpoint avoids its target, the decorated
  walk is simple. Injectivity of targets handles two appended ends.
- append_to_normal_system: from a normal path system of H, H <= G, disjoint
  matching edges, exact edge cover, and simultaneous avoidance, construct a
  same-size indexed PATH family of G.
- path_family_partition turns arbitrary indexed path families (nil allowed)
  into a GoodDecomposition with cardinality at most the index count.
- matching_append_certificate gives 2*D.card <= |V| from the avoidance witness.
The missing simultaneous-avoidance hypothesis is NOT asserted by any theorem.
The certificate does not by itself prove the matching-inactive candidate, and
that candidate still would not alone settle Eulerian graphs lacking near-perfect
matchings (e.g. K2,4). No new global bound has been obtained.

Possible but UNFINISHED proof direction: minimize sums of indexed vertex-set
intersections across the marked nonedge pairs. Exact shortening transfers only
one vertex incidence, so only its marked pair contributes to this potential.
A root a pivot can never transpose the endpoint label b when a,b are nonadjacent.
This observation may preserve b's endpoint slot, but there is no established
closure/termination argument forcing the a-owner to avoid b. It is NOT a proof.

Another UNFINISHED dynamic-matching idea: at an unmatched positive root, select
unmarked endpoint tails, leaving required terminal marked tails fixed. A zero
escape matched to a positive vertex can sometimes be handled by a proxy switch
and updating the matching. The blocked case is when the marked recipient contains
the old root and its positive endpoint also occurs in the donor: the naive proxy
then creates two defects (loses one incidence). No one-defect invariant or global
augmentation argument has been proved for this case. Do not assume the proxy
preserves all terminal matching edges automatically.

A tempting two-path shortcut is FALSE. Even if endpoints a,b of two different
edge-disjoint paths occur on each other's path and a,b are nonadjacent, their
union need not repartition into two paths with a,b paired as endpoints.
Counterexample edges:
  02,12,13,14,25,35,45;
paths 0-2-1-3-5 and 1-4-5-2; desired pair 5,1.
If one path paired 1 with5, the other would pair0 with2; since0 is a leaf at2,
the latter must be singleton02, leaving the three internally disjoint 1-to-5
routes, which cannot be one simple path. The intermediate degree-two vertices
3 and4 must have outside endpoint owners in an all-odd completion, so this does
not refute the missing-edge matching-avoidance candidate. It rules out a naive
local pairing switch. Diagnostic /tmp/two_path_mutual_pairing.py stopped on
this structurally explained example. No axiom or theorem assumes the shortcut.

MatchingAppend has now been inlined into Work and Spec; integration builds are
running. Standalone MatchingAppendAudit passed with only permitted axioms.

LATEST VERIFIED CHECKPOINT

MatchingAppend integration builds passed: Work is warning-free; Spec reports only
its original erdos_583 sorry. IntegratedAudit passed and all new helpers depend
only on propext, Classical.choice, Quot.sound. Spec has 18,573 lines, original
unchanged theorem at line18,533 and its sole sorry at line18,571. The single
FormalConjecturesUtil import is unchanged.

Two further diagnostics finished (no process remains running):
- /tmp/nonedge_matching_fixed_cubic10.py checked all 88,128 orientations of
  perfect nonedge matchings in all 19 connected cubic ten-vertex graphs, passing
  in 189.40 seconds. This does NOT include every non-perfect matching orientation.
- /tmp/nonedge_matching_dense10.py checked all32 orientations of the fixed
  alternating perfect matching in the complement of C10, and all16 orientations
  of one specified four-edge nonedge matching in K5,5. All48 passed, 60.59 seconds.
  These are two explicit examples, not an exhaustive dense-graph check.
No diagnostic is used as a proof. The original Gallai conjecture remains
unresolved in this project, and no counterexample to its actual statement has
been found. The simultaneous-avoidance premise of MatchingAppend remains open
here; even that candidate alone would not handle graphs without near-perfect
matchings. The final global cardinality gap has not been discharged.

SUBMISSION REJECTED; CONTINUATION REQUIRED

A submit_proof call was made with the remaining original sorry, so the user
reported verification failure and requested continued work. No complete proof
was claimed. The current file must NOT be regarded as a valid submission.
The verified checkpoint and original global gap described above are unchanged.


## Simultaneous forest avoidance (verified)

ForestAvoidance.lean proves a simultaneous forbidden-partner theorem for normal
trail systems of forests. Sources form a set S, each source has one specified
nonneighbor target outside S. Target injectivity is NOT needed for avoidance.
A normal path system can be chosen so that the endpoint-owner path of every
source avoids its target.

Proof: orient a violating source a first on its member P. Its first neighbor w
is different from its target, since targets are nonneighbors. The endpoint
owner Q of w is a different member. Forest acyclicity implies Q avoids the
target of a (otherwise the two disjoint w-to-target paths coincide). Moving
the edge a-w from P to Q therefore repairs a. Other source owners only lose
vertices or gain a, which cannot be any source's target. The only possible
new violation is at w, now owner of the shortened P. Minimize the number of
violations, then the cardinality of a violating owner's vertex set; the move
contradicts that lexicographic minimum.

Main APIs: forest_slide, forest_step, forest_avoidance, and
all_odd_forest_matching_addition. The last uses MatchingAppend to prove the
Gallai bound (in fact 2*card <= n) after adding any disjoint matching to an
all-odd forest. The theorem does NOT assert that arbitrary graphs admit such
a representation, or that the avoidance argument holds in cyclic graphs.

Standalone build and audit pass, with only propext, Classical.choice, Quot.sound.
The body is integrated as namespace ForestAvoidance in Work and Spec.
The original theorem still has its one sorry; there is no completed settlement.

ForestAvoidance integration checkpoint: Work compiles warning-free; Spec compiles
with only the original-theorem sorry warning. Expanded IntegratedAudit passes.
The main theorem now has an additional verified branch for an all-odd forest
plus a matching; its statement and sole import are unchanged. The global case
outside the verified branches remains unresolved, and no proof submission was made.


## Unrestricted trail budget and nil-slot obstruction (verified)

NilSlot.lean and TrailBudget.lean are compiled, audited, and integrated in Work
and Spec under NilSlot and TrailBudget. All audited declarations use only
propext, Classical.choice, Quot.sound. No normalization axiom is assumed.

NilSlot proves:
- relocate_nil: with unrestricted endpoint quotas, a nil member can be moved
  to any vertex at unchanged incidence score;
- nonpath_cut: every repeated-vertex walk has a cut whose two portions share
  at least two distinct vertices;
- improve_using_nil: split a nonpath member at such a cut and use a nil member
  for the second portion. The old nil contributed one vertex incidence; the
  cut contributes at least two shared incidences. Score strictly increases;
- max_score_paths_of_nil / max_score_nonpath_no_nil: a global score maximum
  containing a nil member is already all paths. Any nonpath maximum has all
  indexed members nonempty. These statements use unrestricted TrailFamily,
  not fixed endpoint quotas or normal endpoint bijectivity.

TrailBudget proves:
- splice_closed_at_vertex / extend_trail_family_at_vertex: splice an
  edge-disjoint closed trail at any supported vertex, including an internal
  vertex, preserving the indexed endpoints;
- connected_closed_set / cycle_meets_trail: in a connected graph, a nonempty
  indexed family covering the graph together with a nonempty cycle remainder
  has a vertex in common with a remaining cycle;
- absorb_cycles_connected: absorb the cycle remainder one member at a time;
- exists_bounded_trail_family: use the existing parity-forest path-and-cycle
  partition. If its path family is nonempty, absorb cycles into its #odd/2
  trails. Otherwise start with one nil trail and absorb all cycles. In either
  case the trail count is at most ceil(n/2);
- pad_trail_family: add nil indices to reach any larger prescribed count;
- exists_budget_maximum: there exists a global score maximum on exactly
  ceil(n/2) indexed trails for every connected finite graph.

The final unresolved branch of the original theorem now explicitly obtains
such a maximum T. If all its members are paths, the existing indexed-family
projection closes the goal. Otherwise it records that every member is nonempty
and still has one sorry. No theorem rules out this obstruction; this is a
reformulation and structural narrowing, NOT settlement of Gallai's conjecture.

## Maximum-score merger obstructions (verified)

TrailMerge.lean now compiles, has a clean standalone axiom audit, and is inlined
into Work and Spec under TrailMerge. Work is warning-free; Spec still has one
sorry in the original theorem. Expanded IntegratedAudit passes; all newly
audited helpers use only propext, Classical.choice, Quot.sound.

- merge_into_nil: when two members meet at exactly one vertex and their union
  is the subgraph of a trail ending at the second member's old finish, merge
  them and leave a nil member at the first member's old finish. Score is equal:
  the one lost overlap incidence is replaced by the nil member's incidence.
- paths_of_score_eq_maximal_nil: an equal-score nil-containing family forces a
  globally maximum-score original family to consist of paths.
- common_start_merge, common_start_intersection_bound, and
  common_endpoint_intersection_bound: in a nonpath global maximum, distinct
  endpoint-sharing members have at least two common vertices.
- closed_merge and closed_intersection_bound: a closed member in a nonpath
  global maximum cannot meet another member in exactly one vertex. Rotate it
  to that vertex, splice it into the other trail, and apply merge_into_nil.

These are necessary conditions on an obstruction, not a contradiction from
2*k >= |V|. The unrestricted exact-budget normalization statement remains
unproved, and the original Gallai conjecture is still not settled.
Logs: /tmp/trailmerge.log, /tmp/trailmerge_audit.log, /tmp/work_trailmerge.log,
/tmp/spec_trailmerge.log, /tmp/integrated_trailmerge_audit.log.

The new merger conditions alone cannot imply simplicity, even at exact budget.
A concrete diagnostic is now formalized in MergeObstructionCheck.lean:
K5 has the three edge-disjoint trails
  0-2-3-0-1; 1-3-4-2; 2-1-4-0.
They cover all ten edges, all are nonempty and open, every distinct pair has
THREE common vertices, and the first member is not a path. The three slots are
exactly ceil(5/2). Thus counting only the new intersection conditions cannot
close the proof. This family is not a global score maximum, and K5 itself
already satisfies Gallai (proved separately in Spec). The diagnostic theorem
intersection_conditions_insufficient compiles without gaps and its axiom audit
uses only the permitted three axioms. It is not inlined into Spec, because it
is an obstruction to a shortcut, not a case or a disproof of the conjecture.

## Rooted single-defect reduction for the entire conjecture (verified)

New module EdgeDefect.lean compiles warning-free and passes an axiom audit of
all its main declarations. Its body is now integrated as namespace EdgeDefect
in Work and Spec. Work rebuild passed; the Spec rebuild is being checked.

- decomposition_path_family indexes any GoodDecomposition with exactly D.card
  path slots, retaining the representation of every member.
- decomposition_odd_endpoint uses degree parity to find a slot ending at a
  prescribed odd-degree vertex. Degree-parity hypotheses use Nat.card of
  neighbor sets to avoid nondefinitional Fintype instance unification.
- append_new_edge appends one new edge at such an endpoint, retaining the slot
  count. All but the modified member are paths; the total incidence deficit
  is at most one. If it is nonpath, it has a rooted repeated endpoint at the
  other end of the added edge.
- even_degree_delete_edge_odd proves the necessary parity toggle.
- one_defect_of_even_edge_deletion: if G-e already has a k-path bound, e is
  incident to an even-degree vertex of G, and G fails the k bound, there is
  a GLOBAL maximum-score TrailFamily G k with score+1=|E(G)|+k and HasRoot.
  Failure forces the deletion partition to use exactly k slots: otherwise
  restoring e as a singleton path would already suffice.

The key new GLOBAL observation is failure_has_even_nonbridge:
  Choose a normal path partition maximizing the number of inactive vertices.
  If all endpoint multiplicities were at most one, the endpoint count gives
  2*D.card <= n, contradicting failure. So some vertex v has multiplicity two
  (and is even). Its two distinct endpoint members must meet again, by the
  earlier max_inactive_pair_intersects theorem. Edge-disjoint rooted prefixes
  to that second intersection form a nonempty closed trail through v. The
  first edge of a closed trail cannot be a bridge: the rest of the trail,
  reversed, is an alternate endpoint-to-endpoint walk avoiding that edge.
  Thus some nonbridge is incident to an even-degree vertex. This avoids an
  unproved blanket reduction to bridgeless graphs.

failure_has_rooted_one_defect now proves:
  From ANY connected failing G, select a connected failing spanning subgraph
  H <= G with the fewest edges. Select the even-incident nonbridge above.
  Its deletion stays connected and has fewer edges, so minimality gives the
  conjectured path bound for H-e. Restore e with the verified construction.
  Hence there is a connected failing H and T on EXACTLY ceil(n/2) slots with
      T.score + 1 = |E(H)| + ceil(n/2),
      HasRoot T r,
      forall U on the same slots, U.score <= T.score.
  There is exactly one nonpath member and it has exactly one repeated vertex;
  all other members are paths. The existing nil-slot theorem also says every
  member is nonempty. The root need not have endpoint quota at least two.

The conditional theorem gallai_of_rooted_one_defect_repair packages the missing
step. It does NOT assert the repair hypothesis. In particular the fixed-baseline
forest-zero theorem does not discharge this unrestricted rooted-defect case:
there is no proved acyclic zero-baseline hypothesis, and a defect root can have
only one endpoint slot.

The original theorem's last branch is updated to use this sharper global
reduction. Its remaining sorry is now explicitly under connectedness, global
score maximality, exact budget, a SINGLE rooted defect, and no nil members.
No proof rules out that obstruction. The original conjecture remains unresolved.
Standalone logs: /tmp/edgedefect.log and /tmp/edgedefect_audit.log.
Integration logs: /tmp/work_edgedefect.log and /tmp/spec_edgedefect.log.

EdgeDefect integration checkpoint: Spec build passes with only the original
sorry warning; expanded IntegratedAudit passes with the allowed axioms only.
Spec is 19,818 lines, sole sorry at line 19,816, original theorem at line 19,754.
The original theorem's statement and single import are unchanged. Work is
19,730 lines and warning-free. EdgeDefect is 367 lines, no gaps. There are no
pending builds. No proof submission was made because the single-defect repair
remains unproved. Integrated audit log: /tmp/integrated_edgedefect_audit.log.

## Minimum root-quota energy checkpoint (verified)

RootEnergy.lean is now integrated into Work and Spec under RootEnergy.
Both rebuilt successfully. Work is warning-free; Spec has exactly the one
remaining sorry in erdos_583. The expanded IntegratedAudit passes, and every
newly audited helper uses only propext, Classical.choice, and Quot.sound.
Logs: /tmp/rootenergy.log, /tmp/rootenergy_audit.log,
/tmp/work_rootenergy.log, /tmp/spec_rootenergy.log,
/tmp/integrated_rootenergy_audit.log.

The quota energy is sum_v (T.quota v)^2. Minimize it among same-score
families with a rooted defect. At a globally maximal single defect every
exposed outside endpoint label has quota zero. Moving a pair from root r
to such a neighbor x has the exact identity
  energy(new) + 4 * quota_old(r) = energy(old) + 8.
Consequently a minimum-energy root has quota one or two. This does NOT
bound quotas at other vertices.

If every member contains r, its distinct non-root endpoint-tail edges and
the two closed-tail edges imply
  2*k - T.quota r + 2 <= Nat.card (G.neighborSet r).
At 2*k >= |V| and root quota <= 2 this is impossible in a simple graph.
Thus there is an indexed member avoiding r. The root also has two distinct
zero-quota neighbors. Since sum_v T.quota v = 2*k, the budget implies a
vertex w != r of quota at least two. Neither fact supplies a transport of
that surplus to the defective member.

When the root quota equals two, the vertices of zero quota together with
the root induce a cyclic graph. Otherwise the verified fixed-baseline
forest normalization theorem would repair the defect.

The original theorem's last branch now records all these conditions and
still ends in sorry. There is no complete proof or disproof. In particular:
- an outside member need not have an endpoint accessible to rooted exchanges;
- the minimum-energy argument permits root quota one, not only two;
- moving the one free pair while fixing every other pair is insufficient,
  even at the conjectured budget (see the earlier dense zero-core examples).

An exact finite diagnostic of a narrower auxiliary statement was also run:
a spanning n-cycle together with an edge-disjoint Hamilton path on all but
one vertex was tested for a partition into two Hamilton paths. All tested
witnesses for n=5,...,10 passed (respectively 1, 7, 45, 323, 2621, 23811).
Script /tmp/cycle_contained_path.py; log /tmp/cycle_contained_path.log.
This is NOT a proof of the auxiliary statement or of Gallai's conjecture.

Do not generalize fixed-baseline single-defect forest normalization to
arbitrary total defect. K_{2,5} illustrates the danger: the five degree-two
vertices induce an independent set, yet endpoint baseline one at each of
the two degree-five vertices plus one freely located endpoint pair cannot
give two simple paths, since a degree-five vertex requires at least three
path incidences. The existing lemma's single-defect hypothesis is essential
to its proved argument; no unrestricted generalization has been asserted.

## Unrestricted pair replacement and triangle absorption (verified)

New standalone modules:
- GeneralPair.lean (114 lines): replace_two replaces two indexed trail
  members by arbitrary-endpoint trails with the same disjoint edge union.
  It retains the other members and the exact incidence-score identity.
  Unlike QuotaSurgery.replace_two_starts_general, neither pair of finishes
  is fixed. No endpoint-quota invariance is claimed.
- TriangleAbsorption.lean (345 lines): an edge-disjoint triangle and an
  intersecting simple path have an edge partition into two simple paths.
  This includes paths with arbitrarily many vertices outside the triangle.

The triangle proof is explicit, not computational enumeration. Split the path
at its last triangle vertex w. If another triangle vertex u is absent from
its prefix, use the edge u-w with the reversed prefix and the other two
triangle edges with the suffix. If all three occur, label them in order
u,v,w; write P=A+(v-y)+Q+D, with A ending at v and containing u, Q from y
to w, D the final suffix. Edge-disjointness ensures y != w. The two new
paths are A+(v-w)+reverse(Q) and y-v-u-w+D. Nodup of P gives all the
required support separations. Edge union and length/cardinality give exact
edge disjointness of the two new paths.

Main APIs:
  TriangleAbsorption.ordered_triangle_surgery
  TriangleAbsorption.triangle_path_absorption
  TriangleAbsorption.maximal_triangle_no_intersecting_path
  TriangleAbsorption.maximal_single_defect_no_triangle
  TriangleAbsorption.budget_maximum_no_triangle

In a global score maximum, replacing a whole triangle and an intersecting
simple path increases score by one. In a connected single-defect maximum,
every other member is simple. If none meets the triangle, its vertex set
is closed under graph adjacency and hence is all vertices. With at least
two slots that is also impossible. At the Gallai budget three distinct
triangle vertices ensure at least two slots. Thus NO WHOLE TRIANGLE MEMBER
can occur in the remaining exact-budget obstruction.

IMPORTANT LIMIT: this does not exclude a triangular cycle prefix of an open
lollipop. Its stalk cannot in general be merged with another path without
creating additional repetitions. Larger closed cycles are not excluded.
The general rooted single-defect repair remains unproved.

Both module bodies are inlined into Work and Spec under GeneralPair and
TriangleAbsorption, respectively. All standalone and integrated axiom audits
pass with only propext, Classical.choice, Quot.sound. The final original
branch records the new no-whole-triangle condition and still ends in one
sorry. The original theorem statement and sole import are unchanged.
Logs: /tmp/generalpair.log, /tmp/generalpair_audit.log,
/tmp/triangleabsorption.log, /tmp/triangleabsorption_audit.log,
/tmp/work_triangle.log, /tmp/spec_triangle.log,
/tmp/integrated_triangle_audit.log. The final comment-only cleanup rebuilds
use /tmp/work_triangle_final.log and /tmp/spec_triangle_final.log.

## Small-cut direction: scope of the current informal observation

A bridge whose two components have orders n1,n2 can be approached by applying
induction to each side with a temporary leaf at its attachment vertex. The
marked leaf paths can be glued across the bridge (including the singleton
leaf-edge case). The resulting arithmetic bound is
  ceil((n1+1)/2) + ceil((n2+1)/2) - 1.
This meets ceil((n1+n2)/2) if at least one side has odd order. It is ONE TOO
LARGE if both orders are even, unless additional endpoint flexibility or a
saved slot is supplied. Also, strict smaller-order induction requires both
components to have at least two vertices. This observation has NOT been
formalized as a blanket bridgeless or 2-connected reduction. It does not
settle the conjecture and has not been assumed in Spec.


## Additional auxiliary diagnostics from the triangle checkpoint

These are finite checks, not Lean proofs and not proofs of Gallai.

- /tmp/small_cycle_absorb.py, log /tmp/small_cycle_absorb.log: 1,830
  unordered pairs of Hamilton core paths on a five-cycle passed an exact
  three-path-cover test. Every added path edge was privately subdivided,
  with private leaves at the ends; each core vertex had degree six. This
  restricted subclass does NOT justify a general short-cycle absorption rule.
- /tmp/cycle_two_spanning_paths.py, log /tmp/cycle_two_spanning_paths.log:
  a Hamilton n-cycle plus an edge-disjoint spanning two-component linear
  forest was tested for a partition into two Hamilton paths. Nil components
  are allowed. Completed counts for n=4,...,8: 1,10,81,665,6044, all passed.
  No n=9 or n=10 run was started. This auxiliary assertion remains unproved.
- A speculative Hamilton-lock counterexample based on two K4-core port
  gadgets was retracted: after deleting one locked edge and subdividing
  another, two Hamilton paths can cross the remaining cut edges in a
  different pairing. It is not a counterexample to the auxiliary assertion.

## Short-cycle absorption is false (new Lean-verified obstruction)

ShortCycleObstruction.lean is now integrated under ShortCycleObstruction.
The graph on vertices 0,...,8 is the disjoint edge union of:
  C = 0-1-2-3-4-0,
  P = 5-0-2-4-1-3-6,
  Q = 7-5-8.
It is connected. The cycle has length five, at most twice the three-member
count, yet the graph has NO edge partition into three simple paths.

Structural reason: the core {0,...,4} is K5 minus edge 03 and every core
vertex has ambient degree four. The four outside vertices {5,6,7,8} are all
odd. Only edges 05 and 36 cross the core boundary. In any three-path
partition the previously proved degree/endpoint cut inequality forces each
core vertex to have zero endpoint multiplicity. All endpoints would then
be outside; applying the same inequality again gives 4 <= 2, a contradiction.
The formal proof uses this cut argument, not exhaustive path enumeration.

The graph has nine vertices, so this is NOT a Gallai counterexample: its
conjectured bound is five. In fact four paths suffice, for example:
  5-0-1-2; 2-3-4-0; 0-2-4-1-3-6; 7-5-8.
(The four-path upper certificate is recorded here; the Lean module proves
connectedness, the C/P/Q witness, and the three-path impossibility.)

This refutes the proposed general rule that a cycle of length <= 2*k can
always be absorbed into k-1 connected simple-path members. It does not
refute the narrower spanning-cycle-plus-two-spanning-paths diagnostic.
The obstruction has a quota-two root and an outside member, but no surplus
endpoint pair elsewhere; its order exceeds the exact budget.

## Arbitrary-trail quota parity and even-forest repair (verified)

QuotaParity.lean is now integrated under QuotaParity. Main APIs:
  degree_sum
  trail_degree_add_endpoints_even
  quota_even_iff / quota_odd_iff
  zero_quota_even
  even_root_quota_ge_two
  small_root_quota_one_iff
  normalize_root_with_pair_of_even_forest
  normalize_even_root_of_even_forest
  maximum_root_odd_of_even_forest

For ANY indexed trail family, including nil members, the endpoint quota at
v has exactly the parity of the ambient degree at v. Thus zero-quota
vertices have even degree, and an even-degree rooted defect has quota >=2.

If the even-degree vertices induce a forest, a rooted single-defect family
with root quota >=2 can be normalized at the same member count. Remove one
pair at the root to define the fixed baseline c. Every zero-baseline vertex
has even ambient degree, so its induced graph is a subgraph of that forest.
The existing single-defect forest-zero normalization theorem then applies.
This argument does not require score maximality or the Gallai budget.

Consequently, under the even-forest hypothesis, every rooted single-defect
GLOBAL score maximum must have root quota exactly one and odd root degree.
This DOES NOT normalize that remaining case or prove the full even-forest
Gallai theorem. It also does not transfer a surplus pair from another vertex.

The pair hypothesis cannot simply be omitted at arbitrary k. For example,
C=0-1-2-0 with stalk 0-3-4, and the other path 5-3-6, have a two-trail
single-defect witness with root 0 of quota one. Vertices 0,4,5,6 are odd,
and {1,2,3}, the even vertices, induce a forest. Two simple paths would use
all four endpoints at the odd vertices, leaving none in the pendant region
{1,2}, impossible. This explanatory example is not separately formalized;
it is also below the Gallai budget (n=7,k=2).

Both new standalone modules and their axiom audits passed. Work and Spec
were rebuilt after inlining them; Work is warning-free and Spec still has
exactly ONE original-conjecture sorry. The conjecture statement and sole
import are unchanged. Standalone logs:
  /tmp/quotaparity.log, /tmp/quotaparity_audit.log,
  /tmp/shortcycleobstruction.log, /tmp/shortcycleobstruction_audit.log.
Integrated build logs:
  /tmp/work_quotaparity.log, /tmp/spec_quotaparity.log.
The integrated axiom audit is /tmp/integrated_quotaparity_audit.log.
No global proof or disproof has been found, and no proof submission was made.

Final checkpoint for this continuation: integrated audit completed successfully;
all newly audited declarations use only propext, Classical.choice, Quot.sound.
Spec has 20,801 lines, original theorem at line 20,721, and its sole sorry at
line 20,799. Work has 20,698 lines and no gaps or warnings. QuotaParity has
135 lines; ShortCycleObstruction has 106 lines. No builds or diagnostics are
running. The main theorem's unresolved branch was not changed in this turn.

## Rooted incidence and cut capacity (new verified development)

RootCapacity.lean is integrated into Work and Spec under RootCapacity.
The standalone module has 240 lines and compiles warning-free. Its audited
helpers use only propext, Classical.choice, Quot.sound. Main APIs:
  walk_incidence_count
  trail_degree_count / trail_incidence / path_incidence
  repeated_start_incidence
  rooted_member_incidence / rooted_incidence
  rooted_degree_quota_bound / root_eq_of_over_capacity
  trail_endpoint_boundary_bound / ncard_inter_eq_sum
  rooted_cut_bound / root_eq_of_cut_over_capacity

For an arbitrary trail p, degree within its subgraph plus its endpoint-slot
count equals twice the number of occurrences in p.support. For a globally
single-defect family with HasRoot T r this gives the exact identity
  degree_G(v) + quota_T(v)
    = 2 * #{members containing v} + 2*[r=v].
Nil members are permitted and counted correctly: they contribute one vertex
incidence and two endpoint slots but no degree.

The endpoint/boundary inequality previously proved for a simple path actually
only requires a trail. Splitting at a visit to a vertex outside S gives two
edge-disjoint tails; each endpoint in S forces a different boundary edge.
Summing gives the new rooted-single-defect cut constraint, for v outside S:
  degree_G(v) + quota_T(v) + sum_(w in S) quota_T(w)
    <= 2*k + |boundary_G(S)| + 2*[r=v].
Thus an over-capacity vertex or cut pins EVERY endpoint-rooted realization of
a single defect to that vertex. These are necessary constraints, not a
sufficient condition for a path partition or a defect-transport algorithm.

## Rejected attempt to remove quota-one roots (structural, not separately
## instantiated as a finite Lean counterexample)

The claim that a quota-one defect can always be moved to a quota >=2 root
whenever k is greater than half the number of odd vertices is FALSE.

On vertices 0,...,5 take triangles 0-1-2-0 and 0-3-4-0, and edge 05.
The two trails
  0-1-2-0-3-4; 4-0-5
have precisely one defect and quotas q(0)=1, q(4)=2, q(5)=1. There are only
two odd vertices, so k=2 exceeds the odd-vertex lower bound. But degree(0)=5
forces the single defect to occur at 0 in every two-trail maximum; the new
incidence identity also forces its quota to equal one.

Even adding the hypothesis Delta <= 2*k does not repair this claim. Extend
the example by edges 56 and 57, adding the third path 6-5-7. Now n=8,k=3,
Delta=5<=6, and there are four odd vertices 0,5,6,7. The displayed family
has score 11 = |E|+k-1 and quota two at 4. Three simple paths are impossible:
for v=0 and S={5,6,7}, degree=5, the odd contribution is 1+3, and the
boundary has one edge, giving the impossible path bound 9 <= 7.
For ANY rooted one-defect family on three slots, quota parity gives q(0)>=1
and q(S)>=3. The rooted cut bound reads 9 <= 7+2*[r=0], forcing r=0; its
upper bound then forces q(0)=1. Thus no globally same-score rooted family
has root quota at least two. The extra pair at vertex 4 cannot be transported
as proposed. This is NOT a Gallai counterexample: n=8, so its budget is four,
not the three slots used here. No numerical search was needed for either
obstruction.

The EXACT VERTEX BUDGET remains essential. In fact, cut bounds involving
only degree and odd-vertex parity cannot contradict that budget: for v not
in S, simplicity gives
  degree(v) <= n-|S|-1 + #{neighbors of v in S}
            <= n-|S|-1 + |boundary(S)|.
Hence degree(v)+[degree(v) odd]+#odd(S) <= n+|boundary(S)| automatically.
A useful global argument must control actual endpoint-quota excess, not
silently replace it by parity or assume that it is freely movable.

Build logs: /tmp/rootcapacity.log, /tmp/work_rootcapacity.log,
/tmp/spec_rootcapacity.log. Standalone audit: /tmp/rootcapacity_audit.log.
Integrated audit: /tmp/integrated_rootcapacity_audit.log.
The original conjecture still has one sorry; neither its statement nor its
single import was changed. The new lemmas do not discharge the final branch.

RootCapacity final integration checkpoint: expanded IntegratedAudit passed,
all audited new declarations use exactly the permitted axiom set. Spec has
21,041 lines, original theorem at line 20,961 and sole sorry at line 21,039.
Work has 20,938 lines and no gaps or warnings. No jobs remain running. No
submission was made, because the exact-budget endpoint-transport step is
still unproved. The original final branch remains unchanged.

## Component-separated matching addition (verified)

ComponentMatching.lean is now integrated into Work and Spec. Its result does
NOT establish arbitrary matching addition. It proves this precise case:
  H is all-odd, H <= G, G.edgeSet = H.edgeSet union M.edges,
  M is an oriented matching in G, and every matched source/target pair
  lies in DIFFERENT connected components of H.
Then G has a good path partition D with 2*|D| <= |V|. Neither H nor G is
required to be connected, and H may contain cycles. The matching need not
form a forest after the old components are contracted.

Proof: normalize an all-odd trail system of H by the verified global all-odd
normalization theorem. Every walk stays in its old component, so every
source-ending member avoids that source's prescribed target. This is the
simultaneous avoidance certificate required by MatchingAppend. Separation
also implies that the new matching edges are disjoint from H.edgeSet.

APIs:
  ComponentMatching.avoid_of_unreachable
  ComponentMatching.matching_edges_disjoint
  ComponentMatching.intercomponent_matching_addition
  ComponentMatching.gallai_of_intercomponent_matching
The new case is an explicit branch in the original theorem's proof, with
its statement and sole import unchanged. The general final branch still has
one sorry; no unrestricted avoidance, terminal-weight selection, or
exact-budget defect repair theorem has been proved.

A tempting triangular-prism obstruction to matching avoidance was checked
and retracted. For prism edges 01,12,20,34,45,53,03,14,25 and prescribed
nonedge pairs 0->4, 1->5, 2->3, a valid normal avoidance partition is
  1-0-3-4; 0-2-5-3; 2-1-4-5.
The mistaken argument assumed a three-piece partition of a triangle needs
a nil piece; the three singleton edges are another possibility. No false
claim about this example was put into Lean.

Standalone build: /tmp/componentmatching.log (passes without warnings).
Standalone axiom audit: /tmp/componentmatching_audit.log (allowed axioms only).
Integration builds: /tmp/work_componentmatching.log and
/tmp/spec_componentmatching.log (both pass; only the original sorry warning).
Integrated audit: /tmp/integrated_componentmatching_audit.log.

ComponentMatching final checkpoint: integrated audit passed with only
propext, Classical.choice, Quot.sound for every newly audited helper.
Spec has 21,104 lines, original theorem at line 21,016, and its one sorry
at line 21,102. Work has 20,992 lines and no gaps or warnings. The standalone
module has 57 lines. No jobs remain running. No proof submission was made,
because the general conjecture is still not settled.

## Edge-minimal failures retained (verified)

EdgeCritical.lean has been inlined under EdgeCritical in Work and Spec.
The final branch now calls failure_has_edge_minimal_rooted_one_defect and
retains hcritical : EdgeCritical.EdgeMinimal H ceil(|V|/2). This means that
EVERY connected spanning subgraph of H with strictly fewer edges meets the
same budget. It is NOT a vertex-minimality assertion.

New APIs:
  EdgeMinimal
  exists_edge_minimal_failure
  EdgeMinimal.delete_nonbridge
  EdgeMinimal.root_at_other_endpoint
  restore_even_even_edge_of_even_forest
  EdgeMinimal.even_even_edge_isBridge_of_even_forest
  failure_has_edge_minimal_rooted_one_defect

The universal rooting statement: for every nonbridge edge v-u with u even,
an edge-minimal failing connected graph has a globally maximum one-defect
family rooted at v. The original reduction retained only one selected root;
the new statement retains the whole edge-restoration range.

The restoration lemma is stronger than the minimal-counterexample corollary:
if BOTH v and u have even degree in G, the even-degree induced graph of G is
acyclic, and G minus vu admits a k-path partition, then so does G. It needs
neither connectivity nor an exact Gallai budget. This follows from the
single-edge one-defect construction and QuotaParity's even-root repair.
Consequently, in an edge-minimal failing connected graph with an acyclic
even-degree induced graph, every even-even edge is a bridge. This is not a
proof for all even-forest graphs: odd roots of quota one remain unhandled.

A further possible consequence, not formalized here: if the even-induced
forest has a perfect matching, delete those matching edges to make the
whole graph all-odd, then restore them one at a time. At every intermediate
stage the even-degree set is a subset of the original even set, so the
restoration lemma applies. A matching-degree and forest-restriction induction
would be needed to formalize this case. It does NOT handle arbitrary
matching addition, nor even forests without such a matching.

One rejected shortcut from this continuation: independent zero-quota (or
even-degree) vertices do NOT normalize an arbitrary rooted one-defect
family below the vertex budget. On vertices 0,...,5 take
  P = 0-4-1-5-0-3; Q = 2-0-1.
The edge union has degrees (5,3,1,1,2,2), so its even vertices {4,5} are
independent. P has exactly one repeat, at its quota-one odd start 0, and Q
is a path. No two-path partition exists, since degree(0)=5. The one-defect
family is therefore a global maximum. This is NOT a Gallai counterexample:
n=6, so the allowed budget is three. The example is explained structurally,
not separately instantiated in Lean. It also fails the new edge-minimality
condition: deleting edge 14 preserves connectivity and leaves degree(0)=5.

Standalone build /tmp/edgecritical.log passes without warnings. Both
integration builds /tmp/work_edgecritical.log and /tmp/spec_edgecritical.log
pass; Spec's only warning is the original theorem's remaining sorry.
Standalone and integrated axiom audits (/tmp/edgecritical_audit.log and
/tmp/integrated_edgecritical_audit.log) pass with only propext,
Classical.choice, Quot.sound. The original theorem statement and import are
unchanged. No settlement, no purported disproof, and no proof submission.

## Even-forest matching restoration (verified)

EvenMatchingRestore.lean (166 lines) is integrated into Work and Spec under
EvenMatchingRestore. It proves the perfect-matching consequence proposed in
the preceding checkpoint, and a strictly broader deficiency-at-most-three
case. New APIs:
  even_forest_delete_even_edge
  matching_delete_endpoints
  restore_even_matching
  even_after_matching_iff
  even_forest_perfect_matching
  even_forest_matching_deficiency_le_three

General restoration statement: let F <= G be a matching supported entirely
on even-degree vertices of G, with G's even-degree induced graph acyclic.
If G minus F has a k-path partition, then G has a k-path partition. There is
NO connectivity assumption and NO Gallai-budget assumption in this lemma.
Proof is induction on |F.edgeSet|. Delete an edge vu of F. Both endpoints
become odd; every remaining matching endpoint is distinct from u and v and
keeps its even degree. The intermediate even-induced graph embeds into the
original forest. The residual double deletion has exactly the same graph
G minus F, so induction applies. Restore vu with EdgeCritical's even-even
restoration lemma. None of these steps requires the deleted graph connected.

The parity calculation identifies the remaining even vertices of G minus F
EXACTLY as the even vertices of G uncovered by F. If F covers all even
vertices, the existing all-odd theorem plus restoration yields
  2*|D| <= |V|.
If F leaves at most THREE even vertices uncovered, the existing few-even
case yields the requested ceil(|V|/2) bound. This latter case is now an
explicit branch of the original theorem. The graph G minus F may be cyclic,
and matching edges may join vertices in the same component of G minus F;
thus this is distinct from the forest-old-graph and intercomponent cases.

Limit: this is NOT the full even-forest theorem. A forest can have arbitrarily
large matching deficiency, including an arbitrarily large independent even
set. Nor does it prove the original proposed perfect-matching case without
the even-forest hypothesis. Endpoint quotas and simultaneous prescribed
avoidance are not claimed to be retained by the restoration procedure.

All builds and audits passed. Logs:
  /tmp/evenmatchingrestore.log
  /tmp/evenmatchingrestore_audit.log
  /tmp/work_evenmatchingrestore.log
  /tmp/spec_evenmatchingrestore.log
  /tmp/integrated_evenmatchingrestore_audit.log
All newly audited declarations use only propext, Classical.choice, Quot.sound.
Work has 21,249 lines and no gaps or warnings. Spec has 21,369 lines, original
theorem at line 21,273, and its one sorry at line 21,367. The statement and
sole import are unchanged. The final branch retains hcritical from the
preceding checkpoint, but the unrestricted defect-repair step is unproved.
No jobs remain running. No proof submission was made.

## Terminal weight is not a pivot invariant (new verified external obstruction)

Submission/TerminalPivotObstruction.lean is compiled and audited, but is NOT
inlined into Spec or Work: it rules out a naive invariant, without supplying
a new general-case proof. It imports only the existing gap-free Work module.

An explicit all-odd graph on eight vertices has the normal trail system
  P = 0-1-2-3-0-6;
  Q = 1-4-5-0-7;
  R = 2-5;
  S = 3-4.
The marked matching is F={14}. Its edge is triangle-free, and G minus F is
connected. At root 0 the closed tail is 0-1-2-3-0. The tail labelled 1 is
1-4-5-0. The standard pivot at label 1 replaces the changed members by
  P' = 1-2-3-0-6;
  Q' = 0-5-4-1-0-7,
leaving R,S unchanged. Both displayed systems have incidence score 14.
Edge 14, formerly terminal at endpoint 1, is now internal at BOTH endpoints.
The actual MatchingTrim.terminalWeight drops from one to zero.

Lean verifies both explicit NormalTrailSystem records (hence edge-disjoint
trail cover and endpoint bijections), the all-odd/triangle-free/connected
structural hypotheses, the local walk forms, equal score, the exact tables
of MatchingTrim.terminalVertices, and the drop in terminalWeight. All audited
constants use only propext, Classical.choice, Quot.sound.

IMPORTANT scope: this disproves automatic preservation by an arbitrary
pivot, NOT the existence of a suitable sequence of pivots or a global
terminal-weight selection theorem. These two systems are not unconstrained
score maxima (normal all-odd maxima are all paths). Indeed an explicit
marked-terminal path partition of the SAME graph is
  3-2-1-0-6; 1-4-5-0-7; 2-5; 0-3-4.
This follows by reversing the original closed prefix and using the other
exit. That last four-path list is recorded here for clarity, not separately
instantiated in the external module. No Gallai counterexample is claimed.

The obstruction also explains why whole-member or vertex-set tracking
cannot silently be promoted to terminal-edge tracking. A pivot changes the
heads of the root tail and of the pivot-labelled tail; a marked head in the
latter can become internal in the newly reversed closed root tail.

Build log: /tmp/terminalpivotobstruction.log. Audit module:
Submission/TerminalPivotAudit.lean; log /tmp/terminalpivot_audit.log.
Spec and Work were not modified in this continuation. Spec retains its one
original sorry at line 21,367. The unrestricted selection/defect-repair step
is still missing, and no proof submission was made. No jobs remain running.

## Cycle absorption does not give a one-unit terminal-loss budget

Revisited the idea of starting with marked matching edges as singleton
members and paying for cycle absorption out of their extra terminal weight.
No global invariant or proof was obtained, and Spec/Work were not changed.

The naive charge of one incidence defect per absorbed simple cycle is false.
For the six-cycle 0-1-2-3-4-5-0 and the marked chord 03, absorption into that
singleton gives the trail
  0-1-2-3-4-5-0-3,
which repeats BOTH 0 and 3: its length is seven and its vertex count six,
so its path-incidence defect is two. Add singleton chords 14 and 25 to make
an all-odd graph (K3,3), with the three chords a triangle-free matching and
their deletion the connected six-cycle. The resulting three-member normal
trail system has total score ten rather than the path maximum twelve.
This calculation is explanatory, not a new separately instantiated Lean
example. It agrees with the already verified intersection-sensitive
CycleRelocation identities. It is not a Gallai counterexample.

Also, MatchingTrim.terminalWeight uses degree-one vertices of member
subgraphs. On a trail with a repeated endpoint it is NOT automatically the
same as counting marked first and last walk edges. In this displayed trail
both chord endpoints have subgraph degree three, even though 03 is the last
walk edge. Thus a proof transporting the path-only trimming potential through
arbitrary trails needs an explicitly justified invariant, not an implicit
identification of those two notions of terminality.

The cycle-absorption/terminal-weight route still has no proved global
selection step. Spec remains at 21,369 lines with one sorry at line 21,367;
its statement and sole import are unchanged. No jobs are running and no
proof submission was made.

## Three-member defect transfer (verified and integrated)

Implemented the previously proposed local transfer in
Submission/ThreeTransfer.lean (241 lines), integrated under ThreeTransfer in
Work and Spec. No global existence of the exchange is asserted. APIs:
  quota_balance_one_slot
  relocate_nil_tracked
  hasRoot_of_append_rep
  merge_two_tracked
  split_nil_tracked
  three_member_transfer
  shared_endpoint_quota_le_two

The base exchange has weaker hypotheses than initially proposed: it needs
trail disjointness and the exact intersection cardinality, but not that the
two merged members are paths. For three distinct indices i,j,l, suppose:
  * member i is represented by r-x followed by p, with r in p.support;
  * finish(j)=start(l)=w;
  * member j is nonnil and start(j)=z lies on member l;
  * members j,l have exactly two common vertices.
There is then a new family U with:
  U.score=T.score;
  HasRoot U z;
  U.quota(v)+2*[w=v] = T.quota(v)+2*[x=v] for every v.

Construction, with endpoint tracking at every step:
  1. Append j to l and put a nil member at index j, based at w. This loses
     one incidence and preserves all quotas.
  2. Relocate that nil member to x. This preserves score, removes a quota
     pair at w, and adds a quota pair at x.
  3. Split the first edge of old member i into the nil slot. This gains one
     incidence and preserves all quotas.
The merged member is untouched by step 3. Its nonempty first portion and
repeated start z supply the HasRoot witness directly; this is not inferred
from an arbitrary internal repeated vertex.

If T minimizes quota-square energy among same-score ROOTED families, and
T.quota(x)=0, the exchange implies T.quota(w)<=2. Otherwise the verified
pair-energy identity yields a strict energy decrease. This conclusion does
not require edge minimality or the vertex budget, and it does not prove
that all surplus vertices satisfy the bound: availability of this specific
merge configuration is an explicit hypothesis. In a deficiency-one family,
j,l are automatically good paths when i is the defective member. Then the
second common vertex really must be an endpoint of the merged trail for
this rooted-minimum argument. Internal-intersection merges have not been
silently included.

Missing global step remains: a suitable merge pair (or a different global
augmentation) must be shown to exist in every edge-minimal Gallai failure.
Neither connectivity nor the exact member budget has supplied that step.
The verified exchange itself is NOT a proof of the conjecture.

Standalone and integrated builds and axiom audits passed:
  /tmp/threetransfer.log
  /tmp/threetransfer_audit.log
  /tmp/work_threetransfer.log
  /tmp/spec_threetransfer.log
  /tmp/integrated_threetransfer_audit.log
All audited new declarations depend only on propext, Classical.choice,
Quot.sound. Work is now 21,485 lines and gap-free. Spec is 21,605 lines;
the original theorem starts at 21,509 and its sole sorry is at 21,603.
The original statement and sole import are unchanged. No proof submission
was made, and no jobs remain running.

## Nonbridge even-incident core of an edge-minimal failure (verified)

Submission/NonbridgeCore.lean (161 lines) is compiled, audited, and integrated
under NonbridgeCore in Work and Spec. This is a graph-level strengthening of
the critical-failure reduction, not a new proof of the conjecture. APIs:
  repeated_first_edge_not_bridge
  exposed_edge_not_bridge
  two_zero_nonbridge_neighbors
  two_even_nonbridge_neighbors
  nonbridge_has_other_neighbor
  evenNonbridgeCore / evenNonbridgeCore_le
  core_no_dead_end
  core_not_acyclic
  exists_cycle_no_consecutive_odd
  core_endpoints_opposite_of_even_forest
  failure_has_critical_core_cycle

If a trail has first edge r-x and visits r again, r-x is a nonbridge:
the prefix of the tail up to r, reversed, is a walk from r to x avoiding
that edge. In particular, both of the earlier root-exposure edges are
nonbridges. The improved two-zero-neighbor theorem now records this fact.

In an edge-minimal connected failing graph, every nonbridge v-u with even
u admits a globally maximal rooted single-defect witness at v. Its two
zero-quota exposed neighbors x,y are even by quota parity, and the edges
v-x, v-y are nonbridges. Thus an odd vertex with one even nonbridge neighbor
has at least two such neighbors. This assertion is universal over all
eligible original nonbridge incidences, not only over one chosen family.

Define evenNonbridgeCore G by retaining exactly edges that are nonbridges
in G and have at least one endpoint of EVEN DEGREE IN G. In a critical
failure this core has no dead end:
  * At an even endpoint, any second nonbridge neighbor remains in the core;
    such a neighbor exists because the first nonbridge belongs to a cycle.
  * At an odd endpoint, use the two-even-neighbor result above.
The core is nonempty by failure_has_even_nonbridge. The finite no-dead-end
lemma therefore gives a cycle in the core. Mapping it to G produces an
actual simple cycle with no consecutive odd-degree vertices and with every
edge a nonbridge. This certificate is now retained in the main theorem's
last branch alongside hcritical, hscore, and hmin. The final pair of zero
neighbors also retains explicit nonbridge hypotheses.

LIMITS, relevant to the attempted even-forest direction:
If the critical graph ITSELF has an acyclic even-degree induced graph,
its even-even edges are bridges by EdgeCritical's previous result. Hence
the core's endpoints have opposite parity, so the new core cycles simply
alternate even and odd vertices. This is NOT contradictory: an alternating
cycle can exist while even vertices are independent. Taking a critical
spanning subgraph is still NOT known to preserve the original graph's
even-induced-forest condition. No full even-forest theorem or unrestricted
odd-root repair has been established.

Builds and audits passed; all new audited constants use only propext,
Classical.choice, Quot.sound. Logs:
  /tmp/nonbridgecore.log
  /tmp/nonbridgecore_audit.log
  /tmp/work_nonbridgecore.log
  /tmp/spec_nonbridgecore.log
  /tmp/integrated_nonbridgecore_audit.log
Work is now 21,642 lines, gap-free and warning-free. Spec is 21,764 lines;
the original theorem starts at 21,666 and has its sole sorry at 21,762.
Original statement and sole import unchanged. No proof submission was made.
No jobs remain running.

## Tracked edge insertion and deletion-side endpoint obstructions (verified)

Submission/DeletionEndpoint.lean (273 lines) is now integrated into Work and
Spec under DeletionEndpoint. It strengthens the existing single-edge append
construction and the even-forest restoration criterion. APIs:
  quota_balance_one_slot_graphs
  append_new_edge_tracked
  quota_pos_of_endpoint / endpoint_of_positive_quota
  deletion_endpoint_must_meet
  restore_if_other_endpoint_active
  failed_even_forest_deletion_quota_zero
  restore_if_other_endpoint_member
  failed_deletion_card_eq

append_new_edge_tracked appends a genuinely new edge v-u at an existing
endpoint u of one path in an indexed path family. It returns the previous
score bound and rooted-defect conclusion, PLUS:
  U.quota(x)+[u=x] = T.quota(x)+[v=x] for every x;
  if the chosen original path avoids v, all new members are paths.
The proof tracks the initial orientation, every unchanged endpoint slot,
and the graph inclusion explicitly. Nil members are allowed and their two
endpoint slots are counted correctly.

New restoration criterion (no connectivity or exact-budget hypothesis):
Suppose the even-degree vertices of G induce a forest, u is even in G,
and v-u is an edge. A k-path family of G-(v-u) whose quota at v is positive
can be extended to a path partition of G with at most k members. Deletion
makes u odd, so an endpoint at u is available. Appending v-u transfers one
slot from u to v. If this is not already a path partition, the result has
exactly one rooted defect, with quota at v at least two. The existing
forest-zero normalization then repairs it. Only u, not both ends of the
restored edge, is required to be even in G.

The finite-subgraph version uses the concrete certificate that some member
of the deletion partition has neighbor-set cardinality one at v. No
endpoint-activation or endpoint-selection theorem is silently assumed.
In particular, if an even-forest graph were to fail the k-path bound, EVERY
k-slot path family after this eligible deletion would have quota ZERO at v.
This is a universal inactivity consequence, not a proof that it is impossible.

Without ANY parity or forest hypothesis, failure of the k bound implies:
  * every member ending at u in every k-path family of G-(v-u) contains v;
  * any finite deletion partition with at most k members uses exactly k.
Otherwise appending the edge directly, or restoring it as a new singleton,
would meet the budget. The universal path-containment condition is now
retained as hdeletionBlocked in the main theorem's final critical branch.

The attempted cycle-deletion shortcut remains unavailable. Individual edges
of the new core cycle being nonbridges does not justify deleting the whole
cycle while retaining connectivity. Nor do the recorded fixed-baseline
obstructions allow unrestricted cycle restoration. No claim has been made
that either issue is resolved. The original unrestricted repair/selection
step is still missing; even the full even-induced-forest theorem has not
been proved in this development. Its new endpoint-activity certificate is
not asserted to be always available.

All standalone/integrated builds and axiom audits passed. Logs:
  /tmp/deletionendpoint.log
  /tmp/deletionendpoint_audit.log
  /tmp/work_deletionendpoint.log
  /tmp/spec_deletionendpoint.log
  /tmp/integrated_deletionendpoint_audit.log
All newly audited constants use only propext, Classical.choice, Quot.sound.
Work is 21,910 lines, gap-free and warning-free. Spec is 22,038 lines, with
the original theorem at 21,934 and its sole sorry at 22,036. The conjecture
statement and sole import are unchanged. No proof submission was made.
No jobs remain running.

## Internal defects do not admit fixed-quota forest normalization (verified externally)

Submission/InternalDefectObstruction.lean is compiled and audited, but is NOT
integrated in Spec: it is a strategy obstruction, not a new conjecture case.
Its generic path_family_cut_bound allows nil slots and states, for v outside S:
  degree(v)+quota(v)+sum quota(S) <= 2*k + boundary(S).

An explicit connected graph on 12 vertices has edges
  07,01,12,20,06,13,30,04,45,78,89,9-10,10-11.
The six nonempty trails
  7-0-1-2-0-6; 1-3-0-4-5; 7-8; 8-9; 9-10; 10-11
have exactly one INTERNAL defect (at 0), normal endpoint quotas
  [0,1,0,0,0,1,1,2,2,2,2,1],
and no repetitions at any positive-quota vertex. The zero-quota induced graph
is a star. The entire even-degree induced graph is a tree.
Nevertheless no path family with six slots can preserve these quotas:
  degree(0)=6, quota(0)=0,
  sum quota({7,8,9,10,11})=9, boundary({7,8,9,10,11})=1,
so the cut bound would require 15 <= 13.
The family is therefore maximum-score SUBJECT TO THOSE QUOTAS. There is not
even a rooted one-defect realization of the same quotas: the rooted cut
bound forces root 0, whose quota is zero, contrary to root_quota_pos.

This does NOT obstruct unconstrained global maximization, and is NOT a
Gallai counterexample. A kernel-verified three-path partition is included:
  11-10-9-8-7-0-3-1-2; 2-0-6; 1-0-4-5.

Motivating rejected route: splitting off a leaf even vertex in the even-induced
forest preserves other degree parities, but a reduced path may contain several
of the added matching edges. Lifting these through one vertex creates INTERNAL
repetitions. The above example precludes invoking fixed-quota forest
normalization without a root hypothesis. A compatible matching-dispersion
lemma would be needed, and has NOT been assumed or proved. There is also an
independent simplicity issue if paired neighbors were already adjacent.

Build: /tmp/internaldefectobstruction.log
Audit: /tmp/internaldefectobstruction_audit.log
All audited declarations use only propext, Classical.choice, Quot.sound.
The original Spec still has one sorry at line 22036; its statement and sole
import are unchanged. No submission was made.

Additional identification idea (not a proof): identifying two nonadjacent even
vertices with disjoint neighborhoods preserves simplicity and creates one even
vertex in place of two. But lifting a simple path through the identified vertex
splits it if its incident edges belong to different original vertices. Several
paths can be mixed in this way, despite each visiting the identified vertex only
once. For example, take a six-cycle with opposite even vertices 0 and 3 and
attach leaves at its four other vertices. After identification the graph is two
triangles at a common degree-four vertex, with leaves at the other four vertices.
A four-path partition can pair the two sides crosswise twice, requiring two
splits on lifting. Another partition pairs within sides and lifts successfully;
therefore this is only an obstruction to lifting an ARBITRARY partition.
A compatible transition-pairing theorem is still needed; no new general case
has been claimed from vertex identification.

## Exact bridge gluing and global smallest-order reduction (verified)

New standalone files BridgeGlue.lean and VertexCritical.lean are compiled,
audited, and integrated in Work/Spec under BridgeGlue and VertexCritical.

BridgeGlue supplies exact combinatorial gluing, without assuming endpoint
selection. If a single-edge cut separates S and its complement, augment each
side by the opposite endpoint of the bridge. That endpoint is a leaf in the
augmented side. In any path decomposition its bridge-containing member can be
oriented from the leaf. The two selected members glue along their common edge
to ONE simple path; all other members survive. The resulting count satisfies
  new.card + 1 <= left.card + right.card.
The selected members are allowed to be singleton bridge edges, including both
being the same singleton. Nil members elsewhere cause no problem.

The proof includes general partial-partition merging, spanning-side gluing,
conversion between induced and spanning-with-isolates graphs, and connectivity
of each augmented side. The latter collapses the opposite side to its pendant
vertex, mapping every old edge to either a walk edge or a nil walk.

For side orders a,b, using the two Gallai budgets gives
  ceil((a+1)/2)+ceil((b+1)/2)-1.
This meets ceil((a+b)/2) when at least one side has odd order. For TWO EVEN
SIDES it is exactly one too large. Both arithmetic facts are verified. Thus
there is still NO blanket reduction to bridgeless graphs.

VertexCritical chooses a globally smallest-order connected failure on Fin n,
using equivalence invariance to represent the original arbitrary finite type.
SmallerOrders n asserts the conjectured bound for EVERY connected graph on
fewer vertices. It applies on arbitrary finite types and, in particular, to
proper induced subgraphs. The existing spanning edge-minimal reduction is
then applied to this smallest-order witness. Crucially, SmallerOrders remains
valid after arbitrary spanning edge deletion because it was chosen GLOBALLY
by order, not by a parity-preserving inheritance argument.

For such a minimal failure, every bridge gives a cut with either:
  * one side of order one; or
  * both sides of even order.
A one-vertex side makes its endpoint degree one. Consequently, in ODD order,
every bridge is a leaf edge. Even-even bridge cuts and leaf edges remain
possible; they have NOT been excluded.

The original theorem's final branch now first obtains n,J,hsmall, then its
edge-minimal spanning failure H on Fin n. All subsequent rooted-defect and
quota arguments use the budget for Fin n, not the original vertex type V.
The final branch retains hproperInduced, hbridgeStructure, and hbridgeParity
alongside the earlier criticality and deletion-endpoint obstructions. The
original theorem STATEMENT and sole import are unchanged. The final global
augmentation step still has a sorry; no settlement or submission is claimed.

Standalone builds/audits:
  /tmp/bridgeglue.log, /tmp/bridgeglue_audit.log
  /tmp/vertexcritical.log, /tmp/vertexcritical_audit.log
Integrated builds/audit:
  /tmp/work_bridgeglue.log, /tmp/spec_bridgeglue.log
  /tmp/integrated_bridgeglue_audit.log
All audited new declarations use only propext, Classical.choice, Quot.sound
(or no axioms). Work is gap-free; Spec retains only the original theorem gap.

## Smallest odd-order failures are bridgeless (verified)

LeafReduction.lean is compiled, audited, and integrated under LeafReduction.
It uses the new global order minimality, without strengthening the original
conjecture or assuming endpoint flexibility.

- delete_leaf_connected: deleting a leaf vertex leaves the induced graph
  connected (the other endpoint witnesses nonemptiness).
- within_delete_leaf: retaining the induced complement of that leaf on the
  old vertex type is exactly deletion of its one incident edge.
- restore_deleted_leaf: a decomposition after removing the leaf vertex lifts
  and extends with at most one new singleton-edge member.
- no_leaf_of_odd_failure: if n is odd, the budget for n-1 vertices plus one
  is exactly the budget for n. Hence a smallest-order odd failure has no leaf.
- bridgeless_of_odd_failure: combine this with bridge_even_order_or_leaf.
  The original theorem's final branch now retains hoddBridgeless.

The restriction to ODD order is essential here. In even order, the same
one-edge restoration exceeds the budget by one. Neither even-even bridge
cuts nor leaf edges in a smallest even-order failure have been ruled out.
The global rooted-defect augmentation is still not proved.

Builds/audits:
  /tmp/leafreduction.log, /tmp/leafreduction_audit.log
  /tmp/work_leafreduction.log, /tmp/spec_leafreduction.log
  /tmp/integrated_leafreduction_audit.log
Only the permitted axioms occur in all audited new helpers. The standalone
LeafReduction module has 91 lines. Spec and Work compile, with only Spec's
original theorem sorry warning. No incomplete submission has been made.


Latest integrated checkpoint: Spec has 22,666 lines; the unchanged original
theorem starts at 22,552 and its one sorry is at 22,664. Work has 22,528 lines
and no gaps. BridgeGlue has 429 lines, VertexCritical 112, LeafReduction 91.
The sole Spec import remains FormalConjecturesUtil. All builds and the full
integrated audit passed; no jobs are running and no proof was submitted.

Possible next reduction, not yet formalized: suppress a degree-two vertex u
with neighbors a,b by replacing its two edges with ab on the n-1 other
vertices. If ab was absent, the existing expand_edge theorem lifts a bounded
partition without increasing its count. If ab was already present, deleting
u leaves a connected graph (replace excursions through u by ab), and restoring
a-u-b costs at most one path; this meets the budget when n is odd. Connectivity
of the suppressed graph can be proved by collapsing u to a and mapping each
edge to either a walk edge or a nil walk. Thus global order minimality should
force every degree-two vertex of any minimal failure to lie in a triangle,
and rule out degree two entirely in odd order. This uses an actual simple-edge
expansion, not the rejected general matching splitting-off normalization.
No such low-degree conclusion has yet been inserted into Lean.

## Degree-two suppression in a smallest-order failure (verified)

DegreeTwoReduction.lean is compiled, audited, and integrated under
DegreeTwoReduction. It uses SmallerOrders from the preceding checkpoint.

Define bypass G u a b to retain G on V minus u and add the simple edge a-b.
If u has exactly the two neighbors a,b, its induced graph on V minus u is
connected: collapse u to a, send u-a to a nil walk and u-b to the new edge.

Given a decomposition of that smaller graph, restore_bypass lifts it back:
  * if a-b was NOT an old edge, expand the new edge to a-u-b, no count increase;
  * if a-b WAS present, restore a-u-b as a new path, count increase at most one.
The second case is NOT silently treated as a zero-cost expansion.

Consequently, every degree-two vertex in a globally smallest-order failure
has adjacent neighbors, and the order of the failing graph is even. There
are no degree-two vertices in odd order. Combining the previously proved
leaf exclusion with connectedness gives odd-order minimum degree at least
three. The actual main theorem retains hdegreeTwo for its edge-minimal
smallest-order witness H; the subsequent cubic reduction strengthens the
odd-order degree bound further.

Logs: /tmp/degreetworeduction.log, /tmp/degreetworeduction_audit.log,
/tmp/work_degreetwo.log, /tmp/spec_degreetwo.log.

## Cubic vertices excluded from smallest odd-order failures (verified)

DegreeThreeReduction.lean is compiled, audited, and integrated under
DegreeThreeReduction. The conclusion is conditional on ODD order; no
corresponding even-order exclusion is claimed.

Connectivity infrastructure:
  * A nonbridge edge u-a supplies another neighbor b != a reachable from a
    without u. Take a simple u-a path avoiding u-a; its first edge is u-b,
    and its remaining suffix avoids u.
  * If u has degree at most three and all its incident edges are nonbridges,
    all its neighbors are mutually reachable without u. Otherwise two
    neighbor components, each of size at least two, would give four neighbors.
  * Collapse u to one chosen neighbor and map old edges to walks. This proves
    that deleting u preserves connectivity. Nil walks are handled explicitly.

Restoration infrastructure:
  * isolated_mem_support and append_at_odd_to_isolated: a path endpoint forced
    by odd degree can receive a new edge to an isolated vertex, with NO member
    count increase. The avoidance of the new vertex is proved, not assumed.
  * within_neighbor_add_one and delete_edge_neighbor_add_one track the exact
    degree change after deleting a vertex/edge.
  * restore_degree_three: if u has neighbors v,a,b and v is even in G,
    deleting u makes v odd. Append u-v to its endpoint path; restore a-u-b
    as one extra path. Total cost is at most one.
  * restore_path_at_odd_leaf gives a general version: after deleting a simple
    path P, if u is a leaf at v and v is odd in the graph with u removed,
    append u-v first and restore P, total cost at most one.

Excluding a cubic vertex u in a smallest ODD-order failure:
  1. The graph is bridgeless, so deleting u preserves connectivity.
  2. If any neighbor is even, restore_degree_three contradicts failure.
     Thus all three neighbors would have to be odd.
  3. If a pair a,b of its neighbors is nonadjacent, delete its edge to the
     third neighbor v (a nonbridge), suppress the remaining degree-two u,
     and apply SmallerOrders. Expand a-b back to a-u-b, then restore u-v
     as one extra edge path. This also meets the odd-order budget.
     Hence the three neighbors would have to form a triangle.
  4. Delete u and a neighbor edge a-b. The smaller graph stays connected:
     in G-u, the third neighbor v witnesses that a-b is a nonbridge.
     Vertex a was odd and has lost exactly two incident edges, so it is still
     odd in this smaller graph. Append the fresh edge a-u to its endpoint path.
     Restore the simple path a-b-u-v as ONE extra member. These four edges
     are precisely the missing edges; all vertices of that path are distinct.
     Again the count is at most ceil((n-1)/2)+1 = ceil(n/2).
Thus no cubic vertex remains. The final theorem branch now retains
  hoddMinDegree : Odd n -> forall u, 4 <= Nat.card (H.neighborSet u)
as well as hoddBridgeless, hdegreeTwo, hsmall, hcritical, and the preceding
rooted-defect obstruction data.

The two new modules are genuine reductions, NOT a proof of the general
conjecture. Smallest even-order failures can still have leaf edges and
triangular degree-two vertices. Smallest odd-order failures of minimum degree
at least four remain unresolved. No unrestricted splitting-off compatibility,
endpoint selection, or rooted-defect augmentation is assumed.

Logs: /tmp/degreethreereduction.log, /tmp/degreethreereduction_audit.log,
/tmp/work_degreethree.log, /tmp/spec_degreethree.log,
/tmp/integrated_degreethree_audit.log. All audited constants use only the
permitted axioms (some use fewer). Work is gap-free and warning-free;
Spec has only the original theorem's sorry warning. No submission was made.

Latest low-degree checkpoint: Spec has 23,365 lines, original theorem at
23,247, and its sole sorry at 23,363. Work has 23,223 lines and no gaps.
DegreeTwoReduction has 219 lines; DegreeThreeReduction has 485 lines.
The theorem statement was compared with the pre-edit version and is exactly
unchanged. The only import in Spec remains FormalConjecturesUtil. Full
integrated axiom audit passed. No jobs remain running and no submission was made.

Possible degree-four direction, NOT formalized: replacing two disjoint
nonedges among a degree-four vertex's neighbors can lift any reduced path
partition with at most one extra path. If both added edges are in the same
old path, split that path at one of the added edges before expanding the
other; this prevents an internal repetition at the restored vertex. If
in different paths, expand each independently. Connectivity and cases where
some neighbor pairs are already edges still require proofs. Do not replace
this two-edge argument with unrestricted fixed-quota normalization.

In particular, the stronger auxiliary claim that lifting r disjoint edges
through one new vertex increases path number by at most one whenever k>=r
is FALSE. Take K6, subdivide its edge a-b into the five-edge chain
  a-c-d-e-f-b.
This ten-vertex graph H has a three-path partition (expand a-b in a K6
Hamilton-path partition). The three marked edges a-c, d-e, f-b are disjoint.
Replace them by their six spokes to a new vertex u. The result G is K6 with
edge a-b subdivided by u, together with triangles u-c-d-u and u-e-f-u.
It has eleven vertices, and requires at least five paths: the six old K6
vertices are odd, and each pendant triangle needs two endpoint incidences
in its two nonattachment vertices. It also has five paths, by the three
expanded core paths plus c-u-e and c-d-u-f-e. Thus k=r=3 but p(G)=5>k+1.
This is an informal exact strategy obstruction, not a Gallai counterexample:
ceil(11/2)=6. It does not refute a lifting statement with the EXACT VERTEX
BUDGET, and it does not affect the verified one-edge suppression proofs.

## Degree-four vertices excluded from smallest odd-order failures (verified)

DegreeFourReduction.lean (351 lines) is compiled, audited, and integrated under
DegreeFourReduction. Its main conclusion is
  min_degree_five_of_odd_failure : Odd n -> forall u, 5 <= degree(u)
under SmallerOrders n, connectedness, and failure at the exact vertex budget.
The main theorem now retains this stronger bound in hoddMinDegree.

The proof does NOT lift two marked edges simultaneously:
  * suppress_after_path deletes ONE simple path P, suppresses a remaining
    degree-two vertex u when its neighbors a,b are nonadjacent in G-P, and
    restores P. The cost is at most one, fitting the odd-order budget.
  * If G-u is connected and u has degree four, a nonadjacent neighbor pair
    a,b can be suppressed after deleting the other two spokes c-u-d.
    Consequently a failure would have a complete neighborhood at u.
  * In a complete neighborhood choose distinct a,b,c,d and delete the path
      b-a-c-u-d.
    The remaining two spokes are u-a,u-b; edge a-b has been deleted, so
    suppression is fresh. The bypass induced on V\{u} is precisely
      (G-u) - edge(a,c).
    This graph is connected because a-b-c is an alternate route for a-c.
    Expansion and restoration again cost only one path. In fact the local
    lemma needs just the triangle a-b-c among the neighbors, not all six
    neighbor edges, once deletion of u is connected.
  * If G-u is disconnected, choose two neighbors a,b in different components.
    Bridgelessness supplies distinct partners c,d linked to a,b without u.
    All four are distinct and exhaust N(u); thus they cover all the neighbor
    components. Adding a-b to G-u makes it connected, and a-b is absent in G.
    The same two-spoke deletion/suppression applies.

Reusable connectivity lemmas include connected_of_neighbor_cover,
connected_of_delete_vertex, bypass_connected_of_neighbor_cover, and
within_induce. No even-order degree-four exclusion is asserted.

Standalone and integrated audits passed with only propext, Classical.choice,
Quot.sound. Logs: /tmp/degreefourreduction.log,
/tmp/degreefourreduction_audit.log, /tmp/work_degreefour.log,
/tmp/spec_degreefour.log, /tmp/integrated_degreefour_audit.log.

## No cut vertex in a smallest odd-order failure (verified)

CutVertexReduction.lean (439 lines) is compiled, audited, and integrated under
CutVertexReduction. The main theorem now retains
  hoddDeleteVertex : Odd n -> forall u, (H.induce {u}^c).Connected.
This is in addition to the degree-five lower bound and bridgelessness.
It is still conditional on ODD order.

Endpoint flexibility here is justified by a strictly smaller augmentation:
  * project_leaf_family projects any path family in a pendant completion,
    preserving its indexed member count and projecting its endpoints.
  * project_single_leaf_marked projects a decomposition after adding one
    leaf at u and supplies a member represented by a path STARTING at u.
    The marked path is allowed to be NIL. This is necessary when the leaf
    edge was a singleton member, and incurs no false nonemptiness assumption.
  * smaller_order_marked applies SmallerOrders to the one-leaf augmentation;
    it gives a marked partition with budget ceil((m+1)/2) for an m-vertex
    connected side. It does NOT assert prescribed endpoints at ceil(m/2)
    in even order.
  * merge_disjoint_partitions and glue_induced_sides glue the marked members
    at u, saving one path. They cover nil marked paths, including when BOTH
    are the same nil path at u. Finset collisions only reduce cardinality.

For two connected induced sides meeting exactly at u, with orders a,b >=2,
  a+b=n+1.
If n is odd, a and b have the same parity:
  * both even: simply union their smaller-order partitions; the budgets sum
    to ceil(n/2), with no endpoint assumption;
  * both odd: each is at least three, so each one-leaf augmentation has order
    STRICTLY LESS than n. Its bound ceil((a+1)/2)=ceil(a/2), and similarly
    for b. The marked gluing saves the one path required by the sum.
The single_boundary_budget theorem formalizes this split.

single_boundary_connected proves side connectivity by collapsing the other
side to u. Finally, if deleting u disconnected a smallest odd failure,
choose neighbors a,b not connected without u, take S to be u together with
all vertices reachable from a without u, and apply single_boundary_budget
on S and insert u S^c. Both sides have at least two vertices. This gives the
contradiction, independently of any unjustified endpoint selection.

All standalone and integrated audits passed with only the permitted axioms.
Logs: /tmp/cutvertexreduction.log, /tmp/cutvertexreduction_audit.log,
/tmp/work_cutvertex.log, /tmp/spec_cutvertex.log,
/tmp/integrated_cutvertex_audit.log.

Current checkpoint: Spec has 24,155 lines; the unchanged original theorem
starts at 24,035 and its SOLE sorry is at 24,153. Work has 24,011 lines,
no gaps, and no warnings. Spec has exactly the original-conjecture warning.
Its sole import remains FormalConjecturesUtil. No jobs remain running.
The general conjecture is NOT settled and no proof submission was made.

Remaining limitations: the smallest odd-order witness may still be a
vertex-deletion-connected graph of minimum degree at least five. The even
order reductions still permit leaf edges, even-even bridge sides, and
triangular degree-two vertices. There is no proved global augmentation,
terminal-weight selection, or exact-budget compatibility result closing
these possibilities. Do not infer the even-order version of the cut-vertex
lemma from the odd-order proof: its side parity arithmetic is different.

## Bridge endpoints in a smallest-order failure are odd (verified)

BridgeParityReduction.lean (193 lines) is compiled, audited, and integrated
under BridgeParityReduction. This reduction applies in BOTH order parities:
  bridge_endpoints_odd_of_failure
  even_vertex_no_bridge_of_failure.
The final main branch retains hbridgeEnds and hevenNoBridge for its witness H.

For a bridge u-v with u even, let S be the u-side of the bridge cut.
  * within_bridge_neighbor_add_one proves the degree at u on S is one less
    than its ambient degree. Thus u is ODD on that side and must be an
    endpoint of some path of every path partition of the side.
  * The opposite endpoint v is isolated in within G S. Extending at u by
    the bridge u-v therefore costs ZERO additional paths. This uses the
    verified append_at_odd_to_isolated, including its avoidance proof.
  * S has at least two vertices: if it were a singleton, u would have
    degree one in G, contrary to its even degree. Consequently, the other
    augmented side (S^c plus u) has strictly fewer than n vertices, even
    when S^c itself is a singleton leaf side.
  * Apply SmallerOrders to S and to insert u S^c, extend the first side,
    and glue the two bridge-containing paths with a saving of one member.
    If the side orders are a,b, the bound is
      ceil(a/2) + ceil((b+1)/2) - 1 <= ceil((a+b)/2).
    This holds in ALL parity cases. No endpoint was prescribed in an
    arbitrary even-order partition of the opposite side.
Thus an even endpoint of a bridge contradicts smallest-order failure.
Both bridge endpoints must therefore be odd. This does not rule out all
bridges in even order: odd-odd bridges and odd-degree leaf neighbors remain.

Additional explicit-hypothesis corollary:
  even_forest_independent_of_failure.
If the chosen smallest-order, edge-minimal witness H itself has an acyclic
induced even-degree graph, its even vertices are independent. The earlier
EdgeCritical theorem makes any even-even edge a bridge, while the new
parity result forbids that bridge. The main branch retains this as
hcriticalEvenIndependent, conditional on the hypothesis for H itself.
This is NOT a proof that an even-forest condition is inherited under
arbitrary spanning edge deletion, nor a proof of the full even-forest case.

Builds and standalone/integrated axiom audits passed; all audited helpers
use only propext, Classical.choice, Quot.sound. Logs:
/tmp/bridgeparityreduction.log, /tmp/bridgeparityreduction_audit.log,
/tmp/work_bridgeparity.log, /tmp/spec_bridgeparity.log,
/tmp/integrated_bridgeparity_audit.log.

Two informal cautions from this continuation, not used as Lean assumptions:
  * Suppressing a subdividing vertex can INCREASE the minimum path number.
    K5 minus edge 03 has nine edges and needs three paths. Subdivide edge12
    by new vertex5. The resulting graph has the two-path partition
      5-1-4-3-2-0; 5-2-4-0-1-3.
    Thus arbitrary contraction/suppression is not count-nonincreasing.
    This does NOT challenge Gallai: its budgets are three in both orders.
  * Even an INDUCED matching in an all-odd graph cannot in general be made
    terminal at independently prescribed ends. Start with two K2,3 graphs,
    join one degree-three core vertex from each by an edge, and attach one
    leaf to each of those two core vertices. The six degree-two vertices
    are independent and all remaining vertices are odd. Add a matching
    between the three degree-two vertices in opposite copies to make the
    whole graph all-odd; that matching is induced. If all three added edges
    were terminal at their ends in the first copy, projection would make
    its three degree-two vertices inactive. Its other core vertex has
    degree three and endpoint quota one, hence lies in only two paths;
    the three inactive degree-two routes between the core vertices would
    have to lie in three distinct simple paths, impossible. Unoriented
    simultaneous terminality is NOT refuted by this example, and remains
    unproved here. This is only a strategy obstruction, not Gallai.

Latest bridge-parity checkpoint: Spec has 24,356 lines, the original theorem
starts at 24,227, and the sole sorry is at 24,354. Work has 24,203 lines and
no gaps or warnings. The original statement was compared explicitly with
the task statement and is unchanged, as is the sole FormalConjecturesUtil
import. All new standalone and integrated audits passed. No jobs remain
running and no proof submission was made: the general conjecture is still
unresolved.


## Sharp one-even partitions and marked bridge-side budgets (verified)

MarkedBudgets.lean (319 lines) is compiled, axiom-audited, and integrated under
MarkedBudgets in Work and Spec. All fourteen standalone and integrated
lemma audits use only propext, Classical.choice, Quot.sound.

* normal_odd_endpoint_eq_one records the parity consequence of normality.
* one_even_path_partition: when precisely one specified vertex v is even,
  there is a nonempty-member normal path partition with endpoint multiplicity
  zero at v, one everywhere else, and 2*|D|+1=|V|. Connectivity is not needed.
  This correctly includes the singleton edgeless graph.
* few_even_marked: for a connected nontrivial graph with at most three even
  vertices, any specified vertex can be the start of a marked member in a
  ceiling-budget partition. If that vertex is odd, parity supplies an
  endpoint. If it is even and another even vertex exists, choose the latter
  as the sole inactive vertex. With no other even vertex, activate the
  inactive vertex at a cost of one, still within the ceiling bound.
* forest_marked: the same marked ceiling budget holds for connected forests.
  Splitting at an inactive specified vertex costs one; the strict deficit in
  the number of odd vertices pays for that split.

No general marked-endpoint theorem is claimed. The marked walk is permitted
  to be nil, as required by existing gluing interfaces.

Tracked infrastructure:
  map_decomposition_tracked, lift_induce_marked,
  endpoint_of_path_rep, append_marked_to_isolated,
  extend_marked_bridge_side.
In particular, endpoint_of_path_rep handles a nil path as well as nonempty
paths. append_marked_to_isolated extends a marked path by one edge toward a
fresh isolated vertex, with no increase in the number of members.

gallai_of_marked_bridge_side applies the extension on one side S of a bridge
and SmallerOrders to the opposite side augmented by the endpoint in S.
The condition |S|>=2 ensures that augmented side is strictly smaller than n.
Glue the two bridge-containing paths with a saving of one. The same parity
inequality used in BridgeParityReduction gives the full ceiling budget.

Consequences for a smallest-order failure:
  failure_cut_side_many_even,
  failure_cut_side_not_acyclic,
  failure_bridge_side_structure.
EVERY non-singleton side of EVERY bridge is cyclic and has at least FOUR
vertices whose degrees IN THAT INDUCED SIDE GRAPH are even. Ambient parity
must not be substituted for this internal parity. The main unresolved branch
now retains this fact as hbridgeSidesComplex.

Logs: /tmp/markedbudgets.log, /tmp/markedbudgets_audit.log,
/tmp/work_markedbudgets.log, /tmp/spec_markedbudgets.log,
/tmp/integrated_markedbudgets_audit.log. Work compiles without warnings;
Spec has only the original-conjecture sorry warning.

Current checkpoint: Spec has 24,677 lines; the unchanged conjecture begins at
24,546 and its only sorry is at 24,675. Work has 24,522 lines with no gaps.
The sole Spec import remains FormalConjecturesUtil. All statements and
imports were checked explicitly after integration. No proof submission has
been made: the original conjecture is STILL UNRESOLVED.

A further review of endpoint selection did not close the gap. In particular,
the singleton-token cycle obstruction requires an actual singleton-edge
member in a maximal NORMAL EULERIAN partition. There is no established
argument producing the required member or the required inactive-set bound in
general. The existing counterexamples to endpoint-basis exchange and to
unrestricted fixed-quota internal-defect normalization remain relevant.

## At most two leaves in a smallest failure (verified)

LeafPairReduction.lean (322 lines) is compiled, audited, and integrated under
LeafPairReduction in Work and Spec. All eleven lemmas use only the permitted
axioms. The central result applies in BOTH order parities:
  at_most_two_leaves_of_failure.
The final main branch retains hleafCount and hleafNeighbors.

The more precise structural result is leaf_neighbors_bridge_of_failure:
for any two distinct leaves u,v, their respective neighbors a,b are DISTINCT
and a-b is a BRIDGE. This immediately rules out three leaves, because their
three distinct neighbors would form a triangle of alleged bridges.

Proofs of the three two-leaf reductions:
* common_neighbor_reduction: if a=b, remove the leaves and restore the path
  u-a-v at a cost of one. Removing two vertices reduces the ceiling budget
  by exactly one in either parity.
* leaf_neighbors_nonadjacent_reduction: when a,b are distinct and nonadjacent,
  remove u,v and add the fake edge a-b. The remaining induced graph is
  connected. Apply SmallerOrders. In the larger graph temporarily containing
  the extra edge u-v, expand a-b to a-u-v-b at ZERO path cost (fresh internal
  vertices). Delete u-v at a cost of at most one. This yields the original
  graph. No simultaneous endpoint marking or two-edge lifting is assumed.
* leaf_neighbors_nonbridge_reduction: if a-b is present and not a bridge,
  delete u,v and a-b. The remaining induced graph is connected because
  G-(a-b) is connected and deleting leaves preserves connectivity. Restore
  u-a-b-v as one path.

Auxiliary APIs:
  leaf_data, delete_two_leaves_connected, two_leaves_edge_cover,
  two_removed_budget, two_removed_lt, leaf_neighbor_not_leaf_of_failure.
The last result handles the adjacent-leaves degeneracy separately: if two
leaves are adjacent in a connected graph, all vertices lie in that pair,
so the existing subcubic theorem applies. Thus the four vertices in the
nonadjacent-neighbor construction really are distinct.

Standalone/integrated logs:
  /tmp/leafpairreduction.log, /tmp/leafpairreduction_audit.log,
  /tmp/work_leafpair.log, /tmp/spec_leafpair.log,
  /tmp/integrated_leafpair_audit.log.
All passed. The standalone proof does not import the new namespace recursively;
it imports the earlier Work checkpoint. After integration it still builds.

This does NOT prove Gallai for every graph with three leaves: the use of
SmallerOrders is essential. Nor does it rule out a smallest failure with zero,
one, or two leaves.

## Cubic leaf neighbors and the two-leaf degree bound (verified)

LeafCubicReduction.lean (143 lines) is compiled, audited, and integrated under
LeafCubicReduction. All four lemmas use only the permitted axioms.
  leaf_cubic_nonedge_reduction
  leaf_cubic_triangle_of_failure
  leaf_cubic_no_other_bridge_of_failure
  two_leaf_neighbors_degree_ge_five

If u is a leaf at a cubic vertex v, with other neighbors a,b nonadjacent,
remove u and v and add a-b. This preserves connectivity of the nonisolated
part; support cardinality decreases by at least two. Apply SmallerOrders
to that support. Expand a-b to a-v-b at zero cost and restore v-u as one
path. This gives Gallai in BOTH order parities.

Consequently a cubic neighbor of a leaf in a smallest failure must lie on a
triangle with its other two neighbors. Neither of those two edges is then
a bridge. In the two-leaf situation, LeafPairReduction supplies a bridge
between the parents; BridgeParityReduction says each parent is odd; neither
parent is itself a leaf; and the cubic possibility is now excluded. Hence
BOTH leaf parents have degree at least FIVE. The final main branch retains
hleafCubic and htwoLeafDegree.

Logs: /tmp/leafcubicreduction.log, /tmp/leafcubicreduction_audit.log,
/tmp/work_leafcubic.log, /tmp/spec_leafcubic.log,
/tmp/integrated_leafcubic_audit.log. All builds and audits passed. Work has
no warnings or gaps; Spec has only the original-conjecture sorry warning.

Checkpoint: Spec has 25,154 lines, with the unchanged original theorem at
25,011 and its sole sorry at 25,152. Work has 24,987 lines and no gaps.
The original statement and sole FormalConjecturesUtil import were explicitly
rechecked. The general conjecture is STILL UNRESOLVED; no submission was made.

Rejected preliminary shortcut in this continuation: connectivity together
with degree(u)<2*k does NOT imply that u can be an endpoint of a k-path
partition. Take a tree with four leaves and a subdivided edge, k=2, and let
u be the subdividing vertex. All four endpoint slots are forced to the four
leaves by parity, although degree(u)=2<4. This is below the exact vertex
budget and does not refute marked flexibility at that budget; that stronger
claim remains unproved. No numerical search was used for this obstruction.

## Marked double projection and balanced bridges (verified)

MarkedDouble.lean (425 lines) and BalancedBridge.lean (140 lines) are compiled,
axiom-audited, and integrated under MarkedDouble and BalancedBridge.
All audited declarations use only propext, Classical.choice, Quot.sound.

MarkedAt D u records a simple-walk representation of some member starting at
u; nil walks are intentionally permitted. Tracked edge deletion retains a
marked member at each cut endpoint, even when a piece is nil. Projecting the
two copies after deleting the joining bridge, keeping copy labels for nil
members, yields marked partitions in both copies with total size at most
|D|+1. Choosing the smaller proves marked_of_double_bridge: a partition of
the joined double within its vertex budget implies a partition of the base
graph within its own ceiling budget, marked at the chosen joining vertex.

Therefore SmallerOrders n gives the marked ceiling budget whenever twice
the base order is strictly less than n (marked_of_twice_order_lt). Applied
to a non-singleton bridge side in a smallest failure, this contradicts
MarkedBudgets.gallai_of_marked_bridge_side unless the side has at least half
of all vertices. If both sides are non-singleton, both are exactly half;
the previously proved bridge parity then makes both sides even. In
failure_bridge_balanced the alternatives are a singleton side or two sides
of size 2*k and total order 4*k.

BalancedBridge.balanced_cut_unique is independent of the conjecture: any two
one-edge cuts with equal-sized sides in a finite connected graph have the
same edge. A connected half-sized set cannot avoid both cut endpoints: it
would lie wholly on one side and have to equal it. Applying this to the side
of a second balanced cut avoiding the first edge proves uniqueness.
Consequences for smallest failures:
* At most one non-leaf bridge.
* Two leaves imply 4 divides n (their parents form a non-leaf bridge).
* Unless 4 divides n, there is at most one leaf.
The main unresolved branch retains hbridgeBalanced, hnonleafBridgeUnique,
and hleafModulo. These do NOT eliminate balanced bridges or leaves.

Logs: /tmp/markeddouble.log, /tmp/markeddouble_audit.log,
/tmp/balancedbridge.log, /tmp/balancedbridge_audit.log,
/tmp/work_balancedbridge.log, /tmp/spec_balancedbridge.log,
/tmp/integrated_balancedbridge_audit.log. All passed.
Checkpoint: Work has 25,551 lines and no gaps; Spec has 25,727 lines, the
unchanged original theorem begins at 25,575, and its sole sorry is at 25,725.
The sole FormalConjecturesUtil import is unchanged. No submission has been
made; the conjecture remains unresolved.

## Leaves attach to the balanced bridge endpoints (verified)

BridgeLeafLocation.lean (135 lines) is compiled, audited, and integrated
under BridgeLeafLocation. Its four lemmas use only the permitted axioms:
  leaf_neighbors_adj_of_failure_finite
  marked_of_half_order_leaf_away
  leaf_on_balanced_side_at_boundary
  leaf_attached_to_nonleaf_bridge

The first transports the adjacency consequence of LeafPairReduction from
Fin n to an arbitrary finite vertex type of cardinality n, by a genuine
graph reindexing. It does not require edge-minimality.

The second extends the marked-doubling argument to the boundary case
2*|V|=n: a leaf u distinct from the chosen root r, whose parent a is also
distinct from r, ensures a marked own-budget partition. Otherwise the joined
double fails at order n. The two copies of u remain leaves, so their two
parents must be adjacent by the first lemma. The only cross-copy edge is
at r, contradicting a != r.

For a balanced bridge side S, any ambient leaf w in S other than the boundary
root has its parent in S. If that parent differed from the boundary root,
marked_of_half_order_leaf_away would give a marked side partition and the
existing bridge gluing would prove the full budget, a contradiction.
Consequently EVERY leaf in a smallest failure with a non-leaf bridge is
attached to one of the bridge's two endpoints. The final main branch retains
hleafAtBridge. Together with the earlier distinct-parent and uniqueness
results, this confines the bridge edges to a central edge and at most one
leaf edge at either end. The latter description is an immediate informal
consequence; a short-path representation of the entire bridge set has not
been separately formalized.

Builds/audits all passed:
  /tmp/bridgeleaflocation.log
  /tmp/bridgeleaflocation_audit.log
  /tmp/work_bridgeleaflocation.log
  /tmp/spec_bridgeleaflocation.log
  /tmp/integrated_bridgeleaflocation_audit.log
Work now has 25,685 lines, no gaps, and no warnings. Spec has 25,865 lines;
the original theorem begins at 25,709 and its sole sorry is at 25,863.
The original statement and sole FormalConjecturesUtil import are unchanged.
No proof submission has been made. The conjecture remains UNRESOLVED.

### Possible subsequent direction, not a proved result

At a vertex cut, ordinary marked gluing saves one member when each side
has a marked partition. An odd-order side has a marked own-budget partition
from smaller_order_marked, provided its one-leaf augmentation is still
strictly smaller than n. An even-order side whose boundary vertex has odd
internal degree already has an endpoint in every ordinary partition.
These observations may give further parity restrictions on nontrivial
vertex cuts of an even-order smallest failure. Beware the size-two side:
the opposite one-leaf augmentation then has order n, so SmallerOrders does
NOT apply to it.

A stronger prospective gluing lemma could use TWO nonempty marked members
on one side and split a member through the boundary vertex on the other
side. Splitting costs one and two disjoint-side concatenations save two,
for a net saving of one. Even internal boundary degree plus a marked member
supplies two endpoint members, unless the marked member is nil; the nil
case instead saves one by erasure. This has not been formalized here and
would require tracking the second pair through the first merge. It still
would not address the bridgeless, vertex-connected failures that remain.

## Double endpoint gluing and cut-vertex parity (verified)

Four modules have been compiled, axiom-audited, and integrated:
* DoubleEndpointGlue.lean (216 lines), namespace DoubleEndpointGlue.
* CutVertexParity.lean (279 lines), namespace CutVertexParity.
* CutBranches.lean (73 lines), namespace CutBranches.
* CutComponentBound.lean (137 lines), namespace CutComponentBound.
All audited declarations use only the permitted axioms (some are axiom-free).

DoubleEndpointGlue supplies:
  union_partitions_tracked, merge_two_pairs, two_endpoint_members,
  induced_endpoint_union, map_edge_nonempty, ne_of_disjoint_nonempty,
  nonempty_of_endpoint, glue_induced_two_pairs, glue_induced_even_marked.
Two distinct endpoint members from each of two induced sides meeting only
at u can be joined in two independent pairs, saving two members. The second
pair is explicitly retained through the first merge. If a side has even
internal degree at u and a marked member, it can be glued with a net saving
of one even without a marked member on the opposite side. If either
partition has an empty member, erase it and take the union. Otherwise the
marked path is nonempty, giving positive even endpoint multiplicity, hence
at least two distinct members. If the opposite side already has an
endpoint, ordinary gluing suffices. If not, activate_vertex splits a member
through u, costs one, and supplies two members; the two joins then save two.
The opposite-side support hypothesis is essential and is present.

CutVertexParity proves:
  induced_neighbor_card, single_boundary_neighbor_sum,
  gallai_odd_even_sides, failure_odd_even_side_parity,
  nontrivial_cut_boundary_odd, nontrivial_cut_side_parity,
  leaf_edge_bridge, two_vertex_side_bridge, cut_boundary_odd,
  delete_even_vertex_connected_of_failure.
For a vertex cut with both induced sides of size at least three, order
minimality and the odd-order one-leaf marked construction imply:
* In a smallest failure, the odd-order side has ODD internal degree at u.
* The even-order side has EVEN internal degree at u.
Otherwise ordinary gluing or the new even-marked gluing meets the budget.
Thus each side's internal boundary-degree parity equals its order parity.
Their internal degrees add to ambient degree, so u is odd. Odd total order
was already excluded by CutVertexReduction. Size-two sides are handled
separately: their sole non-boundary vertex is a leaf, giving a bridge, whose
endpoints were already proved odd. No invalid order-n augmentation is used.
Therefore ALL cut vertices of a smallest failure are odd, in both order
parities. The formal final form is that deleting ANY EVEN-degree vertex
leaves a connected induced graph.

CutBranches proves branch_parity and two_nontrivial_branches_exhaust.
A branch A excludes its attachment u. If |A|>=2 and the opposite side has
at least two vertices other than u, the number of edges from u into A has
parity |A|+1. For two disjoint branches A,B, each of size >=2, if at least
two vertices remain outside A,B,u, the same rule applies to A, B, and
A union B. Boundary degrees add, but the cardinality expressions differ by
one, contradiction. Hence two such branches leave AT MOST ONE other vertex.
No unproved global decomposition principle is hidden in this parity step.

CutComponentBound turns this into actual component counts after deleting u:
  deletedComponentSet, root_not_in_component, component_set_nonempty,
  component_sets_disjoint, component_set_closed, singleton_component_leaf,
  at_most_one_singleton_component, at_most_two_nonsingleton_components,
  at_most_three_components_after_delete_vertex,
  three_components_imply_leaf_at_vertex.
Components are lifted back to the ambient vertex set by Subtype.val images
of their supports. Distinct supports are disjoint closed branches. A
singleton component is a leaf at u; two would contradict the already proved
distinct-parent restriction. Three nonsingleton components contradict
CutBranches. Thus deletion of any vertex leaves <=3 components; if exactly
three remain, exactly one is a singleton leaf (the other two are nontrivial).

The main unresolved branch now retains hevenDeleteVertex, hcutVertexParity,
hdeleteComponentCount, and hthreeComponentsLeaf. These do NOT rule out odd
cut vertices, nor do they settle the vertex-connected cases.

All standalone builds/audits passed:
  /tmp/doubleendpointglue.log, /tmp/doubleendpointglue_audit.log
  /tmp/cutvertexparity.log, /tmp/cutvertexparity_audit.log
  /tmp/cutbranches.log, /tmp/cutbranches_audit.log
  /tmp/cutcomponentbound.log, /tmp/cutcomponentbound_audit.log
Integrated builds/audit passed:
  /tmp/work_cutparity.log, /tmp/spec_cutparity.log
  /tmp/integrated_cutparity_audit.log
Work has 26,383 lines with no gaps or warnings. Spec has 26,574 lines; its
unchanged original theorem starts at 26,407, and its sole sorry is at 26,572.
The sole import remains FormalConjecturesUtil. No proof submission has been
made. The original conjecture is STILL UNRESOLVED.

## Checkpoint: low-degree adjacency restrictions integrated

LowDegreeAdjacency.lean (249 lines) is now in Work and Spec as namespace
LowDegreeAdjacency. Its eleven audited lemmas use only propext,
Classical.choice, and Quot.sound. The generic support-connected version of
SmallerOrders handles empty support explicitly. A support reduction by two
that costs one path meets the original budget in either order parity.
The already-existing reduce_triangle_degree_two_three supplies that reduction
for a triangle with adjacent degree-two and degree-three vertices. Adjacent
degree-two vertices instead force a pendant triangle: its side size three
and internal boundary degree two violate CutVertexParity. A failing graph
has at least five vertices (orders at most four are subcubic), so the other
side is large enough for that parity theorem. Thus every neighbor of a
degree-two vertex has degree at least four; if the actual witness has
independent even vertices, that lower bound is five. Every even neighbor
of a cubic vertex has degree at least four. In particular a cubic rooted
maximum defect exposes two distinct zero-quota nonbridge neighbors of
degree at least four. This is NOT a cubic-root repair theorem.

The unchanged main theorem retains hdegreeTwoNeighbors and hcubicRoot.
Builds and integrated audit passed:
  /tmp/work_lowdegree.log, /tmp/spec_lowdegree.log
  /tmp/integrated_lowdegree_audit.log
Work has 26,632 lines and no gaps/warnings. Spec has 26,829 lines, its
original theorem starts at 26,656, and its sole sorry is at 26,827.
The import and original theorem statement remain unchanged.

Further informal investigation did not establish cubic-root repair. The
existing RootCapacity.rooted_incidence identity already shows a cubic root
with quota one belongs to exactly one member; this alone does not permit
repair using a path missing the root. In particular, the false two-path
endpoint-repairing claim near the start of this record remains an obstacle.
Adding root 6 between 0 and 3 to that example gives cycle 6-0-1-2-3-6 and
path 1-4-0-3-5-2. A two-path partition MARKED at 6 would force forbidden
endpoint re-pairing in the old graph. The unmarked version for that specific example was not settled here.
IMPORTANT: the general unmarked missing-cycle-vertex shortcut was ALREADY
disproved by the 14-vertex example in the earlier MOBILE DEFECT record. No universal normalization claim has been added.
The original conjecture remains unresolved; no proof has been submitted.

## Global edge minimality and bridge-side edge balance (verified)

GlobalCritical.lean (247 lines) is compiled, axiom-audited, and integrated
under GlobalCritical. Its fifteen audited lemmas use only the permitted
axioms. Unlike EdgeCritical.EdgeMinimal, the new MinimalEdges compares
ALL connected graphs of the same order, not just spanning subgraphs of
one graph. exists_minimal_edges minimizes the edge count among all failures
on Fin n. MinimalEdges.spanning recovers the old property, and
MinimalEdges.on_finite transports the stronger property to an arbitrary
finite type of cardinality n. The transport uses the graph isomorphism's
edge-set equivalence, not an assumed equality of vertex types.

failure_has_global_minimal_root now replaces the spanning-witness choice
in the original theorem. H need not be a subgraph of the previously selected
J, but this loses no used hypothesis: SmallerOrders n was chosen globally,
and the old hHJ was unused. The main branch now retains both hglobal and
hcritical, together with all the previous rooted one-defect data.

New counting infrastructure:
  edge_ncard_iso, sum_neighbor_ncard, pairedCopies_edge_ncard,
  within_edge_ncard, bridge_cut_edge_ncard.
The joined double of an m-vertex graph with e edges, attached by a single
vertical edge, has 2m vertices and 2e+1 edges. A one-edge cut S has total
edge count e(S)+e(complement S)+1, using induced-side edge counts.

marked_of_half_order_fewer_edges extends the doubling marked-budget argument
to EXACTLY half the globally critical order when the joined double has
fewer edges. Applying it to the sparser side of a nontrivial bridge cut
would supply a marked side partition and restore the original graph within
budget. Thus neither side can be sparser:
  failure_cut_side_edge_bound, failure_cut_edges_equal.
Consequently the equal even-order sides also have EQUAL INTERNAL EDGE COUNTS.
The total edge count is therefore odd:
  nonleaf_bridge_odd_edge_count.
In particular:
  bridge_leaf_of_even_edge_count: every bridge is a leaf edge if |E| is even;
  one_leaf_of_even_edge_count: at most one leaf if |E| is even.
The latter uses the previous fact that two distinct leaves have distinct,
non-leaf parents joined by a bridge.

These consequences are retained as hbridgeEdgeBalance,
hnonleafBridgeOddEdges, honeLeafEvenEdges. They do not eliminate non-leaf
bridges when |E| is odd and 4 divides n, nor solve the bridgeless cases.

All builds/audits passed:
  /tmp/globalcritical.log, /tmp/globalcritical_audit.log
  /tmp/work_globalcritical.log, /tmp/spec_globalcritical.log
  /tmp/integrated_globalcritical_audit.log.
Work has 26,879 lines, no gaps or warnings. Spec has 27,086 lines; the
unchanged original theorem starts at 26,903 and its sole sorry is at 27,084.
The sole import remains FormalConjecturesUtil. The conjecture remains
UNRESOLVED, and no proof submission has been made.

Lean note: rewriting a double complement directly under the dependent type
of an induced graph's edgeSet did not simplify. Rewriting induced edge
counts to within_edge_ncard first moves the calculation to the common
ambient vertex type, where compl_compl applies normally.

Additional informal caution, not a new Lean theorem:
The cycle 6-0-1-2-3-6 and path 1-4-0-3-5-2 from the earlier marked-absorption
obstruction remain a useful warning. Attach a genuinely pendant edge 6-7,
without extending the other path through 7. This gives a cubic rooted
lollipop and a path missing the root, but no two-path partition. In any
such partition the four odd endpoints would be 6,7,1,2. A path pairing
6 with 7 could only be the singleton edge, leaving a cyclic graph to one
path, impossible. Hence removing edge 6-7 and then vertex 6 would give the
forbidden endpoint re-pairing of the old two-triangle example. This graph
has eight vertices, so two paths is BELOW its Gallai budget of four. Root
6 is a cut vertex, and degree-two vertices 4,5 have cubic neighbors, so
it does not satisfy the smallest-failure restrictions. The three earlier
exact repair checks instead let the other path meet the lollipop's tail;
they do not contradict this pendant example. No unrestricted cubic-root
repair, or non-cut cubic-root repair, has been established.

## Cycle-ear shortening and higher-degree root selection (verified)

CycleEar.lean (337 lines) and RootHighDegree.lean (115 lines) are compiled,
audited, and integrated as CycleEar and RootHighDegree. All newly audited
lemmas use only permitted axioms (cycle_two_spokes uses only propext).
No theorem asserts that these restrictions suffice for a contradiction.

CycleEar supplies the genuine exchange:
  cycle C = r-u-R-v-r, simple path P containing chord uv, r absent from P.
Move the two-edge ear u-r-v into P, replacing uv; replace the ear in C by uv.
The new P is simple, the new C is a cycle one vertex shorter, the edge union
and disjointness are preserved, and the total incidence score is unchanged.
path_expand_fresh_ear restricts the old graph to P's spanning subgraph so
freshness is required only relative to P, not the whole ambient graph.
cycle_ear_exchange proves the local operation. replace_cycle_and_path
computes score preservation from edge counts and the path/cycle vertex
count identities. shorten_cycle_member applies the unrestricted two-index
replacement to an exact one-defect family.

ShortestCycle T m minimizes cycle length among ALL equal-score families
having a whole cycle member, not merely among representations of one
fixed subgraph. exists_shortest_cycle uses Nat.find. In a smallest graph
failure, a degree-two vertex r has adjacent neighbors u,v. A cycle member
through r uses every edge at r, so every OTHER nonnil path avoids r. The
chord uv is either on that cycle, forcing it to be a forbidden whole
triangle, or belongs to another path. In the latter case the ear exchange
strictly shortens the cycle. Therefore:
  shortest_cycle_no_degree_two,
  shortest_cycle_min_degree_three,
  exists_cycle_min_degree_three.
The final theorem retains the last consequence conditionally as hshortCycle.
A whole cycle member is NOT asserted to exist in every rooted maximum.
Endpoint quotas and quota energy are NOT claimed to be preserved by the ear
exchange, and shortest-cycle selection is independent of root-energy
minimization. Do not silently combine these two minima.

RootHighDegree improves the actual selected root, independently of that
shortest-cycle choice:
  degree_two_root_is_cycle: an exposed repeated-start representative at an
  ambient degree-two root must also FINISH at that root. The local incidence
  identity says its degree plus endpoint count equals four; degree <=2
  forces two root endpoints. Hence the member is a whole simple cycle.
  root_degree_ge_two: the two exposed zero neighbors provide this bound.
  move_degree_two_root: choose an exposed zero-quota neighbor x. The cycle
  uses all incident root edges, so x lies on it. Reroot the CLOSED member
  at x, moving the pair r->x. With old quota(r)=2 and quota(x)=0 the square
  energy is EXACTLY unchanged. LowDegreeAdjacency gives degree(x)>=4.
  exists_small_quota_high_degree_root combines this with RootEnergy's
  minimum-energy selection. Its output has root quota one or two, root
  degree >=3, the SAME maximum score, and the same minimum-energy property.
  A quota-two/even selected root therefore has degree at least four.

The main theorem now calls exists_small_quota_high_degree_root instead of
exists_small_root_quota and retains hrootDegree. Cubic odd roots and higher
roots still remain. This does not exclude degree-two vertices elsewhere in
the smallest failing graph, and does not repair a cubic root.

All standalone and integrated builds/audits passed:
  /tmp/cycleear.log, /tmp/cycleear_audit.log
  /tmp/roothighdegree.log, /tmp/roothighdegree_audit.log
  /tmp/work_cycleear.log, /tmp/spec_cycleear.log
  /tmp/integrated_cycleear_audit.log
The original conjecture remains UNRESOLVED; no proof has been submitted.

Correction to the recent continuation summary: the general UNMARKED
cycle-plus-path absorption claim with a missing cycle vertex was already
rejected in the much earlier MOBILE DEFECT LOCAL DATA entry. Its exact
14-vertex example is
  C = 0-1-2-3-4-5-6-7-8-0,
  P = 9-0-4-11-5-8-12-7-1-13-3-6-10.
Cycle vertex 2 is absent from P, but there is no two-path partition.
The earlier diagnostic record reports all 24 path-plus-cycle partitions
have cycle lengths 9,10,11. Therefore neither missing a cycle vertex nor
minimizing cycle length alone gives absorption. This example is below its
Gallai budget (two members versus seven permitted paths). No new search
was needed; it was already in Research.md and should not be forgotten.

Another informal obstruction derived in this continuation (NOT yet a Lean
module): even POSITIVE quota at an internally repeated vertex does not
suffice for fixed-quota normalization, even with independent zero vertices.
Use the existing 12-vertex InternalDefectObstruction graph, but the six walks
  7-0-1-2-0-6; 1-3-0; 0-4-5; 7-8-9; 9-10; 10-11.
Their quotas are
  [2,1,0,0,0,1,1,2,0,2,2,1].
The only repetition is INTERNAL at vertex 0, whose quota is two. All quotas
are normal, and zeros {2,3,4,8} are independent. For S={7,8,9,10,11},
quota(S)=7, boundary(S)=1, and degree(0)+quota(0)=6+2=8. The path cut bound
would require 8+7 <= 12+1, impossible. Hence no path family realizes those
same quotas. It is also not a globally maximum-score family when quotas
are free: the existing graph has a verified THREE-path partition. This
obstruction therefore does NOT disprove global exact-budget repair.

Cycle/root final checkpoint: small_quota_high_degree_cases is also proved,
audited, and integrated. The selected root satisfies the explicit alternative
  quota 1, odd degree >=3; OR quota 2, even degree >=4.
The main branch retains this as hrootAlternatives. Work now has 27,331 lines;
Spec has 27,544 lines, its original theorem starts at 27,355, and its sole
sorry is at 27,542. All five RootHighDegree and twelve CycleEar lemmas pass
the integrated axiom audit. There are no running build jobs. The original
statement and sole import are unchanged. No complete proof or disproof has
been obtained, and no submit_proof call has been made.

## Cubic-root auxiliary repairs: further rejected local claims

These are exact Python diagnostics, NOT Lean proofs and not searches for a
counterexample to the original conjecture. No global repair claim follows.
The scripts use exhaustive simple-path enumeration with a complementary-path
check. All diagnostic processes mentioned below have finished.

/tmp/cubic_root_target.py and /tmp/cubic_root_stalk.py: adding a stalk from
vertex 2 of the earlier 14-vertex cycle/path obstruction to its outside
vertices repaired all five one-edge attachments and all 320 longer distinct
stalks tested. /tmp/cubic_root_hamilton.py passed 191,370 canonical spanning
lollipop / root-avoiding Hamilton-path cases through core order 10.
These finite passes are NOT proofs of a general lemma.

/tmp/cubic_root_multicore.py allows parallel edges in a suppressed core and
realizes repetitions by fresh degree-two subdivisions. It found a nine-vertex
obstruction to the proposed TWO-path repair even with connected root deletion:
  lollipop 0-1-6-0-2-3-4-5, other path 2-7-3-1-4-8-5.
Root 0 is cubic and not a cut vertex, but no two-path partition exists.
The exposed neighbor 6 has degree two and the even vertex 4 is a cut vertex,
so it violates already proved smallest-counterexample restrictions.
The Gallai budget here is five, not two.

The variant /tmp/cubic_root_multicore3.py, with cycle-core length >=3,
found a TEN-vertex obstruction after 460 cases:
  lollipop 0-1-2-0-3-4-5-6,
  other path 3-7-4-1-8-2-5-9-6.
Both exposed neighbors 1 and 2 have degree four. The root is cubic and its
deletion leaves a connected graph. Nevertheless no two-path partition exists.
Degrees: [3,4,4,3,4,4,2,2,2,2]. Vertex 5 is an EVEN cut vertex; there are
no bridges. Degree-two vertex 7 has cubic neighbor 3, and degree-two vertices
6 and 9 are adjacent. Thus this also violates the known smallest-failure
restrictions. Its Gallai budget is five, so it is not a Gallai counterexample.
Log /tmp/cubic_root_multicore3.log; PID 104577 is defunct.

In particular, neither 'cubic non-cut root' nor the additional condition
'both exposed neighbors have degree >=4' suffices for an unrestricted local
two-member repair. Any valid argument must use more than those hypotheses.
No such lemma has been added to Spec, which still has its original sole gap.

## Degree-two neighborhood packing (verified and integrated)

DegreeTwoPacking.lean (351 lines) has eleven gap-free, warning-free lemmas.
Its standalone audit has passed with only the three permitted axioms.
It is inlined as DegreeTwoPacking in Work and Spec. The unchanged main
conjecture retains hdegreeTwoDisjoint and hdegreeTwoCount. The complete
conjecture still has ONE sorry and remains unresolved.

New exact reductions:
- diamond_path_exchange: given a simple path L-a-b-R and two fresh vertices
  u,v adjacent to both a,b, replace it by the two paths
      L-a-u-b-v,  v-a-b-R.
  Their edges partition the old path plus the four new edges. This is a
  one-additional-path operation, with no endpoint-pairing assumption.
- induce_dominated_boundary_connected: deleting a set whose entire outside
  boundary is adjacent or equal to a retained vertex a preserves connectivity.
  Uses a reachable-map fold, not an assumption about induced connectedness.
- two_triangular_tips_connected applies that fold to two degree-two vertices
  with a common neighbor a, when their other neighbors b,c are adjacent to a.
- two_tips_edge_diff identifies exactly the four removed incident edges.
- distinct_tips_reduction: if b!=c and u,v are nonadjacent, the removed edges
  form the simple path b-u-a-v-c. Delete u,v, induct, restore this single path.
- restore_diamond / twin_tips_reduction: if b=c, choose the member covering
  edge ab in the smaller graph and apply diamond_path_exchange. The edge
  split handles both possible orientations; fresh vertices avoid the entire
  old path. Again deletion of two vertices costs at most one extra path.
- degree_two_triangle_at_neighbor selects the known triangle relative to an
  arbitrary specified neighbor.
- degree_two_neighbors_disjoint excludes a common neighbor of two distinct
  degree-two vertices in a globally smallest-order failure, in both cases.
- degree_two_closed_neighbors_disjoint combines this with the previously
  proved exclusion of adjacent degree-two vertices.
- degree_two_card_bound counts these disjoint closed-neighborhood triples:
      3 * card {u : degree(u)=2} <= n.

No lemma asserts a repair for an arbitrary cubic rooted lollipop. The new
packing restriction does not eliminate all degree-two vertices and does not
supply a global defect-normalization theorem.

Build logs (integrated builds were running when this entry was written):
  /tmp/degree_two_packing.log, /tmp/degree_two_packing_audit.log,
  /tmp/work_degree_two_packing.log, /tmp/spec_degree_two_packing.log,
  /tmp/integrated_degree_two_packing_audit.log.
Work: 27,681 lines. Spec: 27,898 lines; original theorem starts at 27,705;
sole sorry at 27,896. Original statement and import explicitly checked unchanged.

Degree-two packing final checkpoint: both full-file builds completed.
Work is warning-free; Spec has only the original theorem's sorry warning.
The integrated audit completed with 517 axiom reports, no errors, and no
axioms outside propext, Classical.choice, Quot.sound. All eleven new lemmas
are included in that audit. No build or diagnostic job remains running.
The statement/import are unchanged and the sole original gap is still at
Spec line 27,896. No complete proof or disproof has been obtained, and no
submit_proof call has been made.

## Separation of degree-two triangles (verified and integrated)

DegreeTwoSeparation.lean (345 lines) has eleven gap-free, warning-free lemmas
and the definition tipRegion. Its standalone axiom audit passed. The body is
inlined as DegreeTwoSeparation in Work and Spec. The main theorem retains
hdegreeTwoSeparation, houtsideDegreeTwo and the stronger hdegreeTwoCount.

Verified reductions and consequences:
- delete_two_simplicial_connected folds two independent deleted simplicial
  vertices onto (possibly different) retained neighbors. This does NOT assume
  that arbitrary vertex deletion preserves connectivity.
- disjoint_tips_edge_diff identifies the four incident edges removed from two
  degree-two vertices, with four distinct neighbors allowed.
- nonbridge_between_tips_reduction: for degree-two triangles u-a-b-u and
  v-c-d-v with six distinct vertices, a NONBRIDGE edge ac gives a reduction.
  Delete ac first, retaining a connected graph; the two triangle shortcuts
  ab and cd survive, so deleting u,v also preserves connectivity. The removed
  edges form the path b-u-a-c-v-d. SmallerOrders plus one-path restoration
  supplies the original Gallai budget, in either order parity.
- degree_two_cross_edge_bridge: consequently EVERY edge between neighborhoods
  of distinct degree-two vertices in a smallest failure must be a bridge.
  The earlier disjoint closed-neighborhood theorem supplies six distinct
  vertices; no unsupported walk-to-path simplification is used.
- degree_two_cross_edge_large_odd: both endpoints of such an edge are odd
  and have degree >=5. These edges are non-leaf bridges, hence at most one
  exists by the already verified balanced-bridge uniqueness theorem.
- tipRegion is the union of all degree-two closed neighborhoods.
  tipRegion_card gives its cardinality exactly as three times the number
  of degree-two vertices.
- edge_to_other_tip_region identifies any cross-region edge from a tip's
  neighbor as a non-leaf bridge.
- one_neighbor_has_no_cross_edge: at least one of each tip's two neighbors
  has NO edge into any OTHER tip neighborhood. Otherwise the two bridges
  would be distinct, contradicting uniqueness.
- two_outside_tip_region_of_clean_neighbor: that neighbor has degree >=4,
  at most two neighbors in tipRegion, so at least two outside it.
- two_outside_tip_region handles also the empty tipRegion case.
- degree_two_card_bound_strict proves
      3 * card {u : degree(u)=2} + 2 <= n.

No theorem eliminates all degree-two vertices or repairs the general rooted
single defect. The full Gallai conjecture is still unresolved.
Logs: /tmp/degree_two_separation.log,
      /tmp/degree_two_separation_audit.log,
      /tmp/work_degree_two_separation.log,
      /tmp/spec_degree_two_separation.log,
      /tmp/integrated_degree_two_separation_audit.log.
Original statement and import explicitly checked unchanged. Spec has 28,247
lines and still exactly one sorry; Work has 28,025 lines.

### Longer-path caution and possible component-parity extension (informal)

The unrestricted nonseparating-path extension is NOT automatic, even in a
bridgeless graph satisfying the new degree-two separation restrictions.
A structural example (not Lean-formalized here; no numerical search used):
Take four blocks indexed cyclically i=0,1,2,3. Each is K4 minus edge a_i b_i,
with vertices a_i,b_i,c_i,d_i and internal edges
  a_i c_i, a_i d_i, b_i c_i, b_i d_i, c_i d_i.
Join b_i to a_(i+1). The 16-vertex core is cubic and bridgeless. Add tip u
adjacent to a_0,c_0 and tip v adjacent to a_2,c_2. The resulting 18-vertex
graph has two degree-two tips, four degree-four neighbors, and all other
vertices cubic. Its tip neighborhoods are disjoint with no cross edge.

Any path covering both pairs of tip-incident edges must traverse one of
intermediate blocks 1 or 3 between its two ports. Deleting that path's edges
removes both boundary edges of that block. Internal edges remain there,
since a path cannot cover all internal degree-three incidences. Edges also
remain elsewhere. Thus the remaining edge support is disconnected; a
blanket connected-remainder claim would be false.

However this is NOT an obstruction to Gallai or even to a more flexible
one-path reduction. For example use the path
  c_0-u-a_0-b_3-c_3-a_3-b_2-d_2-a_2-v-c_2.
After deletion u,v are isolated; the other components have orders 4 and 12.
Both are even, so smaller-order Gallai bounds sum to 8 and restoring this
path gives the allowed 9. A general even-component restoration criterion
would therefore be more useful than connected-remainder-only restoration.
Such a new component-parity criterion has NOT been added in this continuation,
and no general existence theorem for suitable longer paths is established.

Separation checkpoint completed: Work/Spec rebuilt successfully and the
integrated audit passed through all eleven new declarations, with only the
permitted axioms. The subsequent ComponentBudget development below uses
that checkpoint. The original conjecture remained unresolved.

## Even-component restoration (verified and integrated)

ComponentBudget.lean (168 lines) has eight gap-free, warning-free lemmas.
Its standalone axiom audit passed; it is inlined as ComponentBudget in Work
and Spec. This now supplies the even-component criterion that was still
missing when the preceding longer-path note was written.

- partition_components combines arbitrary component-wise path budgets into
  a global edge partition, proving cross-component edge disjointness and
  the sum-of-budgets cardinality bound. Empty graphs are allowed.
- sum_component_orders proves that the orders of all components sum to the
  ambient cardinality, using fibers of connectedComponentMk.
- smaller_orders_even_components: if the ambient order is below n and all
  components have EVEN order, SmallerOrders n gives a partition D with
      2 * D.card <= card V.
- smaller_orders_even_support applies this after inducing on the support,
  then lifts back. Isolated vertices are ignored, including empty support.
- restore_path_even_components: if deleting a SIMPLE path removes at least
  two vertices from the support and every remaining support component has
  even order, restoration costs one path and meets the original budget.
  Connectedness of the remainder is NOT required. This is a restoration
  criterion, not an existence theorem for a path satisfying it.
- failure_path_leaves_odd_component: in a smallest failure, any simple path
  that isolates at least two vertices must leave an odd support component.
- support_component_order_ge_two: support components cannot be singletons.
- failure_path_leaves_large_odd_component strengthens that odd component's
  order to at least three. The main branch retains this as hpathOddComponent.

This avoids a false connected-remainder assumption in longer-path reductions.
The ring-of-four-blocks discussion above remains informal; the explicit
18-vertex graph and its 4+12 component certificate have not been instantiated
as Lean objects. No global suitable-path existence result has been proved.
The original Gallai conjecture still has its sole unresolved sorry.

Logs: /tmp/component_budget.log, /tmp/component_budget_audit.log,
      /tmp/work_component_budget.log, /tmp/spec_component_budget.log,
      /tmp/integrated_component_budget_audit.log.

Component-budget final checkpoint: both full-file builds completed. Work is
warning-free; Spec has only the original theorem's sorry warning. The final
integrated audit completed with 536 axiom reports, no errors, and only
propext, Classical.choice, Quot.sound. All nineteen new lemmas from
DegreeTwoSeparation and ComponentBudget are included. The original type and
sole import were explicitly checked unchanged. Work has 28,192 lines, Spec
28,417; the original theorem starts at 28,216 and its sole sorry is at 28,415.
No complete proof or disproof has been obtained; no submit_proof call was made.

## Component rounding deficits (verified; integrated)

ComponentDeficit.lean has eighteen lemmas and three definitions, compiled
without gaps or warnings and with a clean standalone axiom audit. It is
inlined as ComponentDeficit in Work and Spec. Its first integrated Work/Spec
builds passed; Spec still has only the original conjecture gap.

Define evenCount G as the number of even-degree vertices. BadComponent G C
means C has odd order and its induced graph does not have exactly one even
vertex. badCount is the number of these components. "Bad" refers ONLY to
this rounding budget; it does not assert that the floor bound is impossible.
Both counts use Set.ncard, avoiding definitional dependence on Fintype data.

- odd_order_iff_evenCount_odd is the parity form of handshaking.
- component_neighbor_card and component_evenCount_eq identify internal
  component degrees and even vertices; sum_component_evenCounts sums them.
- sharp_one_even_partition uses the already verified marked partition to
  obtain 2*D.card+1=card V when there is exactly one even vertex.
- bad_component_three_even: each bad component has >=3 even vertices.
- three_badCount_le_evenCount: 3*badCount G <= evenCount G.
- component_deficit_budget: assuming SmallerOrders n and EVERY component
  order < n, a good partition satisfies 2*D.card <= card V+badCount G.
- component_budget_of_one_bad / component_budget_of_five_even recover the
  ceiling bound. The proper-component hypothesis C.order<n is essential;
  this is NOT a proof of the connected critical-order case with E<=5.
- support_budget_of_one_bad ignores isolated vertices, then lifts back.
- restore_path_one_bad_component / restore_path_five_even_support: a SIMPLE
  path isolating >=2 vertices is reducible if the remaining support has <=1
  bad component, in particular if it has <=5 even vertices.
- failure_path_two_bad_components / failure_path_six_even_support give the
  contrapositive necessary conditions on a smallest failure.
- failure_path_two_odd_even_rich_components gives two distinct odd support
  components, each with >=3 INTERNAL even-degree vertices.

The main branch retains hpathTwoOddComponents and hpathSixEven. Degrees in
these statements are measured after path deletion, not in the original G.
Logs: /tmp/component_deficit.log, /tmp/component_deficit_audit.log,
/tmp/work_component_deficit.log, /tmp/spec_component_deficit.log,
/tmp/integrated_component_deficit_audit.log.

### Prescribed independent inactive-pair caution (informal)

Even with four even-degree vertices, an arbitrary nonadjacent pair of even
vertices need not be simultaneously inactive in a normal partition.
Consider edges 01,02,03,12,13,04,45, with degrees [4,3,2,2,2,1] and even set
{0,2,3,4}. Prescribing the exact inactive pair {2,3} would give three normal
paths with quotas q(0)=q(4)=2, q(1)=q(5)=1, q(2)=q(3)=0. The degree-two
vertex 4 with quota two forces edge 45 to be a singleton member. But
 degree(0)+q(0)=6 forces all three paths to contain 0: contradiction.
If a normal partition had a larger inactive set containing {2,3}, activation
at the other even vertices would reduce it to this impossible exact pair.
The graph does have a TWO-path partition: 5-4-0-1-3 and 3-0-2-1. This is only
an obstruction to arbitrary prescribed independent inactive pairs, NOT to
existence of some suitable pair or to Gallai. This particular six-vertex
example is not Lean-formalized here and is not used as a proof lemma.

## Two degree-two tips force six original even vertices (verified; integrated)

TipParity.lean has ten gap-free, warning-free lemmas. Its body is now inlined
as TipParity. Standalone audit and final integrated builds are in progress
at the time of this note; append the finished checkpoint after checking them.

- shortest_path_neighbor_not_mem: a neighbor of the first vertex of a
  shortest path, other than its second vertex, is outside the whole path.
  Proof: the prefix to that neighbor is itself shortest and has length one.
- exists_path_internal_two: in a connected graph, two vertices each of
  degree >=2 with disjoint neighbor sets lie internally on some simple path.
  Choose a shortest u-v path, then prepend/append unused neighbors. The
  disjoint-neighbor hypothesis makes the two new endpoints distinct.
  No connected-remainder or arbitrary prescribed-order assumption is made.
- degree_two_internal_isolated: deleting a path through a degree-two vertex
  internally isolates it. This follows from the exact internal path degree.
- delete_path_degree_parity: path deletion preserves degree parity away
  from the two endpoints.
- support_evenCount_eq measures even support vertices in the ambient type.
- delete_path_evenCount_le_of_two_isolated: if two ORIGINAL even vertices
  are isolated by path deletion, the residual support even count is at most
  the original even count. Remove those two from the original even set;
  the only potentially new even vertices are the path's two endpoints.
- support_card_bound_two_missing bounds the residual support order.
- failure_path_isolating_two_even combines these facts with ComponentDeficit
  to conclude >=6 original even vertices in any smallest failure admitting
  such a path.
- two_degree_two_implies_six_even uses the previously proved disjoint tip
  neighborhoods and the shortest-path construction.
- degree_two_at_most_one_of_five_even: a globally smallest failure with <=5
  even vertices has at most one degree-two vertex.

The main branch retains htwoTipsEvenCount and hsmallEvenTipCount. This does
NOT prove the conjecture for E<=5 and does not rule out high-minimum-degree
failures. The global endpoint-selection / rooted-defect gap remains open.
Logs: /tmp/tip_parity.log, /tmp/tip_parity_audit.log,
/tmp/work_tip_parity.log, /tmp/spec_tip_parity.log.

TipParity checkpoint completed: standalone audit passed, Work/Spec rebuilt
successfully, and the integrated audit finished with 564 axiom reports using
only propext, Classical.choice, Quot.sound. Work was warning-free and Spec
had only the original theorem's sorry. The original type/import were explicitly
checked unchanged. Spec had 28,916 lines with the theorem at 28,704 and its
sole gap at 28,914. The subsequent LowDegreeParity extension follows.

## Path deletion and arbitrary low-degree pairs (verified; integrated)

LowDegreeParity.lean (246 lines) has sixteen gap-free, warning-free lemmas.
It strengthens the preceding parity calculation: the two vertices missing
from the residual support need NOT have been even-degree. Its body is
inlined as LowDegreeParity. Standalone audit and final full-file builds are
running at the time of this note; check the final checkpoint below.

Key exact identity for any finite graph:
  evenCount G = evenCount (G.induce G.support) + card (G.support complement).
Isolated vertices are even but excluded from the induced support.
Deleting a simple path changes parity only at its two endpoints, so
  evenCount (G.deleteEdges P.edges) <= evenCount G + 2.
Combining the two gives, for H = G.deleteEdges P.edges,
  evenCount (H.induce H.support) + card V
    <= evenCount G + card H.support + 2.
Thus if at least two vertices are missing from H.support, its internal even
count is no greater than the ORIGINAL even count. No parity assumption on
those missing vertices is required. This accounts correctly for isolated
odd-degree leaves, which consume endpoint parity changes.

New restoration and smallest-failure consequences:
- restore_path_five_original_even: SmallerOrders plus E(original)<=5 and a
  path leaving at least two vertices outside the support is reducible.
- failure_path_six_original_even: every such path in a smallest failure
  forces >=6 even-degree vertices in the original graph.
- failure_path_evenCount_deficit strengthens this to
      n + 4 <= evenCount G + card H.support,
  i.e. E(original) >= number of missing support vertices + 4.
- degree_one_endpoint_isolated complements the earlier degree-two internal
  isolation lemma.
- two_leaves_implies_six_even uses a simple leaf-to-leaf path.
- path_with_prescribed_start_and_internal: a shortest u-v path can be
  extended beyond v through an unused neighbor when degree(v)>=2.
- leaf_and_degree_two_implies_six_even uses that extension.
- two_low_degree_implies_six_even covers all pairs of distinct vertices of
  degrees one or two, including the degree-two pair case from TipParity.
- low_degree_card_le_one_of_five_even: a smallest failure with <=5 original
  even vertices has at most ONE vertex of degree one or two in total.

The main branch retains hpathEvenDeficit and hsmallEvenLowDegreeCount.
These are still conditional smallest-failure restrictions, not a proof of
Gallai for the entire E<=5 class, and not a way to exclude high-minimum-degree
failures. The original conjecture remains unresolved; no submit_proof call
has been made.
Logs: /tmp/low_degree_parity.log, /tmp/low_degree_parity_audit.log,
/tmp/work_low_degree_parity.log, /tmp/spec_low_degree_parity.log,
/tmp/integrated_low_degree_parity_audit.log.

Final checkpoint for this continuation: all three standalone modules and
axiom audits passed. Both final full-file builds completed successfully:
Work is warning-free; Spec has only the original theorem's sorry warning.
The final integrated audit completed with 580 reports, zero errors, and no
axioms outside propext, Classical.choice, Quot.sound. All 44 new lemmas from
ComponentDeficit, TipParity, and LowDegreeParity are covered by that audit.
The original conjecture type and the sole import were explicitly verified
unchanged. Work has 28,925 lines; Spec has 29,166. The original theorem
starts at line 28,949 and its sole remaining sorry is at line 29,164.
No proof builds or audits remain running. The general conjecture is still
unresolved; no complete proof/disproof and no submit_proof call occurred.

The central remaining difficulty has not changed: the restrictions above do
not rule out high-minimum-degree smallest failures and do not repair the
exact-budget rooted single defect, especially the odd root with quota one.


## Root locality (verified and integrated)

RootLocality.lean proves root_unique, members_off_root_acyclic, and
member_cycle_contains_root. In a single-defect rooted trail family the root
is unique, every member restricted away from it is acyclic, and every cycle
contained in a member passes through the root. The proof extracts the simple
tail of a repeated-start representative; its sole extra edge is incident to
the root. These three lemmas are inlined under RootLocality in Work and Spec.
The main branch retains hrootLocality and hrootUnique.

Work and Spec full builds passed. Work is warning-free; Spec still has the
original theorem's sole sorry. The integrated audit now has 583 reports,
all using only propext, Classical.choice, Quot.sound. Logs:
/tmp/work_root_locality.log, /tmp/spec_root_locality.log,
/tmp/integrated_root_locality_audit.log.

## Positive-quota internal rootification is false (verified externally)

PositiveRootObstruction.lean is complete, warning-free, and audited in
PositiveRootObstructionAudit.lean (all 24 lemmas, permitted axioms only).
This obstruction remains EXTERNAL, not a branch or disproof of Gallai.
Logs: /tmp/positive_root_obstruction9.log and
/tmp/positive_root_obstruction_audit.log.

On eleven vertices, take the seventeen edges
  02,03,04,05,07,12,14,19,25,29,34,37,38,48,56,5-10,6-10.
Two covering edge-disjoint trails are
  1-2-0-3-4-0-5-6
  0-7-3-8-4-1-9-2-5-10-6.
Only the first repeats a vertex: 0, INTERNALLY. Its endpoint quota at 0 is
ONE, not zero. The quota vector is [1,1,0,0,0,0,2,0,0,0,0]. The score is 18,
exactly |E|+2-1, and this is globally maximum among all two-trail families:
degree(0)=5 excludes two simple paths.

Nevertheless there is NO rooted single-defect realization with these quotas.
Root capacity forces its root to be 0. The other member must be a simple
path with endpoint 1 and containing 3 and 4 internally. RootLocality forces
each member to meet both triangles 129 and 348, which avoid 0. Zero-quota
degree-two vertices 7,8,9 pair their incident edges within each member.
Meeting triangle129 forces the simple path's sole edge at 1 to be 12 or19,
not14. Meeting triangle348, without containing that whole cycle, forces
exactly one of routes 34 and384. Degrees two at 3 and4 then force one of
routes 03 or073 and the edge04. These make a cycle in the simple path,
a contradiction. All four cycle cases are kernel-checked in no_path_pattern.

The verified good family consists of THREE simple paths:
  1-2-0-3
  3-4-0-5-6
  0-7-3-8-4-1-9-2-5-10-6.
The actual Gallai budget is SIX. Thus witness disproves only an auxiliary
fixed-quota rootification shortcut. It does not refute the original theorem,
and it cannot be used to fill its remaining sorry.

The new work has not closed the global exact-budget defect-repair problem.
In particular, a positive endpoint quota at an INTERNAL repetition is not
sufficient to apply rooted minimum-energy lemmas. High-minimum-degree
smallest failures and the odd quota-one rooted defect remain unresolved.


## Quadrilateral absorption (verified; integrated)

QuadrilateralAbsorption.lean (575 lines) has 22 complete lemmas. Its final
standalone build is warning-free, and QuadrilateralAbsorptionAudit.lean
reports only permitted axioms for all 22. The body is inlined into Work
and Spec as QuadrilateralAbsorption. Full integration builds passed (with
an extra module-docstring warning that has now been corrected to a regular
comment). Spec retains its sole original sorry. The expanded integrated
605-report audit was still running when this note was written.
Logs: /tmp/quadrilateral_absorption_final.log,
/tmp/quadrilateral_absorption_audit.log,
/tmp/work_quadrilateral_absorption.log,
/tmp/spec_quadrilateral_absorption.log,
/tmp/integrated_quadrilateral_absorption_audit.log.

The new theorem quadrilateral_path_absorption proves: an edge-disjoint
four-cycle and ANY intersecting simple path have a two-simple-path partition.
This is a structural proof, not finite verification. Exact pattern diagnostics
(/tmp/c4_path_patterns.py, /tmp/c4_path_patterns.log) passed 464 reduced
intersection patterns and guided discovery of three explicit surgeries:
- missing_corner: the first cycle vertex has a neighbor absent from the path;
- adjacent_first: the path's first two cycle visits are adjacent on the cycle;
- crossing_order: cycle u-v-w-z-u, path visits u,w,v,z in that order.
first_hit_split, opposite_first, and absorb_at_first prove these cases cover
all intersection patterns. The old path may have arbitrarily long segments.
The diagnostic is not used in any Lean proof.

Global maximum consequences:
- maximal_square_no_intersecting_path;
- maximal_single_defect_no_square (connected graph, at least two slots);
- budget_maximum_no_square;
- whole_cycle_length_ge_five (using the earlier triangle exclusion).
The main conjecture branch now retains hwholeCycleLength. This excludes WHOLE
quadrilateral members, not four-cycle prefixes of open lollipops. It does not
settle the exact-budget rooted defect or the independent-even-vertex case.

Next local development in progress: PentagonIntersection.lean. It aims to
prove that a five-cycle and an intersecting path can be absorbed whenever
the path misses a cycle vertex. The proposed proof shortens the cycle at a
missing corner: exchange the ear with an existing path chord, or add a
virtual chord and expand it again after quadrilateral absorption. The generic
expand_pair and four_cycle_path_absorption helpers have compiled; the longer
missing_ear_five proof is currently being checked. This module is NOT yet
integrated or audited and must not be assumed complete.


## Five-cycle intersection saturation (verified; integrated)

PentagonIntersection.lean (336 lines) is complete and warning-free. All ten
lemmas pass the standalone axiom audit with only propext, Classical.choice,
Quot.sound. Its body is now inlined as PentagonIntersection into Work and
Spec; full integration builds and the expanded 615-report audit are pending
at the time of this entry. The earlier quadrilateral 605-report audit
completed successfully. Logs for this extension:
/tmp/pentagon_intersection_final.log,
/tmp/pentagon_intersection_audit.log,
/tmp/work_pentagon_intersection.log,
/tmp/spec_pentagon_intersection.log,
/tmp/integrated_pentagon_intersection_audit.log.

Key new lemmas:
- expand_pair lifts a two-path edge cover when one edge is replaced by an
  internally fresh path; it does not require covering all ambient edges.
- four_cycle_path_absorption is the arbitrary-walk representation wrapper.
- endpoint_edge_forces_length_one: a simple path using the edge joining its
  endpoints must have length one.
- missing_ear_five: C=r-u+R+v-r, length(R)=3, and an intersecting path P
  avoiding r can be covered by two paths. If uv is in P, exchange that chord
  with the two-edge ear using CycleEar. Otherwise work in the graph obtained
  by deleting r and adding the virtual edge uv, apply four-cycle absorption,
  and expand uv back to u-r-v. Edge cover and freshness are fully tracked.
- five_cycle_missing_start and five_cycle_missing_absorption remove the
  chosen-representation restriction and rotate to any missing vertex.
- maximal_cycle_not_absorbable gives the generic strict score contradiction
  for replacing one whole cycle and another path by two paths.
- maximal_five_cycle_path_contains / single_defect_five_cycle_contains:
  every path meeting a whole five-cycle in the appropriate maximum contains
  ALL its cycle vertices.
- five_cycle_equal_members: all five cycle vertices have exactly the same
  set of member indices in a single-defect global maximum.

The original main branch retains hfiveCycleIncidence as well as
hwholeCycleLength. These do NOT eliminate five-cycles or open lollipops,
and do not close the exact-budget global repair gap.

### Rejected outside-path transfer shortcut (exact diagnostic, not formalized)

The assertion that two PRIVATE vertices of one path can always be separated
between two replacement paths if the other path intersects between them is
false. /tmp/private_vertices_exchange.py stopped at its 54th structural
configuration. Its paths are
  P = 6-0-3-1-2-4-7
  Q = 0-2-5-1,
and the private vertices are 3 and4. Vertex2 has degree4, so both members of
ANY two-path partition must contain2. The four odd vertices are 0,1,6,7,
so all endpoint slots are fixed there. The degree-two vertices3,4,5 have no
endpoint slots and pair their incident edges. The triangle 1-2-5-1 must
split into its two 1-to-2 arcs, one per path (otherwise one member contains
the whole triangle). Thus the path using 0-3-1 continues along its triangle
arc to2. It cannot next use2-0, which would repeat0, so it uses2-4-7.
Therefore3 and4 are forced into the same member.
This only invalidates an unrestricted TWO-member private-vertex transfer;
it is not a Gallai counterexample and was not added as a proof assumption.
Log: /tmp/private_vertices_exchange.log. The diagnostic has finished.


Quadrilateral/pentagon final checkpoint: both full integration builds passed.
Work is warning-free; Spec has only the original theorem's sorry warning.
The integrated audit finished with 615 reports, zero errors, and only the
three permitted axioms. The original theorem type and sole import were
explicitly checked unchanged. Work has 29,897 lines; Spec has 30,149.
The original theorem begins at line29,921 and its sole remaining sorry is
at line30,147. All proof builds and audits from this continuation have
finished. No conjecture disproof or complete proof has been obtained; no
submit_proof call was made.

The central blocker remains a GLOBAL rearrangement of a maximum-score,
exact-budget single rooted defect into paths. Whole cycles of length3 or4
are now ruled out; a whole five-cycle is either wholly contained in each
other path or missed by it. These constraints do not supply the required
multi-member exchange, and open lollipops are not excluded by them.

## Cycle endpoint-slot counting (verified; integrated)

CycleEndpointSlots.lean (123 lines) contains four complete lemmas. Its
standalone compilation is warning-free and all four axiom reports contain
only propext, Classical.choice, Quot.sound. The body is inlined into Work
and Spec as CycleEndpointSlots. The original branch retains hfiveCycleSlots.
Work integration has finished successfully; Spec integration and the expanded
integrated audit are pending at the time of this entry.

- common_cycle_vertex_other_endpoint: if every indexed trail contains a
  vertex v of a whole cycle member and |V| <= 2*k, some OTHER member has
  endpoint v. No score or maximality hypothesis is needed. Replace the cycle
  by its rotation at v using replace_one_general. If there were no other
  endpoint slot there, the new quota would be two, contradicting the existing
  root-degree capacity bound and the fact that every member contains v.
- common_cycle_length_bound: if all members contain every cycle vertex,
  inject those vertices into {j : Fin k // j != i} x Bool to obtain
  C.length + 2 <= 2*k.
- cycle_avoiding_path_card: a nonnil path disjoint from a cycle's vertices
  gives C.length + 2 <= |V|.
- five_cycle_four_slots: a whole five-cycle in a single-defect global score
  maximum at |V| <= 2*k requires k >= 4. If all members contain its vertices,
  apply the slot injection. Otherwise pentagon incidence saturation yields
  a nonnil path avoiding all five vertices, so |V| >= 7.

Logs: /tmp/cycle_endpoint_slots4.log,
/tmp/cycle_endpoint_slots_audit.log,
/tmp/work_cycle_endpoint_slots.log, /tmp/spec_cycle_endpoint_slots.log,
/tmp/integrated_cycle_endpoint_slots_audit.log.

Additional exact diagnostics (NOT Lean proofs and NOT used in any theorem):
/tmp/c5_internal_excursion.py passed all 480 reduced patterns in which a path
visits all five cycle vertices and has an internal vertex outside the cycle.
The analogous six- and seven-cycle tests passed 5008 and 61600 patterns.
However the proposed UNRESTRICTED internal-excursion absorption is FALSE.
The eight-cycle diagnostic finished all 876624 patterns, with eight failures.
One is
  C = 0-1-2-3-4-5-6-7-0,
  P = 0-3-8-4-7-9-6-1-10-2-5.
It visits every cycle vertex and has three internal excursions, but the
exact two-path partition check returns no partition. This matches the
longer-cycle limitations already recorded above; do not promote the small
finite passes to a general theorem. Logs are /tmp/c[5-8]_internal_excursion.log.
A separate C6 missing-vertex test passed 25608 patterns; the known C9
counterexample still rules out the unrestricted missing-vertex assertion.

No Lean proof of five-cycle internal-excursion absorption was developed.
No complete Gallai proof or counterexample has been obtained. A network
attempt to check the current literature status failed at DNS resolution;
it supplied no new mathematical information. The only source change in
the main conjecture branch is the additional verified hfiveCycleSlots fact.
The original statement and sole import remain unchanged; the sole remaining
sorry is the original general case. No new submit_proof call was made.

Cycle endpoint-slot final checkpoint: both full integration builds passed.
Work is warning-free; Spec has only the original theorem's sorry warning.
The full integrated audit finished with 619 reports, no errors or warnings,
and only the three permitted axioms. The original statement and sole import
were explicitly checked unchanged. Work has 30,019 lines; Spec has 30,274.
The original theorem begins at line30,043, and its sole sorry is at line30,272.
All development builds, diagnostics, and audits in this continuation have
finished. The Gallai conjecture remains unresolved; no proof was submitted.

## First-cycle-visit exchanges and bounded intersection (verified; integrated)

CycleFirstVisits.lean (236 lines) has eight complete, audited lemmas. A
cycle can be reoriented to start at any specified cycle edge
(cycle_edge_first). The generic adjacent_first_surgery and its wrappers
absorb a cycle of ANY length with a path whose first two visits to it are
adjacent along the cycle. The path excursion's first edge is split off,
and the cycle's complementary arc is traversed backwards. The missing-
first-neighbor surgery absorbs if a neighbor of the first visit never
appears later. Hence, at a global score maximum, first two cycle visits of
another path are not adjacent on the cycle, and both cycle neighbors of
the first visit occur later in that path. These facts do not claim that any
particular neighbor can be exposed by the rooted-tail algorithm.

CycleIntersectionBound.lean (315 lines) has five complete audited lemmas.
small_intersection_absorption proves: an arbitrary-length cycle and an
intersecting edge-disjoint path have a two-path cover if their vertex
intersection has cardinality at most FOUR. The induction shortens at a
cycle vertex absent from the path. If the resulting chord belongs to the
path, cycle_ear_exchange moves the ear into the path; the new cycle/path
intersection is contained in the old one. Otherwise use a virtual chord
in the graph with the missing vertex removed, apply induction, and lift
with expand_pair. Triangles and quadrilaterals are the base cases. This
is a structural induction, not an inference from finite diagnostics.

Consequently every path meeting a WHOLE cycle member of a single-defect
global score maximum shares at least FIVE vertices with that cycle. The
main branch records hcycleIntersection. This generalizes the pentagon's
incidence saturation but still does not absorb open lollipops.

Both modules are inlined into Work and Spec. Full integration builds passed
(Work warning-free; Spec only its original sorry warning). The expanded
integrated audit finished with 632 reports, no errors/warnings, and only
permitted axioms. Logs:
/tmp/cycle_first_visits3.log, /tmp/cycle_first_visits_audit.log,
/tmp/cycle_intersection_bound_final.log, /tmp/cycle_intersection_bound_audit.log,
/tmp/work_cycle_intersection_bound.log, /tmp/spec_cycle_intersection_bound.log,
/tmp/integrated_cycle_intersection_bound_audit.log.

Lean detail: in a recursively defined theorem, an automatically included
section variable G is fixed in recursive calls. Explicitly declare
{G : SimpleGraph V} in the theorem's binder when induction changes the
ambient graph. small_intersection_absorption is well-founded on C.length
and recurses across the virtual-chord graph.

A direct odd-root/forest normalization shortcut was NOT established.
Do not infer fixed-quota normalization merely from |V| <= 2*k and an acyclic
zero-quota induced graph, even for rooted defects: the eight-vertex rooted
obstruction described earlier becomes an exact-budget four-trail example
by adding a nil member at vertex6. Its quotas on {5,6,7} sum to five, and
at vertex0 the path cut bound would require 5+1+5 <= 8+1. Its zero-quota
graph is still the single edge12 plus isolated3, a forest. This family is
NOT globally score-maximal when quotas are free (it has a nil slot), so it
does not refute the conjecture or the global-maximum reduction. It shows
that maximality cannot be silently omitted from a proposed new argument.

## Tail-preserving lollipop ear exchanges (verified; integrated)

LollipopEar.lean (436 lines) contains twelve complete, warning-free lemmas
and the RootedCycleRep structure. All twelve standalone axiom reports use
only propext, Classical.choice, Quot.sound. The body has been inlined in
Work and Spec. Full integration builds are pending at this entry.

The local theorem ear_exchange_with_tail extends cycle_ear_exchange:
C = x-u + R + v-x has a missing ear vertex x in another simple path P,
P uses chord uv, and a fixed root r lies on R. A simple tail S starts at r
and meets C only at r. Exchanging the ear into P shortens C, re-roots the
new cycle at r, and leaves S unchanged. The new path is edge-disjoint from
S because its edges come from the old C/P union. The new cycle still meets
S only at r because its vertices are a subset of C's vertices.

shorten_rooted_member performs this surgery in a trail family. It preserves
score, the rooted defect, and EVERY endpoint quota exactly. This is not a
rootification theorem for an internal repetition. Its input is already an
explicit rooted cycle with an attached simple tail.

RootedCycleRep T r stores an oriented member, its root cycle, simple tail,
endpoint equalities, freshness, and subgraph equality. exists_rooted_cycle_rep
obtains this structure from HasRoot and one-defect score; replace_one_general
only reorients that member, preserving every indexed subgraph and all quotas.
exists_shortest_rooted_cycle minimizes cycle length over families with the
same score, fixed root r, and fixed endpoint quotas. This is an honest
nonempty minimization over rooted representations; no internal defect is
silently promoted to a rooted one.

RootedCycleRep.no_removable_ear records the resulting obstruction. In a
smallest failing graph, a degree-two cycle vertex has adjacent neighbors.
If the rooted cycle has length at least four and the fixed root has degree
at least three, that neighbor chord belongs to another path, and the other
path avoids the degree-two vertex. The tail-preserving ear exchange shortens
the cycle, a contradiction. The chord cannot belong to the old tail because
both its endpoints lie on the cycle, which meets the tail at only one vertex.

exists_shortest_rooted_cycle_structure packages the valid conclusion:
  a shortest rooted cycle is a TRIANGLE, OR every cycle vertex has degree >=3.
The triangle alternative MUST remain: a triangular ear cannot be replaced
by a two-cycle in a simple graph. This is not a proof that all lollipop
cycles have length at least five, nor that triangle lollipops can be repaired.

Main branch update: after selecting the high-degree minimum-energy root in
T₁, the proof now selects T and L : RootedCycleRep T r with the same score,
root and endpoint quotas. Thus quotaEnergy is exactly unchanged, and the
old global minimum-energy property is explicitly transferred to T. All
previous maximum-score, quota-one-or-two, high-degree-root and locality
facts remain available for T. The new hrootCycleCases and hrootCycleMin
refer to THIS same selected T, not an independently optimized family.
This compatibility is stronger than the earlier whole-cycle minimization.
The independent shortest-whole-cycle theorem remains separate.

Logs: /tmp/lollipop_ear7.log, /tmp/lollipop_ear_audit.log,
/tmp/work_lollipop_ear.log, /tmp/spec_lollipop_ear.log.

The remaining mathematical obstacle is still the global exact-budget repair.
The selected defect may be an open triangular lollipop, or a larger rooted
cycle all of whose vertices have degree at least three. None of the new
lemmas repairs those configurations in full. The original conjecture's
statement and import are unchanged, and its sole sorry remains. No proof
or disproof submission has been made.

Lollipop-ear final integration checkpoint: Work compiled warning-free. Spec
compiled with only the original conjecture sorry warning. The complete
integrated audit finished with 644 reports, all explicitly parsed to use
only propext, Classical.choice, Quot.sound, and no errors or warnings. The
original theorem starts at line 31027; its sole sorry is at line 31274.
Work and Spec have 31003 and 31276 lines respectively. The conjecture is
still unresolved; no proof submission has been made.

## Whole-member-group expansion and endpoint activation (verified; integrated)

MemberExpansion.lean and MemberNormalExpansion.lean supply 25 complete lemmas
(17 and 8). Their standalone builds and axiom audits passed with only the
three permitted axioms. The first full integration checkpoint also passed:
Work warning-free, Spec only the original sorry warning, and 669 permitted
axiom reports in /tmp/integrated_member_expansion_audit.log.

MemberExpansion defines selectedGraph, selectedParts, and intersectionGraph.
replace_selected replaces an ARBITRARY selected group by a path partition,
retaining all outside path members. selected_paths_partition realizes the
original selected paths in their own edge-union graph. Connectivity of the
selected support follows either from a common vertex or from connectivity
of the member-intersection graph. In a smallest-order failure:
- A connected group containing the sole defective member, if its support is
  proper, has at least 2*|A|+1 support vertices (defect_group_expands and its
  single-defect and intersection-connectivity wrappers).
- Deleting one normal member, if the rest has connected support, leaves at
  least 2*ceil(n/2)-1 support vertices. In odd order this is all n vertices.
  This condition is not an unconditional assertion that deletion is connected.

MemberNormalExpansion proves one_defect_two_paths for arbitrary one-defect
trails, including INTERNAL repetitions. This merely splits into two paths;
it does not preserve the member count and is not a rootification theorem.
The proof uses NilSlot.nonpath_cut and the vertex-intersection cardinality
identity; with total defect one the two portions must both be paths.
replace_selected_and_member permits a whole group replacement and a separate
single-member replacement, with the count tracked. normal_group_cannot_save
then shows that a group excluding the defect cannot be compressed by a slot:
the freed slot would split the defect and complete the whole graph.
Consequences:
- normal_group_expands: every connected normal group satisfies
    2*|A| <= |support|+1.
  No separate smaller-support assumption is needed; a violating group would
  automatically have fewer than n vertices at the exact Gallai budget.
- normal_group_exact: the selected graph has path number exactly |A|, and an
  optimal partition has no empty-edge members.
- tight_normal_group_three_even: if |support|=2*|A|-1, its support-induced
  graph has at least three even-degree vertices. The sharp one-even formula
  would otherwise free a slot.
- tight_normal_group_marked: in this tight odd case, EVERY support vertex
  can be a genuine nonnil path endpoint in a partition of exactly |A| paths.
  Add one leaf and use smaller-order minimality. The augmented order is
  strictly below n because A omits the defective index. Project the leaf,
  and exclude a nil marked path using normal_group_cannot_save.

GroupActivation.lean adds five complete, warning-free lemmas. It is inlined
as GroupActivation. Its standalone audit and the expanded full integration
checkpoint are pending at this entry.
- replace_path_group_tracked replaces a group of paths by any equal-cardinality
  path partition of its selected graph. Every unselected indexed member keeps
  both endpoints AND its entire subgraph. The score is exactly preserved,
  proved by equality of every indexed defect. Endpoint quotas inside the
  changed group are NOT claimed to remain fixed.
- repair_with_marked_outside_group: if a group wholly avoids the repeated
  start but admits a marked endpoint at the exposed first neighbor, reoptimize
  that group, orient the marked member, and apply the original endpoint slide.
  The donor and the attached tail stay unchanged until this last slide.
- tight_outside_group_misses_neighbor: a tight connected outside group cannot
  contain the exposed neighbor, by the proved marked-group theorem.
- rooted_cycle_tight_group_avoids_neighbors: orient either root-incident edge
  of the cycle in RootedCycleRep as its first edge, preserving the attached
  tail. Thus BOTH cycle neighbors of the root avoid every tight connected
  normal group wholly avoiding the root.
- outside_group_meeting_cycle_neighbor_expands strengthens the normal-group
  bound to 2*|A| <= |support| for a connected outside group meeting either
  of these cycle neighbors.

The main branch retains hdefectGroupExpansion, hnormalGroupExpansion,
htightGroupEven, htightGroupMarked, and houtsideGroupExpansion for its selected
family T and the same shortest-cycle witness L. The original statement and
sole import were explicitly checked unchanged at both integrations. The sole
original sorry remains; these results do NOT settle the conjecture.

Build and audit logs:
 /tmp/member_expansion6.log, /tmp/member_expansion_audit.log
 /tmp/member_normal_expansion6.log, /tmp/member_normal_expansion_audit.log
 /tmp/work_member_expansion.log, /tmp/spec_member_expansion.log
 /tmp/integrated_member_expansion_audit.log (669 reports, verified)
 /tmp/group_activation5.log, /tmp/group_activation_audit.log
 /tmp/work_group_activation.log, /tmp/spec_group_activation.log
 /tmp/integrated_group_activation_audit.log (expected 674 reports; pending)

The global gap remains: an outside group meeting a root-cycle neighbor may
have >=2*|A| vertices and need not admit a marked partition at its current
count. No argument forces a suitable tight group or makes an arbitrary
outside surplus reachable by the rooted exchange procedure.

Possible next direction, NOT PROVED: for a WHOLE cycle member, reroot it at
any cycle vertex outside a tight normal group's support. The new activation
lemma should force the group's intersection with the cycle to be closed under
cycle adjacency. If this closure can be formalized, a tight normal group
meeting the whole cycle would contain all of it; then defect-group expansion
would rule it out. This remains a prospective deduction, not a lemma in Spec,
and would still leave non-tight groups and open lollipops unresolved.

GroupActivation integration checkpoint completed: Work clean; Spec only the
original sorry warning. The full audit has 679 (not 674 as previously
expected) distinct reports, each parsed and verified to use only permitted
axioms. No errors or warnings. The separate five GroupActivation reports
were also parsed and verified.

CycleGroupDisjoint.lean now compiles warning-free, and all five lemma
reports have been parsed and verified to use only permitted axioms. It is
inlined as CycleGroupDisjoint in Work and Spec. The rotation-and-closure
argument described above is now proved for WHOLE cycle members. The
statement/import checks passed; full integration builds are pending.
Logs: /tmp/cycle_group_disjoint2.log, /tmp/cycle_group_disjoint_audit.log.
The original sorry remains and the full conjecture is still unresolved.

CycleGroupDisjoint full integration checkpoint completed: Work clean,
Spec only the original sorry warning. The expanded audit has 684 distinct
reports; all parsed and verified with only permitted axioms, no warnings
or errors. Original statement/import unchanged.

MarkedCycleGroups.lean is separately verified (8 lemmas and 8 permitted
axiom reports). This generalizes whole-cycle closure to any normal group
with arbitrary genuine endpoint flexibility at its exact path budget. If
the group contains the cycle, has proper support, and at most 2|A|+2
vertices, defect-group expansion gives a contradiction. The doubled bridge
argument gives the required marked flexibility for connected groups with
at most 2|A| vertices whose doubled support has order below n. At doubled
order exactly n, global edge minimality suffices if the doubled group plus
one bridge has fewer edges than G. This module is not yet inlined.
Logs: /tmp/marked_cycle_groups2.log, /tmp/marked_cycle_groups_audit.log.

## Whole-cycle normal components and half-order marking (verified; integrated)

MemberComponents.lean (14 lemmas) and MarkedCycleGroups.lean (8 lemmas)
compile warning-free and their 22 axiom reports have been parsed and
verified to use only the three permitted axioms. CycleComponentBudget.lean
adds 11 further complete lemmas with a clean build and the same audit.
All three are now inlined in Work and Spec. The original theorem statement
and sole import were explicitly checked unchanged. Full builds are pending.

MemberComponents defines normalGraph (the intersection graph after deleting
one indexed member) and componentMembers. Each member component has
connected selected support; distinct components have disjoint support.
The member counts sum to k-1 and their support sizes sum to the support
size of the union of all normal members. In connected G every normal
component meets the removed member. Therefore, for a whole cycle member
in a smallest-order failure, each component with a paths has at least 2a
vertices: the previous tight-group disjointness theorem excludes 2a-1.
Thus the normal members together cover at least 2(k-1) vertices.

CycleComponentBudget defines the nonnegative surplus m-2a of each component.
The sum of these surpluses is at most two, or at most one in odd order.
A zero-surplus component has at least half the ambient order, by the marked
doubling argument. If it has exactly half the order, its doubled edge count
plus one is at least |E(G)|, by global edge minimality. Two distinct zero
surplus components would both have exactly half the order. Their edge-count
lower bounds contradict the disjointness of their edges and the at least
three additional cycle edges. Hence there is at most one zero-surplus
component. Since positive surplus components consume at least one of the
remaining at most two units, there are at most THREE normal components,
or at most TWO in odd order.

The main branch retains hcycleNormalSupport, hcycleComponentCount, and
hoddCycleComponentCount for its selected T, as conditional facts about
WHOLE cycle members. These results do not apply to an arbitrary attached
lollipop. They also do not exclude a single spanning normal component
with surplus one (odd n) or two (even n). No final contradiction is known.
The original sorry remains; this is not a completed solution.

Logs: /tmp/member_components4.log, /tmp/member_components_audit.log;
/tmp/marked_cycle_groups2.log, /tmp/marked_cycle_groups_audit.log;
/tmp/cycle_component_budget4.log, /tmp/cycle_component_budget_audit.log.

Lean note: sums over ConnectedComponent can acquire different Fintype
instances from computable versus classical DecidableEq on a subtype.
A direct rewrite or calc step with sum_component_orders failed even though
the statements are propositionally equal. The working proof uses convert,
Finset.sum_congr, and ext/simp on the two univ finsets. Do not repeatedly
attempt to unfold those instances; definitional comparison took minutes.

Auxiliary exact diagnostics, NOT proof assumptions: endpoint marking at a
saturated even-order path budget was checked on every connected graph of
orders 2, 4, and 6 in the graph atlas (119 graphs, 53 saturated), and all
11117 connected unlabelled graphs of order 8 (1284 saturated). Every vertex
was markable in an optimal n/2-path partition in those saturated cases.
This is only finite evidence for an auxiliary statement, not a general
proof and not a Gallai counterexample search. The order-8 run was restarted
at row 11001 with degree/parity pruning; rows 1--11000 and the final 117 rows
both completed. Logs: /tmp/marked_saturated.log, /tmp/marked_saturated8.log,
/tmp/marked_saturated8_tail.log. Script: /tmp/marked_saturated.py.

Do NOT generalize this to the proposed bound that at most n-2p vertices
can fail to be endpoints in all optimal p-path partitions. That bound is
false. On five vertices take edges 01,02,03,04,12,13,14 (two adjacent hubs
0,1 joined to three independent vertices 2,3,4). Its path number is two:
  2-0-1-3; 3-0-4-1-2.
One path cannot cover its seven edges. Both hubs have degree four, so in
ANY two-path partition they are internal in both paths, and neither can
be an endpoint. Thus there are at least two unmarkable vertices, whereas
n-2p=1. This obstruction does not invalidate the narrower even-order
saturation diagnostic, and is not a counterexample to Gallai.

Whole-cycle components integration build checkpoint: Work rebuilt without
warnings; Spec rebuilt with only the original theorem's sorry warning.
Spec has 32871 lines and Work 32556 lines. The theorem starts at line32580,
with its sole sorry at line32869. The expanded integrated audit is still
running (expected 717 reports). No complete proof or disproof was found,
and no proof has been submitted as a solution.

Final whole-cycle component checkpoint: the full integrated helper audit
finished with 717 distinct reports, no errors/warnings, and only propext,
Classical.choice, Quot.sound (each report parsed and checked). Both full
builds passed, with only the original sorry warning in Spec. All 38 new
lemmas from this continuation are in Spec and audited. Original statement
and sole import unchanged; original sorry remains. No proof was submitted
because the full conjecture is still unresolved. No builds or diagnostics
from this continuation remain pending.
Log: /tmp/integrated_cycle_components_audit.log.

## Lollipop outside groups and shortest tails (verified; integration underway)

LollipopGroups.lean has seven verified lemmas. A connected normal group
avoiding the repeated root and meeting either root-cycle neighbor cannot
have a same-count marked partition at that neighbor. If its doubled support
order is below the smallest failure order, it therefore has at least
2*|A|+1 vertices. At exactly half order the same holds if twice its edge
count plus one is smaller than the globally minimal failure's edge count.
Two support-disjoint outside groups meeting cycle neighbors cannot BOTH
have at most 2*|A| vertices: each would occupy at least half the graph,
but both omit the root. This works for open lollipops and quota-one roots.

TailEar.lean has fifteen verified lemmas. Exchanging a tail ear u-v-w for
a chord uw owned by a path avoiding v shortens the tail by one, leaves the
literal rooted cycle fixed, and preserves every endpoint quota and score.
One can minimize the tail after minimizing the cycle compatibly with the
minimum root-quota energy. In a smallest-order failure, a private internal
tail vertex has degree two, and degree-two reduction supplies the chord;
the exchange therefore proves every internal vertex of a shortest tail
belongs to some normal member. Separately, a vertex missing from all normal
support has degree at most three at the root, or two elsewhere. Thus in
odd order (minimum degree at least five) the normal support is spanning.

Both modules compiled warning-free. Their 22 standalone axiom reports
were parsed and use only the permitted axioms. They have been inlined in
Work and Spec; the main selection now uses exists_shortest_rooted_structure
and retains the shortest-tail, odd-spanning, and small-outside-expansion
consequences. Full builds and the expanded audit are pending. Statement
and sole import are unchanged. The original sorry remains.
Logs: /tmp/tail_ear7.log, /tmp/tail_ear_audit_final.log,
/tmp/lollipop_groups_audit_final.log, /tmp/work_tail_ear.log,
/tmp/spec_tail_ear.log.

## Independent even vertices do not rescue fixed-quota normalization

IndependentRootObstruction.lean is a verified EXTERNAL obstruction to an
auxiliary shortcut, not a counterexample to Gallai. It is not in Spec.
Its 17 audited results use only the permitted axioms.
On Fin 8 take edges 01,02,03,12,13,04,45,06,67 and four trails:
  0-2-1-3-0-6; 1-0-4; 4-5; 6-7.
The family has exactly the Gallai budget, a single rooted defect with root
quota one, all quotas at most two, and independent even-degree vertices.
The quotas are [1,1,0,0,2,1,2,1]. No four-path family can retain them:
at v=0 and S={4,5,6,7}, the degree/endpoint cut inequality would give
5+1+6 <= 8+2. Thus the family is maximum-score subject to those quotas.
It is NOT a free-quota maximum. Three paths suffice:
  7-6-0-1-3; 3-0-2-1; 0-4-5.
This three-path partition is also verified in Lean. The global free-quota
maximum hypothesis must not be replaced by fixed-quota maximality, even
with exact budget and independent even vertices.
Log: /tmp/independent_root_obstruction_audit.log.

LollipopGroups/TailEar integration checkpoint: Work compiled warning-free;
Spec compiled with only the original sorry warning. The expanded integrated
helper audit completed with 739 distinct reports: 734 with permitted axioms
and five axiom-free reports. All reports were parsed and checked. Note that
an audit parser must include the `does not depend on any axioms` format.
Log: /tmp/integrated_tail_ear_audit.log.

## Normal-remainder support for open lollipops (verified; inlined)

NormalRemainder.lean contains eleven new complete, warning-free lemmas.
Its standalone audit has eleven reports, all using only permitted axioms.
It is inlined in Work/Spec, and the main branch retains its three support
bounds. The updated full builds are pending at this entry.

A missing normal-support vertex has exactly one member incidence. If it is
the tail's final vertex and is not the root, its positive endpoint quota
forces degree ONE. Every other missing vertex lies on the rooted cycle:
a private internal tail vertex contradicts the verified shortest-tail lemma.
At most one cycle vertex can be missing. If the cycle is long, its vertices
have degree at least three, so the only possible missing vertex is the root.
If it is a triangle, two distinct missing vertices would be adjacent, one
having degree two and the other degree at most three. The smallest-failure
low-degree adjacency restriction excludes this.

Consequently the normal remainder omits at most TWO vertices, or at most
ONE if the graph is leafless. Combined with the odd-order spanning theorem,
its support always has at least 2*(ceil(n/2)-1) vertices for this compatible
cycle/tail optimization. This extends the previous whole-cycle normal-support
bound to arbitrary rooted lollipops; it does not prove every normal component
has nonnegative surplus or exclude a single spanning component.

Logs: /tmp/normal_remainder4.log, /tmp/normal_remainder_audit.log,
/tmp/work_normal_remainder.log, /tmp/spec_normal_remainder.log.
The original conjecture, import, and sole sorry are unchanged. The full
Gallai conjecture is still unresolved in this development.

## Another rejected local exchange (exact diagnostic only)

A triangle lollipop plus a path avoiding its root need NOT be replaceable by
two simple paths, even if the path meets BOTH other triangle vertices. Exact
edge-subset/path enumeration found this nine-vertex auxiliary obstruction:
  lollipop: 0-1-2-0-3-4-5-6
  path:     3-7-4-1-8-2-5.
Their edges are disjoint and the path avoids root 0. All nonroot triangle
vertices have degree four, and every internal tail vertex meets the path.
The graph has no two-path edge partition (diagnostic result, not yet separately
formalized). Its Gallai budget is FIVE, so this is not a counterexample to the
original conjecture. The weaker version allowing only one nonroot triangle
visit already fails at eight vertices:
  lollipop: 0-1-2-0-3-4-5
  path:     3-6-4-1-5-7.
Scripts/logs: /tmp/triangle_lollipop_test.py,
/tmp/triangle_lollipop_test.log, /tmp/triangle_lollipop_two_test.py,
/tmp/triangle_lollipop_two_test.log. Both diagnostics terminated at these
obstructions. Neither result has been used as a Lean assumption.

Normal-remainder final integration checkpoint: Work compiled warning-free;
Spec compiled with only the original conjecture sorry warning. The full
integrated helper audit has 750 distinct reports (745 with allowed axioms,
five axiom-free), all parsed and checked, and no errors or warnings.
Spec is 33659 lines; the unchanged theorem begins at line 33344 and its
sole sorry is line 33657. Work is 33320 lines and has no sorry. No build
or diagnostic from this continuation remains pending. The conjecture
is still unresolved, and no proof has been submitted as a solution.
Log: /tmp/integrated_normal_remainder_audit.log.

## One missing normal vertex (new verified modules; integration pending)

Five standalone modules, 22 complete lemmas, have now been inlined:
- ShortLollipop (9): a triangle with exactly one tail edge can be absorbed
  with an edge-disjoint path that avoids the repeated root and meets a
  nonroot triangle vertex. Arbitrary longer tails are NOT covered.
  At a cubic quota-one root every normal member avoids the root, and a
  triangular cycle has tail length at least two in a smallest failure.
- LeafTipSeparation (2): a leaf and a degree-two vertex cannot share a
  neighbor. Delete the two vertices; restore the path leaf-anchor-tip-b.
- TerminalTail (5): replace_two_finishes_general, and an exact
  terminal-edge transfer preserving every quota, score, and the literal
  rooted cycle. A shortest tail with a private finish distinct from its
  root has length ONE: the private finish is a leaf; its bridge neighbor
  has odd degree, hence a normal endpoint unless it is the root; transfer
  the last tail edge onto that member to contradict tail minimality.
- LeafCubicEven (3): a cubic neighbor of a leaf cannot have an even-degree
  neighbor. The other two neighbors are adjacent by the existing cubic
  leaf reduction. Delete leaf u and cubic v; the chosen even neighbor a
  becomes odd. Append v-a, then u-v at zero cost; restore v-b at cost one
  for two removed vertices. Thus no cubic rooted maximum has a leaf neighbor.
- NormalRemainderOne (3): normal support omits AT MOST ONE vertex; for a
  cubic root of quota at most two, it is exactly the complement of the root.
  If a cycle vertex x and the finish were both missing, the tail would have
  length one. If x is the root, the root would be cubic and adjacent to a
  leaf. Otherwise x is degree two on a triangle and shares the root with
  the finish leaf. Both cases are excluded by the preceding graph reductions.

All standalone development files compiled warning-free. Their audits use
only permitted axioms (the nonnil-last-edge lemma is axiom-free). The latest
cubic-support corollary is included in the pending full integrated audit.
The main branch now retains the improved missing-vertex count, exact cubic
normal support, private-finish tail length, cubic leaf-neighbor parity, and
leaf/degree-two neighbor separation. Original statement and import unchanged.
There is still ONE original sorry; the full Gallai conjecture is NOT proved.
Full builds/audit pending:
 /tmp/work_normal_one.log (PID 131578)
 /tmp/spec_normal_one.log and /tmp/integrated_normal_one_audit.log (PID 131579).
Note: Spec's final hnormalMissingCount call was changed after that build was
launched; ensure the final version is rebuilt if the build read the old file.

### New auxiliary marking question, not a theorem

For a connected graph on 2p+1 vertices with minimum path number p, can there
be two vertices of degree <2p which cannot be endpoints in ANY p-path
partition? An exact atlas diagnostic found no such pair: all 876 connected
odd-order atlas graphs (3,5,7 vertices), 585 saturated at p, passed. This is
finite evidence only, not a proof or a Gallai counterexample search.
Script/log: /tmp/marked_odd_capacity.py, /tmp/marked_odd_capacity.log.
The condition on degree is essential: K2 joined to three independent
vertices has p=2 and two unmarkable degree-four hubs. Without the order
condition, a tree with two adjacent degree-four vertices and six leaves
has p=3, both degree-four vertices unmarkable despite degree<2p, because
all six endpoints are forced at odd vertices. No general marking lemma
has been assumed or added to Lean.

One-missing-vertex final integration checkpoint: Work compiled warning-free;
Spec rebuilt after the final main-branch edit, with only its original sorry
warning. All 772 distinct integrated helper reports were parsed and checked: 
766 use only permitted axioms and six are axiom-free. Audit has no errors or
warnings. Spec is 34523 lines, Work 34168 lines. Original theorem starts at
34192, its sole sorry is line 34521; statement and sole import unchanged.
No complete proof or disproof exists, and no proof has been submitted.
Logs: /tmp/work_normal_one.log, /tmp/spec_normal_one_final.log,
/tmp/integrated_normal_one_final_audit.log. No builds remain pending.

The auxiliary odd-order marking diagnostic was also checked on the 6207
graph/pair constructions obtained by adding a degree-two vertex to a connected
all-odd graph on eight vertices, excluding pairs whose two old endpoints
already have degree seven (leaving fewer than two candidate vertices).
Of these, 1690 have path number four; none had two unmarkable vertices
of degree below eight. The diagnostic terminated normally. This is ONLY
finite evidence, not a proof, and no marking hypothesis was added to Lean.
Script/log: /tmp/marked_odd_capacity_extension.py and
/tmp/marked_odd_capacity_extension.log. No diagnostics remain pending.

## Prefix/free-tail checkpoint and external boundary obstruction (verified)

Work has 35,341 lines and no sorry. Spec has about 35,722 lines and exactly
the original conjecture sorry. The sole import and original statement are
unchanged. Work builds warning-free; Spec builds with only that sorry warning.
Integrated audit: 814 distinct helper reports, 808 with allowed axioms and six
axiom-free. Logs: /tmp/work_prefix_free.log, /tmp/spec_prefix_free_final.log,
/tmp/integrated_prefix_free_audit3.log. No proof of Gallai has been obtained.

42 newly integrated lemmas:
- TriangleTailTwo (18): a cubic triangular rooted lollipop has tail length >=3.
- CubicRemainder (5): its normal remainder is on 2*p+1 supported vertices,
  has minimum path number p, and has two distinct even-degree unmarkable
  vertices of degree <2*p. Connectivity of this remainder is NOT asserted.
- CyclePrefixRepair (6): a fully markable outside group misses the entire
  rooted cycle. Consequently an outside connected group meeting the cycle
  has nonnegative support surplus; a sufficiently small one has positive surplus.
- FreeTailGroups (13): a separate shortest-tail choice fixes score, root,
  literal cycle and tail nonnil, but not quotas or minimum quota energy.
  Fully markable normal components contain the finish, hence are unique.
  At cubic root quota is automatically one; the normal support is the root
  complement and there is at most one tight normal component.
Main branch keeps the original energy-minimal family and the new free-tail
choice as a SEPARATE existential certificate. Do not conflate their optima.

CycleBoundaryMarks.lean is external, complete, audited, NOT yet inlined.
Four results show first and last cycle visits to an outside normal group
are unmarkable; if there are at least two visits these give distinct even
unmarkable vertices. Logs: /tmp/cycle_boundary_marks1.log and
/tmp/cycle_boundary_marks_audit.log. All four reports have allowed axioms.

Important rejected auxiliary claims:
- Three-edge triangle-tail absorption fails (nine-vertex exact obstruction):
  lollipop 0-1-2-0-3-4-5; path 3-6-4-1-7-2-5-8.
- Deleting an edge from an Eulerian graph can increase minimum path number:
  three triangles in a chain have path number two; delete the middle triangle
  edge between its two articulation vertices, obtaining two triangles joined
  by a two-edge path, which has path number three.
- A cycle C plus two paths P,Q need not have a three-path partition even
  if Q avoids C and the endpoints of P both lie on Q. Replace the middle
  edge in the preceding chain by a corridor through five new vertices and
  add a complementary five-cycle there (core K5 minus one edge). The core
  and complement each require three local path pieces; two boundary edges
  permit at most two joins, so the twelve-vertex union needs at least four.
  This is not a Gallai counterexample (budget six).

Unproved auxiliary marking question remains: a connected graph on 2*p+1
vertices with minimum path number p cannot have two distinct unmarkable
vertices of degree <2*p. Exact finite checks have not found an obstruction.
Biconnected + endpoint slack (#odd <2*p) + this order condition may even
force every degree-<2*p vertex markable. Without slack, it fails at order
five. Without the order condition, it fails at order seven with p=2.
Finite checks: 479 biconnected odd-order atlas graphs (290 saturated/slack),
and 3442 structured order-nine constructions (1031 relevant); no obstruction.
These diagnostics are NOT proved lemmas and are not assumptions in Lean.

Potential unformalized reduction: a two-terminal region of >=5 vertices,
whose edges consist of a spanning path plus a cycle and whose only external
edges attach to the spanning path ends, can be replaced by a degree-two
proxy vertex. Induct on the smaller graph, expand the proxy into the path,
and restore the cycle with two extra paths. Removing >=4 vertices saves
at least two budget slots. This does not handle interspersed outside visits
or extra boundary edges, and is not a complete global argument.

Boundary-marks integration is now complete. Work compiles warning-free;
Spec has only the original sorry warning. The unchanged theorem begins at
line 35518. Integrated audit has 818 unique reports (812 permitted-axiom
reports and six axiom-free), all checked. Logs: /tmp/work_boundary_marks.log,
/tmp/spec_boundary_marks.log, /tmp/integrated_boundary_marks_audit.log.
No completed proof or disproof.

A broader auxiliary unmarkability bound has passed exact atlas diagnostics:
for a connected graph with minimum path number p, the number of vertices
unmarkable in every p-path partition and of degree <2*p may be at most
max(0,n-2*p). All 995 connected nontrivial atlas graphs passed. This bound
is only a candidate, not a theorem; it has NOT been assumed in Lean.
Script/log: /tmp/marked_general_capacity.py and .log.

The broader auxiliary bound from the preceding entry is FALSE. A structural
counterexample (confirmed by exact path enumeration) is as follows. Let A
have hubs 0,1,2 forming a triangle and adjacent to each of 3,4,5,6; those four
vertices are independent. Three paths partition A:
  3-0-1-4-2-6; 3-1-2-5-0-4; 3-2-0-6-1-5.
All three hubs have degree six, hence cannot be endpoints in any three-path
partition. Attach a disjoint triangle 7,8,9 by the single bridge 3-7.
The resulting ten-vertex graph has minimum path number four: restricting to
A and the triangle requires at least three and two local pieces, and the
single bridge permits at most one join. A four-path partition exists by
joining at 3 and 7. In every such partition the A-restriction has exactly
three pieces, so its three hubs remain unmarkable, now of degree 6<8.
Thus there are THREE low-degree unmarkable vertices but n-2p=2. This is an
auxiliary obstruction, NOT a counterexample to Gallai (budget five).
Log: /tmp/marked_split_blocks.log. The narrower odd saturated pair question
is not refuted by this example. Identifying rather than bridging a triangle
in several related nine-vertex split-graph constructions did not refute it.

Final checkpoint of this continuation: 35,873 lines in Spec, 35,492 in Work.
The unchanged erdos_583 statement starts at line 35,518; its sole sorry is
line 35,871. The only import is FormalConjecturesUtil. All builds/audits and
exact diagnostics have terminated. No complete proof or disproof exists.
The 64 variants formed by adding arbitrary edges among the four nonhubs
of the seven-vertex split graph and then attaching two leaves at one hub
also did not refute the odd saturated pair question. This is finite evidence
only. Script/log: /tmp/marked_split_leaves.py and .log.
An attempted reference-status check at erdosproblems.com was unavailable
because external DNS resolution failed; no external result was obtained.

## Two-terminal corridor compression (new verified external module)

Submission/CorridorReduction.lean now contains thirteen complete lemmas;
it compiles warning-free and all thirteen standalone audit reports use only
permitted axioms. It has NOT yet been inlined. A region S with two distinct
outside ports can be replaced by a single retained vertex a. Its proxy graph
is (within G S-complement plus u-a) plus a-v. Expanding the one edge a-v
through a fresh path restores the corridor with no increase in path count.
Restoring q additional path pieces then meets the vertex budget whenever
|S|>=2*q+1 (q>0). This avoids a needless two-case argument about which paths
contain the two proxy edges.

For a cycle, q=2, so a five-or-more-vertex region consisting internally of
one path and an edge-disjoint cycle is reducible if its only boundary edges
are at the two path ends. The final lemma, failure_no_single_contiguous_carrier,
connects this to the exact-budget maximal trail family: a whole-cycle defect
cannot have just one other member visiting its vertices in one contiguous
segment while every other member avoids the cycle. The lemma does NOT assert
that all cycle/path intersections are contiguous or have only one carrier.
Logs: /tmp/corridor_reduction8.log, /tmp/corridor_reduction_audit1.log.
The original conjecture still has its sorry and remains unresolved.

## Further rejected even-independent restoration shortcuts

Even when even-degree vertices are independent, deleting an even-to-even
path with odd internal vertices may reduce minimum path number. Length-three
example: K2 joined to four independent vertices (with the hub edge included),
delete a path leaf-hub-hub-leaf. Original path number is three, remainder two.

Even length TWO does not allow unrestricted zero-cost restoration. On nine
vertices take a K4 on hubs 0,1,2,3 and degree-two vertices with neighborhoods
4:{0,1}, 5:{0,1}, 6:{0,2}, 7:{0,3}, 8:{2,3}. The even vertices 4..8 are
independent. Vertex 0 has degree seven, so the original graph needs >=4 paths.
Deleting 4-0-5 leaves these three edge-disjoint simple paths covering all edges:
  4-1-0-2-3; 5-1-2-8-3-0; 1-3-7-0-6-2.
The path cover and degree were checked exactly. Neither example disproves
Gallai, and neither rules out a restoration theorem at the exact vertex budget.
The two-edge shortcut had passed all 78 relevant atlas graphs (328 paths),
illustrating why those finite checks were not a proof. Scripts/logs:
/tmp/even_independent_restore.py and .log;
/tmp/even_independent_two_restore.py and .log.

Corridor integration checkpoint: all fifteen lemmas plus the proxy definition
are now in Work and Spec. Work compiles without warnings; Spec compiles with
only the original sorry warning. Integrated audit: 834 distinct reports, 828
with permitted axioms and six axiom-free. The main branch retains the no-single-
contiguous-carrier reduction and the deleted-cycle corridor certificate.
The last two lemmas allow the removed cycle/subgraph to extend outside the
compressed region, provided its deletion is connected and the remaining region
is a clean corridor. Logs: /tmp/work_corridor_final.log,
/tmp/spec_corridor_final2.log, /tmp/integrated_corridor_final2_audit.log.

## Carrier splitting and a new global optimization (external, verified)

CarrierCuts.lean has three complete, warning-free, audited lemmas. At a first
visit z to a marked outside group, reoptimize the group to a path Q starting
at z. Split a carrier P=A+B there and replace P,Q by B,A+Q. The prefix A
avoids Q except at z, so both new members are simple; score and edge partition
are preserved. If both sides meet the unchanged whole cycle, each must meet
it in >=5 vertices. Their cycle intersections are disjoint (z lies outside
the cycle), hence the cycle has length >=10. This works for ANY cycle length,
without claiming that arbitrary marked vertices can be exposed simultaneously.
Logs: /tmp/carrier_cuts2.log, /tmp/carrier_cuts_audit.log.

CarrierCount.lean develops the stronger global version and currently compiles
warning-free. Touches S H means an EDGE of H is incident to S (nil members do
not count); carrierCount is the number of such members. With score and the
literal cycle member fixed, a maximum count exists. A marked outside-group
cut with cycle visits on both sides preserves score and the cycle, and raises
carrierCount by exactly one. Therefore it is impossible in a maximum-carrier
choice, with NO restriction on cycle length. This is a separate free-quota
optimization; it has NOT been claimed compatible with the main minimum quota
energy or minimum-cycle selection. The main conjecture remains unresolved.
Standalone count audit is being run at this entry; neither external module
has yet been inlined.

## Incidence-preserving carrier optimization (integrated checkpoint)

The free-quota carrier optimization has now been strengthened to preserve,
for EVERY vertex x of the fixed cycle, the number of members with an edge
incident at x. Nil members contribute zero. This does not claim preservation
of all endpoint quotas or global minimum quota-square energy.

New integrated namespaces (64 declarations in total):
- CarrierCuts (3 lemmas): marked outside cuts, disjoint intersections, and
  the length-ten consequence when both halves meet the cycle.
- CarrierCount (17 declarations, including the incidence API): choose a
  maximum carrier count with score, cycle subgraph, and all cycle incidences
  fixed. The internal marked-cut exchange raises count and preserves these
  constraints, so no such cut exists at the optimum.
- CarrierLength (10): minimize total carrier length among these maxima.
  Any fully marked outside group meeting a normal carrier contains an
  endpoint of that carrier. Both internal-cut and prefix-shortening
  exchanges now explicitly return incidence-preservation certificates.
- CarrierGroups (3): disjoint fully marked outside groups charge injectively
  to normal-carrier endpoint slots, so there are at most 2*t of them.
- GroupComponents (14): components of an arbitrary selected member-index
  set; support disjointness, connectivity, closure, and cardinal sums.
- OutsideCarrierBudget (11): for a smallest Gallai failure and this optimal
  whole-cycle family, with t normal carriers and cycle length l,
      l + 2*ceil(n/2) <= n + 4*t + 2.
  Hence l<=4*t+2, improved to l<=4*t+1 at odd order. Tight outside components
  are fully marked and are charged to carrier endpoints. This is a bound,
  NOT a contradiction.
- CarrierDeficiency (6): a small-quota root has incidence count below k;
  the new optimization preserves that deficiency. For a whole five-cycle,
  every normal carrier visits all five vertices, so its total carrier count
  equals its count at the original root. Consequently the optimized family
  still has a member avoiding the ENTIRE five-cycle and t+2<=k.

The incidence lemmas were inlined into CarrierCount to avoid an import cycle;
Submission/CarrierIncidence.lean remains a separate redundant development,
not imported by the integrated file. All comparison hypotheses in the count,
length, endpoint, and outside-budget theorems now have the required incidence
premise, which is supplied by the actual exchanges. No unrestricted optimum
has been silently conflated with the constrained optimum.

All seven namespaces are in Work and Spec. The main unresolved branch keeps
hoptimizedRootCycle and hoptimizedCycleBound as additional certificates.
The original statement and import are unchanged; the sole original sorry
remains. Work compiles warning-free; Spec has only the original sorry warning.
Standalone audits: /tmp/carrier_upgrade_audit.log (58 reports) and
/tmp/carrier_deficiency_audit.log (6 reports), all permitted.
Integrated build/audit logs:
  /tmp/work_carrier_upgrade_final.log
  /tmp/spec_carrier_upgrade_final.log
  /tmp/integrated_carrier_upgrade_audit.log
Backups before integration:
  /tmp/work_before_carrier_upgrade.lean
  /tmp/spec_before_carrier_upgrade.lean
  /tmp/audit_before_carrier_upgrade.lean
Unrestricted external module backups: /tmp/carrier_free_checkpoint/.

No complete proof or disproof of the original conjecture has been obtained.

The narrow odd saturated unmarkability candidate remains only a candidate.
Ten additional structural bridge-plus-leaf variants of the seven-vertex
three-hub split graph did not refute it (seven met the saturation premise;
three did not). The cases attach the triangle bridge at a hub or nonhub,
then attach one leaf at a hub, nonhub, or triangle vertex, giving order eleven.
This finite exact check is NOT a proved lemma or assumption. Script/log:
/tmp/marked_hub_attachment.py and /tmp/marked_hub_attachment.log.

## Pentagon excursion and whole-pentagon exclusion (integrated)

The whole-pentagon case has now been excluded from a smallest-order Gallai
failure. This is a genuine verified reduction, NOT a solution of the general
conjecture. Thirteen production modules have been inlined in Work/Spec:

- PieceRoutes: generic edge-labelled routes, preserving parallel abstract
  pieces via their IDs; expansion to walks, path simplicity, edge coverage,
  and two-route partition certificates.
- PentagonFinite and PentagonRoutes (one namespace): 160 explicit finite
  route pairs for a five-cycle and a path with one inserted outside vertex.
  All checks use kernel `decide`, NOT native_decide. The finite checker is
  stated with five nested Fin variables and an explicit vector; direct
  enumeration of a function Fin5 -> Fin5 overflowed the default stack.
- PathIntervals: closed support intervals, half-open edge intervals,
  intersection/disjointness, edge and support congruences, and path splitting.
- OrderedPathPieces: consecutive marked intervals and their complete cover.
- PathIntervalRestore: reattach the old path's exterior tails to a two-path
  cover of its middle plus an edge-disjoint cycle.
- PentagonCoordinates: ordered cycle visits along a path, insertion of an
  excursion position, and the six-vertex coordinate map.
- PentagonPieceSystem: realizes finite route certificates by five actual
  cycle edges and five actual marked path pieces.
- PentagonExcursion: if an edge-disjoint simple path contains all five
  vertices of a five-cycle and their union has no two-path cover, all five
  visits are contiguous. The middle path has exactly four edges and the
  same vertex set as the cycle. The family corollary is
  `maximum_carrier_contiguous`.
- PentagonCarriers: two distinct carriers would contribute 5+4+4=13
  distinct edges on five vertices, exceeding choose(5,2)=10. Hence a whole
  pentagon has at most one normal carrier in a single-defect global maximum.
- OddContiguousRegion: strip the last edge of a prefix / first edge of a
  suffix; a one-tail odd-cycle region contradicts bridge-cut parity, a
  two-tail region contradicts corridor compression.
- PentagonExclusion: a normal carrier exists by connectedness. It is unique
  and contiguous. The earlier four-slot bound gives n>=7; the preceding
  odd-region reduction rules it out. Main results:
    `failure_no_whole_pentagon`
    `whole_cycle_length_ge_six`.

The main unresolved branch now retains `hwholeCycleLength` with conclusion
6 <= C.length (instead of 5 <= C.length). Original statement and import were
checked unchanged; the original sorry remains. No proof has been submitted.

First full successful integration checkpoint:
  /tmp/work_pentagon_upgrade3.log       (clean, exit 0)
  /tmp/spec_pentagon_upgrade3.log       (original sorry warning only, exit 0)
  /tmp/integrated_pentagon_upgrade_audit.log (exit 0)
The integrated audit had 1012 unique reports: 992 with permitted axioms and
20 axiom-free. The 114-declaration standalone audit also passed:
  /tmp/pentagon_excursion_audit2.log.

Two technical integration failures were fixed:
- Parallel full Work/Spec builds exceeded the cgroup's 10 GiB memory limit
  (both exit 137). Host free memory is irrelevant. Full builds are now
  sequential. No proof failure was involved.
- PieceRoutes redeclared universe u, which the enclosing integrated
  namespace already declares. Its inlined universe declaration is `v w`;
  the standalone module still declares `u v w`.

Integration script: /tmp/integrate_pentagon.py (already run; do not rerun on
an already integrated source). Pre-integration backups:
  /tmp/work_before_pentagon_upgrade.lean
  /tmp/spec_before_pentagon_upgrade.lean
  /tmp/integratedaudit_before_pentagon_upgrade.lean

### Parity-free contiguous-carrier strengthening (integrated, final rebuild pending)

ContiguousRegion.lean adds six complete lemmas, all standalone audited with
only allowed axioms. In a one-tail region the attachment vertex has degree
four: two cycle edges and two carrier edges. Its unique crossing edge is a
bridge, whereas every bridge endpoint in a smallest failure is odd. This
removes the odd-cycle restriction, provided the middle segment is nonnil.
The other cases use connectedness or the existing two-terminal corridor
reduction.

`failure_no_single_contiguous_member` gives the direct family consequence:
no whole cycle in a smallest failure has exactly one normal carrier whose
cycle visits form one nonempty contiguous segment, even if either exterior
tail is nil. The other members avoid the cycle; there are at least three
slots, so one such other member witnesses that the cycle does not span all
vertices. This supplies the proper-region size condition automatically.

The main branch's hnoContiguousCarrier is now this stronger theorem.
Backups before these six lemmas:
  /tmp/work_before_contiguous_upgrade.lean
  /tmp/spec_before_contiguous_upgrade.lean
Standalone logs:
  /tmp/contiguous_region3.log
  /tmp/contiguous_region_audit.log
Sequential final rebuild/audit launched at this entry:
  /tmp/work_pentagon_final.log and .exit
  /tmp/spec_pentagon_final.log and .exit
  /tmp/integrated_pentagon_final_audit.log and .exit
Do not assume this pending final rebuild has finished until checking exits.

### Further finite diagnostics — no new mathematical assumptions

The broad cycle-plus-path absorption claim when one cycle vertex is absent
was briefly revisited, then immediately rejected on re-reading the earlier
14-vertex obstruction (see MOBILE DEFECT above). Moreover, even the narrower
version with NO internal excursions is false: C is the natural cycle on
0,...,10, and
  P = 3-5-2-4-1-8-10-7-9-6
misses vertex 0, yet C+P has no partition into two paths. Exact exhaustive
solver log: /tmp/cycle_missing_vertex_large.log (first failure at length 11).
The preceding checks through length 10 passed; they prove nothing general.
This is not a Gallai counterexample (two paths versus a budget of six).

Additional symbolic route checks (not used in Lean): splitting a cycle edge
in the five-cycle plus a spanning path admits 200 finite certificates after
outer-adjacency exclusions. Similar one-split templates for six/seven cycles
have failures when unsplit abstract path links are parallel to cycle edges;
those links require additional fresh vertices in any actual edge-disjoint
realization. Thus the earlier actual six/seven-cycle excursion diagnostics
are not contradicted, but a direct copy of the pentagon certificate does not
suffice. Script: /tmp/small_cycle_routes.py; data /tmp/routes_*.json.

Open directions remain multi-carrier cycles and arbitrary open lollipops.
The current carrier optimization gives l<=4t+2 (l<=4t+1 for odd order), not
an elimination. An informal attempt to charge only t rather than 2t marked
outside components has no proof: a carrier can leave and reenter an outside
component along its tail, so unique endpoint incidence alone does not give
a unique crossing edge. Do not silently infer a bridge from that fact.


Final pentagon/contiguous-region checkpoint completed: all three sequential
build/audit exits are zero. Work is warning-free; Spec has only the original
conjecture's sorry warning. The final integrated audit has 1018 unique
reports (998 permitted-axiom reports and 20 axiom-free), all parsed and
checked. The standalone ContiguousRegion audit was rerun after adding its
module docstring and is warning-free. No build or diagnostic remains pending.
Work has 38,974 lines; Spec has 39,364 lines. The unchanged conjecture starts
at line 39,000, and its sole original sorry is line 39,362. Its only import
remains FormalConjecturesUtil. The general conjecture remains unresolved;
no proof or disproof has been submitted.

## Five shared vertices force a pentagon (external, verified)

Seven additional production modules now compile and have a complete 57-report
standalone axiom audit (52 permitted-axiom, five axiom-free):
  HexagonFinite, HexagonRoutes, PathRestoreIntersection, HexagonCoordinates,
  HexagonPieceSystem, HexagonMissing, CycleIntersectionSix.
They are NOT yet inlined at this entry.

HexagonFinite checks 48 route pairs with ordinary kernel `decide`. They cover
a six-cycle whose vertex 5 is absent from a path visiting vertices 0,...,4,
after first/last adjacent cycle visits have been absorbed by the old lemma.
HexagonCoordinates uses shifted coordinates C.getVert(i+1), so the cycle's
base vertex is coordinate 5. HexagonPieceSystem realizes six cycle edges and
four ordered path intervals. PathRestoreIntersection strengthens tail
restoration: the new paths may use fresh vertices off the old path, as long
as their intersection with the old path lies in its middle interval.

HexagonMissing.missing_vertex_absorption: a six-cycle and an intersecting,
edge-disjoint simple path can be absorbed into two paths if the path misses
any cycle vertex. Arbitrary internal excursions along the path are allowed.

CycleIntersectionSix.five_intersection_absorption: if C.length>=6 and the
cycle/path intersection has at most five vertices, they absorb into two
paths. This uses the old missing-ear induction with bound five instead of
four, taking the preceding six-cycle theorem as the base case. At an
inductive step C.length>6, the reduced cycle still has length>=6.

Further verified corollaries:
- A nonabsorbable pair sharing at most five vertices consists of a pentagon
  and a carrier with a contiguous four-edge middle spanning the pentagon.
- In a smallest-order failure, every path meeting a whole cycle shares at
  least SIX cycle vertices (`failure_cycle_intersection_ge_six`).
- Every normal carrier of a whole six-cycle visits all six cycle vertices
  (`maximum_hexagon_carrier_contains`).

Logs: /tmp/hexagon_finite1.log, /tmp/hexagon_routes1.log,
/tmp/path_restore_intersection1.log, /tmp/hexagon_coordinates1.log,
/tmp/hexagon_piece_system2.log, /tmp/hexagon_missing5.log,
/tmp/cycle_intersection_six3.log, /tmp/cycle_intersection_six_audit1.log.
No claim of a full Gallai proof is made.

### Six-cycle internal excursions (development pending)

A useful simplification of the finite route problem was discovered. For a
six-cycle and six path visits, a chosen internal excursion gap need not
itself admit the one-split certificate. There are 48 failing abstract
(p,gap) patterns among 1440 with nonadjacent outer pairs. But in every such
pattern visits p1,p2 are adjacent on the cycle, and choosing gap 1 instead
works. Edge-disjointness forces that adjacent gap to have an internal
outside vertex. Thus use
  chosenGap p d = if adjacent (p 1) (p 2) then 1 else d.
All 960 distinct (p,chosenGap) pairs have two simple-route certificates.

HexagonExcursionFinite.lean contains these explicit certificates in a
balanced binary lookup tree. The six-variable finite check was split into
six fixed-first-coordinate lemmas. Important build-performance lesson:
Lean's asynchronous proof checking ran the six large reductions together,
reaching the 10 GiB cgroup limit. `set_option Elab.async false` now serializes
the checks. Earlier linear-list / unsplit / async builds were deliberately
terminated (exit 143), not accepted as proofs. Current pending build:
  /tmp/hexagon_excursion_finite4.log and .exit.

Prepared, but NOT yet compiled at this entry (waiting on that finite file):
  HexagonExcursionRoutes, HexagonExcursionCoordinates,
  HexagonExcursionPieceSystem, HexagonExcursion,
  HexagonCarriers, HexagonExclusion.
A background chain will compile them, stopping at the first error; logs are
/tmp/HexagonExcursionRoutes1.log etc. The expected mathematical corollary is
that two distinct six-cycle carriers would supply 6+5+5=16 edges on six
vertices, exceeding 15. Combined with the parity-free contiguous-carrier
reduction, this would exclude whole six-cycles. These pending files must
NOT be treated as established until the builds and audits pass.

Relevant generators/data:
 /tmp/hexagon_excursion_templates.py
 /tmp/hexagon_good_gap.json
 /tmp/hexagon_chosen_templates.json
 /tmp/make_hexagon_excursion.py (linear initial version, do not rerun blindly)
 /tmp/balance_hexagon_certificates.py
 /tmp/clone_hexagon_excursion_helpers.py
 /tmp/clone_hexagon_excursion.py
The current production source includes later manual fixes and is authoritative.

## Final integrated six-cycle checkpoint (supersedes pending entry above)

All fourteen six-cycle modules were verified, audited, and inlined into Work
and Spec. The finite excursion checker uses a balanced certificate tree,
List.permutations', and serial kernel decide; previous vector-enumeration
checker attempts are obsolete.

Work/Spec builds and the complete integrated audit all passed (exit zero):
 /tmp/work_hexagon_upgrade1.log
 /tmp/spec_hexagon_upgrade1.log
 /tmp/integrated_hexagon_upgrade_audit1.log
The audit has 1,145 unique declarations: 1,113 permitted-axiom reports and
32 axiom-free reports. No other axiom occurs. Work has 42,860 lines; Spec
has 43,252 lines. The unchanged conjecture starts at 42,886; the only sorry
is 43,250. The only import remains FormalConjecturesUtil.

Verified strengthened results: a six-cycle carrier is contiguous; two such
carriers would give 16 edges on six vertices, impossible. Consequently whole
six-cycles are excluded in a smallest failure. Whole cycles have length at
least seven; every carrier shares at least six cycle vertices; the
incidence-preserving carrier optimization has at least two carriers.

A direct seven-cycle missing-vertex argument is now in development (not yet
verified). There are 336 visit orders with nonadjacent first and last pairs.
332 admit routes ending at the missing cycle vertex. The four exceptional
orders are (2,0,1,4,5,3), (2,4,5,0,1,3), (3,1,0,5,4,2), and (3,5,4,1,0,2).
They all have adjacent visits at positions 1 and 2, forcing an outside
vertex in that gap. Splitting there admits routes ending at the outside
vertex, not the missing vertex. Certificates and helper files have been
prepared; builds are pending. This direct route avoids the proposed
contracted-six-cycle argument. No full proof or disproof has been found.

## Seven-cycle missing vertices and a general rooted-core contraction

The ten-module seven-cycle missing-vertex development compiled and passed its
94-declaration audit (85 permitted-axiom reports, nine axiom-free). It was inlined
into Work/Spec by /tmp/integrate_heptagon_missing.py. The first full rebuild
failed on namespace ambiguities; those were fixed, and the complete inlined
block passes Submission/HeptagonInlineTest.lean. A full Work/Spec rebuild has
NOT yet passed after that integration. The current sources are 44,959 and
45,351 lines, respectively; the main theorem still has its original sorry.
Standalone result: every normal carrier of a whole cycle in a smallest failure
shares at least SEVEN cycle vertices (CycleIntersectionSeven).

The pending seven-cycle excursion finite checker had a generation bug: the
script's loop variables overwrote its source splice offsets, producing a file
beginning `importdef`. Attempt 6 was terminated and is not accepted. The source
was restored from /tmp/heptagon_excursion_finite_encoded5.lean and regenerated
with /tmp/split_heptagon_excursion_checks_fixed.py. Attempts 7 and 8 reached the
final permutation-recovery wrapper after the finite checks, but failed on a
List.Perm notation and a Fin.succ-zero simplification. These wrapper issues were
fixed; the wrapper passes Submission/HeptagonRecoveryTest.lean. Build attempt 9
is pending: /tmp/HeptagonExcursionFinite9.log and .exit, followed by the seven
excursion helper modules. Do NOT rerun old generators over manually fixed files.

A general contraction-to-a-star reduction is now VERIFIED externally. Twelve
modules are audited together in Submission/StarReductionAudit.lean:
  FinitePortLabels, HeptagonPortRoutes, HeptagonPortLabels,
  StarPathPieces, InjectivePathReplacement, StarContraction,
  BoundaryPorts, PortSplicing, ArmExtension, StarExternalPaths,
  StarReduction, HeptagonPortCover.
Audit /tmp/star_reduction_audit1.log and .exit: zero errors/warnings, 139 unique
reports, 125 using permitted axioms only and fourteen axiom-free.
These modules are NOT yet inlined.

Main generic statement (StarReduction.reduction_or_full): suppose S has at least
two vertices and G[S] has q edge-disjoint rooted paths covering its edges, with
2q <= |S|+1. If, at each v in S, the number of boundary edges is at most the
number of path starts at v, then smaller-order minimality implies the Gallai
bound for G. The boundary edges inject into distinct core-path slots.

Proof: contract S to one retained vertex, preserving exterior edges and one
star edge for each distinct exterior neighbor. Split each old path at the
center. Its nonempty arms have different first neighbors. Assign an arm to one
representative boundary edge at its first neighbor; all other boundary edges
receive empty exterior arms. Attach each exterior arm, its boundary edge, and
its distinct core path. Keep old paths avoiding the center. At least one old
path met the center, so the count is old_count-1+q. The order decreases by
|S|-1, and 2q <= |S|+1 pays for the increase. Crucially, no resulting path joins
two potentially intersecting exterior tails. A full-core case is handled
separately by the explicit core cover.

HeptagonPortCover.core_reduction applies this to any seven-vertex induced core
that is K7 minus two edges and whose ambient vertex degrees are all <=6. The
two possible deleted-edge patterns have explicit four-path covers with starts
at the four missing-edge incidences. Capacity equality is verified by kernel
decide and transported through a graph isomorphism. This theorem is complete.

Submission/HeptagonExclusion.lean is PREPARED but NOT YET COMPILED: it would use
the pending excursion/core chain to exclude whole seven-cycles, giving whole
cycle length >=8. It must not be treated as established until that chain and
its own build/audit pass. Larger whole cycles and open lollipop defects still
remain unresolved; even the intended seven-cycle exclusion is NOT a proof of
the full conjecture.

### Seven-cycle exclusion verified; integration rebuild pending

The corrected excursion finite checker (attempt 9) passed. All seven dependent
modules also passed on their first standalone builds:
  HeptagonExcursionRoutes, HeptagonExcursionCoordinates,
  HeptagonExcursionPieceSystem, HeptagonExcursion, HeptagonCarriers,
  HeptagonRegion, HeptagonCore.
HeptagonExclusion then compiled successfully. Its combined excursion/exclusion
audit has 107 unique reports: 98 permitted-axiom reports and nine axiom-free.
Logs /tmp/heptagon_exclusion1.log and /tmp/heptagon_exclusion_audit1.log are clean.

The mathematical seven-cycle exclusion is thus established externally: every
carrier is contiguous and spans the seven-cycle, at most two carriers fit on
seven vertices, and a smallest failure must have at least two. Their induced
core has nineteen edges, so it is K7 minus two edges; ambient core degrees are
at most six. HeptagonPortCover.core_reduction contradicts smallest failure.
The resulting whole_cycle_length_ge_eight lemma is complete. It does NOT
exclude arbitrary longer whole cycles or open lollipop defects.

All 21 new modules (the twelve core-contraction modules and nine excursion/
exclusion modules) were inlined by /tmp/integrate_heptagon_upgrade.py. Do NOT
rerun the integration script on the integrated files. Backups:
  /tmp/work_before_heptagon_upgrade.lean
  /tmp/spec_before_heptagon_upgrade.lean
  /tmp/integratedaudit_before_heptagon_upgrade.lean
The script root-qualifies every new external development reference and preserves
both the original conjecture statement and sole FormalConjecturesUtil import.
Work now has 57,024 lines; Spec has 57,416. The original theorem begins at 57,050,
and its sole sorry is at 57,414. The integrated audit lists 1,485 unique targets.

Sequential full builds and audit are pending:
  /tmp/work_heptagon_upgrade1.log and .exit
  /tmp/spec_heptagon_upgrade1.log and .exit
  /tmp/integrated_heptagon_upgrade_audit1.log and .exit
Launching chain /tmp/heptagon_upgrade_chain1.log; no concurrent full builds.
No complete proof or disproof of the original conjecture has been obtained.

The first integrated heptagon-upgrade build was deliberately terminated as
asynchronous elaboration approached the cgroup memory limit; it is not an
accepted build. `set_option Elab.async false` was added immediately after the
unchanged import in Work and Spec. The second build chain is sequential and
currently pending:
  /tmp/work_heptagon_upgrade2.log and .exit
  /tmp/spec_heptagon_upgrade2.log and .exit
  /tmp/integrated_heptagon_upgrade_audit2.log and .exit
Source line counts and theorem/sorry locations are two greater than above.

The second integrated build failed with a stack overflow (exit 134), not a
Lean proof error. Attempt 3 was restarted immediately to set both process and
worker stacks explicitly. Attempt 4 uses `ulimit -s 65536` and
`lake env lean -s 65536`, with serial elaboration, for Work, Spec, and audit in
that order. Logs:
  /tmp/work_heptagon_upgrade4.log and .exit
  /tmp/spec_heptagon_upgrade4.log and .exit
  /tmp/integrated_heptagon_upgrade_audit4.log and .exit
At 22 minutes the Work process was still running at one CPU and about 8.7 GiB
cgroup memory, with no Lean error output. The process recovered after briefly
approaching the 10 GiB limit; no new OOM event occurred in that interval.

## Final verified integrated heptagon/core-contraction checkpoint

All three sequential attempt-4 jobs finished with exit zero:
  /tmp/work_heptagon_upgrade4.log
  /tmp/spec_heptagon_upgrade4.log
  /tmp/integrated_heptagon_upgrade_audit4.log
The complete integrated helper audit has 1,485 unique reports: 1,421 use only
propext, Classical.choice, Quot.sound; 64 are axiom-free. No error or warning
occurs in the audit. The build logs contain a module-header lint warning
because the serialization option preceded the module docstring. That option
was moved immediately below the docstring in both sources; no declaration or
proof was changed. The corrected header passes ModuleHeaderTest.lean.
Spec's only substantive warning is still the ORIGINAL theorem's sorry.

Current sources: Work 57,026 lines; Spec 57,418. The original conjecture begins
at line 57,052, and its sole sorry is line 57,416. Its exact statement and sole
FormalConjecturesUtil import were checked against the pre-upgrade backup.
There are no remaining external-development references or Work imports in
Spec. Full builds used 64 MiB process/worker stacks and serial elaboration.

New verified results include the general rooted-core contraction reduction,
the four-port K7-minus-two-edges reduction, and exclusion of whole seven-cycles
in a smallest failure. Whole cycles now have length at least EIGHT, and every
normal carrier still shares at least SEVEN cycle vertices. These are partial
results: arbitrary larger cycles and open lollipop defects remain unresolved.
No complete proof or disproof of erdos_583 has been obtained or submitted.
All build/audit jobs have terminated.

## Terminal-tail preservation continuation (external, verified)

The endpoint-marking candidates remain unproved. The most recent exact hub
attachment check (/tmp/marked_hub_core_detail.py) found that attaching a triangle
by a bridge to a hub of K3 joined to four independent vertices gives order ten,
minimum path number five, and no unmarkable vertices. Attaching at a peripheral
vertex gives minimum path number four and three unmarkable hubs. This is the
previous obstruction to the broad n-2p marking inequality, NOT a refutation of
the narrower n <= 2p endpoint-marking candidate.

The independent-even star-completion idea is still only a plan. It asks for at
least floor(|I|/2) star edges terminal at their independent even endpoint after
an all-odd completion; forcing ALL such spokes is false for K2,3. The current
force_first_edge proof shortens a whole prefix and can repair at vertices outside
I, so independent-endpoint protection does not automatically prove the needed
cardinal bound.

A useful local invariant is now proved in Submission/TerminalDarts.lean
(350 lines, not yet inlined). Ten declarations compile without warnings:
  realize_escape_orbit_with_tails
  iterate_avoids_fixed_before_exit
  iterate_neighbors_before_exit
  expose_escape_preserving_tails
  tail_partner
  tail_is_member_prefix
  orient_with_tails
  escape_slide_with_members
  finish_exposed_with_tails
  improve_preserving_tails
The pivot orbit retains all unprocessed endpoint tails. It never reaches a
non-neighbor of the root or a fixed point of the tail-penultimate successor.
In particular, every direct one-edge tail to the root is fixed. The final
strict-improvement slide retains ALL nonroot tails as literal prefixes of
members, even if their containing index or opposite endpoint changes. Thus a
rooted repair can simultaneously retain endpoint tails at non-neighbors and
direct star spokes. This is stronger than old whole-subgraph preservation,
but does not establish the missing augmentation or terminal-count theorem.
Build /tmp/terminal_darts5.log and .exit: clean, exit zero.
Audit /tmp/terminal_darts_audit1.log and .exit: ten permitted-axiom reports,
exit zero; the audit file initially lacked a module docstring (cosmetic warning).
Spec and Work remain at the verified seven-cycle checkpoint, with the original
single sorry. No completed proof or disproof has been found.

A second possible general reduction is being developed: a cycle with two
contiguous carriers has a four-path rooted cover without classifying its
missing edges. Orient each carrier from one core endpoint; split the cycle
into two paths starting at the other two endpoints (even if these coincide).
The four core paths supply a slot for every possible boundary edge. For a core
with at least seven vertices the existing star-contraction theorem pays for
four slots. This should extend the seven-cycle dense-core reduction to arbitrary
long two-carrier contiguous regions. The general cover/reduction is not yet
formalized. It does not handle three or more carriers or arbitrary excursions.

## General two-carrier cycle-region reduction (external, verified)

CyclePortCover.lean (142 lines) and TwoCarrierRegion.lean (180 lines) now
compile without warnings. Their nine declarations have clean permitted-axiom
audits. Logs:
  /tmp/cycle_port_cover4.log and .exit       # 0
  /tmp/two_carrier_region3.log and .exit     # 0
  /tmp/cycle_port_cover_audit1.log and .exit # 0

cycle_two_roots splits a simple cycle into two edge-disjoint paths rooted at
ANY two selected cycle vertices; the selected roots may coincide. Combining
these with two core carrier paths yields a four-path rooted cover at their
four endpoints. two_carrier_boundary_capacity bounds each exterior tail's
contribution by one at its core endpoint. The old StarReduction then gives
  TwoCarrierRegion.two_contiguous_carrier_region
  TwoCarrierRegion.failure_no_two_contiguous_members
for arbitrary cycle length >=7, not just seven vertices. These lemmas do not
require the two carriers to span the cycle; nil middle segments are also
permitted. Their exterior tails may intersect arbitrarily. A local incidence
cover condition says that no third member supplies an edge incident to the
cycle. This extends the previous finite dense-core reduction, but does NOT
handle three or more carriers, noncontiguous excursions, or open lollipops.

Potential future direction considered, NOT proved: endpoint charging of
fully markable outside components might give a stronger carrier-length bound
than the current C.length <=4*c+2. The existing theorem only says a fully
markable outside group meeting a carrier contains one of its endpoints; it
does NOT make that carrier's entire intersection contiguous. In particular,
if both endpoints lie in the same group, internal excursions into the group
are not yet excluded. Do not infer a bridge or a two-port condition from the
endpoint-charging theorem alone.

The n<=2p marking candidate and the Hamilton-path endpoint-exchange candidate
remain unproved. The latter would imply absorption of a contiguous Hamilton
carrier missing one cycle vertex: after deleting the missing cycle vertex,
the two remaining Hamilton paths need an alternative endpoint pairing. No
Thomason/Kotzig parity theorem has been assumed, and no proof was obtained.

The next integration includes TerminalDarts, CyclePortCover, TwoCarrierRegion
(19 new declarations in total). The main conjecture remains unresolved.

## Hamilton endpoint-exchange candidate is FALSE (structural obstruction)

The old test through order nine missed an order-ten obstruction. The targeted
quartic-transition diagnostic /tmp/hamilton_transition_diagnostic.py found it
at quartic order eleven (delete vertex 2). Log:
  /tmp/hamilton_transition_diagnostic.log
This is NOT a Gallai counterexample and is not yet Lean-formalized.

Use vertex set {0,1,3,4,5,6,7,8,9,10}, partitioned into
  A={0,3,5,6,8}, B={1,4,7,9,10}.
Internal A edges: 03,05,06,08,35,36,38,58.
Internal B edges: 14,17,19,1-10,47,49,4-10,7-10.
Cross edges: 5-9,6-10.
There are two edge-disjoint Hamilton paths covering all eighteen edges:
  P = 6-3-8-0-5-9-4-1-10-7
  Q = 8-5-3-0-6-10-4-7-1-9.
Their four endpoints are distinct, with pairing (6,7),(8,9).

Any two-Hamilton-path partition must send EACH path across the A-B cut exactly
once, since both span A and B and the cut has just two edges. In A the overall
path endpoints are 6 and 8, while the two crossing ports are 5 and 6. The path
using crossing edge 6-10 cannot end at 6 (it would omit the other A vertices),
so it must end at 8. In B the overall endpoints are 7 and 9, while crossing
ports are 9 and 10. The path using crossing edge 5-9 cannot end at 9, so must
end at 7. This forces exactly the original pairing (6,7),(8,9).

Consequently, even the contiguous missing-one-cycle-vertex absorption claim
is false. Add a new vertex x and edges x-8,x-9 to H above. Q plus these edges
is an eleven-cycle; P is a contiguous Hamilton path on its other ten vertices.
The union has twenty edges on eleven vertices. A two-path partition would
therefore consist of two Hamilton paths. The degree-two vertex x must be an
endpoint in both, so deleting x would give an alternative forbidden endpoint
pairing in H. Thus no two-path partition exists. Gallai still allows six paths,
and three are immediate by splitting the cycle; this does NOT disprove Gallai.

Do not spend further effort proving the old Hamilton endpoint-exchange or
contiguous missing-one absorption candidates: both are now structurally refuted.
The diagnostic stopped on the first obstruction; no process remains running.

## Final verified terminal-tail/two-carrier integration checkpoint

All sequential integration jobs completed successfully (exit zero):
  /tmp/work_tail_core_upgrade1.log and .exit
  /tmp/spec_tail_core_upgrade1.log and .exit
  /tmp/integrated_tail_core_upgrade_audit1.log and .exit
Work is warning-free. Spec's only warning is the ORIGINAL conjecture's sorry
at theorem line 57721 (the sorry itself is line 58088). The expanded helper
audit has 1504 unique reports: 1440 use only propext, Classical.choice,
Quot.sound; 64 are axiom-free. Every report was parsed and checked; the audit
has no errors or warnings. It explicitly EXCLUDES the unresolved conjecture.

The original conjecture type was checked unchanged against the pre-integration
backup; the sole import remains FormalConjecturesUtil. Exactly one sorry
remains, and no native_decide occurs. No build or diagnostic remains running.

This continuation verified the pending integration and structurally refuted
the Hamilton endpoint-exchange / contiguous missing-one absorption candidates
as recorded immediately above. It did NOT obtain a full proof or disproof
of erdos_583. In particular, the original theorem still depends on its sorry;
the successful helper audit must not be described as verification of Gallai.
No proof was submitted as a completed solution.

## Outside-terminal root relocation and global cycle minimum

Two new modules are externally verified and axiom-audited:
  SurplusNeighbor.lean (nine declarations)
  RootCycleMinimum.lean (five declarations).
The updated SurplusNeighbor build is /tmp/surplus_neighbor6.log (.exit 0);
its audit /tmp/surplus_neighbor_audit2.log has nine permitted-axiom reports.
RootCycleMinimum build /tmp/root_cycle_minimum2.log (.exit 0) and audit
/tmp/root_cycle_minimum_audit2.log (.exit 0) are warning-free. All fourteen
reports were parsed and use only propext, Classical.choice, Quot.sound.

The first module exchanges leading edges r-x and w-x between a rooted
lollipop and a normal path avoiding r. At a global incidence maximum this
preserves the score and EVERY endpoint quota, relocates the defect to w,
and forces w into the old defective suffix. At minimum quota-square energy,
such w has quota at most two. A three-member variant transfers an endpoint
pair from w to x without any intersection bound on the two normal members;
only the first normal member must avoid r. It cannot be assumed that these
first-edge representatives exist for arbitrary surplus vertices.

The second module minimizes rooted-cycle length over ALL roots at fixed
score and quota-square energy (unlike the old fixed-root minimization).
If the outside terminal w described above lies on the cycle, the leading-edge
swap strictly shortens that cycle. Thus at this global cycle minimum, w
must lie on the tail, outside the cycle. This selection does NOT guarantee a
root of degree at least three, does NOT eliminate an open lollipop, and
still does NOT provide the required global augmentation.

The fourteen declarations have now been inlined under SurplusNeighbor and
RootCycleMinimum using /tmp/integrate_surplus_cycle_upgrade.py. Do not rerun
that script. Backups are /tmp/{work,spec,integratedaudit}_before_surplus_cycle_upgrade.lean.
The exact conjecture type and sole import were checked unchanged. The main
branch now retains hglobalShortestCycle; the ORIGINAL sorry still remains.
No proof or disproof of the original conjecture has been obtained.
Sequential full Work/Spec builds and integrated audit are being launched:
  /tmp/work_surplus_cycle_upgrade1.log and .exit
  /tmp/spec_surplus_cycle_upgrade1.log and .exit
  /tmp/integrated_surplus_cycle_upgrade_audit1.log and .exit.

A further local routing observation was considered but has NOT been formalized.
Write the defective member as r-x ++ R(x,r) ++ S(r,w) ++ B(w,b), with its
simple tail split at the outside terminal w; write the outside path as
w-x ++ q(x,c), avoiding r. If q avoids S entirely, the same edges have the
two simple-path routing
  R.reverse(r,x) ++ x-w ++ B(w,b),
  S.reverse(w,r) ++ r-x ++ q(x,c).
The original cycle/tail separation makes the first path simple, and the
assumed avoidance makes the second simple. This would repair the defect
without changing any endpoints. Consequently the configuration from the new
global minimum should force q to meet the INTERIOR of S (its endpoints r,w
are already avoided). If there is exactly one such meeting, the routing has
an INTERNAL repeated vertex, not automatically a rooted defect. The old
fixed-quota internal-rootification obstruction still applies: do not silently
rootify this new trail. No global augmentation follows from this observation.

## Verified surplus-neighbor/global-cycle integration checkpoint

All three sequential jobs completed with exit zero:
  /tmp/work_surplus_cycle_upgrade1.log
  /tmp/spec_surplus_cycle_upgrade1.log
  /tmp/integrated_surplus_cycle_upgrade_audit1.log
Work is warning-free. Spec's sole warning is the ORIGINAL theorem's sorry.
The complete helper audit has 1,518 unique reports: 1,454 use only permitted
axioms and 64 are axiom-free. Every report was parsed and checked. The audit
has no warnings or errors and explicitly EXCLUDES the unresolved conjecture.

Work is 58,230 lines; Spec is 58,627 lines. The original theorem starts at
58,256 and its sole sorry is at 58,625. The exact statement, sole import, and
absence of external-development/Work references were checked against the
pre-upgrade backup. No native_decide occurs. There are no pending builds.

This continuation has NOT settled erdos_583. The global augmentation is
still missing, particularly the existence of the requisite outside terminal
configuration and normalization of the resulting internal repetition. No
complete proof or disproof has been obtained, and no completed solution has
been submitted. The new helpers are sound partial results, not a verification
of the original theorem.

## Tail-return continuation (verified externally; not yet inlined)

Submission/TailReturn.lean now has five complete, warning-free lemmas:
  tail_return_routing, maximum_tail_return, global_minimum_tail_return,
  length_ge_two_of_internal_vertex, global_minimum_terminal_distance.
Build /tmp/tail_return4.log (.exit 0) and audit /tmp/tail_return_audit2.log
(.exit 0) cover them. This refines the previous INFORMAL routing observation:
at the global cycle minimum, an outside terminal's suffix returns to the
strict interior of the old tail prefix; that prefix has length at least two.
It still does not rootify an internal repetition or settle Gallai.

Additional endpoint-flexibility shortcuts were rejected by exact small
auxiliary tests, not original-conjecture counterexample searches:
  /tmp/one_even_flexibility.py and .log: a three-vertex path already refutes
  arbitrary nonneighbor avoidance in a graph with one even vertex.
  /tmp/one_even_flexibility_separated.py and .log: forbidding a common
  neighbor at the unique even vertex is still insufficient (order five).
  /tmp/one_even_first_nonbridge.py and .log: even a nonbridge edge cannot
  always be prescribed at a chosen odd starting endpoint in a one-even graph.
  Exact example: edges 01,13,14,23,24,34, unique even vertex 2; two paths
  cover it, but no two-path cover has a member starting 3-1. After 3-1,
  ending at 0 leaves a cycle-with-tail; ending at 4 leaves a triangle and
  edge01. Continuing through 2 would revisit 3. These are strategy
  obstructions, not counterexamples to Gallai, and are not Lean assumptions.
A join construction using B=K6 plus vertex6 adjacent to hubs0,1,2 did NOT
refute the narrow near-saturated marking question: the required four-path
quota [2,0,0,3,1,1,1] is explicitly feasible. Exact log:
/tmp/marked_hamilton_join_core.log. No diagnostic remains running.

New plan under investigation, NOT PROVED: drop PreservesIncidence from the
fixed-whole-cycle carrier optimization. A tight outside component on 2t-1
vertices can potentially absorb a carrier's first edge into a graph on at
most 2t vertices, using t paths by smaller-order induction. If the next
vertex is off the cycle, this shortens carrier length; if on it, it creates
an extra carrier (but changes cycle incidence, explaining why the old
constrained optimum does not rule it out). Excluding all tight outside
components this way would sharpen C.length <=4*c+2 to C.length <=2*c+2.
The required group replacement and strictness bookkeeping have NOT yet
been formalized. Do not cite this proposed bound as a theorem.

## Unrestricted fixed-cycle carrier optimization (external proofs verified)

The formerly proposed tight-group leading-edge absorption has now been proved.
EdgeAbsorption.lean has ten verified declarations, including tracked replacement
with a distinguished suffix and absorb_first_edge. FreeCarrier.lean has ten
verified declarations. It optimizes at fixed whole cycle and fixed global score,
WITHOUT PreservesIncidence or a quota restriction. At this optimum every tight
outside component is excluded: a tight group absorbs a carrier's first edge
using no extra members by smaller-order induction; exact group size follows
from normal_group_cannot_save. If the new endpoint is off the cycle, carrier
length drops; if on the cycle, the group gains a carrier. Both contradict the
unrestricted optimum. A fully marked tight component would meet a carrier at
an endpoint, so connectedness excludes every tight outside component.

The new proved bound is C.length <= 2*c+2, or <= 2*c+1 in odd order, where c
is the number of normal carriers. In conjunction with the existing whole-cycle
length >=8, the existential certificate has c>=3 (c>=4 in odd order).
The optimized family does NOT assert preserved quotas, quota-square energy,
root degree, or individual cycle incidences. It does NOT handle an arbitrary
open lollipop and does NOT eliminate the final defect.

External builds /tmp/edge_absorption10.log and /tmp/free_carrier8.log are clean,
exit zero. Audits /tmp/edge_absorption_audit1.log (10 declarations) and
/tmp/free_carrier_audit1.log (10) were parsed in full and have only the three
permitted axioms. The five-report TailReturn audit was also explicitly checked.

TailReturn, EdgeAbsorption, and FreeCarrier have now been inlined via
/tmp/integrate_free_carrier_upgrade.py (do not rerun); backups are
/tmp/{work,spec,integratedaudit}_before_free_carrier_upgrade.lean.
The original statement and sole import were checked unchanged; exactly one
sorry remains in the original theorem. No proof or disproof has been obtained.
Sequential full builds and integrated audit are RUNNING, not yet verified:
  /tmp/work_free_carrier_upgrade1.log (.exit pending)
  /tmp/spec_free_carrier_upgrade1.log (.exit pending)
  /tmp/integrated_free_carrier_upgrade_audit1.log (.exit pending).

## Arbitrary-defect anchor extension (external proofs verified)

The carrier bound now also covers OPEN lollipops. TightAttachment proves that
an endpoint in a tight normal group cannot belong to a one-edge normal member:
absorbing that entire edge would compress the enlarged group by one path.
This replaces the whole-cycle intersection lower bound previously needed to
show the carrier suffix remains nonempty. The generic marked-cut/shortening
arguments require only a fixed nonpath anchor, not a cycle. AnchorCarrier
therefore excludes tight outside components and bounds the anchor's support
cardinality by 2*c+2 (2*c+1 in odd order), where c counts other paths touching
that entire anchor. In the lollipop certificate this is
  cycle.length + tail.length <= 2*c+2.
It still does not eliminate that defect, preserve quota energy, or retain
shortest-tail properties in the separately optimized family.

TightAttachment build /tmp/tight_attachment4.log is clean. AnchorCarrier
build /tmp/anchor_carrier3.log (.exit 0) is clean. Their audits were parsed:
one and eighteen declarations, all only propext, Classical.choice, Quot.sound.
An earlier auxiliary AnchorCarrier build was deliberately stopped by the
memory guard (exit125), not accepted as verification. No second full build
was run concurrently.

The initial 25-declaration full Work build completed cleanly, exit zero:
/tmp/work_free_carrier_upgrade1.log (.exit 0). Its parent chain was paused
before Spec, allowing the anchor extension to be inlined into Spec first.
/tmp/integrate_anchor_carrier_spec.py (do not rerun) added the new nineteen
lemmas ONLY TO SPEC, not Work, and updated IntegratedAudit. Backups:
/tmp/{spec,integratedaudit}_before_anchor_carrier_upgrade.lean.
Submission/AnchorIntegrated.lean imports Work and reopens Erdos583Work with
TightAttachment and AnchorCarrier. This development layer compiles cleanly
(/tmp/anchor_integrated1.log, .exit 0), avoiding a second full Work rebuild.
Future development can import Submission.AnchorIntegrated for the new names.

The resumed serial chain is now building the final Spec with ALL 44 new
helpers, then its 1,562-report integrated helper audit. Pending logs retain
names /tmp/spec_free_carrier_upgrade1.log and
/tmp/integrated_free_carrier_upgrade_audit1.log. Check exit files before
claiming full integration verified. The conjecture's single sorry remains,
and its statement and sole import were checked unchanged again.

## Final carrier/anchor integration checkpoint

All sequential jobs completed with exit zero:
  /tmp/work_free_carrier_upgrade1.log
  /tmp/spec_free_carrier_upgrade1.log
  /tmp/integrated_free_carrier_upgrade_audit1.log.
Work is warning-free; Spec has exactly the original theorem's sorry warning.
The integrated helper audit has 1,562 unique reports: 1,498 permitted-axiom
reports and 64 axiom-free. Every report was parsed and checked. The unresolved
original theorem is explicitly excluded from this helper audit.

Current files:
  Work.lean: 59,052 lines (includes TailReturn, EdgeAbsorption, FreeCarrier)
  AnchorIntegrated.lean: separately compiled layer adding TightAttachment
    and AnchorCarrier under Erdos583Work; import this for subsequent work.
  Spec.lean: 60,135 lines, containing all of the above with its sole original
    FormalConjecturesUtil import. The original theorem starts at line59,760;
    its sole sorry is at line60,133.
The statement and sole import were checked unchanged against the pre-upgrade
backup. No external-development or Work references remain in Spec, and no
native_decide occurs. No build or auxiliary diagnostic remains running.

This continuation proved the unrestricted fixed-cycle carrier bound and its
arbitrary-defect/lollipop extension, but has NOT settled erdos_583. The global
augmentation that removes the single defect is still missing. No full proof
or counterexample has been obtained, and no completed proof was submitted.

## Marked absorption and outside-component budget (external proofs verified)

MarkedAbsorption.lean has thirteen warning-free verified declarations. A
connected normal group on at most twice its member count can absorb an
incident carrier edge if its starting vertex is marked in an exact-size
partition. If the new endpoint is outside the group, append at the mark;
if it is inside, smaller-order induction partitions the enlarged graph.
Absorbing an entire one-edge carrier would save a normal member and is
impossible in a failure. Hence unrestricted fixed-anchor optimization
excludes carriers meeting a fully markable outside group at this budget.

A zero-surplus outside component (support size twice member count) therefore
has an unmarkable even-degree vertex. Its support-induced graph has at least
four even vertices and its order is at least half the ambient order. Two
such disjoint components would occupy all ambient vertices, leaving no room
for the nonempty anchor, so at most one exists. At exact half-order, global
edge minimality additionally forces |E(G)| <= 2|E(component)|+1.

AnchorComponentBudget.lean adds eight audited declarations (one definition
and seven lemmas). At the SAME unrestricted anchor optimum, all outside
components have nonnegative surplus and at most one has zero surplus. Thus,
with B the outside indices, N their member-intersection component count, and
c the number of normal carriers,
  2*|B| + N <= outsideSupport.ncard + 1,
  K.verts.ncard + N <= 2*c + 3,
with the latter bound improving to 2*c+2 in odd ambient order. The existential
lollipop certificate replaces K.verts.ncard by cycle.length+tail.length.
These facts do NOT preserve quota energy, prescribed quotas, or shortest-tail
properties, and do NOT eliminate the single defective member.

External verification logs, all exit zero and warning-free:
  /tmp/marked_absorption7.log (clean build; no .exit file was made)
  /tmp/marked_absorption_audit1.log (.exit 0; 13 permitted-axiom reports)
  /tmp/marked_integrated2.log (.exit 0)
  /tmp/anchor_component_budget3.log (.exit 0)
  /tmp/anchor_component_budget_audit1.log (.exit 0; 8 permitted-axiom reports)
  /tmp/component_integrated1.log (.exit 0).
Each axiom report was parsed, not merely counted; only propext,
Classical.choice, Quot.sound occur.

The two modules were inlined into Spec by
/tmp/integrate_marked_component_upgrade.py (DO NOT RERUN). Backups:
/tmp/{spec,integratedaudit}_before_marked_component_upgrade.lean.
Spec's sole import and the original theorem statement were checked unchanged;
exactly one original sorry remains. The helper audit now requests 1,583
reports. Full Spec build and integrated audit are pending at this entry.
Work was not changed. Further development may import
Submission.ComponentIntegrated, which exposes all new modules under
Erdos583Work without rebuilding Work.

No complete proof or counterexample has been found. A star-copy amplification
idea did not close the marking gap, and no unproved amplification or asymptotic
path bound has been assumed in Lean.

## Final verified marked-component integration checkpoint

The full sequential chain completed with exit zero:
  /tmp/spec_marked_component_upgrade1.log (.exit 0)
  /tmp/integrated_marked_component_upgrade_audit1.log (.exit 0).
Spec has only its original conjecture's sorry warning, at line60351.
The complete helper audit has 1,583 unique reports: 1,519 with only permitted
axioms and 64 axiom-free. Every report was parsed, and the set was checked
against all 1,583 audit requests. The unresolved original theorem is excluded
from this helper audit; it has NOT been verified as a proof.

Spec is 60,728 lines. The original theorem starts at line60,351 and the sole
sorry is at line60,726. Original statement and sole FormalConjecturesUtil import
were checked unchanged against the pre-upgrade backup. No external development
references, Work references, or native_decide occur in Spec. Work remains
59,052 lines. ComponentIntegrated is a separately verified development layer
with all newer helpers under Erdos583Work. No build or audit remains running.

This continuation integrated 21 newly audited declarations and sharpened the
outside-component counting bound. It did NOT prove or disprove erdos_583.
No completed proof has been submitted; a global exact-budget augmentation is
still required to remove the one defective lollipop member.

## Tail-edge absorption and a joint optimum (external proofs verified)

A new augmentation is verified: a normal group can absorb the LAST edge of
the defective lollipop's tail, retaining the same cycle and one total defect.
Unlike carrier-edge absorption, the donor is now the defective member itself.
The shorter member may become a whole cycle; this case is explicitly allowed.

TailEdgeAbsorption.lean (6 lemmas) supplies:
- padded_path_family and replace_group_and_trail: a normal group and a separate
  trail can be replaced simultaneously. Nil indexed paths pad any unused slots,
  avoiding an unjustified assumption that the enlarged partition has exact size.
- replacement_score: a single-defect replacement keeps the total score.
- absorb_tail_edge / absorb_last_tail_edge: if the enlarged normal group has
  a partition using at most its previous number of members, shorten the tail.
- shorten_at_small_marked_group: the marked-edge partition lemma supplies this
  replacement for a connected group on at most twice its member count.

FreeTailAbsorption.lean (21 lemmas) minimizes tail length over ALL tails,
including NIL tails, at fixed root, literal cycle and score. Endpoint quotas
and quota energy are NOT fixed. Fully marked normal groups meeting the tail
must contain the finish, even when the group contains the root. A small such
group could then absorb the last edge, contradicting minimality. Groups that
avoid the tail also avoid the root, so the cycle-prefix repair excludes their
meeting the cycle. A nil tail is treated separately by the existing whole-cycle
marked-group disjointness theorem.

Consequences at this free-tail optimum:
- EVERY normal component has support size >= twice its member count. The old
  possible tight component at the finish is eliminated, not merely counted.
- A zero-surplus component has an unmarkable vertex and support size at least
  half the ambient order.
- Global edge minimality excludes two zero-surplus components, using their
  disjoint edges and the at least three additional cycle edges.
- At most THREE normal components; at most TWO in odd order.
- At most TWO normal components for an OPEN lollipop with cubic root.
These conclusions now cover open lollipops, not only whole-cycle members.
They still do not remove the remaining defect.

JointTailCarrier.lean (2 lemmas) verifies compatibility with the unrestricted
fixed-anchor optimization. First minimize tail length, then fix its whole
subgraph and maximize carrier count/minimize carrier length. Reorient only
the distinguished member to restore the literal rooted representation. This
changes no indexed subgraph, so the carrier optimum and shortest-tail property
hold in the SAME family. The certificate combines the normal-component bounds
above with both |K| <= 2*c+2 and |K|+N_outside <= 2*c+3 (2*c+2 in odd order).
No root-quota or quota-energy preservation is asserted.

All standalone builds are warning-free, exit zero:
  /tmp/tail_edge_absorption4.log (.exit 0)
  /tmp/free_tail_absorption4.log (.exit 0)
  /tmp/joint_tail_carrier1.log (.exit 0).
All 29 separate axiom reports were parsed and use only permitted axioms:
  /tmp/{tail_edge_absorption,free_tail_absorption,joint_tail_carrier}_audit1.log.
Submission/TailIntegrated.lean, importing ComponentIntegrated and exposing all
new names under Erdos583Work, also compiled warning-free:
  /tmp/tail_integrated1.log (.exit 0).

The 29 lemmas were inlined into Spec by
/tmp/integrate_tail_absorption_upgrade.py (DO NOT RERUN). Backups:
/tmp/{spec,integratedaudit}_before_tail_absorption_upgrade.lean.
The sole import and original statement were checked unchanged, and exactly
one original sorry remains. Work was not modified. Full Spec build and the
expanded 1,612-report helper audit are pending at this entry. The unresolved
original theorem remains excluded from that helper audit.

### Endpoint-pair diagnostic: no unproved flexibility assumption

An exact targeted test of simultaneous marking was run in all 119 connected
even-order atlas graphs and all 11,117 connected eight-vertex graphs. In the
saturated cases with at least four even vertices (18 and 688 cases), no vertex
was pair-incompatible with two different vertices. A bridged-triangle
construction explains the relevance to the previously proposed odd-order
near-saturated unmarkability question. This finite evidence is NOT a proof
of that question or of Gallai, and no marking-flexibility axiom was introduced.
Script/log: /tmp/marked_even_pairs.py, /tmp/marked_even_pairs8.log (.exit 0).
The particular eight-vertex core formed from K3 joined to four independent
vertices by adding vertex7 adjacent to 0 and 3 DOES permit the demanded pair
of marks 1 and 3; an explicit four-path partition was found. See
/tmp/marked_even_pair_bridge_core.py. All diagnostics have terminated.


## Final verified tail-absorption/joint-optimum integration checkpoint

The full sequential build and helper audit completed with exit zero:
  /tmp/spec_tail_absorption_upgrade1.log (.exit 0)
  /tmp/integrated_tail_absorption_upgrade_audit1.log (.exit 0).
Spec has only its original conjecture's sorry warning, at line 61086.
All 1,612 unique helper reports were individually parsed and matched against
the audit requests: 1,548 use only the permitted axioms and 64 are axiom-free.
The unresolved original theorem is excluded; this is NOT a verification of
that theorem. No build or audit remains running from this checkpoint.

Spec is 61,465 lines. The original theorem starts at 61,086; its sole sorry
is at 61,463. Statement and sole import remain unchanged. No Work references,
external-development references, or native_decide occur in Spec. Work was
not changed; subsequent development can import Submission.TailIntegrated.

The compatible shortest-tail/carrier certificate remains a partial result.
In particular, one near-spanning connected normal remainder is not excluded,
and the single defective member has not been repaired at the exact budget.
No full proof or disproof has been obtained or submitted.

## Root-cycle edge absorption and a compatible free cycle minimum

Twenty-five new external declarations compile warning-free and pass their
individual permitted-axiom audits. Their bodies have now been inlined in Spec;
this integration's full Spec build and expanded helper audit are pending.

CycleEdgeAbsorption (9 lemmas) adds a genuine repair operation. Absorb the
first edge of a repeated-start member into a normal group, when the enlarged
group has a partition within its previous member count. The remainder of the
defective member is a PATH, so this eliminates the defect, unlike tail-edge
absorption which only shortened it. Either root-incident cycle edge works for
an attached lollipop, and ANY cycle edge works for a whole-cycle member.

Smaller-order induction can partition a normal group plus an edge internal
to its support without increasing its path count if support size <= twice
the member count. A marked endpoint also permits absorbing a boundary edge.
Consequently, in a whole-cycle failure, such a connected normal group has an
INDEPENDENT intersection with the cycle, and EVERY vertex of that intersection
is unmarkable (and even-degree in the selected graph). No endpoint quota
preservation is required or asserted by this repair.

CycleIndependent (3 lemmas) proves by the cyclic-successor injection that an
independent set occupies at most half a simple cycle. Its cycle intersection
size is at most its ambient complement size. ZeroCycleGroup (5 lemmas) combines
this with the existing seven-vertex carrier-intersection bound. If a connected
normal group with support size <= twice its member count meets the whole cycle,
then the cycle has length >=14 and the group omits at least SEVEN ambient
vertices. This applies in particular to every zero-surplus normal component.
(The weaker four-omitted-vertices result does not require the group to meet the
cycle.) These are conditional bounds, not a general exclusion of zero surplus.

FreeCycleChoice (8 lemmas) first minimizes cycle length at a FIXED ROOT and
score, with NO quota or energy constraint, then invokes the free shortest-tail
and fixed-anchor maximum-carrier/minimum-carrier-length optimization. All
three optima thus hold in ONE family. The literal cycle can differ from the
original input; the root is unchanged. If the root has ambient degree >=3:
- Either the cycle is a triangle or every cycle vertex has degree >=3.
- The normal remainder omits at most one ambient vertex.
- If the tail is nil, the normal remainder spans all vertices.
- In odd ambient order it also spans all vertices (existing minimum-degree
  theorem applies, independent of the new cycle minimization).
- For an open lollipop with cubic root, the normal support is exactly the
  complement of the root; no minimum-energy hypothesis is needed.
The final existential certificate combines these facts with the previous
component-count and anchor/carrier bounds. It still does NOT repair a
near-spanning connected normal remainder.

Verified standalone production builds:
  /tmp/cycle_edge_absorption4.log (.exit 0)
  /tmp/cycle_independent5.log (.exit 0)
  /tmp/zero_cycle_group4.log (.exit 0)
  /tmp/free_cycle_choice5.log (.exit 0).
The four *_audit2.log files have respectively 9,3,5,8 reports, all individually
parsed, with only propext, Classical.choice, Quot.sound. The initial audit
runs had module-docstring warnings; these were corrected and all four rerun
warning-free. No proof gaps were involved.

Integration script: /tmp/integrate_cycle_absorption_upgrade.py, ALREADY RUN;
do not rerun. Backups:
  /tmp/spec_before_cycle_absorption_upgrade.lean
  /tmp/integratedaudit_before_cycle_absorption_upgrade.lean.
New development layer: Submission/CycleIntegrated.lean, importing TailIntegrated
and exposing all four modules under Erdos583Work. Work remains unchanged.

Spec is now 62,051 lines; original theorem starts at 61,670, and its sole sorry
is at 62,049. Statement and the sole FormalConjecturesUtil import were checked
unchanged. The main branch records the new free-cycle component certificate
using its previously verified high-degree root. Expanded IntegratedAudit has
1,637 requests; it EXCLUDES the unresolved original theorem. A helper audit
must not be described as verification of the conjecture.

No complete proof or disproof has been obtained. The last global augmentation
remains missing, despite the new cycle-edge repair and compatible optimizations.

### Two additional structural cautions (not Lean assumptions)

Cycle minimality plus a spanning normal remainder does NOT alone force a
carrier to visit a whole cycle contiguously. The earlier Hamilton-pairing
obstruction admits the following alternative representation. Keep the old
vertices {0,1,3,4,5,6,7,8,9,10}, and use vertex2 for the new vertex adjacent
to8,9. The same twenty-edge graph is partitioned by
  C = 5-8-0-3-6-10-1-7-4-9-5       (ten-cycle),
  P = 6-0-5-3-8-2-9-1-4-10-7      (Hamilton path on eleven vertices).
These explicit edge sets were checked disjoint with the required union. The
old cut argument still excludes a two-path partition. Any whole-cycle plus
one-path partition has cycle length >=20-10=10, so this C is globally minimum
among WHOLE-cycle representations. Every cycle vertex belongs to P, and the
normal remainder spans all eleven vertices, but P has an outside excursion
through vertex2. That vertex has degree two and nonadjacent neighbors, so
this is not a smallest Gallai failure. Also k=2 does NOT meet the Gallai budget,
and the anchor bound fails (10 > 2*1+2). No claim about minimum cycles over
all rooted lollipops is made by this edge-count observation.

Unrestricted deletion of a NONBRIDGE ODD-ODD edge can increase path number,
even when the deletion graph stays connected. On vertices0,...,6 take triangles
012 and345, plus edges03,16,46. A two-path partition is
  1-2-0-3-5-4; 0-1-6-4-3.
Edge03 has odd-degree endpoints and is not a bridge. In every two-path
partition both paths must cross each triangle's two-edge boundary once;
otherwise one path would have to contain a whole triangle. Thus the path
using03 must start at1 and end at4, making03 internal at both ends. Deleting03
leaves two triangles joined by the two-edge path1-6-4, which needs three paths
(the two local pieces per triangle can share at most one path across the
connecting corridor). Three suffice, for example
  2-0-1-6-4-3-5; 1-2; 4-5.
This rules out a general single-edge terminality shortcut, not a budget-aware
one: the original graph has n=7,p=2, well below its Gallai budget4. These
observations are structural research notes, not formal helper assertions or
counterexamples to erdos_583.


## Final verified cycle-edge/free-cycle integration checkpoint

The full sequential build and helper audit completed with exit zero:
  /tmp/spec_cycle_absorption_upgrade1.log (.exit 0)
  /tmp/integrated_cycle_absorption_upgrade_audit1.log (.exit 0).
Spec has only its original conjecture's sorry warning, at line 61670.
All 1,637 unique helper reports were individually parsed and matched against
the audit requests: 1,573 use only the permitted axioms and 64 are axiom-free.
The unresolved original theorem is excluded; this is NOT a verification of
that theorem. No build or audit remains running from this checkpoint.

Spec is 62,051 lines. The original theorem starts at 61,670; its sole sorry
is at 62,049. Statement and sole import remain unchanged. No Work references,
external-development references, or native_decide occur in Spec. Work was
not changed. Submission/CycleIntegrated.lean also compiled warning-free:
  /tmp/cycle_integrated2.log (.exit 0).
Subsequent development may import Submission.CycleIntegrated.

The 25 newly integrated lemmas prove cycle-edge absorption, independent
cycle intersections for zero-budget normal groups, and a compatible free
cycle/tail/carrier optimum with a near-spanning normal remainder. They do
NOT prove or disprove erdos_583. The one remaining sorry has not been removed,
and no completed proof has been submitted.

## Two-sided matching-cut gluing (verified externally; integrated build pending)

MatchingCutGlue.lean (24 declarations) and MatchingCutMarked.lean (10 declarations)
prove an actual path-gluing construction, not just a support-count restriction.
Both production modules compile warning-free; their independent audits were
parsed report-by-report and use only the permitted axioms. Logs:
  /tmp/matching_cut_glue4.log (.exit 0)
  /tmp/matching_cut_marked3.log (.exit 0)
  /tmp/matching_cut_glue_audit2.log (.exit 0)
  /tmp/matching_cut_marked_audit1.log (.exit 0).

Construction: contract each side of a vertex cut to a temporary center, partition
the two smaller proxy graphs, split the members at each center, and lift their
remaining arms back to the original graph. The arm from each side of an original
boundary edge splices across that edge into a simple path, since the sides are
disjoint. Paths avoiding the proxy centers are retained. This generic gluing
works for any cut with the precise count
  |D| <= d + avoidA + avoidB.
If BOTH boundary endpoint maps are injective (the cut edges form a matching),
center degree is exactly d. For each path family, including nil members, the
verified identity is
  degree(center) + quota(center) + 2*avoid = 2*memberCount.
Consequently the matching gluing gives
  2*|D| + quotaA + quotaB <= 2*(kA+kB).
This is the endpoint-sensitive saving theorem matching_glue_quota; the corollary
matching_glue_saving converts a quota sum >=2*s into a saving of s paths.

Odd cut size forces each center quota odd and positive, hence saves one path.
When each side has >=2 vertices and at least one side has odd order, induction
on the two proxies fits the original Gallai budget. Thus, in a smallest failure,
any odd matching cut with both sides of size >=2 has BOTH sides even.

For an EVEN matching cut, mark each proxy center via the existing single-leaf
smaller-order lemma. Each marked center has quota >=2, so gluing saves TWO paths.
The two marked budgets fit whenever each side has >=3 vertices and at least one
side has even order. No parity shortcut is assumed: if both sides are odd the
arithmetic is one too large, and that case is NOT claimed. Thus an even matching
cut with sides of size >=3 in a smallest failure has BOTH sides odd.

Together: any matching cut with sides of size >=3 in a smallest failure has even
ambient order, equally paritied side orders, and boundary parity opposite to the
side orders. In an ODD-order smallest failure, there is no proper matching cut at
all. The last strengthening uses the existing minimum-degree-five theorem and
a new injection showing degree(x) <= |S| whenever x belongs to a matching-cut
side S. It rules out the small-side cases without extra assumptions.

This does NOT settle the conjecture. A connected, near-spanning normal remainder
may have no matching cut. In particular, a cut through independent cycle visits
has two boundary edges at each visited vertex and does NOT satisfy the matching
hypothesis. No universal augmentation follows from these gluing reductions.

Already executed integration script (DO NOT rerun):
  /tmp/integrate_matching_cut_upgrade.py.
Backups: /tmp/spec_before_matching_cut_upgrade.lean and
  /tmp/integratedaudit_before_matching_cut_upgrade.lean.
The source bodies are inlined in Spec under MatchingCutGlue/MatchingCutMarked;
Work remains unchanged. New import layer: Submission/MatchingIntegrated.lean.
The final branch records hmatchingCutParity and hoddMatchingCut. Original statement
and sole import were checked unchanged; the original sorry remains.
Spec has 62,579 lines; original theorem starts at 62,186; sole sorry is at 62,577.
IntegratedAudit now has 1,671 requests; it EXCLUDES the unresolved original theorem.
Full sequential build/audit is pending via /tmp/build_matching_cut_upgrade.sh:
  /tmp/spec_matching_cut_upgrade1.log and
  /tmp/integrated_matching_cut_upgrade_audit1.log.
No completed proof/disproof has been obtained or submitted.


## Final verified matching-cut integration checkpoint

The full sequential Spec build and helper audit both completed with exit zero:
  /tmp/spec_matching_cut_upgrade1.log (.exit 0)
  /tmp/integrated_matching_cut_upgrade_audit1.log (.exit 0).
Spec reports only its original theorem's sorry warning, at line 62186.
All 1,671 unique helper reports were parsed and matched against audit requests:
1,607 use only permitted axioms, and 64 are axiom-free.
The unresolved original theorem is excluded. This is NOT verification of erdos_583.

Spec remains 62,579 lines, with its unchanged original theorem beginning at
62,186 and its sole sorry at 62,577. Original statement and sole import were
checked unchanged. No external-development/Work references or native_decide
occur in Spec. Work was not changed. MatchingIntegrated compiled warning-free:
  /tmp/matching_integrated1.log (.exit 0).
New development may import Submission.MatchingIntegrated.

The new exact-budget matching-cut reductions have been completely verified,
but a no-matching-cut near-spanning normal remainder remains possible. The
conjecture has neither been proved nor disproved. No completed proof was
submitted. All builds/audits from this checkpoint have finished.

## Independent cycle-visit suppression (external verified; integrated build pending)

New modules, all complete and independently axiom-audited:
  IndependentSuppression.lean       12 declarations
  CycleNeighborClosure.lean          5 declarations
  NormalComponentComplement.lean    4 declarations
  ZeroComponentSuppression.lean     8 declarations
Their standalone audit logs are /tmp/<Module>_audit1.log, with exit zero.
Every report was individually matched to its request and checked for only
propext, Classical.choice, Quot.sound. No helper uses sorry or native_decide.

The construction is a real same-budget repair of a zero-surplus component,
not merely a counting obstruction. Remove a normal component with support S
and p members, where |S|=2p. Prior cycle-edge absorption makes S's intersection
with the whole defective cycle independent. Every remaining edge at S thus
belongs to a two-edge spoke a-r-b, with a,b outside S. For a globally shortest
WHOLE-cycle representation, the shortcut a-b is absent from the outside graph:
an owner of that chord avoids r, and swapping the ear and chord would shorten
the cycle at unchanged incidence score. Shortcut edges are pairwise distinct,
since two vertices sharing both cycle neighbors close a cycle of length <=4,
whereas failure cycles have length >=8.

Removing one normal component leaves the distinguished cycle connected to all
other normal components. Suppression preserves support connectivity. Apply
smaller-order induction on the outside support, expand all fresh distinct
shortcut edges back into their original two-edge spokes, and restore the p
original normal paths. Expansions have fresh internal vertices, so they neither
repeat vertices within a path nor increase path count. The total count is
  p + ceil((n-2p)/2) = ceil(n/2).
Thus a shortest whole-cycle representation in a smallest failure has NO
zero-surplus normal component. Each component's support order is at least
2*(its member count)+1. The previous total-surplus bound gives at most TWO
normal components; in odd order, at most ONE. In odd order the normal remainder
is moreover support-connected and SPANNING. A compatible existential certificate
selects a shortest whole-cycle family with the same score and these properties.

These assertions require an initial WHOLE-cycle member. They do not establish
that an arbitrary rooted lollipop can be made into a whole cycle; nor do they
repair the connected spanning normal remainder. No proof or disproof of the
original conjecture has been obtained.

Already executed integration script (DO NOT rerun):
  /tmp/integrate_suppression_upgrade.py.
Backups: /tmp/spec_before_suppression_upgrade.lean and
  /tmp/integratedaudit_before_suppression_upgrade.lean.
The 29 helpers are inlined in Spec, and Work remains unchanged. Development
layer Submission/SuppressionIntegrated.lean compiled warning-free:
  /tmp/suppression_integrated1.log (.exit 0).
Spec is now 63,287 lines; its unchanged original theorem starts at 62,885;
the sole sorry is at 63,285. Its sole FormalConjecturesUtil import is unchanged.
The main branch records conditional hshortestCycleComponents and a separate
hoddWholeCycleConnectedChoice existential; no optima are conflated.
IntegratedAudit now has 1,700 requests, excluding the unresolved conjecture.
Full sequential build/audit is running via /tmp/build_suppression_upgrade.sh:
  /tmp/spec_suppression_upgrade1.log
  /tmp/integrated_suppression_upgrade_audit1.log.

Further informal observation (not a Lean claim): an unrestricted assertion that
any two vertices can both be marked using p+1 paths from a p-path partition is
false even for a four-vertex path. Marking its two internal even vertices needs
six endpoint incidences, hence three nonempty paths; p+1 is only two. Any such
marking approach must explicitly account for endpoint parity/slack. This does
not refute the narrower odd saturated pair question already recorded above.

### Why mere endpoint marking does not repair a spanning whole-cycle remainder

A structural obstruction to a stronger proposed auxiliary step: in a connected
optimal p-path graph on 2p+1 vertices, a nonedge x-y need not admit any optimal
partition whose path ending at x avoids y, even when x is markable and has
degree <2p. Take H=K7 minus the triangle on {0,1,3}. Its eighteen edges partition
into these three Hamilton paths:
  1-6-2-5-3-4-0
  1-2-0-5-4-6-3
  3-2-4-1-5-6-0.
The edge sets were checked disjoint and their union checked exactly. Every
three-path partition of H consists of Hamilton paths, by eighteen edges and
the six-edge maximum path length. Thus every member contains every vertex.
Vertices 0,1,3 are markable (indeed each has two endpoint incidences), and each
has degree four <2p=6, but no nonedge can be appended to an endpoint path while
preserving simplicity. Adding the missing triangle gives K7, which DOES meet
Gallai with four paths. So this is not a counterexample to Gallai or to the
narrower unmarkability question. It shows that endpoint marking alone, even
at every vertex of the defective cycle, cannot justify a one-edge absorption
argument when the normal remainder spans. A real repair may need multiple
paths/edges to be changed together. This is an informal explanatory obstruction,
not a newly asserted Lean theorem.


## Final verified independent-suppression integration checkpoint

Full sequential Spec build and helper audit completed with exit zero:
  /tmp/spec_suppression_upgrade1.log (.exit 0)
  /tmp/integrated_suppression_upgrade_audit1.log (.exit 0).
Spec has only the original conjecture's sorry warning, at line 62885.
All 1,700 unique helper reports were parsed and matched to audit requests:
1,636 use only the permitted axioms, and 64 are axiom-free.
The unresolved original theorem is excluded: this is NOT verification of it.

Spec is 63,287 lines; original theorem starts at 62,885; sole sorry at 63,285.
Statement and sole import remain unchanged. No Work/external-development
references or native_decide occur in Spec. Work remains unchanged. The new
SuppressionIntegrated layer compiled warning-free, and may be imported for
further development. No build or audit remains running from this checkpoint.

The shortest whole-cycle positive-component reduction is complete, but the
connected spanning normal remainder and the general open-lollipop case remain
unresolved. No completed proof or disproof of erdos_583 was obtained or submitted.

## Shared-center paired suppression (new verified helpers; integrated build pending)

Four modules have been completed and individually audited:
  SharedExpansion (4 declarations), PairedSuppression (13),
  SeparateTwoEdges (4), FiveSpokeReduction (9).
All 30 axiom reports were parsed and matched to requests. Each uses only
propext, Classical.choice, Quot.sound. Production logs are warning-free:
  /tmp/shared_expansion5.log (.exit 0)
  /tmp/paired_suppression4.log (.exit 0)
  /tmp/separate_two_edges3.log (.exit 0)
  /tmp/five_spoke_reduction2.log (.exit 0).
Audits: /tmp/{SharedExpansion,PairedSuppression,SeparateTwoEdges,FiveSpokeReduction}_audit1.log.

SharedExpansion expands fresh shortcut edges along replacement paths whose
internal vertices avoid the old graph support. Different replacements may
share internal vertices, PROVIDED each original partition member receives
at most one replacement. This explicit Separated hypothesis is essential.
Specializations expand disjoint pairs through one removed center, and optionally
restore a leftover spoke at a cost of one additional path.

PairedSuppression defines the proxy (G restricted away from r) plus a matching
of fresh shortcuts. Smaller-order induction supplies a proxy partition if
its support is connected. A smallest failure forces shortcut co-ownership;
ordinary induction does not supply the missing separated partition.
SeparateTwoEdges splits a common owner and separates any two distinct edges,
with at most ONE extra path. This is not a same-budget separation theorem.
FiveSpokeReduction consequently restores two pairs plus a fifth spoke with
at most TWO extra paths. In an odd-order smallest failure, every good proxy
partition needs at least ceil((n-1)/2) paths, and every partition within this
budget has both shortcuts in one member. The final certificate supplies an
exact-budget proxy partition and universal lower bound. Connectivity follows
from the already verified fact that every vertex deletion of an odd-order
smallest failure is connected.

Integration script /tmp/integrate_paired_upgrade.py has ALREADY RUN; do not rerun.
Backups /tmp/{spec,integratedaudit}_before_paired_upgrade.lean.
New layer Submission/PairedIntegrated.lean imports SuppressionIntegrated and
compiled warning-free (/tmp/paired_integrated1.log, .exit 0).
Work remains untouched. Spec is 63,960 lines, original theorem starts at 63,558,
sole sorry at 63,958. The original statement and sole import are unchanged.
Expanded IntegratedAudit has 1,730 requests, excluding the unresolved theorem.
Full sequential build/audit is running via /tmp/build_paired_upgrade.sh:
  /tmp/spec_paired_upgrade1.log
  /tmp/integrated_paired_upgrade_audit1.log.
No complete proof or disproof has been obtained.

### Diagnostic status and a rejected local repair

Matching-separated budget tests: the atlas run passed 994 connected graphs
and 41,434 matching choices. The eight-vertex run remains pending at this entry:
/tmp/matching_separated8.log, last prefix 11100, 1,335,962 matching choices.
The marked separated-core test FINISHED: all 11,117 connected eight-vertex
graphs, 331,820 marked perfect-matching cases passed (exit 0). Its atlas run
passed 119 graphs and 894 marked cases. These tests concern an auxiliary
strengthening, not the original conjecture; no separation theorem is inferred.

The tempting TWO-PATH five-spoke repair is FALSE even when the two proxy paths
intersect. Proxy paths
  P=0-1-2-3, Q=4-0-5-6
meet at 0. Replace P edges 01 and 23 by 0-7-1 and 2-7-3 and add spoke 7-5.
The result has edges 04,05,07,12,17,27,37,56,57. It needs four paths, not three.
Six vertices {0,3,4,5,6,7} have odd degree, already forcing six endpoint
incidences. The pendant triangle 7-1-2-7 forces at least one of its two
internal even vertices 1,2 to be an endpoint (otherwise its whole cycle
would lie in one simple path). That vertex contributes at least two more
endpoint incidences. Thus at least four paths are necessary. This graph has
eight vertices and meets, rather than violates, the Gallai bound.
Exact diagnostic /tmp/five_spoke_local.py found this obstruction after passing
all the smaller cases; /tmp/five_spoke_local.log, .exit 1 denotes the auxiliary
obstruction, not a Lean build failure. The cut/endpoint argument above is
informal; it has not been inserted as a Lean theorem.

A narrower diagnostic requires Q to meet the middle P segment between the
two shortcut edges (the cycle created by restoration). It is running in
/tmp/five_spoke_cycle_hit.py with maximum old order eight. This additional
condition is NOT proved available in a general smallest failure, and even
if the test passes it does not establish the repair lemma.

One more rejected shortcut, independent of these tests: splitting a vertex
and adding an edge between the two split copies can increase path number by
TWO, not merely one. Let A have vertices r,w,x_i,y_i (i=1,2,3) and paths
r-x_i-w-y_i. Two copies identified at r have a three-path partition, pairing
corresponding arms through r. Split r back into two vertices and add a bridge.
Each side needs three local pieces (degree(w)=6), and the bridge allows at
most one join, so five paths are necessary and sufficient. The split graph
has sixteen vertices and is well below the Gallai budget eight. This is an
informal structural obstruction, not a conjecture disproof or Lean assumption.

Build correction: attempt 1 aborted with a stack overflow (exit 134), not a
proof error. The earlier proven full builds require BOTH `ulimit -s 65536`
and `lake env lean -s 65536`; these were accidentally omitted in attempt 1.
Further, compiled modules must be written to .lake/build/lib/lean/Submission,
not Submission itself, because the former is on LEAN_PATH. The two stray
source-directory oleans were removed. FiveSpokeReduction (warning cleanup)
and PairedIntegrated are being rebuilt at the proper locations, with a fresh
FiveSpokeReduction audit. No proof statement or proof term was changed.
Corrected sequential chain /tmp/build_paired_upgrade2.sh logs:
  /tmp/five_spoke_reduction3.log
  /tmp/FiveSpokeReduction_audit2.log
  /tmp/paired_integrated2.log
  /tmp/spec_paired_upgrade2.log
  /tmp/integrated_paired_upgrade_audit2.log.
The report-by-report checker /tmp/check_paired_upgrade2.py waits for the last
two successful exits; /tmp/check_paired_upgrade2.log will record its result.
Attempt 1 is NOT an accepted integrated build.

The general eight-vertex matching-separated-budget diagnostic has FINISHED:
11,117 connected graphs, 1,344,111 matching choices, all passed in 2361.5 seconds
(/tmp/matching_separated8.log, .exit 0). No universal lemma follows from this.

The stronger fixed-TWO-path separation condition fails even if the second path
meets the middle segment. On five vertices take
  P=0-1-2-3-4, Q=0-2-4-1-3, marked edges 12 and 34.
Their union is K5 minus 03,04, and both paths are Hamilton. Any two-path
partition must again consist of two Hamilton paths, both ending at 0 (which
has degree two), with the other ends 3 and 4. Removing the first edge incident
with 0 leaves Hamilton paths of K4, each starting in {1,2} and ending in {3,4}.
Such a three-edge path contains either both marked edges or neither: its
number of cross-edges across {1,2}|{3,4} is odd. Hence the marked edges cannot
be separated into two paths. Three paths are allowed by the Gallai budget,
so this does not refute budget-aware matching separation.
Exact script /tmp/two_path_cycle_hit_separate.py, .log, .exit 1 (auxiliary
obstruction). The argument above is informal, not an added Lean assertion.
The narrower THREE-path five-spoke restoration test still runs independently.

## Unique-intersection separation (verified externally, NOT yet in Spec)

Submission/SingleIntersectionSeparation.lean imports PairedIntegrated and has
five complete lemmas: separated_of_distinct_owners, replace_pair_separated,
swap_single_intersection, separate_at_single_intersection,
forced_owner_no_single_intersection. Swapping tails at the ONLY common vertex
of two paths yields two simple paths with the same edge union and no increase
in partition size. If the two marked edges straddle that vertex in the first
path, this separates them. Thus universal forced co-ownership implies a SECOND
common vertex for every such candidate path. The hypothesis is essential.
Build /tmp/single_intersection_separation2.log (.exit 0) is warning-free;
/tmp/SingleIntersectionSeparation_audit1.log (.exit 0) has five individually
parsed reports, all using only the permitted axioms. Olean is correctly at
.lake/build/lib/lean/Submission/SingleIntersectionSeparation.olean.
This module has NOT yet been integrated into Spec or the 1,730-report audit.

### The narrower cycle-hit five-spoke repair is also FALSE

A structural twelve-vertex obstruction uses the forced-pairing two-triangle
core on S={0,1,2,3,4,5}: triangles 014 and235 joined by edges03 and12. Any
TWO-path partition of this core has endpoint pairs (0,3) and (1,2).
Indeed both paths must cross the two-edge boundary between the triangles once;
a path using a cross edge cannot end at that edge's incident vertex on either
side, since the other path alone could not cover the entire triangle.

Take proxy paths
  P=7-0-1-2-3-8,
  Q=9-10-1-4-0-3-5-2-11.
Replace shortcuts70 and38 by 7-6-0 and3-6-8, then add spoke6-10. Here r=6,
z=10; Q DOES meet the middle P segment, at 0,1,2,3. The resulting graph has
six odd vertices {6,7,8,9,10,11}, all outside S. A three-path partition would
therefore have exactly these endpoints. The four boundary edges of S are
06,36,1-10,2-11, so restricting such a partition to S gives at most two nonempty
path pieces (each has two boundary incidences, as no endpoint lies in S).
The core requires two pieces, and their forced pairing includes 0-to-3.
Both corresponding boundary edges return to r=6, forcing a repeated vertex
on that global simple path. Contradiction. Thus three paths are impossible.
Four suffice, as checked exactly:
  7-6-10-1-4-0-3-5-2-11;
  9-10;
  0-1-2-3-6-8;
  0-6.
The graph has twelve vertices, with Gallai budget SIX. This is only an
auxiliary local-repair obstruction, not a disproof of the conjecture.

Script/log /tmp/five_spoke_rigid_core.py and .log, .exit 0; the explicit four
path edge sets were checked disjoint with exact union. The cut argument is
currently informal, not a newly inserted Lean theorem. The exhaustive small
cycle-hit diagnostic was stopped deliberately after this larger structural
obstruction was verified: /tmp/five_spoke_cycle_hit.exit is 143, not a found
counterexample or a completed exhaustive pass. Its last completed prefix was
old order eight, first-path order six, 232,089 tested cases. No diagnostic
remains running. The proposed cycle-hit lemma MUST NOT be promoted to a theorem.

The general matching-separated Gallai-budget assertion remains unproved and
unrefuted by these local examples; all displayed bad proxy partitions are
well below the relevant Gallai budgets. Neither the new unique-intersection
criterion nor the 30 integrated conditional helpers settles erdos_583.


## Final verified paired-suppression integration checkpoint

Full sequential Spec build and helper audit completed with exit zero:
  /tmp/spec_paired_upgrade2.log (.exit 0)
  /tmp/integrated_paired_upgrade_audit2.log (.exit 0).
Spec has only the original conjecture's sorry warning, at line 63558.
All 1,730 unique helper reports were individually parsed and matched to requests:
1,666 use only the permitted axioms, and 64 are axiom-free.
The unresolved original theorem is excluded: this is NOT its verification.

Spec is 63,960 lines; original theorem starts at 63,558; sole sorry at 63,958.
Statement and sole import remain unchanged. No Work/external-development
references or native_decide occur in Spec. Work remains unchanged.
PairedIntegrated compiled warning-free and may be imported for development.
No build or audit remains running from this checkpoint. The same-budget
matching separation and the original global augmentation remain unproved.
No completed proof or disproof of erdos_583 has been obtained or submitted.


Unique-intersection integration has now run AFTER the paired-suppression build
and audit passed. Do not rerun /tmp/integrate_single_intersection_upgrade.py.
Backups /tmp/{spec,integratedaudit}_before_single_intersection_upgrade.lean.
The five verified helpers are now in Spec; IntegratedAudit has 1,735 requests.
Spec has 64080 lines; unchanged original theorem starts at 63678.
Only the original sorry remains. New development layer SingleIntersectionIntegrated
imports PairedIntegrated. Final sequential build/audit is pending at this entry;
logs /tmp/single_intersection_integrated1.log, /tmp/spec_single_intersection1.log,
/tmp/integrated_single_intersection_audit1.log. No conjecture proof was obtained.


## Final verified unique-intersection integration checkpoint

Full sequential build and helper audit exited zero:
  /tmp/spec_single_intersection1.log (.exit 0)
  /tmp/integrated_single_intersection_audit1.log (.exit 0).
Only the original conjecture's sorry warning occurs, at line 63678.
All 1,735 distinct helper reports were parsed and matched to requests:
1,671 use only permitted axioms, 64 are axiom-free. The unresolved
conjecture is excluded; this is NOT its verification. Statement/import unchanged.
Spec is 64080 lines, sole sorry at 64078.
No external-development or Work references or native_decide occur in Spec.
Work was not modified. SingleIntersectionIntegrated compiled warning-free and
may be imported for later work. No build, audit, or diagnostic remains running
from this checkpoint. No complete proof or disproof of erdos_583 was obtained.


## Hub amplification and one-unit terminal-weight slack

New standalone StarCopyAmplification.lean compiles warning-free, and all 20
constant reports passed the individual axiom audit: 18 use only permitted
axioms, two are axiom-free. Logs /tmp/star_copy_amplification9.log and
/tmp/star_copy_amplification_audit1.log; both .exit files are zero.

The generic project_hub_partition splits paths at a hub in Option W, discards
hub edges, and projects to H.comap Option.some. It proves
  2*new_count <= 2*old_count + degree(hub).
The proof uses the existing disjoint-arm splitting and exact arm/neighbor
bijection; nil pieces cannot increase the finset-image cardinality.

fourHub takes four disjoint copies of G and joins one selected vertex in each
to a new degree-four hub. It is connected when G is, has 4*n+1 vertices, and
any p-path partition yields a G partition of size q with 4*q <= p+2.
Consequently gallai_of_odd_order proves that solving ALL odd-order connected
graphs would suffice for the ENTIRE conjecture. This does not let a
smallest-odd-order failure assume smaller EVEN graphs solved: amplification
increases order. No contradiction with the prior degree-four restrictions
is claimed.

odd_double_bridge_one_slack absorbs one extra path at odd order. Combined
with the four-copy amplification, gallai_of_matching_deletion_one_slack
reduces the full conjecture to 2*p(H-F) <= |H|+2 for connected triangle-free
matching deletions of all-odd H. Finally,
  gallai_of_terminal_weight_one_slack
weakens the previously sufficient terminal-selection condition from
  terminalWeight >= |F|
to
  terminalWeight + 1 >= |F|.
The selection condition is STILL UNPROVED. This is not a proof or disproof
of Gallai; arbitrary pivots still need not preserve terminal weight.

Integrated by /tmp/integrate_star_copy_upgrade.py (DO NOT RERUN); backups
/tmp/{spec,integratedaudit}_before_star_copy_upgrade.lean. New development
layer StarCopyIntegrated imports SingleIntersectionIntegrated; Work unchanged.
Spec has 64420 lines, unchanged theorem starts at 64018; sole original
sorry remains. IntegratedAudit now requests 1,755 helper reports. Full
sequential build/audit is pending; logs /tmp/star_copy_integrated1.log,
/tmp/spec_star_copy1.log, /tmp/integrated_star_copy_audit1.log.

### Singleton-only terminal-weight packing is false, even with connected deletion

A new structural obstruction rules out a tempting STRONGER route to the
one-unit terminal-weight target. It is NOT a Gallai or terminal-weight
counterexample. The universal upper bound below is an informal cut/transition
argument, not yet a Lean theorem; the displayed witness and graph hypotheses
are checked exactly by /tmp/terminal_singleton_packing_obstruction.py (.exit 0).

Use nine triangles a_i-b_i-c_i-a_i, i=0,...,8, each joined by a_i-r to one hub r.
Partition their indices into three triples. In each triple, add matching edges
b_i-c_next(i) cyclically. These nine edges form F. The resulting H has 28
vertices, all of odd degree (triangle vertices degree three, hub degree nine).
Every F edge is triangle-free, and H-F is connected.

In a NORMAL H path partition, at most one external incidence at any triangle
can be terminal. If two triangle vertices had their external edges terminal,
their two internal darts would be paired; the edge between them would force
all three triangle edges into one member, making a repeated vertex. Thus each
F-only singleton consumes the unique permitted external terminal incidence
in both incident triangles. On the quotient triple, selected singleton edges
must form a matching in a three-cycle, of size at most one. Across the three
clusters there can be at most THREE F-singletons, whereas
floor((|F|-1)/2)=FOUR. Hence even the singleton packing needed to reach weight
|F|-1 cannot be guaranteed this way.

Nevertheless a normal H partition of FOURTEEN paths has terminal weight NINE:
- for each i, take a_next(i)-c_next(i)-b_i;
- pair triangles 0/1, 2/3, 4/5, 6/7, using
  c_i-b_i-a_i-r-a_j-b_j-c_j;
- take c_8-b_8-a_8-r.
All nine F edges are terminal at their b_i ends. Exact checks verify edge
disjointness and cover, simple paths, and exactly one endpoint at each vertex.
Thus ordinary one-ended terminal edges, not just singleton compensation, are
essential to a general selection argument. No finite counterexample search
was used or remains running. The full Spec build/audit continues separately.


The first full hub-amplification integration build failed at line 63910:
`a universe level named u has already been declared`. This is a standalone-to-
inline scoping collision, not a failed mathematical lemma. The new universe
was renamed uStarCopy in the standalone module, development layer, and inlined
Spec block. The conjecture statement is untouched. Attempt 1 is NOT an
accepted full build; no audit ran against its stale Spec.olean. Corrected
standalone/layer/full builds and fresh audits will use attempt-2 logs.


## Final verified hub amplification integration checkpoint

Full sequential build and helper audit exited zero:
  /tmp/spec_star_copy2.log (.exit 0)
  /tmp/integrated_star_copy_audit2.log (.exit 0).
Only the original conjecture's sorry warning occurs, at line 64018.
All 1,755 distinct helper reports were parsed and matched to requests:
1,689 use only permitted axioms, 66 are axiom-free. The unresolved
conjecture is excluded; this is NOT its verification. Statement/import unchanged.
Spec is 64420 lines, sole sorry at 64418.
No external-development or Work references or native_decide occur in Spec.
Work was not modified. StarCopyIntegrated compiled warning-free and
may be imported for later work. No build, audit, or diagnostic remains running
from this checkpoint. No complete proof or disproof of erdos_583 was obtained.

## Maximum-weight exposure is false (14-vertex structural obstruction)

The absolute-maximum exposure strategy is abandoned. Both the unoriented claim
("every marked edge is terminal in some maximum-weight normal partition") and
the directed claim (a specified marked endpoint) fail, under ALL the hypotheses
used by the triangle-free matching-deletion reduction.

Take G0 = K7 minus the triangle on {4,5,6}. Use two copies on 0..6 and 7..13,
add all seven vertical edges i-(i+7), and mark the six with i=0..5. H has 14
vertices and 43 edges, all degrees odd. F is a triangle-free matching and H-F
is connected by the unmarked bridge 6-13.

Informal universal bound (NOT yet Lean-formalized): restricting a normal H
partition to either G0 core yields a normal partition of its 18 edges. If I is
the set of vertices where the vertical edge is terminal in that copy, it has
exactly 7-|I| nonempty pieces. Each piece has at most six edges, so |I|<=4.
Equality forces three Hamilton paths and therefore I={0,1,2,3}, by the degree
formula. Total marked weight is consequently <=8. An explicit normal partition
attains eight. If edge 4-11 is terminal at either end, one core has |I|<=3,
hence total weight <=7. Thus this marked edge is internal in every optimum.

/tmp/terminal_weight_exposure_obstruction.py (.exit 0) checks exactly the graph
hypotheses, a normal weight-eight partition, and a normal weight-seven partition
having edge 4-11 first at vertex 4. Its log contains the full witnesses. It does
NOT exhaustively check the universal upper bound; that is the argument above.
This is NOT a counterexample to Gallai or to the sufficient one-slack threshold:
|F|=6, so only weight FIVE is required. Any useful augmentation must be allowed
to spend surplus weight, rather than preserve an absolute maximum.

Completed exact diagnostics before this structural obstruction:
- unoriented, all-odd order 8: 224 graphs / 233 eligible matching cases;
- unoriented, cubic order 10: 19 graphs / 1,796 cases;
- directed, all-odd order 8: 224 graphs / 652 cases;
- directed, cubic order 10: 19 graphs / 2,537 cases (159.08 seconds).
All passed, all .exit files are zero, and none remains running. They tested
auxiliary claims, not Gallai. Small-case success was misleading here.
Spec remains at the verified 64,420-line checkpoint with its original sorry.

## Exact terminal trimming and a Lean-verified exposure obstruction (external)

Three new modules are complete, compiled, and individually axiom-audited. They
are NOT in Spec/Work or an integrated layer yet. All source files import the
existing verified development chain, starting at StarCopyIntegrated.

  Submission/TerminalCapacity.lean                 271 lines, 9 declarations
  Submission/TerminalCopyBounds.lean               151 lines, 4 declarations
  Submission/TerminalExposureObstruction.lean      251 lines, 40 audited declarations

Namespaces are Erdos583TerminalCapacityDevelopment,
Erdos583TerminalCopyBoundsDevelopment, and
Erdos583TerminalExposureObstructionDevelopment. Imports for further external
work may use Submission.TerminalCopyBounds (general helpers only) or
Submission.TerminalExposureObstruction (also the finite obstruction).

TerminalCapacity strengthens the old trimming inequality to an EXACT identity
for nonempty members:
  E.card + terminalWeight D F = D.card + F.edgeSet.ncard.
It also retains endpoint-zero information: if endpointMultiplicity D v = 1
and v is a terminal incidence of F, then endpointMultiplicity E v = 0.
The restriction is obtained from forest_normal_decomposition and an exact
nonempty-piece refinement. This is a counting/transport theorem, not a lower
bound on attainable terminal weight.

Other general helpers:
- path_length_le_of_avoids: avoiding a specified vertex lowers maximum length;
- edge_capacity_at_vertex:
    2*|edges G| <= 2*(|V|-2)*D.card + degree(v) + endpointMultiplicity D v;
- terminal_weight_of_deletion_lower_bound and terminal_weight_copy_lower_bound;
- decompose_both_copies: project BOTH unpaired copies, counts sum <= original,
  nonempty members retained, and zero endpoint counts remain zero;
- terminalVertices_mono / terminalWeight_mono under enlarging the marked graph.

The 14-vertex maximum-weight exposure obstruction above is now FULLY
Lean-proved, not merely an informal universal argument. The finite graph is
Bool x Fin 7, with core K7 minus the last triangle, all seven vertical edges
M, and F the first six vertical edges. The module verifies the all-odd,
triangle-free-matching, connected-deletion hypotheses, M.card=7, F.card=6,
and that the peripheral edge at coordinate four really belongs to F.

The general capacity bound gives at least three paths in each core. If core
vertex four has no endpoint, it gives at least FOUR paths: 36 <= 10*p + 4.
Exact trimming and both-copy projection therefore prove:
  terminal_weight_le_eight;
  exposed_peripheral_weight_le_seven (either endpoint).
An explicit seven-path NormalTrailSystem optimum attains weight EIGHT. Its
paths, edge partition, endpoint bijection, exact parts cardinal, and terminal
weight are all kernel checked. Finally maximum_weight_exposure_false negates
the existence of an absolute-weight optimum exposing this marked edge. This
is explicitly an AUXILIARY disproof, NOT a disproof of erdos_583.

The weight-seven forced witness from the earlier Python log is NOT separately
instantiated in Lean; it is unnecessary for the universal negation. The sufficient
one-slack target is only |F|-1=FIVE, so the obstruction still has surplus and
DOES NOT refute that target. Any new augmentation must not assume absolute
maximum exposure. No bounded-loss or threshold-preserving exposure theorem has
been proved.

Verified logs/exits (all zero):
  /tmp/terminal_capacity6.log
  /tmp/terminal_capacity_audit2.log                  9 matched permitted reports
  /tmp/terminal_copy_bounds4.log
  /tmp/terminal_copy_bounds_audit1.log               4 matched permitted reports
  /tmp/terminal_exposure_obstruction5.log
  /tmp/terminal_exposure_obstruction_audit2.log     40 matched reports:
                                                   39 permitted, 1 axiom-free.
All reports individually parsed; no errors or warnings. The finite obstruction
needs maxRecDepth 16384, plus the usual 64-MiB stack settings. No native_decide.

Reminder from older research: minimum path partitions need not be normal
(K6 plus a degree-three seventh vertex). This does not refute the stronger
normal Gallai BUDGET bound, but one cannot assume normality at an unrestricted
minimum. No relation proving equivalence of those two optimization problems
was obtained during this continuation.

Spec remains UNCHANGED at 64,420 lines, with the original statement/import
and sole sorry at line 64,418. No full Spec rebuild is required for this
external checkpoint, and no build, audit, or diagnostic remains running.
No proof/disproof of the original conjecture has been obtained or submitted.

## Uniform additive slack reduction (external, verified)

Submission/AdditiveAmplification.lean, namespace
Erdos583AdditiveAmplificationDevelopment, imports StarCopyIntegrated.
Three lemmas reduce_odd_uniform_slack, odd_bound_of_uniform_slack, and
gallai_of_uniform_odd_additive_bound prove that a UNIFORM additive constant
in the Gallai bound for connected odd-ORDER graphs would imply exact Gallai
for all connected graphs. Four-hub projection removes one unit of universal
slack; induction removes the constant. This does not prove or assume that
such a universal additive bound exists. Odd order is not all-odd degree.
Unique universe uAdditive avoids integration collisions.
/tmp/additive_amplification1.log and /tmp/additive_amplification_audit1.log
both exited zero, warning-free; all three audit reports parsed and matched,
using only propext, Classical.choice, Quot.sound. Not yet integrated into Spec.

Additional informal caution: two triangles joined by a bridge have path number
three, but making that bridge terminal requires at least four paths. Thus
even a Gallai-budget partition need not expose an arbitrary edge. This is
not a Gallai counterexample. No odd-order analogue was established.

## Single-owner neighborhood diagnostic — not a theorem

An additional auxiliary candidate was considered: in an all-odd graph, can
one specified vertex a have its endpoint-owning path entirely contained in
its closed neighborhood N[a]? This would imply single directed nonedge
avoidance, but no proof was obtained. It would not by itself establish the
simultaneous matching-avoidance certificate needed for the global reduction.

/tmp/owner_neighborhood_test.py exactly enumerated normal path partitions
subject to this condition on the 224 all-odd order-eight graphs in odd8.g6.
All 1,792 specified-vertex cases passed in 1.88 seconds:
/tmp/owner_neighborhood_odd8.log, .exit 0. This is finite evidence only,
not an original-conjecture counterexample search and not a Lean theorem.
No further diagnostic is running. In particular, the existing theorem for
at most three even vertices does not automatically prove prescribed-edge
terminality or this endpoint-avoidance assertion.

No new helpers were integrated during this continuation. Spec remains at
64,420 lines with its unchanged statement/import and its original unresolved
sorry. No proof or disproof of erdos_583 has been obtained.

## Compact submission and degree-sensitive core lifting

After the submission verifier exceeded its resource limit, the entire old
64,420-line Spec was preserved as Submission/SpecDevelopmentSnapshot.lean.
The actual Spec is now 24 lines: the SAME import, definitions, and conjecture
statement, with its unresolved sorry at line 22. A local check completed in
4.22 seconds, with the expected sorry warning. This is NOT a valid completed
proof; compaction fixes checking cost, not the mathematical gap. Work and the
external integrated development chain remain unchanged.

The cycle-absorption route was revisited, but the unrestricted missing-vertex
claim is already refuted by the order-eleven obstruction recorded above.
/tmp/cycle_almost_spanning_path.py checked cycle-plus-almost-spanning-path
instances: order 8 (323 cases), 9 (2,621), and 10 (23,811) passed. At order 11
it stopped at case 93,030 with another labeling of the same obstruction:
C=(0,1,...,10,0), P=(3,5,2,4,1,8,10,7,9,6). The earlier structural proof
already ruled out this strategy; no further diagnostic remains running.
Do not attempt the false general absorption or Hamilton endpoint-exchange
claim again. None of these examples disproves Gallai.

A new external module Submission/BoundaryStarSavings.lean (79 lines, three
lemmas) imports StarCopyIntegrated and proves a sharper legitimate reduction.
Namespace: Erdos583BoundaryStarSavingsDevelopment. If S has a rooted core
cover with q indexed paths and the required distinct boundary-edge slots,
lifting a k-path partition of the contracted graph gives
  2*new_count + degree(contracted center) <= 2*k + 2*q.
This retains the full degree saving, rather than saving only one touched path.
Smaller-order induction therefore suffices when
  2*q+1 <= |S|+degree(contracted center),
or, at odd ambient order, when
  2*q <= |S|+degree(contracted center).
The proof also handles S=univ; no proper-subset premise is required.
The required rooted-cover and boundary-capacity certificates are NOT supplied
for general graphs. These are conditional reductions, not a Gallai proof.

Verified: /tmp/boundary_star_savings2.log (.exit 0),
/tmp/boundary_star_savings_audit2.log (.exit 0). The latter's three reports
were parsed and matched individually, using only propext, Classical.choice,
Quot.sound. Both files are warning-free. The first audit's missing docstring
warning was fixed. No helpers were added to the compact Spec.
No complete proof or disproof has been obtained.

## Accumulated-constraint diagnostic and another local limitation

Submission/AccumulatedConstraintCheck.lean imports StarCopyIntegrated and
copies the old main proof attempt, replacing its final sorry by a diagnostic
tactic. It is NOT imported by Spec and does NOT compile as a proof.
/tmp/accumulated_constraints1.log records the full residual state: omega
failed and retained a satisfiable arithmetic abstraction. Its illustrative
branch involving n/4 is not a theorem that n is divisible by four.
/tmp/accumulated_constraints_aesop1.log records a bounded aesop attempt,
which reached 1,200,000 heartbeats in simp without completing. Both exits
are 1. No new contradiction or main-theorem proof was obtained.

A further informal local caution: a quota-two-root lollipop plus another
root-ending path need not be replaceable, using only these two members, by
two paths OR by a whole cycle and a path. On vertices 0,...,5 use
  L = 0-1-2-0-3-4-5,
  P = 0-4-1-3-2-5.
The eleven edges are disjointly covered by these two trails. The degree
sequence is (4,4,4,4,4,2), so the union is Eulerian. Two simple paths have
at most ten edges. A cycle plus a nonempty simple path would have two odd
degree vertices, while a cycle plus an empty path cannot cover eleven
edges on six vertices. Thus neither two-member replacement exists. The
Gallai budget is THREE, not two, so this is not a conjecture counterexample.
The edge sets and degrees were checked exactly; this observation has not
been formalized in Lean. It merely rules out another overstrong local lemma.

Spec remains the compact, unchanged conjecture with one unresolved sorry.
No new development module was integrated, and no diagnostic is running.

## Actual-zero-forest edge restoration (external, verified)

Submission/EvenEdgeRestoration.lean imports StarCopyIntegrated, namespace
Erdos583EvenEdgeRestorationDevelopment. Five declarations:
  decomposition_path_family_tracked
  restore_of_zero_forest
  acyclic_of_edges_incident
  even_count_delete_edge
  gallai_of_few_even_and_nonedge

The tracked append API already existed in DeletionEndpoint; it was reused.
The new indexing API equates TrailFamily.quota with endpointMultiplicity for
nonempty-member path decompositions. Restoration at unchanged slot count
holds when the deleted endpoints both have quota one and the ACTUAL zero
set together with those endpoints induces a forest.

The new special case: a graph with <=5 even-degree vertices has the Gallai
budget if there are distinct even a,u,v with vu an edge and au a nonedge.
No connectivity assumption. Delete vu, force a inactive using the existing
EndpointSelection lemma, and use normal_count. A strict budget allows a
singleton restoration; equality forces a to be the sole inactive vertex.
Thus the zero-baseline set after appending is {a,u,v}, an acyclic subgraph.
ForestZeroNormalization repairs the deficit without adding a slot.

Verified /tmp/even_edge_restoration6.log exit 0 warning-free;
/tmp/even_edge_restoration_audit2.log exit 0 warning-free, all FIVE reports
programmatically parsed/matched, permitted axioms only. No integration into
compact Spec. This is NOT the unrestricted Gallai proof. The independent
and complete even-induced cases are not covered by this new argument.

## Normality-preserving forest restoration and even girth (verified external)

Submission/NormalForestRestoration.lean, namespace
Erdos583NormalForestRestorationDevelopment, imports EvenEdgeRestoration.
Ten declarations, including three definitions. Crucial strengthening:
normalize_zero_root_forest retains a ZERO-baseline final root, provided the
initial root has baseline zero. The existing reachable-root proof admits this
invariant directly. Therefore a baseline bounded by two produces final quotas
bounded by two. This is NOT a general normalization theorem for arbitrary
zero graphs, nor a proof that unrestricted minimum partitions are normal.

Other declarations: path_family_partition_quota_le removes nil members and
bounds resulting endpoint counts by the family quotas; restore_normal_of_zero_forest;
restore_path_subgraph_tracked; evenCount, SmallEvenForests, NormalBound;
evenCount_eq_filter, normal_bound_of_three_even, restore_normal_small_even_forests.
SmallEvenForests G says every S of even vertices with 2*|S|<=e(G)+2 induces a
forest. For an even-even deleted edge, a strict normal budget permits singleton
restoration. At full budget, normal_count bounds the actual inactive set plus
the two restored endpoints by this small-set threshold. Normality survives.

Submission/EvenGirthRestoration.lean imports NormalForestRestoration, namespace
Erdos583EvenGirthRestorationDevelopment. Five verified lemmas:
 small_even_forests_delete_edge
 restore_matching_small_even_forests
 normal_bound_of_matching_deficiency_le_three
 small_even_forests_of_egirth
 normal_bound_of_even_girth

Thus a matching on even vertices, leaving <=3 unmatched, suffices when the
even-induced graph has extended girth > floor(e/2)+1. Forests have infinite
extended girth. The proof gives NORMAL decompositions and requires no
connectivity. Unlike the earlier five-even case, evenCount is unbounded here.
Both the matching-deficiency and small-zero-cycle obstructions remain in the
general conjecture. No assertion that these conditions always hold was made.

Warning-free builds:
 /tmp/normal_forest_restoration5.log exit 0
 /tmp/even_girth_restoration3.log exit 0
Warning-free audits:
 /tmp/normal_forest_restoration_audit1.log exit 0, TEN matched permitted reports
 /tmp/even_girth_restoration_audit1.log exit 0, FIVE matched permitted reports
All reports programmatically parsed/matched, allowed axioms only. No changes
or integrations into compact Spec. The original sorry remains unresolved.

## Exact normal quota purification (external, verified)

Submission/NormalQuotaPurification.lean, namespace
Erdos583NormalQuotaPurificationDevelopment, imports NormalForestRestoration.
Its one lemma path_family_partition_quota_exact shows that a normal indexed
PATH family on a graph without isolated vertices can be replaced by a
nonempty-member finset decomposition of EXACTLY the same cardinality and
EXACTLY the same endpoint quotas. Proof: discard nil members, then use the
already-proved realize_subset to reactivate precisely those vertices whose
quota had consisted of a discarded nil slot. Normality plus parity and the
specified zero set force equality of quotas; summing gives exact cardinality.
No arbitrary quota-feasibility or minimum-partition normality is asserted.

/tmp/normal_quota_purification1.log and
/tmp/normal_quota_purification_audit1.log both exit 0 warning-free. The single
axiom report was parsed/matched, permitted axioms only. Spec remains unchanged
at 24 lines with its unresolved original sorry; no build or diagnostic running.

Possible NEXT direction, not yet proved: preserve one active even vertex in
each even-induced cycle while restoring a matching. The zero-root invariant
means old positive baseline quotas stay fixed. Plain nil-discarding loses this
invariant, but exact purification above repairs that issue on graphs without
isolated vertices. If the even-induced graph is a disjoint union of cycles
and paths and a matching covers all but <=3 vertices, restoring selected cycle
edges first might protect each cycle from becoming wholly zero later. This
could remove the GLOBAL girth restriction for this subclass. The required
ordered restoration/active-vertex certificate is NOT formalized. Even then,
arbitrarily many unmatched independent even vertices remain the main blocker.

A locality strengthening also seems available directly from the forest proof:
carry membership in the initial zero-component along reachable roots; only
that component, rather than the entire zero graph, would need to be acyclic.
No such localized theorem has yet been written or claimed proved.

The independent-even hub-completion route still needs roughly half the spokes
terminal at their independent endpoints. TerminalDarts preserves endpoint
tails in a fixed-root repair, but force_first_edge can create intermediate
roots outside the independent set; it therefore does NOT automatically keep
all previously terminal spokes. No sufficient cardinal augmentation obtained.

## Local zero-region normalization (external, verified)

Submission/LocalZeroNormalization.lean imports NormalQuotaPurification,
namespace Erdos583LocalZeroNormalizationDevelopment. Four complete lemmas:
 normalize_in_zero_region
 repair_of_subsingleton_zero_neighbors
 normalize_region_partition
 append_edge_away_from_inactive

The first retains both the zero-baseline-root invariant and membership in a
specified region Z. Z contains the initial root, is closed under adjacency to
zero-baseline vertices, and induces a forest. Zero cycles outside Z are now
allowed. The partition corollary uses exact purification on graphs without
isolated vertices, so positive baseline labels really stay active.

The second lemma repairs a rooted one-defect family at EXACTLY the same quotas
when the root has at most one zero-quota neighbor; it needs no available pair
and no restrictions on other zero vertices. The two root exposures force a
positive quota at one of their distinct labels.

append_edge_away_from_inactive applies this to a genuinely new edge v-u appended
at an endpoint u of a path family. If v has no inactive neighbor in the OLD
family, the extension can be repaired with unchanged slot count and the exact
balance q_new(x)+[u=x]=q_old(x)+[v=x]. Neither old-quota normality nor parity
hypotheses are needed. The actual inactive-neighbor hypothesis is explicit.

Warning-free /tmp/local_zero_normalization4.log exit 0 and
/tmp/local_zero_normalization_audit1.log exit 0. All FOUR reports parsed and
matched, only permitted axioms. Compact Spec is unchanged and unresolved.

The parity-forest route to independent even vertices was reconsidered: it fixes
odd endpoints but leaves an UNCONTROLLED number of cycle pieces. One-defect
forest normalization cannot simply be applied to multiple cycles, and its
one-free-pair count cannot be dropped. No independent-even Gallai theorem has
been obtained. Existing fixed-quota obstructions remain relevant.

Possible next concrete step: a guarded matching-restoration theorem. If an
initial normal partition has a set A of active even vertices, all further
matching endpoints avoid A, and the final even-induced graph minus A is a
forest, normal zero-root restoration followed by exact purification should
preserve A and the slot count throughout. For disjoint even-induced cycles,
one could restore one selected matching edge per cycle FIRST, using the new
no-inactive-neighbor append lemma to keep its chosen end active. These selected
edges form an induced matching in that subclass. The other matching edges
could then be restored with those cycle-breaking active labels protected.
This argument has NOT yet been formalized as a theorem. It would still not
handle arbitrary matching deficiency or unrestricted even-induced graphs.

## Guarded restoration and seed initialization (external, verified)

Submission/GuardedMatchingRestoration.lean imports LocalZeroNormalization,
namespace Erdos583GuardedMatchingRestorationDevelopment. Six lemmas:
 restore_one_edge_zero_forest_tracked
 even_vertices_delete_edge_subset
 even_forest_off_delete_edge
 restore_even_edge_guarded
 restore_matching_guarded
 partition_of_guarded_matching
The tracked one-edge restoration keeps all positive old quotas away from the
two restored ends exactly fixed. An active guard set A, disjoint from all
remaining matching ends, can consequently be retained throughout matching
restoration whenever the even-induced graph minus A is a forest.

IMPORTANT strengthening over the prior proposed plan: intermediate graphs do
NOT need to have no isolated vertices. Keep indexed path families (including
nil slots) until all edges have been restored; remove nil slots only at the
end. This preserves the guard quotas needed during the induction, even when
some guards are temporarily carried by nil slots. The finset corollary gives
a nonempty-member normal decomposition with no larger count, but does NOT
claim that it retains the guards after that final removal.

Build /tmp/guarded_matching_restoration2.log exit 0, warning-free.
Audit /tmp/guarded_matching_restoration_audit1.log exit 0, SIX reports parsed
and matched, only permitted axioms. The first audit-parsing script split on
comma-space and rejected newlines; the corrected whitespace-stripping parser
matched all reports. This was a parser issue, not a Lean build issue.

Submission/SeedMatchingRestoration.lean imports GuardedMatchingRestoration,
namespace Erdos583SeedMatchingRestorationDevelopment. Three lemmas:
 matching_support_delete
 restore_induced_seed_matching
 gallai_of_seeded_matching
Starting from a path family with every quota one, any INDUCED matching can be
restored with arbitrary orientations. Each chosen head acquires quota two,
each tail quota zero, and every other vertex keeps quota one. Because the
seed endpoints induce exactly the seed matching, an unprocessed head has no
neighbor among any previous seed tails. append_edge_away_from_inactive thus
repairs each edge at the exact prescribed quotas.

The combined Gallai special case assumes:
 - F is a perfect matching on the even-degree vertices of G;
 - S <= F is an induced matching in G;
 - A selects precisely one end of each edge of S, with A subset S.support;
 - the even-induced graph of G minus A is a forest.
It proves a nonempty-member normal partition with 2*D.card <= |V|. Restore S
first to initialize the active guards A, then restore F\\S guarded. This can
handle an arbitrary number of separately seeded cycles, unlike a single
small-even-set criterion. The existence of these certificates is NOT proved
for arbitrary graphs. In particular the independent-even matching-deficiency
obstruction is untouched. No universal maximum-degree-two classification was
formalized here; the theorem is explicitly certificate-based.

Build /tmp/seed_matching_restoration5.log exit 0, warning-free.
Audit /tmp/seed_matching_restoration_audit1.log exit 0, THREE reports parsed
and matched, only permitted axioms. Neither new module was inlined into the
compact Spec, whose original sorry remains unresolved.

Lean notes from this continuation:
 - SimpleGraph.support uses SetRel.dom. After extracting a witness, `change
   (F.deleteEdges ...).Adj x y` can be needed before rw [deleteEdges_adj].
 - Different Decidable instances for support membership can block defeq of
   ite expressions. Split on membership and simp the two concrete branches.
 - When transporting a path family indexed by D.card across a graph equality,
   generalize can fail because D has a graph-dependent type. Instead build
   an existential family on the target graph, rw the graph equality in that
   goal, and supply the original family. This suffices if only fixed quotas,
   rather than identity with the original family, need to be retained.

## Asymptotic amplification (external, verified)

Submission/AsymptoticAmplification.lean imports AdditiveAmplification,
namespace Erdos583AsymptoticAmplificationDevelopment. Six lemmas:
 reduce_odd_linear_offset
 odd_linear_offset_two
 odd_linear_bound_offset_two
 gallai_of_arbitrarily_good_linear_bounds
 normal_partition_card_le_vertices
 gallai_of_asymptotic_odd_bound

This strengthens the previous UNIFORM ADDITIVE sufficient condition to an
ASYMPTOTIC leading-coefficient condition. It suffices that, for every rational
epsilon>0, all sufficiently large connected odd-order graphs have a partition
of at most (1/2+epsilon)*n paths. The threshold may depend arbitrarily on epsilon.
Equivalently for the reduction, one may supply a uniform bound
  p(G) <= (1/2+epsilon)*n + c_epsilon
with an arbitrary finite offset depending on epsilon. No approximation bound
of this kind has been proved or imported unconditionally here.

Proof details: fourHub projection takes a uniform rational linear bound
  p <= a*n+(c+3)
to p <= a*n+(c+2), for a<=1. Induction reduces any nonnegative integer offset
to two. On each fixed odd order n take epsilon=1/(2*n+2), obtaining
p <= ceil(n/2)+2. The already verified uniform-additive amplification then
removes that constant. To pass from sufficiently-large bounds to uniform
offsets, the small orders use the elementary normal-partition bound p<=n.

Build /tmp/asymptotic_amplification3.log exit 0, warning-free.
Audit /tmp/asymptotic_amplification_audit1.log exit 0, SIX reports parsed and
matched, only permitted axioms. This conditional reduction is NOT a solution
of Gallai: its asymptotic premise is still absent. In particular do not assume
that a general n/2+o(n) path bound is known merely because similar theorems exist
under density or regularity assumptions. Neither such hypotheses nor an
unrestricted approximation theorem have been supplied.

Checkpoint: the actual Spec remains 24 lines with its original sorry at line
22 and unchanged conjecture/import. New modules have 219, 216, and 135 lines,
respectively. All three builds/audits are complete. No process is running.
There is still no valid full proof or counterexample to erdos_583.

## Strict multi-defect forest improvement (external, verified)

Submission/MultiDefectForestImprovement.lean imports LocalZeroNormalization,
namespace Erdos583MultiDefectForestImprovementDevelopment. Ten lemmas:
 improve_at_outside_start
 improve_at_outside_start_endpoints
 exposedRoot_improve_positive
 move_pair_score_or_root
 move_pair_score_or_root_endpoints
 exposedRoot_move_pair_score_or_root
 improve_in_zero_region
 improve_pair_forest
 improve_root_pair_of_even_forest
 maximum_root_quota_one_of_even_forest

The surgeries used by one-defect normalization extend to arbitrary total
defect when their conclusion is only ONE UNIT OF SCORE IMPROVEMENT, not a
complete path family. The positive-exposure slide gains exactly one, and a
pair move either gains one or leaves score fixed with a new rooted defect.
Thus forest reachability still yields a gain of exactly one. The localized
version retains the final root-pair label in a zero-closed forest region Z
and at zero baseline. Positive baseline quotas stay fixed. There is no
assertion that the improved family is all paths, or even that it retains a
rooted defect. These omissions are essential, not missing proof steps.

For any graph whose even vertices induce a forest, ANY rooted defect with
quota >=2 admits strict free-quota improvement, independent of the total
defect and of the number of slots. Consequently, at ANY unrestricted score
maximum, every rooted repetition has quota exactly ONE and odd ambient
degree. This removes the former single-defect hypothesis from this necessary
condition. It still does not handle odd quota-one roots or internal defects.

This is consistent with K_{2,5}: at two slots, moving a pair from a closed
cycle can increase the score while leaving internal repetitions. It does NOT
prove that one pair normalizes an arbitrary number of defects.

Build /tmp/multidefect_forest_improvement2.log exit 0, warning-free.
Audit /tmp/multidefect_forest_improvement_audit1.log exit 0, TEN reports parsed
and matched, only permitted axioms. Original Spec remains untouched with its
sorry. No compilation is pending.

Potential new direction, UNPROVED: internal single-defect rootification when
the repeated vertex has quota AT LEAST TWO (rather than the disproved quota-
one assertion). No generic rootification theorem has been obtained. The
old eleven-vertex positive-quota obstruction was tested after adding one more
root-ending path: a new leaf, a direct root-to-6 edge, a subdivided root-to-6
edge, and one longer unused-edge path. Every tested extension DOES have a
same-quota rooted realization, found by exact cycle/tail/path enumeration.
These few examples are not a proof of the stronger candidate. Script:
 /tmp/quota_two_internal_root.py
The output witnesses are not incorporated into Lean and no assertion depends
on the diagnostic. In a hypothetical proof, endpoint paths may meet the
internal cycle many times; simply detaching that cycle can lose score.

A fresh curl attempt to erdosproblems.com/583 still failed DNS resolution.
No external new result or approximation theorem has been retrieved.

### The general quota-two internal-rootification candidate is FALSE

The later targeted parallel-copy diagnostic finished, exit 0:
 /tmp/quota_two_internal_root_parallel.py
 /tmp/quota_two_internal_root_parallel.log
It found NO rooted realization for the following three-trail family (not a
Gallai counterexample):
 P = 1-2-0-3-4-0-5-6
 Q = 0-7-3-8-4-1-9-2-5-10-6
 R = 0-11-3-12-4-13-1-14-2-15-5-16-6.
There are 17 vertices, 29 edges, and exactly one INTERNAL defect, at 0.
Quotas are q(0)=2, q(1)=1, q(6)=3, and zero elsewhere. Actual Gallai budget
is NINE, whereas this family has three slots. The diagnostic exhausts simple
root cycles and disjoint tails, then exact two-path covers of their remainder.
It is an auxiliary diagnostic, not a Lean theorem or a proof assumption.

There is also a direct structural explanation, so no generic assertion of
quota-two rootification should be pursued. Suppress the quota-zero degree-two
vertices in the explanation (this is not a Lean graph operation here). The
core vertices are 0,...,6, with edge multiplicities:
 02:1, 03:3, 04:1, 05:1, 12:3, 14:2, 25:2, 34:3, 56:3.
The core degrees are [6,5,6,6,6,6,3]. Degree(0)+q(0)=8 forces the unique
repetition to be at 0 in any three-trail deficit-one realization. The three
endpoints at 6 force each member to end at 6; hence a rooted realization
would have a rooted 0-to-6 member and two simple members with core endpoint
pairs (0,6) and (1,6). Degree and quota counts force every member to visit
every core vertex. The two normal core Hamilton paths are uniquely:
 0-3-4-1-2-5-6
 1-4-3-0-2-5-6.
Removing them leaves a disconnected double-edge component between 1 and 2,
as well as 0-3-4-0 with tail 0-5-6. One remaining trail cannot cover that.
This rules out a rooted family with those quotas. The example's even-induced
graph has cycles; it does not disprove a specifically even-forest version.
No such restricted rootification theorem has been proved either.

All diagnostics and Lean audits are complete. Compact Spec is unchanged and
unresolved. No original-conjecture proof or disproof has been found.

## One-forbidden-zero forest improvement (external, verified)

Submission/OneForbiddenRoot.lean imports MultiDefectForestImprovement, namespace
Erdos583OneForbiddenRootDevelopment. Five lemmas:
 tree_leaf_away
 cycle_of_two_successors_except_one
 improve_zero_forest_avoiding
 normalize_zero_forest_avoiding
 restore_edge_tail_zero

A movable pair at r can gain one unit of score while avoiding one prescribed
label a != r, provided baseline-zero vertices induce a forest. Positive
baseline quotas remain fixed and the pair finishes at another baseline zero,
not a. There is NO assertion that a general improved family retains a root or
has become paths. The one-defect score hypothesis supplies paths in the
normalization corollary. The combinatorial escape argument restricts to a
reachable connected component and finds a tree leaf other than a.

restore_edge_tail_zero restores an edge u-v from a normal path family with
q(u)=q(v)=1, assuming old zero vertices together with u,v induce a forest.
It retains the slot count and normality, fixes old positive quotas away from
u,v, and ensures q_new(u)=0. It does NOT ensure the head v remains active.
Intermediate nil slots are permitted as in earlier indexed restoration.

Build /tmp/one_forbidden_root4.log exit 0, warning-free.
Audit /tmp/one_forbidden_root_audit2.log exit 0, warning-free; FIVE reports
parsed and verified to use only propext, Classical.choice, Quot.sound.
The first audit passed axiom checks but had a missing-module-docstring warning;
the second includes the docstring and is clean. This is NOT a proof of the
independent-even-vertex base case or of the original conjecture. Spec remains
24 lines with its original sorry, and no process is running.

## Connected forbidden zero subtree (external, verified)

Submission/ForbiddenSubtree.lean imports OneForbiddenRoot, namespace
Erdos583ForbiddenSubtreeDevelopment. 253 lines, six lemmas:
 tree_leaf_outside_preconnected
 cycle_of_two_successors_except_preconnected
 cycle_of_two_successors_except_subtree
 improve_zero_forest_avoiding_subtree
 normalize_zero_forest_avoiding_subtree
 restore_edge_avoiding_subtree

The pair-avoidance invariant now permits an entire connected set A of
baseline-zero vertices, rather than just one label. Assumptions are explicit:
A is contained in the baseline-zero set, G.induce A is PRECONNECTED (so the
empty set is allowed), the initial pair root is outside A, and all baseline
zeros induce a forest. The score-improvement lemma allows other defects and
only gains ONE score unit. The normalization corollary uses the one-defect
score equality to conclude every member is a path. Restoration from quotas
q(u)=q(v)=1 keeps A inactive, all old positive quotas away from u,v fixed,
normality, and the slot count. The head v must be outside A. It need not stay
active, and unprotected old zeros can become active.

The graph argument maximizes distance from a forbidden vertex over reachable
allowed vertices. Two successors would both have to be the unique predecessor
on the tree path. If no forbidden vertex is reachable, ordinary two-successor
forest contradiction applies. tree_leaf_outside_preconnected is also proved
separately by the same distance argument, but is not needed by the main chain.

Build /tmp/forbidden_subtree6.log exit 0, warning-free.
Audit /tmp/forbidden_subtree_audit1.log exit 0, SIX axiom reports parsed and
matched, only propext, Classical.choice, Quot.sound. Spec remains 24 lines,
unchanged with its original sorry. This is NOT the missing quota-one repair,
independent-even base case, or unrestricted Gallai bound.

A new auxiliary endpoint question is being investigated, NOT PROVED:
in a graph with exactly one even-degree vertex, can every edge joining odd
vertices be terminal at AT LEAST ONE of its ends in a sharp floor(n/2)-path
partition? Prescribing WHICH end was already refuted; see the five-vertex
example in the tail-return entry. The new unoriented assertion passes exact
checks of all 138 one-even connected atlas graphs through seven vertices:
1024 eligible edges, or 208 when both ends are nonneighbors of the unique
even vertex. /tmp/one_even_unoriented_edge.py, .log, .exit=0.
These finite checks are not a proof or a Lean assumption. Such a theorem
would imply a sharp floor(n/2) bound for graphs with three even vertices
whenever some pair of them is nonadjacent, by adding that edge and then
trimming a terminal occurrence. The existing all-odd force_first_edge proof
cannot simply be reused: its PROTECTED repair can be blocked by the zero
vertex as well as by the protected receiver, despite there being only one
zero vertex. No unproved extension is assumed.

### One-even unoriented edge exposure: complete order-nine diagnostic

/tmp/one_even_unoriented_nine.py generated ALL 12,346 unlabeled graphs H on
eight vertices with nauty-geng. For each, it added vertex 8 adjacent exactly
to the EVEN-degree vertices of H. Every original vertex then has odd degree;
vertex 8 has even degree by handshaking. Conversely, deleting the unique even
vertex from any pointed one-even graph on nine vertices yields precisely
this construction, up to isomorphism. Disconnected outputs were discarded.
All 11,936 connected outputs passed, covering 167,991 odd-odd edges, in 51.31
seconds using four workers. /tmp/one_even_unoriented_nine.log, .exit=0.
No process remains running. This is exact finite evidence, NOT a proof of
the unrestricted auxiliary assertion, and no Lean lemma assumes it.

The possible implication for three even vertices must be stated carefully:
adding a missing edge a-b leaves a third even vertex c. A sharp one-even
partition exposing a-b at either end would, on trimming, keep c inactive and
make ONE of a,b inactive. It does not prescribe which pair is inactive.
The earlier six-vertex prescribed-pair obstruction remains relevant. For
example attaching a new leaf at vertex 0 in that obstruction gives a
seven-vertex graph with three independent even vertices {2,3,4}, still with
no normal partition making BOTH 2 and 3 inactive. This does not contradict
the unoriented exposure candidate: the other pair {2,4} or {3,4} may work.
This observation is informal and is not a new Lean theorem.

A further conditional consequence, not proved: graphs with four or five
even vertices and a nonadjacent even pair could be treated by adding that
pair, attaching leaves to all but one remaining even vertex, applying the
one-even exposure assertion, and trimming the new edge and leaves. The
vertex-count budget matches Gallai. This remains entirely dependent on the
unproved exposure assertion.

Final checkpoint of this continuation: ForbiddenSubtree (253 lines, six
lemmas) and OneForbiddenRoot (five lemmas) both compile and pass all-axiom
audits. Original Spec is unchanged, 24 lines, theorem at line 17 and sorry
at line 22. No complete proof or disproof, no original theorem audit, and
no new proof submission. The main quota-one and arbitrary-even-graph gaps
remain unresolved.

## Sharp one-even bridge exposure (external, verified)

Submission/OneEvenBridgeExposure.lean imports Work, namespace
Erdos583OneEvenBridgeExposureDevelopment. Four lemmas:
 induced_neighbor_card_of_subset
 expose_cut_away_from_even
 one_even_card_eq_of_bound
 one_even_bridge_exposure

Every bridge in a graph with exactly one even-degree vertex c can be terminal
at one end in a SHARP path partition: 2*D.card+1=card V. Connectivity is not
required. The cut-side version prescribes terminality at the bridge end on
the side NOT containing c. Both odd-odd bridges and bridges incident to c
are covered. No arbitrary orientation is claimed.

Proof: orient the cut u in S, v outside S, c in S. The augmented left side
S union {v} is a one-even graph with unique even c and v a leaf. The right
side S-complement is a one-even graph with unique even v. Apply the existing
sharp one-even partition theorem on both sides and take their edge-disjoint
union; the sides overlap only at v. Their vertex counts sum to n+1, so their
path counts sum to (n-1)/2. The left leaf supplies a literal path beginning
v-u, tracked through the inclusion map into the union. The parity lower
bound proves the resulting upper bound is exact.

Build /tmp/one_even_bridge_exposure3.log exit 0, warning-free.
Audit /tmp/one_even_bridge_exposure_audit1.log exit 0, FOUR reports parsed and
matched, only propext, Classical.choice, Quot.sound. The temporary API probe
OneEvenExposureCheck.lean has unknown-identifier errors and is not a proof;
the actual module and its audit compile cleanly.

LIMIT: a missing edge added to a CONNECTED graph is a nonbridge, so this
bridge theorem does NOT complete the proposed three/four/five-even-vertex
nonedge reduction. The nonbridge exposure case is still missing. The direct
force_first_edge extension fails to justify its protected repair: the
protected receiver's start and the single inactive vertex can be the only
two possible exits. No unconstrained improvement is silently substituted
for the required protected exchange.

## Related unique-zero avoidance diagnostic (finite evidence only)

New auxiliary question, NOT PROVED: in a one-even graph with unique even c,
for every odd a NOT ADJACENT to c, can a sharp partition be chosen so the
path ending at a avoids c altogether? This is narrower than the previously
refuted arbitrary-nonneighbor avoidance claim (whose forbidden vertex was
not necessarily the unique even vertex).

/tmp/one_even_zero_avoid.py and /tmp/one_even_zero_avoid_nine.py checked the
same complete 8-core construction used for the order-nine exposure test.
All 11,936 connected one-even outputs passed, covering 46,638 eligible
vertices a, in 44.02 seconds. /tmp/one_even_zero_avoid_nine.log, .exit=0.
These exact finite checks are not a proof or a Lean assumption. No process
remains running.

If this avoidance assertion were proved, it would yield prescribed exposure
for an edge incident to the unique even vertex: delete that edge, which
moves the unique even vertex to its other end; choose the endpoint-owning
path at the old even vertex avoiding the new even vertex; append the edge.
The reverse implication also follows by adding a missing edge between a and
c, exposing it at the necessarily odd end, and trimming it. Neither direction
has been formalized and neither assertion has been established universally.

The attempted further reduction of general unoriented exposure by deleting
and restoring a shortest path from c to the marked edge is NOT justified.
Preserving a terminal marked edge through all intermediate repairs would
need an additional theorem, particularly when a restoration root is adjacent
to BOTH ends of the marked edge. No such invariant has been proved.

A fresh external-access check failed even with direct IP resolution: arxiv
at 151.101.3.42 and DNS-over-HTTPS at 1.1.1.1 both timed out. No external
mathematical result was retrieved or used.

Checkpoint: Spec is still the unchanged 24-line conjecture, with its original
sorry at line 22. The new bridge theorem is auxiliary; erdos_583 is not proved
or disproved. No completed original-conjecture submission was made.

## Nonneighbor-protected shortening and degree-two exposure (verified)

New external modules, NOT integrated into Work or Spec:

* NonneighborShortening.lean (namespace Erdos583NonneighborShorteningDevelopment):
  member_of_path_subgraph, member_orient_tracked, shorten_oriented_preserving,
  shorten_member_preserving, extend_suffix_preserving.
  Prefix shortening in a maximum-score all-odd normal trail system preserves
  a specified whole indexed member when all discarded prefix vertices avoid
  its CLOSED neighborhood. The surviving suffix may extend at its far end.
  No nonadjacent-donor-endpoint hypothesis is imposed. The proof uses the
  tracked single escape receiver; if that receiver is the donor, the suffix
  gains one edge at the far end, rather than asserting exact preservation.
  Build /tmp/nonneighbor_shortening4.log exit 0, warning-free.
  Audit /tmp/nonneighbor_shortening_audit2.log exit 0, all five reports checked,
  only propext, Classical.choice, Quot.sound, warning-free.

* DegreeTwoExposure.lean (namespace Erdos583DegreeTwoExposureDevelopment):
  avoids_leaf_of_disjoint, force_split_preserving_leaf,
  force_first_preserving_leaf, projected_member_mem,
  one_even_degree_two_exposure.
  If c is the unique even vertex and Nat.card(G.neighborSet c)=2, either
  incident edge u-c can be prescribed starting at u in a sharp partition:
     GoodDecomposition G D, 2*D.card+1=Fintype.card V,
     (u-c followed by a simple suffix) is a member of D.
  Connectivity is NOT required. This includes incident nonbridges.
  The generic all-odd helper protects a singleton c-d with d a leaf and
  c having at most two other neighbors u,w. A simple path through u-c must
  next visit w; its prefix contains none of u,c,w,d, so every discarded
  root avoids the singleton's closed neighborhood. Projecting the all-odd
  leaf completion loses the singleton and retains the prescribed first edge.
  The parity lower bound proves exact cardinality.
  Build /tmp/degree_two_exposure5.log exit 0, warning-free.
  Audit /tmp/degree_two_exposure_audit1.log exit 0, all five reports checked,
  only propext, Classical.choice, Quot.sound, warning-free.

These are auxiliary theorems. The unique-even exposure claim without the
DEGREE-TWO hypothesis remains open here. The full erdos_583 remains unchanged
and unresolved in the 24-line Spec.lean; its sole sorry is still at line 22.
No completed-conjecture submission has been made in this continuation.

## Structured many-carrier absorption diagnostics (not proofs)

An unproved possible bridge back to the cycle route was considered:
if a simple cycle C of length L and t edge-disjoint simple paths partition a
connected graph, EVERY one of the t paths meets C, and L <= 2*t+2, can their
union always be partitioned into t+1 paths? No proof or counterexample was
obtained. This is substantially stronger than Gallai on graphs with many
vertices outside C; do NOT use it as a theorem. The older short-cycle
obstruction has a path avoiding C and does not directly refute this version.
Nor does this proposed WHOLE-cycle statement handle an open lollipop.

Exact auxiliary diagnostics, none involving the original conjecture:

1. /tmp/cycle_parallel_carriers.py models t repeated Hamiltonian core paths,
   each with private leaf ends and all its core edges privately subdivided.
   The core is a cycle on q vertices, and t=floor((q-1)/2). Degree saturation
   forces every path in a prospective (t+1)-cover to visit all core vertices.
   After choosing the sole extra endpoint pair on a subdivided edge, the
   script checks an exact Hamiltonian-path multicover of the core.
   q=8, t=3: all 2,880 tested orders pass (/tmp/cycle_parallel_carriers8all.log).
   q=9, t=4: all 20,160 tested orders pass (/tmp/cycle_parallel_carriers9all.log).
   q=10, t=4: the 962 cases whose prescribed-end core Hamiltonian path is
   unique pass, out of 201,600 scanned orders
   (/tmp/cycle_parallel_carriers10unique.log).
   Separate unique-path runs at q=8 (69 cases), q=9 (246 cases), and q=8,t=1
   (69 cases) passed. These are only the stated restricted constructions.

2. /tmp/cycle_many_carriers.py permits different full or almost-full core
   paths with private leaf ends. Only duplicate core edges need subdivision.
   It exactly searches the sole extra endpoint pair, either on a subdivided
   edge or at an eligible core vertex. The two special endpoint ports must
   occur in DIFFERENT paths; allowing them on one path would wrongly accept
   a closed route. Remaining core paths, including zero-edge core pieces
   between distinct private leaves, are enumerated explicitly.
   1,000 seeded structural instances each passed for q=8,t=3 and q=9,t=4:
   /tmp/cycle_many_carriers8.log and /tmp/cycle_many_carriers9b.log (.exit=0).
   The first q=9 run was deliberately stopped and replaced by a version
   adding the valid remaining-degree capacity pruning condition.

3. /tmp/cycle_locked_carriers.py starts from the known order-eleven
   almost-spanning obstruction C=(0,...,10,0), P=(3,5,2,4,1,8,10,7,9,6).
   Add four copies of a Hamiltonian core path Q whose two end edges belong
   to P rather than C, with private leaf ends and duplicate-edge subdivisions.
   All 40 such Q passed the exact six-path test, so this particular attempt
   to retain the old obstruction after adding carriers did not work.
   /tmp/cycle_locked_carriers.log, .exit=0.

All of these processes have finished. They supply no Lean assumption and no
universal absorption result. The only new verified Lean modules in this
continuation remain NonneighborShortening and DegreeTwoExposure, audited
above. Spec.lean is still the unchanged unresolved conjecture.

## Latest carrier diagnostics (finite evidence only)

/tmp/shared_tail_cycle_absorb.py tests C5 with two Hamiltonian core carriers
and an outside vertex shared by their tails. The port-aware search forbids
joining the two ports whose outside arms intersect, as well as joining the
two free endpoint ports. All 120 core orders passed; see
/tmp/shared_tail_cycle_absorb.log. This is not a general absorption proof.

/tmp/bad_carrier_packing.py classifies individually unabsorbable C8 carriers
in a restricted private-tail model: 298 representatives gave 1,968 labeled
unoriented bad paths, 1,960 with seven direct noncycle edges and eight with
four. It then tests triples whose direct chord sets are pairwise disjoint.
All 2,000 tested triples passed, after 50,292 construction attempts;
/tmp/bad_carrier_packing.log, /tmp/bad_carrier_packing.exit = 0.
No diagnostic process from these tests remains running. None of these
finite computations supplies a Lean assumption or a proof of erdos_583.

## Single nonedge endpoint separation (verified externally)

EndpointUnpairing.lean proves separate_nonadjacent_endpoints. In an all-odd
normal path system, any specified DISTINCT NONADJACENT vertices can be made
to have different endpoint-owner indices, at unchanged score and path count.
It is a direct corollary of the previously proved exact nonadjacent-end
shortening: orient their common member, discard its first edge, retain its
nonempty suffix exactly, and use endpoint parity to retain the far endpoint
at that index while the discarded endpoint is absent. Equal maximum score
ensures that all members remain paths. No connectivity assumption is needed.
Build /tmp/endpoint_unpairing3.log exit 0, warning-free. One-declaration audit
/tmp/endpoint_unpairing_audit3.log exit 0, only propext, Classical.choice,
Quot.sound. The module is external, not inlined into Work or Spec.

A stronger simultaneous assertion for a MATCHING of forbidden nonedge
endpoint pairs is NOT PROVED. /tmp/nonedge_matching_unpair.py exactly checked
61,501 nonempty complement-matchings over the 224 connected all-odd graphs
of order eight and 19 triangle-free all-odd minimum-degree-three graphs of
order ten. All passed; /tmp/nonedge_matching_unpair.log, .exit=0. This finite
evidence does NOT establish simultaneous separation: repeating the one-pair
lemma can destroy prior separations. No process from this test remains live.
Spec still has the unchanged original conjecture and its one sorry. Neither
the global cycle absorption nor inactive-set augmentation gap is closed.

## Shared-outside-vertex cycle diagnostic (finite evidence only)

/tmp/shared_outside_dense_cycle.py checks a minimal shared-outside construction:
five cycle vertices induce K5; four outside vertices have base degree three,
with one outside edge and attachment degrees (2,2,3,3); each outside vertex
has a private leaf. Deleting the C5 must give two Hamilton paths on the
nine-vertex base, with the four outside vertices as endpoints. A prospective
three-path cover must put its sole extra endpoint pair at one outside vertex:
core vertices have degree six and hence must be internal in all three paths.
After leaf removal, the cover consists of three paths from the chosen outside
vertex to the other three, each containing all five core vertices.

There are fifteen classes under the stated cycle and outside symmetries.
All fifteen satisfy the two-carrier premise and pass the exact three-path
search. /tmp/shared_outside_dense_cycle.log, .exit=0. This checks genuinely
shared outside vertices, unlike the private-tail diagnostics, but is still
only this finite subclass. No universal absorption assertion follows, and
no new Lean hypothesis was introduced. No process remains running.

## Bounded-cycle many-carrier absorption (verified externally)

ShortCycleCarrierAbsorption.lean (namespace
Erdos583ShortCycleCarrierAbsorptionDevelopment) packages five corollaries of
the existing local cycle arguments:
  carrier_hit
  short_cycle_carrier_bound
  absorb_short_cycle_dense_carriers
  score_of_cycle_and_paths
  cycle_and_paths_absorption_le_seven

In ANY finite graph, a single-defect globally maximum-score family with a
whole cycle C of length <=7 satisfies
  2 * (number of other nonempty members touching C) + 3 <= C.length.
For lengths 3/4 no carrier is possible (intersection would have >=5 vertices).
For lengths 5/6 existing carrier uniqueness gives at most one. For length 7
existing HeptagonCarriers gives at most two. No smallest-counterexample,
connectivity, ambient Gallai budget, or outside-intersection restriction is
needed for this local bound.

Consequently, a cycle C of length <=7 and other SIMPLE PATH members covering
G admit a path partition with at most the original total number k of slots
whenever C.length <= 2*carrierCount+2 (here carrierCount excludes C itself).
The proof derives the exact one-defect score from the cycle-plus-path data.
If a k-path partition did not exist, that score would already be globally
maximum, contradicting the carrier bound. Arbitrary outside intersections
are permitted.

Build /tmp/short_cycle_carrier_absorption3.log exit 0, warning-free. Audit
/tmp/short_cycle_carrier_absorption_audit1.log exit 0, warning-free; all FIVE
reports parsed, declaration names matched, permitted axioms only. External
module only; not inlined into Work or Spec.

This establishes the proposed many-carrier absorption assertion THROUGH
LENGTH SEVEN, not for arbitrary cycles. In particular the preceding shared
outside C5 diagnostic was already covered mathematically by these existing
local ingredients. The first unhandled cycle length remains eight; open
lollipops also still need the unrestricted augmentation argument. No complete
proof or disproof of erdos_583 has been obtained. Spec remains the original
24-line file, sole sorry at line 22. No incomplete proof was submitted.

## Overlapping virtual C8 edges (finite diagnostic only)

/tmp/cube_overlap_pair_check.py tests all eight eligible pairs of the eight
exceptional C8 cube-type carriers in the cached restricted classification.
Their direct chord sets are disjoint, but they share privately subdivided
routes between a pair of consecutive cycle vertices. All eight pairs admit
the exact three-path cover in the private-tail model; log
/tmp/cube_overlap_pair_check.log and exit file report success. This does NOT
prove that overlapping virtual core pairs always allow an exchange, and does
not treat arbitrary shared outside routing. No process remains running.

Caution: older cycle_parallel_carriers.py used unlabeled endpoint counts and
did not explicitly require the two special cut-subdivision ports to lie in
different paths. Its positive diagnostics should not be relied on without
repair/recheck. The later cycle_many_carriers.py enforces that condition.

## C8 two-carrier shortcut diagnostic (finite, private-route model only)

/tmp/cube_pair_repair_check.py fixes the cached cube-type carrier
(0,3,4,7,6,1,2,5) and checks all 412 cached individually obstructed carriers
with disjoint direct chord sets. Every pair admits a three-path cover in the
private-route model. Thus this restricted test produces no triple requiring
a simultaneous three-carrier repair: each eligible partner already repairs
with the fixed cube. Log /tmp/cube_pair_repair_check.log, exit 0, no process
running. This is not a general two-carrier exchange lemma, not an unrestricted
C8 absorption proof, and not a result about arbitrary shared outside routes.

## Unbounded core-edge counting (verified externally)

CarrierCoreCounting.lean imports Work and proves five general lemmas under
namespace Erdos583CarrierCoreCountingDevelopment:
  core_load_bound
  full_core_load_carrier_bound
  spanning_core_segment_load
  spanning_core_segments_carrier_bound
  dense_carriers_have_core_gap

For a whole cycle C in ANY finite trail family and ANY index set F excluding
its index, the sum of all F-members' edge counts restricted to C's vertex set,
plus C.length, is at most choose(C.length,2). Therefore, if each such member
contributes at least C.length-1 core edges (in particular, if it contains a
simple path spanning precisely C's vertices), then
  2*F.card+3 <= C.length.
No global maximum-score, connectivity, or small-order hypothesis is needed.
Under the dense-carrier hypothesis C.length <= 2*carrierCount+2, some carrier
must have fewer than C.length-1 core edges. Counting alone does NOT repair this
carrier, nor prove the missing/excursion case impossible. This is an unbounded
counting statement with explicit segment hypotheses, NOT general absorption.

Build /tmp/carrier_core_counting2.log exit 0, warning-free. Audit
/tmp/carrier_core_counting_audit1.log exit 0, all five reports parsed and matched,
only propext, Classical.choice, Quot.sound. Module not inlined into Work/Spec.
Spec still has its unchanged conjecture and one sorry; no completed original
proof or disproof has been obtained or submitted.

## A deficient carrier plus a contiguous carrier need not repair (structural)

The proposed UNBOUNDED two-carrier shortcut is false, even with just one
outside excursion and both carriers visiting every cycle vertex. This is not
a counterexample to the dense-carrier assertion or to Gallai.

On each seven-vertex block use K7 minus the three star edges 01,02,03. Its
edges partition into paths from 0 to 1,2,3 respectively:
  R1=(0,4,2,3,5,6,1)
  R2=(0,5,1,4,3,6,2)
  R3=(0,6,4,5,2,1,3).
Take a second copy shifted by seven and add cross edges 0-7,2-9,3-10.
Add vertex 14 joined to 1 and 8, two leaves 15,17 at 0, and leaves 16,18 at 7.
The resulting graph has a 14-cycle using R2, reversed shifted R2, and edges
2-9,7-0. One carrier is 15,R1,14,reversed shifted R1,16 and the other is
17,R3,reversed shifted R3,18. These disjointly cover all 45 edges. The former
has precisely one outside excursion 1-14-8; the latter is contiguous in the
cycle core. /tmp/locked_excursion_construction.py checks the edge sets,
path/cycle distinctness, all degrees, and the three-edge cut exactly; log
/tmp/locked_excursion_construction.log. This is not yet Lean-formalized.

Why three paths are impossible: each of the fourteen core vertices has degree
six, hence is internal in all three putative paths. The four leaves account
for four endpoints. Vertex 14 (degree two) must supply the other endpoint pair,
on DIFFERENT paths. Trim the leaves and 14. The three resulting core paths
are Hamilton paths, and each crosses the seven/seven cut exactly once because
there are exactly three cut edges. The path using 0-7 cannot end at 0 or 7:
it would then omit the other vertices on that side. Its endpoints must
therefore be 1 and 8, but those came from the two cut ports at vertex 14,
which must belong to different paths. Contradiction.

Here L=14 and t=2, so L <= 2*t+2 is emphatically NOT satisfied. Gallai allows
ten paths on this 19-vertex graph. No universal or dense absorption conclusion
has been inferred from this obstruction.

## Prescribed complete-core pairing and saturated-core splicing (verified)

Three new external modules, NOT inlined into Work or Spec:

CompletePrescribedPairs.lean: five lemmas. A sharp all-odd trail family has
bijective endpoint labels, even if its members are not paths. Complete even
graphs admit path partitions with ANY specified perfect matching of endpoint
labels: take an all-odd normal path system and relabel the complete graph by
the permutation from its endpoint bijection to the prescribed one. This is
transported to any complete induced core. After deleting a cycle from a
complete even core, a sharp trail partition automatically has distinct ports.
Build /tmp/complete_prescribed_pairs6.log exit 0, warning-free.

CompleteCoreSplicing.lean: two lemmas. splice_clique_pairs joins paired exterior
arms through the prescribed-pair partition of a complete core. The arms are
paths, meet the core only at their assigned ports, are globally EDGE-disjoint,
and the two arms in each prescribed pair have disjoint VERTEX supports.
Different pairs may intersect arbitrarily outside. clique_cycle_remainder_splice
gets the port bijection from a sharp trail partition of the cycle-deleted
complete core, and returns a GoodDecomposition at the same k-piece budget.
Build /tmp/complete_core_splicing3.log exit 0, warning-free.
Joint audit /tmp/complete_core_splicing_audit1.log exit 0; all SEVEN reports
parsed/matched and only permitted axioms.

SaturatedCycleCore.lean: four lemmas. A core with maximum possible edge count
is complete. For a spanning cycle C on 2*k core vertices and k disjoint simple
core pieces partitioning the other core edges, the incidence equality
  sum (number of vertices in each core piece) = (k-1)*(2*k)
forces this maximum edge count and hence a complete core with bijective ports.
saturated_cycle_core_splice then supplies a k-path partition of the ambient
graph when its exterior arms satisfy the explicitly stated pairing/coverage
conditions. No bound on cycle length is imposed. This incidence pattern is
what arises from k-1 spanning carriers when one is split across a single
outside excursion, but a top-level theorem extracting these pieces from a
bare numeric core-gap hypothesis HAS NOT BEEN PROVED.
Build /tmp/saturated_cycle_core3.log exit 0, warning-free. Audit
/tmp/saturated_cycle_core_audit1.log exit 0; all FOUR reports parsed/matched,
only propext, Classical.choice, Quot.sound.

These are unbounded but CONDITIONAL local repair results. No argument yet
reduces arbitrary multiple-excursion carriers, missing core vertices, or open
lollipops to their hypotheses. Spec still has its original sole sorry, and
no completed proof or disproof of erdos_583 has been obtained or submitted.

## One-full-core-gap absorption (verified externally)

The numeric saturation result is now connected all the way to a genuine
path decomposition. No exterior-arm data is assumed at the top level.

New/extended modules, all external to Work and Spec:
* PathCoreIntervals.lean: coreVerts/coreEdges, exact cons counts, core edge
  bound, contiguous_of_core_count, one_gap_split (14 declarations).
* OneGapArithmetic.lean: one_gap_arithmetic, sum_one_unique (2 declarations).
* CycleOneCoreGap.lean: inside-edge partition/count, clique saturation,
  high_degree_on_every_path, spanning_of_complete_core (5 declarations).
* CoreIntervalSplicing.lean: induce_edge_iff, clique_cycle_ports,
  explicit_core_interval_splice, contiguous_clique_cycle_absorption (4).
* SplitPathFamily.lean: split_path_family (1).
* OneCoreGapAbsorption.lean: one_core_gap_absorption (1).

Top-level theorem: if a cycle C and t disjoint simple path carriers cover G,
every carrier meets C, C.length <= 2*t+2, and
  sum_i (C.length-1-coreEdges(P_i,C).ncard) <= 1,
then G has a partition into at most t+1 simple paths. No bound on cycle
length and no restriction on intersections between different paths outside
the core. The proof forces C.length=2*t+2, a complete induced core, and every
carrier spanning that core. Exactly one carrier has one outside excursion;
split it there. The resulting t+1 paths each meet the core in one interval.
Inducing those intervals gives a sharp trail partition of K_(2t+2) minus C;
odd degree forces a bijection of endpoint ports. Repartition the complete
core with the same endpoint pairs, then splice the original exterior arms.
Their within-pair vertex disjointness follows from original path simplicity
and the distinct core ports (not assumed in advance).

Build logs (all exit 0, warning-free):
/tmp/one_gap_arithmetic3.log
/tmp/cycle_one_core_gap5.log
/tmp/core_interval_splicing4.log
/tmp/split_path_family4.log
/tmp/one_core_gap_absorption2.log
The previously built PathCoreIntervals module remains warning-free.
Audit: Submission/OneCoreGapAudit.lean, /tmp/one_core_gap_audit2.log.
All 27 reports parsed and names/counts matched; permitted axioms only.

This is an UNBOUNDED SPECIAL CASE, not the unrestricted absorption theorem.
The global minimal-failure reductions do not bound the aggregate deficit by
one. Multiple gaps, carriers missing core vertices, and open lollipops remain
unresolved. Spec still has the unchanged original conjecture and its sole
sorry; no complete proof or disproof has been obtained or submitted.

## Prescribed first edges and near-complete collision ports (verified externally)

CompleteEdgeExposure.lean imports CompletePrescribedPairs, namespace
Erdos583CompleteEdgeExposureDevelopment. Three lemmas:
  complete_path_lengths
  path_second_ne_finish
  complete_prescribed_first_edge
Every k-path partition of K_(2k) is Hamilton. Given any prescribed perfect
matching of endpoint labels, any selected path may also have its first edge
prescribed to lead to ANY endpoint of a DIFFERENT pair. Proof: start with an
arbitrary prescribed-pair partition, locate its first neighbor's endpoint
owner, and relabel whole endpoint pairs (with a possible orientation flip).
The source pair is fixed; reindex and reorient the mapped paths afterward.
No arbitrary-graph edge-exposure assertion is made.
Build /tmp/complete_edge_exposure3.log exit 0, warning-free. Three-declaration
parsed/matched audit /tmp/complete_edge_exposure_audit1.log, permitted axioms.

FirstEdgeFamilyDeletion.lean imports Work, namespace
Erdos583FirstEdgeFamilyDeletionDevelopment. Two lemmas:
  tail_edgeSet
  delete_first_edge_family
Deleting the first edge of a specified member of ANY indexed simple path
partition preserves its slot count and moves just that initial endpoint.
Build /tmp/first_edge_family_deletion3.log exit 0, warning-free.

NearCompletePairs.lean imports these two modules, namespace
Erdos583NearCompletePairsDevelopment. Two lemmas:
  complete_minus_edge_prescribed_pairs
  near_complete_prescribed_pairs
K_(2k) minus edge u-v has a k-path partition with any prescribed endpoint
pairing having u omitted, v duplicated, all other vertices once, PROVIDED
the duplicated v labels belong to DIFFERENT pairs. The formal collision-port
version assumes that replacing a specified initial v label by u makes the
endpoint map bijective, and its paired finish is not v. This is proved by
prescribing the deleted first edge in K_(2k), then deleting it.
Build /tmp/near_complete_pairs3.log exit 0, warning-free. The four declarations
from the last two modules audited together in NearCompletePairsAudit.lean:
/tmp/near_complete_pairs_audit1.log exit 0, all four reports parsed/matched,
permitted axioms only. All modules remain external to Work and Spec.

Possible next special-case extension, NOT DONE: aggregate core deficit two
usually forces K_(2t+2) minus one edge. If exactly one core-vertex incidence
is missing and one outside excursion occurs, splitting the excursion gives
k=t+1 contiguous pieces with collision ports of the above form. A singleton
core interval at the duplicated vertex can create a FORBIDDEN v-v pair; it
must be repaired by exchanging the two arm pairings from the same original
split path. The cross-pairing that joins both arms incident to the outside
split vertex is invalid (repeats that vertex); the other cross-pairing is
compatible. None of this extraction/splicing has yet been formalized.
The two-excursion/no-missing-vertex case is an additional gap. More broadly,
no reduction to any bounded core deficit is known, and the original
conjecture remains unresolved with its sole sorry in Spec.

## Two-gap saturation classification (verified externally)

TwoGapSaturation.lean imports CycleOneCoreGap. Three audited lemmas:
  two_gap_arithmetic
  missing_one_edge
  two_core_gaps_force_almost_clique
For C.length >=4, C plus t simple carriers covering G, and the same dense
bound C.length <=2*t+2, aggregate full-core deficit <=2 forces length exactly
2*t+2 and an induced core either complete or complete minus one edge.
The exact arithmetic identity is
  C.length + sum(coreEdges) + (totalDeficit-1) = choose(C.length,2).
The length-three exception is intentionally excluded; short-cycle absorption
already handles it. This is saturation ONLY, not deficit-two absorption.
Build /tmp/two_gap_saturation2.log and three-declaration parsed/matched audit
/tmp/two_gap_saturation_audit1.log both exit 0, warning-free, permitted axioms.

Important strategic limitation: the optimized anchor bound in an ODD-order
smallest failure is C.length <=2*t+1. Thus neither the one-gap theorem nor
this constant-two-gap classification reaches that odd-order extremal branch
(for cycles >=4); arithmetic already forces more deficits there. In the
boundary complete odd core C.length=2*t+1, the total full-core deficit is
exactly t+1, unbounded with t. A useful broadening may require handling this
complete ODD core rather than only the next even near-clique case.

Unproved structural observation for such an odd complete core: after removing
C, its core degree at each vertex is 2*t-2. The t original simple carriers
therefore visit each core vertex either t or t-1 times, and the collection of
maximal core intervals has endpoint quota respectively two or zero at that
vertex. This gives paired collision ports at many vertices, not a bijective
port map. There is no proven reconstruction for these multiple collisions,
and arbitrary intersections between different exterior routes remain a
separate obstacle. No assertion about their compatibility has been added.

## Structured parallel-lock check (diagnostic only)

A possible way to extend the 14-core two-carrier obstruction to the dense
regime was considered: add privately subdivided parallel copies of its Q
carrier. This creates new degree-two vertices INSIDE either seven-core half,
so the extra endpoint pair can move away from the original cross subdivision.
Those new cuts invalidate the old forced-opposite-port argument.

/tmp/parallel_lock_local_check.py checks the local seven-vertex trade: union
of R3 with R1 or R2, delete a selected subdivided R3 edge not incident to 0,
and partition the eleven remaining edges into a Hamilton path and a path
on the six vertices other than 0, with the two cut ports in different paths.
The exact enumeration finds repairs for all five cuts using R2, and four of
five using R1. Log /tmp/parallel_lock_local_check.log. This is NOT a proof of
general absorption or a global reconstructed partition, but the proposed
parallel-copy obstruction does not survive this local test. No process is
running and no Lean theorem relies on this computation.

Further caution: a proposed bound saying a p-path graph on >2p vertices has
at least 2p markable vertices is FALSE, already contradicted by K7 minus the
triangle on {4,5,6}. Its optimal three paths are Hamilton; vertices 0..3 have
degree six and can never be endpoints in three paths, so only {4,5,6} are
markable. Outside optimal groups may therefore contain many unmarkable
vertices despite a support surplus of only one. This rules out a naive
outside-excursion counting extension of the anchor argument.

All new Lean modules in this continuation are compiled and audited. Spec
remains the unchanged 24-line original statement with one sorry. The general
conjecture is neither proved nor disproved; no completed original proof has
been submitted.

## Compact final-branch test (not a proof)

Submission/FinalBranchDiagnostic.lean imports the compiled StarCopyIntegrated
chain and reproduces the final minimal-counterexample branch without the
outer special-case splits. All existing reductions elaborate successfully.
The final omega call fails: /tmp/final_branch_diagnostic.log, exit 1.
In particular the graph-level critical core cycle is not a whole defective
member, and the latter hypothesis is still needed for whole-cycle exclusions.
Independent optimized family witnesses must not be identified. The diagnostic
is intentionally not a verified theorem and is not imported by Spec or Work.
This check found no immediate arithmetic closure. Spec is unchanged.

## Even-root energy minimization (verified externally)

EvenRootEnergy.lean supplies four audited lemmas. Unlike the unrestricted
root-energy minimum, its feasible set requires the root quota to remain even.
Starting from an even rooted single-defect global score maximum, this produces
a same-score global maximum whose root quota is exactly two. Pair transfer
into an exposed zero quota preserves evenness, so an even root of quota >=4
cannot minimize the square energy in this restricted class.

`even_even_edge_quota_two_root` instantiates the result at an even-even
nonbridge of an edge-critical failure, using the existing edge-restoration
root witness. It retains the restricted minimum and global score maximality.

Build /tmp/even_root_energy2.log is warning-free, exit 0. Four exact audit
reports in /tmp/even_root_energy_audit1.log were parsed and matched; only
propext, Classical.choice, Quot.sound. No Spec or Work integration.

This does NOT prove even-root-to-whole-cycle conversion. The old six-vertex
Eulerian example (two slots rather than its actual Gallai budget three) already
refutes the budget-free two-member conversion, even at global maximum score.
Any argument now needs the ambient vertex budget and potentially other members.
The original conjecture remains unresolved in Spec.

## Near-complete contiguous core absorption (verified externally)

Five modules now give an unbounded-length absorption theorem for a cycle C
and t edge-disjoint simple carrier paths covering G, with C.length=2*t+2,
G induced on C equal to K_(2*t+2) minus one edge uv, and each carrier having
a nonempty contiguous core intersection. Outside intersections between
DIFFERENT carriers are unrestricted. The conclusion is t+1 simple paths.

Modules and declarations:
  NearCompleteCorePorts: bijective_add_two_labels,
    cycle_remainder_ports_omit_two, splitStart, splitFinish,
    split_labels_bijective, near_complete_extended_pairs,
    near_complete_cycle_ports
  CorePairSplicing: splice_given_core_pairs, map_induced_partition
  SplitPortSets: split_port_sets_pairwise, split_port_sets_union
  NearCompleteCoreSplicing: splice_near_complete_fresh_pair
  NearCompleteContiguousAbsorption: explicit_near_complete_interval_splice,
    contiguous_near_complete_cycle_absorption

Sharp parity gives distinct old ports omitting u and v. Replace one old pair
(a_j,b_j) by (a_j,v),(v,b_j), using nil exterior arms at fresh v. The existing
near-complete prescribed-pair partition then supplies the core; freshness
ensures vertex compatibility with both old arms. This is an endpoint-pair
reconstruction, not a claim that the original carrier visits v.

All five modules compile warning-free. Joint audit
/tmp/near_complete_contiguous_audit2.log exits 0; all 14 reports (including
both defs) were parsed and exact declaration names/counts matched. Only
propext, Classical.choice, Quot.sound. Audit file:
Submission/NearCompleteContiguousAudit.lean. No Work/Spec integration.

This settles only the no-excursion branch of near-complete deficit two.
The one- and two-excursion branches remain. In particular, nothing reduces
the original conjecture to bounded deficit: the complete odd core boundary
already has unbounded deficit t+1. The original Spec theorem remains open.

## Near-complete one-excursion absorption (verified externally)

The entire one-excursion branch (including a singleton/nil core interval) is
now proved, with no cycle-length bound and no restriction on intersections
between different original carriers. Main theorem:
  NearCompleteOneExcursionAbsorption.near_complete_at_most_one_excursion_absorption
(namespace Erdos583NearCompleteOneExcursionAbsorptionDevelopment).
For C plus t simple paths partitioning G, C.length=2*t+2 and induced core
K_(2*t+2)-uv, aggregate INTRINSIC excursion count
  sum_i (coreVerts(p_i,S).ncard - 1 - coreEdges(p_i,S).ncard) <= 1
implies a good decomposition into at most t+1 simple paths.

Proof ingredients:
- Split the unique excursion outside the core. Vertex-incidence counts away
  from the splitting vertex are preserved exactly; sigma-valued metadata
  tracks both new pieces and the untouched carriers.
- Every ordinary core vertex is visited by every original carrier. In
  particular each unsplit carrier has at least two core vertices.
- Among the t+1 resulting intervals, every ordinary core vertex has quota
  exactly one. The two exceptional vertices have even quotas. Equal domain
  and codomain sizes force one omitted exceptional label and one duplicated
  exceptional label. Replacing one duplicate by the omission is bijective.
- If all pairs are nonnil, reconstruct the core with prescribed pairs.
- Any nil interval is unique and belongs to one of the two split pieces.
  Its other split piece is a valid crossing partner. With exterior arms
  oriented outer-to-core, exchange the nil pair's unselected slot with the
  opposite slot of that partner. The selected duplicate stays fixed. Paired
  arms are vertex-disjoint because they come from separated portions of the
  SAME original simple path. This is the valid crossing, not the invalid
  reconnection of both arms meeting the outside splitting vertex.
- Generic permutation-based splicing reconstructs the near-complete core
  while preserving edge coverage and simplicity.

Fifteen new modules (33 lemmas) compiled warning-free:
  CollisionEndpointLabels, CycleIntervalCapacity, CollisionCorePairs,
  NearCompleteIntervalPairs, NearCompleteCapacitySplicing,
  SplitPathFamilyCapacity, ReindexedCoreArms, OneCollisionCrossing,
  NearCompleteIntervalCollision, NearCompleteCrossingSplicing,
  CrossingArmSupport, NearCompleteCrossingAbsorption, SplitCorePartners,
  NearCompleteCarrierSupport, NearCompleteOneExcursionAbsorption.
The last build /tmp/near_complete_one_excursion_absorption2.log exits 0.
Joint audit /tmp/near_complete_one_excursion_audit1.log exits 0, warning-free;
all 33 exact names/counts matched by a parser supporting multiline axiom
lists AND the 'does not depend on any axioms' report. Only permitted axioms.
Audit file: Submission/NearCompleteOneExcursionAudit.lean.
No Work/Spec integration.

The near-complete two-excursion branch (no missing vertex incidences) remains
unproved. Completing it would still NOT settle Gallai: no reduction to
bounded full-core deficit is known, and the complete odd core boundary has
unbounded deficit. Spec remains unchanged with its original sole sorry.

### Weighted common-cycle slots and unrestricted cycle rotations

Twelve declarations in WeightedCycleEndpoints, DeleteMemberFamily, and
WholeCycleWeightedSlots have compiled and passed the joint exact-name axiom
audit (WholeCycleWeightedSlotsAudit.lean; /tmp/whole_cycle_weighted_slots_audit1.log).
The parser accepted both multiline lists and the no-axioms report; only permitted
axioms. For a whole cycle in a k-slot trail family and common cycle vertices S:
  2*k*|S| <= sum_{v in S} degree(v) + 2*(k-1).
The strict budget |V|+1<=2*k implies |S|+1<=k; if every cycle vertex is common,
cycle.length+1<=k. These bounds need no score maximality.

Six further declarations in GeneralPairEndpoints, CycleEndpointRotation, and
FreeRootCycleMinimum compiled warning-free and passed exact-name axiom audit
(FreeRootCycleMinimumAudit.lean; /tmp/free_root_cycle_minimum_audit2.log).
They minimize rooted cycle length over ALL roots and quota energies at a fixed
score, and prove a cycle-edge/path-edge rotation at a cycle endpoint. At a
score maximum the new root is on the old cycle, and the new rooted cycle is
strictly shorter. Hence other simple members' endpoints avoid a whole cycle
in an unrestricted minimum. No quota-energy optimality is asserted.

The first-core-visit extension (a path prefix outside the cycle retained as
new tail) is under development, not yet proved. Even if it excludes all whole
cycles in an unrestricted minimum, the open-lollipop case remains: an old
nonnil tail may obstruct the rotation. No Gallai reduction to bounded core
deficit or full repair exists. Original Spec is unchanged with its sole sorry.

### First-visit rotation: whole-cycle exclusion without a length bound

CycleFirstVisitRotation.lean and FreeRootWholeCycleExclusion.lean now compile
warning-free (last logs /tmp/cycle_first_visit_rotation2.log and
/tmp/free_root_whole_cycle_exclusion3.log). Five declarations jointly audited
with exact names/counts, only permitted axioms:
  /tmp/free_root_whole_cycle_exclusion_audit1.log.

For P=A(a,u)+R(u,w)+wv+B(v,b), with A meeting C=uv+Q only at u, exchange to
  X=reverse(R)+uv+B,
  Y=wv+Q+reverse(A).
Q+reverse(A) and X are paths. At score maximum w is on Q, or both new members
are paths and the score increases. Thus Y is a lollipop with cycle strictly
shorter than C. No quota constraints are retained or needed.
Consequently at an unrestricted shortest rooted-cycle minimum, no other simple
member can meet a whole-cycle member. Connectivity then excludes the whole
cycle as soon as there are at least two slots: its vertex set would be closed
under all graph edges, hence all vertices, contradicting another member's
start. Nil slots require no separate argument.

Main reduction:
  FreeRootWholeCycleExclusion.unrestricted_minimum_tail_not_nil
A connected one-defect score maximum with k>=2, unrestricted minimum cycle
length, has a NONNIL tail. This holds at arbitrary cycle length and uses no
smaller-order minimality. It does not show that an arbitrary whole-cycle
family cannot be score-maximum: the unrestricted minimum condition is essential.
The existing-tail obstruction remains, so this is not a proof of Gallai.
Spec is unchanged with its original sole sorry.

### Compatible open-defect certificate and retained-tail endpoint rotation

Three modules compiled warning-free:
  UnrestrictedDefectCertificate (3 lemmas),
  LollipopEndpointRotation (4 lemmas),
  RootEndpointTailCapacity (6 lemmas).
All 13 exact names/counts passed UnrestrictedTailAudit.lean, log
/tmp/unrestricted_tail_audit1.log, with only permitted axioms.
Last individual builds: /tmp/unrestricted_defect_certificate2.log,
/tmp/lollipop_endpoint_rotation2.log, /tmp/root_endpoint_tail_capacity2.log.

UnrestrictedDefectCertificate.failure_has_unrestricted_open_defect starts from
an arbitrary connected exact-budget failure and produces a spanning connected
failure with a one-defect score maximum, a globally shortest rooted cycle
(across ALL roots and quota energies), a nonnil tail, and compatible free-tail
minimality at the resulting fixed oriented cycle. The underlying existence
lemma also preserves fixed-anchor carrier-count maximization and carrier-length
minimization. Root quota-energy minimality is NOT asserted.

For C=rv+Q and old tail S, a normal path P=A(r,w)+wv+B admits the rotation
  Y=wv+Q+S, X=reverse(A)+rv+B.
The simple suffix Q+S is unchanged; X has exactly P's vertex set, and Y has
insert(w, old-lollipop-vertices). Score maximality puts w in the old lollipop.
Global cycle minimality excludes w on C, hence w lies strictly on the old tail.
A separate first-edge transfer ensures both cycle neighbors of r occur on
any simple member starting at r. Their predecessors in that path are distinct
(unique successors in a simple walk), so the old tail has length at least two.
This holds for an arbitrarily oriented simple representative of another member.

Consequences:
- A tail of length <=1 at this global minimum has no OTHER member endpoint at r.
- A tail of length exactly 1 has root quota exactly 1.
- An even-degree root cannot have a one-edge tail at this minimum.
These do not exclude longer tails. They do not supply evenness or small quota
for the root selected by unrestricted cycle minimization. The exact conjecture
is still unproved; Submission/Spec.lean remains unchanged with its sole sorry.

### Root quota charging and two-edge triangle endpoint exclusion

RootQuotaTailBound.lean compiled warning-free (second build) and all 3 exact
axiom reports passed /tmp/root_quota_tail_bound_audit1.log. At an unrestricted
minimum with nonnil tail:
  T.quota r <= L.tail.length+1.
Proof injects root endpoint slots into tail vertices: the defective slot maps
to r, and every other slot maps to its predecessor of a fixed cycle neighbor.
Two normal slots mapping to the same tail vertex would reuse an edge. All
member endpoints are distinct (nonnil tail and no nil slots), so equal member
indices also force equal slots. This inequality alone does not close the budget.

Four further modules compiled warning-free and all 16 exact declaration reports
passed /tmp/short_triangle_root_audit1.log (ShortTriangleRootAudit.lean):
  TriangleTailRootTemplates, TriangleTailRootLocked,
  TriangleTailPentagonTransfer, ShortTriangleRootExclusion.
Only permitted axioms; no proof gaps. Individual last builds end in 2.log.

New substantive conversion:
  ShortTriangleRootExclusion.triangle_two_tail_root_path_gives_pentagon
A one-defect score maximum, unrestricted shortest rooted cycle of length 3,
tail length 2, and another simple member with endpoint r can be replaced at
unchanged score by a family with a WHOLE PENTAGON member.

Proof: write the triangle r-x-y-r and tail r-s-t. The two cycle-neighbor
predecessors on the normal root-starting path must be the distinct vertices
s,t. An inner-first order always admits a two-path repair by splitting the
last edge of the root-to-s prefix. In the outer-first order, any root-to-t
prefix longer than one edge, or x-to-s middle segment longer than one edge,
also admits an explicit two-path repair. Nonabsorbability therefore forces
  P = r-t-x-s-y + D,
up to swapping x,y, with D exterior to the five-vertex core. The union of the
lollipop and this prefix is K5 minus ty. Repartition it as the whole pentagon
  r-x-y-s-t-r
and the path
  t-x-s-r-y + D.
All templates and their edge partitions were proved directly in Lean.

The already proved whole-pentagon exclusion applies in a smallest-order
counterexample, giving:
  failure_short_triangle_no_other_root_endpoint;
  failure_two_tail_triangle_root_quota_one.
Thus a two-edge tail at a globally shortest rooted triangle in such a failure
has root quota exactly 1 (hence odd root degree); no even-root hypothesis or
quota-energy compatibility was smuggled in. Longer tails and non-triangular
cycles remain unresolved. Spec is unchanged with its original sole sorry.

### Free-tail bridge and short-triangle component restrictions

ShortestTailBridges, ShortTriangleComponents, and ShortTriangleBounds compile
warning-free. Their 8 exact axiom reports passed ShortestTailStructureAudit.lean
(/tmp/shortest_tail_structure_audit1.log); only permitted axioms.
Last builds: /tmp/shortest_tail_bridges1.log,
/tmp/short_triangle_components2.log, /tmp/short_triangle_bounds2.log.

ShortestTailBridges.shortest_tail_no_internal_bridge is an UNBOUNDED-tail
statement: in a smallest-order counterexample, for a free shortest tail at
fixed cycle, any bridge edge of that tail must be its first edge. If a bridge
w-v occurs after a nonempty prefix, bridge parity makes w odd. The defective
member has no endpoint at w, so a normal path has endpoint w. Bridge separation
makes that path disjoint from the remaining tail except at w. Transfer the
entire tail suffix to the path, strictly shortening the defective tail without
changing its cycle or total score. No quota-energy premise is used.

For a triangle with a two-edge tail r-s-t, every normal component in a free
tail minimum contains r or s. A component missing both must meet t by
connectivity. It cannot meet the cycle: the existing short-triangle absorption
forces every normal member meeting the cycle to contain r. Thus t is its sole
intersection with the defective member, and the cut from this component is
the single edge t-s. That edge is a forbidden internal bridge. Components have
disjoint supports, so charging each to r or s gives at most TWO normal
components. This bound does not require a global cycle minimum or odd order.

Combined with unrestricted cycle minimization and the pentagon conversion:
- A triangular rooted defect with tail length <=2 has root quota 1 and odd
  ambient root degree at least 5 in a smallest-order failure.
- In particular an even-degree root with a triangular cycle has tail length
  at least 3.
The first result also uses the existing cubic short-triangle exclusion; the
root degree at least 3 follows from its nonnil lollipop member.

These constraints still leave non-triangular cycles, longer tails, and
high odd-degree short-triangle roots. No final contradiction or path
partition at the conjectured bound has been proved. Spec remains the same
24-line file, sole import FormalConjecturesUtil, original theorem and sorry.

### Any short triangle: incidence dominance and carrier degree

ShortTriangleIncidence.lean compiles warning-free. All seven exact declaration
reports in ShortTriangleIncidenceAudit.lean passed the axiom audit
(/tmp/short_triangle_incidence_audit1.log), using only permitted axioms.

A triangular cycle is automatically unrestricted-minimal by the universal
three-edge lower bound. The recent short-triangle restrictions therefore
apply to ANY triangular rooted defect, without another witness optimization.
For a one-defect maximum with a one- or two-edge tail, every member visiting
the triangle also visits its root. Rooted incidence then gives, for any
other triangle vertex v,
  deg(v) + quota(v) + 2 <= deg(r) + quota(r).
In a smallest-order failure the root quota is 1, so this becomes
  deg(v) + quota(v) + 1 <= deg(r).
Odd-order failures have minimum degree five; combined with the odd root
degree, their short-triangle roots have degree at least SEVEN.

The exact root degree identity is
  deg(r) = 2 * (number of triangle-touching members) + 1,
where the count includes the defective member. Thus degree five means one
ordinary carrier, and degree seven means two. No argument yet excludes
the degree-five even-order case or higher-degree roots. The full conjecture
is still unresolved; Spec retains its sole original sorry.

### Cubic-pair fresh shortcut at a degree-five short triangle

CubicTriangleReduction, ShortTriangleSingleCarrier, CubicTriangleCarrier
compile warning-free; 11 exact axiom reports in CubicTriangleAudit passed
(/tmp/cubic_triangle_audit1.log), only permitted axioms.

A degree-five short-triangle defect has a unique ordinary carrier. If both
other triangle vertices x,y are cubic, they are that carrier's two endpoints.
It can be oriented x-to-y and passes through root r internally. Its first/last
external neighbors a,b are distinct and both outside {r,x,y}. The interior
carrier supplies a-to-r reachability after deleting x,y, and cannot use edge ab.
If ab is absent, delete x,y and add ab. Expand ab to a-x-y-b and restore x-r-y
as one extra path. This deletes two supported vertices at cost at most one
path and proves, in a smallest-order failure, that ab must be present.

This is not the full degree-five exclusion: triangle vertices of degree four
remain, as does the existing-ab case. The following parity-controlled
restoration is being developed separately; it has not yet been axiom-audited
or applied to the original failure. Spec remains unchanged with its sorry.

### Cubic triangle pair: odd-attachment repair and even-even chord

CubicTriangleOddAttachment, CubicTrianglePuncture, CubicTriangleEvenChord
compile warning-free. Their 8 exact reports passed CubicTriangleParityAudit
(/tmp/cubic_triangle_parity_audit2.log); only permitted axioms.
Last builds: /tmp/cubic_triangle_odd_attachment2.log,
/tmp/cubic_triangle_puncture1.log, /tmp/cubic_triangle_even_chord1.log.
No Work or Spec integration.

General parity repair: triangle r-x-y-r, x and y cubic with external
neighbors a,b, all five vertices distinct, ab an edge, and a simple x-to-y
carrier passing through r while avoiding the triangle edges and ab. The
carrier's interior proves that deleting x,y AND ab leaves connected support.
If r and a are odd in G, both remain odd after this deletion (each loses
exactly two neighbors). Attach new leaf x at a and new leaf y at r, without
increasing path count. Then restore the single simple path r-x-y-b-a.
This recovers all six missing edges and costs at most one path after removing
two vertices. The two append operations are performed sequentially and do
not assume that the two endpoint paths are distinct.

Consequently, in a smallest-order failure, both a and b must have EVEN degree
when r is odd. The same interior carrier proves ab is a NONBRIDGE. In
particular, any degree-five root with triangle and tail length one or two,
whose other triangle vertices are both cubic, forces this even-even nonbridge.
This still is not a contradiction: general failures may have such edges,
and degree-four triangle vertices and all longer-tail cases remain.

A targeted exact diagnostic guards against a tempting false next step.
  P = 6-0-1-8-2-3-7,
  Q = 1-4-0-3-5-2,
  L = 8-6-7-8-9.
Here Q uses the edge 0-3 between the external neighbors of P's leaf endpoints
6,7 and avoids root8. P+Q cannot be repartitioned into two paths separating
6 and7. Thus fixed-two-member endpoint separation is NOT a valid repair.
Script/log: /tmp/cubic_pair_forced_pattern.py and .log. This is an external
exact diagnostic, not a Lean theorem or conjecture disproof.
Importantly, the FULL union DOES have a three-path partition:
  1-4-0-6-7-3-5-2-8-9, 6-8-1-0-3-2, 8-7.
So it does not refute a possible THREE-member repair in the cubic-pair/chord
branch. Such a general repair remains unproved. The ambient Gallai budget
is five, so none of these observations is an original-conjecture disproof.

All new builds and audits have finished. Spec is still the unchanged
24-line file, sole FormalConjecturesUtil import and original sole sorry.
No complete proof/disproof has been obtained or submitted.

### Cubic pair: two restoration templates and guarded diagnostics

TwoMemberExtension, CubicTriangleDistinctEndpoints, OneMemberReplacement,
and CubicTriangleSingleton compile warning-free. Five exact axiom reports
in /tmp/cubic_triangle_restoration_audit1.log were parsed and passed; only
permitted axioms. No Work or Spec integration.

Deleting the two cubic triangle vertices x,y can be reversed at cost at
most one path whenever the external neighbors a,b are endpoints of DISTINCT
reduced members: extend them by a-x-y and b-y, then add x-r-y. This needs
no parity hypothesis and does not require edge ab. If ab is a singleton
reduced member, replace it by r-x-a-b-y and r-y-x, again at cost at most one.
These are conditional restorations, not a proof of the general case.

A fixed-tail-arm three-member repair is FALSE. Exact diagnostic example:
  P = 0-1-2-3-4-5-6-7-8-9-10
  Q = 6-4-2-11-1-9-7
  L = 3-0-10-3-12.
Neither 0-3-12 nor 10-3-12 can be held fixed as a member of a three-path
partition. Nevertheless the full union HAS a three-path partition:
  0-1-11-2-4-5-6-7-8-9-10-3-12, 10-0-3-2-1-9-7, 3-4-6.
Another fixed-arm failure uses
  P = 0-1-2-3-4-5-6-7-8-9-10-11,
  Q = 6-4-2-7-1-10-8, L = 3-0-11-3-12.
Scripts/logs: /tmp/cubic_chord_fixed_arm_diagnostic.py,
/tmp/cubic_chord_fixed_arm_11_1.log and _12_0.log.
These are external exact diagnostics, not Lean theorems or Gallai disproofs.

General three-path local repair remains unproved and unrefuted. Completed
targeted finite diagnostic passes in /tmp/cubic_chord_three_diagnostic.py:
N=8 extra=1: 184; N=9 extra=2: 13,288; N=10 extra=1: 13,956.
The N=11 extra=1 and N=12 extra=0 runs timed out (at least 46,000 and
30,000 cases respectively): they were NOT completed passes. An 81-case
tail-variant diagnostic on the fixed-arm obstruction passed. Logs retain
the corresponding cubic_chord_three_* and cubic_chord_tail_variants names.
No universal theorem is inferred from these finite passes.

Spec still has its sole sorry. No complete proof/disproof has been obtained.

### Cubic pair excluded at an odd root: complementary parity repair

New warning-free builds: CubicTriangleEvenAttachment (4 lemmas) and
CubicTriangleExclusion (2 lemmas). Also LockedEndpointPair (5 general
lemmas) compiles warning-free. All 11 exact axiom reports in
/tmp/cubic_triangle_exclusion_audit1.log passed; only permitted axioms.
Build logs: /tmp/cubic_triangle_even_attachment2.log,
/tmp/cubic_triangle_exclusion1.log, /tmp/locked_endpoint_pair2.log.

The forced endpoint-pairing route was unnecessary for the odd-root cubic
pair! If an external neighbor a is EVEN in G, after deleting x,y it is
odd, while the odd root r stays odd. Append fresh leaf x at a and fresh
leaf y at r SEQUENTIALLY, then restore r-x-y-b as one extra simple path.
This costs at most one path and does not require the two endpoint owners
to be distinct. If they are the same a-to-r path, the two new leaves
extend its opposite ends and still give a simple path.

This combines with the earlier fresh-shortcut and odd-attachment repairs:
in a smallest-order failure, a cubic-to-cubic triangle carrier through an
ODD root had forced a,b even and ab present. The new complementary parity
repair contradicts this. Hence failure_no_odd_root_cubic_triangle_carrier
is proved. In particular, failure_no_degree_five_short_triangle_cubic_pair
excludes the degree-five short-triangle branch with both other triangle
vertices cubic. It does NOT exclude the remaining degree-four cycle
vertices or general longer cycles/tails.

The generic LockedEndpointPair lemmas are independent conditional facts:
forced pairing plus positive endpoint multiplicities yields a unique a-b
member, endpoint multiplicities exactly one, and (if ab cannot be singleton)
ab lies internally in another member. They are NOT needed for the new
cubic-pair exclusion and were not applied to an assumed failure.

No complete proof or disproof of Gallai; Spec still has its sole sorry.

### Degree-five short triangle: remaining degree-four vertex and fresh shortcuts

ShortTriangleDegreeFour compiles warning-free; its exact single axiom report
/tmp/short_triangle_degree_four_audit1.log passed. Combining incidence
bounds, the exclusion of adjacent degree-two/three vertices, and the new
cubic-pair exclusion shows that a degree-five short triangle in a smallest
failure has at least one nonroot vertex of degree FOUR and quota ZERO.
This is a restriction, not a contradiction.

New warning-free modules RestoreTriangle (1), SupportSmoothing (4),
DoubleSmoothTriangle (2), ShortTriangleExternalCarrier (3), and
ShortTriangleFourPairChord (1) have 11 exact passing axiom reports in
/tmp/double_smooth_triangle_audit1.log. Only permitted axioms.

RestoreTriangle adds any edge-disjoint triangle meeting the old supported
partition at cost at most one path, using the existing arbitrary-path
triangle absorption. SupportSmoothing suppresses a degree-two vertex on
connected support, restoring a fresh shortcut without increasing path count.
DoubleSmoothTriangle applies this twice before restoring the triangle:
two vertices disappear, at cost at most one path.

At a degree-five short triangle with BOTH other vertices degree four, the
unique ordinary carrier uses all their external spokes. Deleting the
triangle edges leaves connected support, since the carrier visits all three
triangle vertices. The two external shortcut pairs are distinct: equality
would put a four-cycle inside that simple carrier. If both shortcuts were
absent, the double-smoothing reduction would repair the graph. Consequently
failure_degree_five_short_triangle_four_pair_chord forces at least one of
the two external shortcut edges to exist. Existing-shortcut cases, mixed
cycle-vertex degrees, and general cycles/tails remain.

### Two-triangle core: guarded diagnostics and universal interval machinery

The following proposed stronger absorption is FALSE: a butterfly (two
triangles sharing a vertex avoided by P) plus an intersecting simple path P
always has a two-path cover, even when a selected petal vertex has neighbors
in P other than the opposite petal pair. With triangles 0-1-2-0 and 0-3-4-0,
P = 3-1-4-2-5 is a counterexample to this local two-path statement.
The graph is K5 minus edge 2-3 plus a leaf at2; it needs three paths, which
is exactly its six-vertex Gallai budget. It is NOT a Gallai counterexample.
The targeted 303-case compressed-pattern check found six such failures;
including the formerly excluded neighbor pair gave 328 cases and sixteen
two-path failures. Every failing pattern had a five-cycle-plus-path cover.
Scripts/logs: /tmp/butterfly_path_diagnostic.py and .log,
/tmp/butterfly_cycle_path_diagnostic.py and .log. No universal result was
inferred merely from these external checks.

Generic CorePathPieces (12 lemmas) and OrderedCoreVisits (1 lemma) are now
proved. CorePathPieces combines an arbitrary finite embedded edge core with
ordered intervals of a simple path, expands checked edge-labelled routes,
and reattaches the exterior path portions. It permits core vertices absent
from P; hmarked asserts that every core vertex actually on P was marked.

ButterflyRoutes has two KERNEL-CHECKED finite route families, using `decide`
(not native_decide): 40 partial outer-visit orders with a missing outer
vertex, and 72 full outer-visit orders with a fresh interior excursion.
External generators: /tmp/butterfly_missing_routes.py,
/tmp/butterfly_hamilton_routes.py, /tmp/generate_butterfly_routes.py.
Their generated routes are checked for compatibility, vertex simplicity,
edge disjointness and coverage in Lean, then expanded by the generic theorem.

ButterflyOrderedAbsorption, ButterflyMissing, ButterflyExcursion and
ButterflyContiguous compile warning-free. The actual unrestricted conclusions
are: missing a nonhub core vertex gives two paths; an internal fresh sixth
vertex gives two paths; and a nonabsorbable P must visit all four outer
vertices CONSECUTIVELY (all three intervening gaps have length one).
The common butterfly hub is assumed absent from P throughout. Exterior
prefixes/suffixes and arbitrary simple path lengths are permitted.

All 29 exact reports in /tmp/butterfly_contiguous_audit1.log passed, matching
/tmp/butterfly_audit_expected.txt; only permitted axioms. These cover the
12 generic piece lemmas, 1 ordered-core lemma, 5 finite-certificate/route
lemmas, 5 ordered absorption lemmas, 1 missing-vertex lemma, 1 excursion
lemma and 4 contiguity/coordinate helpers.

The subsequent PathIntervalReplacement, ButterflyPairs and ButterflyPentagon
modules also compile warning-free. Their nine-declaration audit is being
checked separately. No Work or Spec integration. The original Spec is still
24 lines with its sole sorry; /tmp/spec_butterfly_checkpoint.log contains
only the expected sorry warning. No full proof/disproof has been obtained.

### Universal butterfly path-or-pentagon theorem completed

All nine exact reports in /tmp/butterfly_pentagon_audit1.log passed and
matched /tmp/butterfly_pentagon_audit_expected.txt; only permitted axioms.
Builds /tmp/path_interval_replacement1.log, /tmp/butterfly_pairs2.log, and
/tmp/butterfly_pentagon2.log are warning-free.

The new lemma butterfly_path_or_pentagon is a genuine universal theorem:
two edge-disjoint triangles sharing a hub, together with an edge-disjoint
simple path P avoiding that hub and meeting the core, have either a
two-path cover OR a cover by one whole PENTAGON and one simple path. The
remaining path has the SAME endpoints as P. No length bound on P, no bound
on its exterior prefix/suffix, and no restriction on its other intersections
are imposed. The five core vertices are distinct.

Proof of the non-two-path case: contiguity already forces the four outer
vertices into a consecutive order u-v-w-z. Since the path avoids triangle
edges, u,w are one petal pair and v,z the other. If the hub is x, use
  pentagon x-u-w-v-z-x
  path     u-v-x-w-z
and reattach P's original exterior portions. These cover exactly the core
and the replaced three-edge interval. Edge disjointness follows from the
cover and total trail lengths. The new interval replacement lemma checks
simplicity, including both old exterior portions.

Next possible application (NOT YET PROVED): the degree-four pair branch
with one existing external shortcut and one fresh shortcut. Delete the
pair and the existing shortcut, suppress/expand the fresh one, then use
butterfly_path_or_pentagon to restore the two triangles at cost at most one
slot. A raw partition containing a pentagon within budget should be ruled
out by the existing Work.PentagonExclusion.failure_no_whole_pentagon, but
this requires assembling and padding a TRACKED trail family, proving its
one-defect score and maximality from the assumed failure. Existing
EdgeDefect.decomposition_path_family is tracked; TrailBudget.indexed_trail_family
and pad_trail_family return only Nonempty and lose the necessary tracking.
One can instead explicitly index the old paths, one cycle and spare nils
by Option(Fin D.card) plus Fin(k-(D.card+1)), then reindex to Fin k.
Do not claim this bridge or the one-existing-shortcut reduction yet.

Both-existing-shortcut cases, mixed degree-four cycle vertices, and the
unbounded cycle/tail cases remain. No full proof or disproof of Gallai,
no final Spec modification, no completed submission.

### Tracked cycle-partition bridge verified

Submission/TrackedCyclePartition.lean compiles warning-free
(/tmp/tracked_cycle_partition2.log). All four exact declarations in
/tmp/tracked_cycle_partition_audit1.log use only propext, Classical.choice,
Quot.sound. The audit file initially had only a missing-docstring style
warning; a module docstring has been added.

The new cycle_and_paths_family explicitly indexes one cycle, m old paths,
and spare nil walks by Option(Fin m) + Fin(k-(m+1)), retaining the cycle's
index. one_cycle_family_score proves score+1=edges+k. A failed k-path budget
makes any such family score-maximal (one_defect_maximal_of_failure).
failure_no_pentagon_partition applies the existing smallest-order pentagon
exclusion to a raw partition consisting of a pentagon and D.card paths,
provided D.card+1 fits the Gallai budget. No reduced-support connectivity
is required for this bridge.

The original Spec remains unchanged, with its sole sorry. These are partial
results, not a proof or disproof of the conjecture.

### Edgewise transfer and budget-aware butterfly restoration completed

Submission/OneMemberTransfer.lean contains three new verified lemmas:
* erase_one_transfer: transfer the unselected members to a target graph
  containing their edges, without assuming containment of the whole old graph;
* replace_one_by_one: replace one member at no increase in count;
* replace_one_keeping_separate: replace one selected path by a new path plus
  a separate edge set C, obtaining a good partition of G.deleteEdges C.
Build /tmp/one_member_transfer3.log is warning-free.

Submission/ButterflyRestoration.lean now proves two more lemmas.
butterfly_partition_or_pentagon takes an edge-disjoint butterfly core, whose
hub is isolated in F but some outer vertex meets F.support, and a good
F-partition D. It gives either a good G-partition of size at most D.card+1,
or a whole pentagon and a good partition of its complement of size at most
D.card. It uses the universal butterfly_path_or_pentagon result and the
new edgewise transfer helper.
failure_no_butterfly_partition excludes this configuration in a smallest-order
failure when D.card+1 fits the Gallai budget, by the tracked pentagon bridge.
Build /tmp/butterfly_restoration1.log is warning-free. All five exact reports
in /tmp/butterfly_restoration_audit1.log use only permitted axioms.

This does NOT establish the intended one-existing/one-fresh shortcut
reduction: reduced support can disconnect, and the sum of component budgets
can cost an extra slot. A separate connectivity or disconnected-budget
argument is still necessary. No change to Spec; no full proof/disproof.

### Two vertex-disjoint carriers absorb a butterfly at no path cost

A targeted compressed-pattern diagnostic /tmp/butterfly_two_disjoint_paths.py
checked 349 structurally indexed configurations (not random graphs) and found
no two-path failures. This was only exploratory; the theorem below is proved
universally without trusting the Python computation or finite samples.

Submission/TriangleArms.lean proves three lemmas. A triangle r-x-y-r plus
a path P avoiding r and meeting x can be split into two r-rooted simple
arms. Given z distinct from the triangle, the first arm can avoid z; when
y is absent from P, the second arm avoids y. No edge-disjointness assertion
is made at this arm stage; it tracks coverage and total length instead.
The proof splits P at x, chooses the side missing z, and attaches the
triangle's two-edge leg to a side missing y. Path reversal handles the other
orientation. No finite path-length bound is imposed.

Submission/ButterflyTwoPaths.lean proves butterfly_core_ncard and
butterfly_two_disjoint_paths. If vertex-disjoint P,Q avoid the hub and meet
different petals, and both avoid all core edges, the whole union has a
TWO-path cover, not three. The controlled arms are paired so that their
only cross-intersection is the hub. Coverage plus total length proves
edge disjointness. All five exact reports in
/tmp/butterfly_two_paths_audit1.log passed with only allowed axioms.
Builds /tmp/triangle_arms2.log and /tmp/butterfly_two_paths2.log are warning-free.

Submission/TwoMemberReplacement.lean proves replace_two_by_two at no increase
in partition size. Submission/ButterflyAcrossComponents.lean proves
restore_butterfly_across_components: if two outer vertices on different
petals lie in distinct components of F, the butterfly can be restored to
ANY good F-partition at no extra path cost. It selects nonnil carriers via
path_through_support; nonreachability makes them vertex-disjoint.
Both exact reports in /tmp/butterfly_across_components_audit1.log use only
allowed axioms. Builds /tmp/two_member_replacement1.log and
/tmp/butterfly_across_components2.log are warning-free.

This supplies a possible way around the disconnected reduced-budget issue,
but the degree-five reduction still requires the two-component support
bound, the smoothing lift and the correct parity/cardinality calculation.
No full proof or disproof of Gallai. Spec is unchanged with its sole sorry.

### Disconnected-budget issue resolved; one-existing/one-fresh branch closed

The new support machinery is verified:
* TwoComponentBudget (six lemmas): induce supported reachability, propagate
  support along reachability, bound component count by two from two reachable
  classes, sum smaller-order budgets to 2*D.card ≤ support.ncard+2, and extract
  both supported representatives from a disconnected two-class cover.
* SmoothReachability (four lemmas): exact support after smoothing is the old
  support minus the suppressed vertex; reachability transfers in both
  directions away from that vertex; puncturing a degree-two vertex and deleting
  its external shortcut leaves at most two reachable classes.
* ButterflySmoothingReduction (two lemmas): swap the petal tips; exclude a
  butterfly complement with an outer degree-two vertex having a fresh shortcut,
  when its support is covered by the two outer-petal reachable classes.

The last theorem handles BOTH reduced-support cases explicitly. Connected:
remove hub and smooth one tip, obtain a path partition saving one slot, and
restore the butterfly at cost one or invoke the whole-pentagon exclusion.
Disconnected: the two representatives are supported; smoothing preserves their
support and the two-class cover; the component budget gives 2*D.card ≤ n;
restore the butterfly across components at NO extra path cost. Thus no
unproved connectivity assertion is being used in this reduction.

All twelve exact reports in /tmp/butterfly_smoothing_audit1.log use only the
allowed axioms. Builds /tmp/two_component_budget4.log,
/tmp/smooth_reachability2.log, and /tmp/butterfly_smoothing_reduction4.log are
warning-free. Lean pitfall: Fintype.card for components can use different
computable/classical Fintype instances; normalize both sides via
[←Nat.card_eq_fintype_card] rather than asking definitional equality to unfold
these instances. Explicit (V := G.support) also avoids an elaboration timeout.

ExistingShortcutTriangle (two lemmas) identifies puncture/delete-shortcut with
deleting the degree-two triangle, then applies the butterfly smoothing theorem
to the original triangular pair. This genuinely proves
failure_no_one_existing_one_fresh_shortcut, including disconnected reductions.
TwoExistingShortcuts.failure_two_shortcuts_present combines this with the
previous two-fresh reduction, with a symmetry step for the opposite mixed case.
ShortTriangleBothChords.failure_degree_five_short_triangle_both_chords instantiates
it for the unique-carrier short triangle: if both nonroot vertices have degree4,
BOTH external shortcut edges must exist, and the shortcut pairs are distinct.
All four exact reports in /tmp/short_triangle_both_chords_audit1.log passed;
builds /tmp/existing_shortcut_triangle2.log, /tmp/two_existing_shortcuts1.log,
and /tmp/short_triangle_both_chords1.log are warning-free.

A combined exact-name audit across all six new audit modules checked all 32
new declarations, with no missing reports or forbidden axioms. The new proof
modules contain no sorry/admit/native_decide/axiom declarations.

Remaining: BOTH-existing shortcut branch, mixed degree4 with degree2/3,
and general longer cycles/tails. Do not assume that a chain of three triangles
plus one arbitrary intersecting path has a two-path cover. For example, the
triangles (0,1,2), (0,3,4), (1,5,6), plus leaf edge 2-7 require at least three:
each pendant triangle forces two endpoints in its two nonattachment vertices,
and the two odd vertices 2,7 force two more. This is NOT a Gallai counterexample
(order8, budget4). In an induction such isolated outer tips give extra support
slack, which must be tracked rather than assuming universal local absorption.

Actual Submission/Spec.lean still has its original sole sorry, line22.
/tmp/spec_both_chords_checkpoint.log confirms only that expected warning.
No full proof or disproof has been obtained; no completed submission claimed.

### Degree-two neighbors now have degree at least five

Eleven new lemmas in ButterflySupportBudget, DegreeTwoFourTriangle,
DeleteTriangleLink, DegreeTwoNeighborFive, and ShortTriangleMixedCases compile
warning-free and were audited in /tmp/degree_two_neighbor_five_audit1.log.
All eleven exact reports use only propext, Classical.choice, Quot.sound.

This is stronger than only eliminating the short-triangle (4,2) case:
degree_two_neighbors_ge_five proves that EVERY neighbor of a degree-two
vertex in a smallest-order failure has degree at least five. The proof uses
connected deletion of the even degree-four vertex, contracts the remaining
triangular leaf to get the required support link, and handles fresh/existing
external shortcuts via smoothing/butterfly restoration. The old bound was
only four (five previously required even-vertex independence).

The degree-five short-triangle nonroot pair must consequently be (4,3),
(3,4), or (4,4); for each nonroot vertex, degree+quota=4. No general
root-degree-five exclusion or complete Gallai proof is claimed here.

### Quartic pair excluded; one-edge triangular tails require root degree at least seven

PathEarExchange, ShortTriangleEarCarrier, ShortTriangleTailChord, and
ShortTriangleQuarticPairExclusion supply seven verified lemmas. An ordinary
carrier of the external shortcut ab can exchange it with the a-x-b ear in
the unique cycle carrier, preserving maximal score but violating the rule
that every carrier through a nonroot cycle vertex contains the root. Thus
any existing shortcut at a quartic nonroot vertex lies on the defective
tail. For two quartic nonroot vertices, the two distinct shortcuts would
both be the unique noninitial edge of a tail of length at most two: impossible.

LeafPuncture, MixedTriangleFresh, MixedTriangleTailLock, and
TriangleOneTailDegreeSeven supply eight more verified lemmas. In a mixed
cubic/quartic triangle, a fresh quartic shortcut is reducible: delete the
cubic leaf after removing the triangle, smooth the quartic vertex, induct
after saving two supported vertices, expand, append the root-to-leaf edge
at the odd root at no path cost, and restore one extra path. Therefore the
shortcut exists and lies on a tail of length exactly two. The only remaining
root-degree-five short-triangle pair is cubic/quartic. A one-edge triangular
tail in a smallest failure now has root degree at least seven.

All 26 new declarations across the three audit modules passed a combined
exact-name/allowed-axiom parser. Logs:
/tmp/degree_two_neighbor_five_audit1.log (11),
/tmp/short_triangle_quartic_pair_audit1.log (7),
/tmp/triangle_one_tail_degree_seven_audit1.log (8).
All proof builds are warning-free. Only propext, Classical.choice, Quot.sound
appear. Actual Spec remains unchanged with its sole sorry. The locked
two-edge mixed case, larger roots, and general cycle/tail lengths remain open.

### Full degree-five short-triangle exclusion completed

Nine first lemmas in RootedPairReplacement, TriangleTerminalSwitch, and
MixedTriangleTerminalExclusion verify the proposed terminal-neighbor rotation.
The new cycle r-x-s-r and tail r-y-t, with normal path y-x-t-s-R, preserve
score. The old carrier forces degree(s)>=4; new short-triangle incidence
forces degree(s)<=4; quartic-pair exclusion gives contradiction. The helper
replace_rooted_pair retains an explicit new RootedCycleRep after replacement
and reorientation, not an unproved rerooting.

A simpler inductive reduction then closed ALL remaining locked mixed cases.
PrivateProxy supplies five generic lemmas: support connectivity by contracting
a private vertex set, the cubic/quartic boundary specialization, proxy residual
edgeSet, proxy expansion with an existing-edge prefix restored to the extra
path, and the two-missing-vertices Gallai budget.

For cycle r-x-y-r, tail r-s-t, neighbors(x)={r,y,s,t} and
neighbors(y)={r,x,c}:
* c=s: remove x,y; use proxy rt (fresh or existing); expand to r-y-x-t;
  restore r-x-s-y, prefixed by t-r if proxy rt was an original edge.
* c=t: the same generic tip reduction with s,t swapped uses proxy rs;
  expand r-y-x-s and restore s-r-x-t-y.
* c outside the five old vertices: if sc is fresh, use proxy sc, expand
  s-x-y-c, restore t-x-r-y; if tc is fresh, swap s,t.
* BOTH sc and tc existing: take H=(G-{x,y})-sc, expand tc to t-x-y-c,
  restore the path t-c-s-x-r-y. This restores both the consumed proxy and
  the deleted cross-edge in the single extra path. H stays connected on
  support: r-s-t-c connects all private-boundary vertices, and the deleted
  sc edge is bypassed by s-t-c. All expansion interiors are missing from H.
Each case saves two vertices and costs at most one path.

Verified modules: MixedPrivateTip, MixedPrivateFresh, MixedPrivateBothCross,
LockedMixedTriangleReduction, and ShortTriangleDegreeSeven. The latter proves
failure_no_mixed_degree_five_short_triangle,
failure_no_degree_five_short_triangle, and
failure_short_triangle_root_degree_ge_seven for BOTH one- and two-edge tails.
No order-parity restriction is used.

All 21 new declarations passed exact-name/allowed-axiom audits:
/tmp/terminal_triangle_audit2.log (9),
/tmp/short_triangle_degree_seven_audit1.log (12). All proof modules compile
warning-free. The old proposed c=s private-three/four-vertex gadget reductions
are unnecessary; the two-vertex proxy argument suffices.

Remaining: root degree>=7 even for short triangles, and unbounded cycle/tail
lengths. This is NOT a complete Gallai proof. Spec remains unchanged with its
original sole sorry; no completed submission has been made.

Final checkpoint for this continuation: /tmp/spec_short_triangle_seven_checkpoint.log
contains only the expected original sorry warning. All nine new proof modules
were scanned: no sorry/admit/native_decide/axiom declarations. No full
proof or disproof; no completed submission tool call.

### Arbitrary-root mixed-pair exclusion (verified)

Eleven lemmas in PunctureConnectivity, MixedConnectedCross,
MixedConnectedReduction, MixedOddTriangleReduction, ShortTriangleDeletion,
and ShortTriangleMixedExclusion compile warning-free. A mixed degree4/3
triangle at an ODD root is reducible whenever deleting the triangle leaves
connected support. Fresh quartic shortcut uses the earlier leaf/smoothing
repair. A present shortcut lets us delete both private vertices while
retaining connected support; the cross-edge repairs apply without needing
a root-to-tail-tip edge. Deleting a short-triangle defect leaves connected
support because every nonroot external carrier contains the root. No
unique-carrier or root-degree-five assumption is used.

Thus failure_no_short_triangle_mixed_pair excludes degree4/3 nonroot pairs
for arbitrary root degree. All eleven reports in
/tmp/short_triangle_mixed_exclusion_audit1.log show only permitted axioms.
The combined exact-name parser has not yet been run for this audit.

Further development IN PROGRESS: QuarticPairProxy, QuarticPairCross,
DoubleSuppressionPartition, and QuarticTwins compile warning-free but have
not yet been axiom-audited. Distinct external quartic pairs are reducible
when both shortcuts exist and the punctured graph has connected support.
The identical-pair case is globally reducible: remove xb,xy,ya and the
possibly present ar,rb; the retained path a-x-r-y-b bypasses every removed
edge. Suppress the two independent degree-two vertices x,y, saving one
path slot. The removed edges form a simple path of length3 or4, or a whole
pentagon if both ar and rb exist. Restore the path, or invoke the verified
smallest-failure whole-pentagon exclusion.

Next: combine the quartic reductions into arbitrary-root 4/4 short-triangle
exclusion. A potential cubic-pair extension uses endpoint transfer: if
a cubic nonroot v has external neighbor b, any ordinary path ending at b
and avoiding the root can take edge bv from v's carrier, preserve score,
and contradict cycle-carrier root containment. This may rule out the
remaining bridge obstruction for two cubic nonroot vertices. Not yet
formalized or claimed. No full Gallai proof/disproof; Spec unchanged.

### Arbitrary-root quartic-pair exclusion (verified)

The exact-name parser now passed all eleven mixed-pair reports in
/tmp/short_triangle_mixed_exclusion_audit1.log. The ten new declarations in
QuarticPairProxy, QuarticPairCross, DoubleSuppressionPartition, and
QuarticTwins passed /tmp/quartic_pair_audit2.log (allowed axioms only).

QuarticTriangleReduction.failure_no_quartic_triangle_data combines the
true-twin repair with the distinct-pair shortcut forcing and successive
suppression. It excludes a quartic nonroot pair whenever deleting its
triangle leaves connected support and supports the root. The instantiated
ShortTriangleQuarticExclusion.failure_no_short_triangle_quartic_pair
excludes degree4/4 at ANY short-triangle root, not just degree five.
Both compile warning-free and passed /tmp/quartic_triangle_audit1.log.

Still no full Gallai proof/disproof. Cubic/cubic at arbitrary roots,
larger nonroot degrees, and unbounded cycle/tail lengths remain unresolved.
The original Spec conjecture and sole sorry are unchanged.

### Arbitrary-root cubic-pair exclusion (verified)

The proposed endpoint transfer is now proved in ShortTriangleEndpointTransfer:
move the first edge v-b of a nonroot cycle endpoint's ordinary carrier to
another ordinary path ending at b and avoiding the root. The replacement
preserves score and the literal rooted defect, contradicting root containment.
OrdinaryPairReplacement retains the rooted witness under two path replacements.

CubicCutReachability formalizes two sides of a deleted edge and the contraction
of x,y to r after deleting ab,yb. ShortTriangleCubicCut proves that the b-side
attachment must be even: its carrier owns both cut edges, all other members
through b avoid r, and an odd b would supply an endpoint for the transfer.
The proof checks that the endpoint is neither the carrier nor the defective
member. CubicTriangleDeletion establishes residual connectivity and r-a/r-b
links by two leaf deletions. CubicExternalCarrier obtains oriented carriers.
ShortTriangleDistinctCubicExclusion combines the bridge obstruction with the
fresh-edge and even-attachment reductions, excluding distinct a,b at any root.
All ten declarations passed /tmp/cubic_cut_audit1.log.

The common-attachment case is also closed. ResidualOddAttachment generalizes
the earlier lift to an odd residual neighbor. CubicTwinsExisting expands ra to
r-x-y-a and restores x-a-r-y. CubicTwinsFresh, for absent ra and even a, smooths
x after deleting y, restores x, appends leaf ya at the now-odd a, and restores
r-y-x. CubicTwinsReduction combines these with the odd-a residual lift.
ShortTriangleCubicExclusion.failure_no_short_triangle_cubic_pair now excludes
ALL degree3/3 nonroot pairs at short triangles with arbitrary root degree.
These five declarations passed /tmp/cubic_twins_audit1.log.

All new modules compile warning-free; audits report only permitted axioms.
Combined with mixed and quartic exclusions, all nonroot degree pairs in
{3,4}^2 are excluded. This remains local progress, not a complete proof:
higher degrees and unbounded cycle/tail lengths are unresolved. Spec is
unchanged with its original sorry.

Combined consequence: ShortTriangleNonrootBound defines reverse_cycle_rep
(reversing only the cycle, not freely changing the root) and proves
failure_short_triangle_nonroot_degree_ge_five. At least one of the two
nonroot vertices of any short triangular defect has ambient degree >=5.
The degree-two cases use the older degree-two-neighbors>=5 theorem; all
3/4 cases use the new arbitrary-root exclusions. Both declarations passed
/tmp/short_triangle_nonroot_bound_audit1.log. Compilation is warning-free.

This continuation added seventeen audited declaration reports after the
quartic combination (ten endpoint/cut, five twins/full cubic, two final bound).
Actual Spec remains unchanged with its original sole sorry. No completed
proof/disproof exists and no completion submission has been made.

### Directed first-visit constraints and subdivided-K5 absorption (verified)

A targeted route diagnostic tested a triangle r-x-y-r, three-edge tail
r-s-t-u, and an ordinary path with endpoint r. The predecessor constraints
already proved force the incoming edges to x and y to come directly from
distinct nonroot tail vertices. /tmp/triangle_three_root_routes.py enumerated
228 guarded finite configurations (symmetry normalized): 210 admit two paths,
14 a core cycle plus a path, and four fail both. These are AUXILIARY finite
computations, not a Lean classification or a proof of Gallai.

The exceptional direct core is
  triangle 0-1-2-0, tail 0-3-4-5, path 0-4-1-3-2-5.
Its union is K5 on 0..4 with edge 2-4 subdivided by vertex5. The other three
diagnostic variants add a continuation after5 and/or subdivide the path gap
2-to-5. A blanket two-member path-or-short-cycle conversion for length-three
tails is therefore false. This is NOT a Gallai counterexample (the six-vertex
core meets its three-path budget, not the attempted two-path auxiliary budget).

Seven new modules compile warning-free:
  CyclePredecessorConstraint
  SubdividedFiveFinite
  SubdividedFiveCycles
  SubdividedFiveAbsorption
  TwoReplacementTransfer
  SubdividedFiveRestoration
  SubdividedFivePairExclusion

CyclePredecessorConstraint.nonabsorbable_first_predecessor proves a LOCAL
necessary condition without a trail-family or optimization hypothesis: if
C plus P has no two-path cover, every cycle neighbor of P's first visit has
its predecessor in P on C. This follows from the earlier first-visit rotation;
an exterior predecessor would directly yield two paths. path_no_opposite_steps
formalizes impossibility of two oppositely oriented occurrences of one edge
in a simple path, using injectivity of vertex positions.

SubdividedFiveFinite gives three explicit (C5,C6) cycle partitions of the
single-subdivision K5. Their six-cycles together contain every core edge;
all finite properties are checked by Lean's kernel (no native_decide).
SubdividedFiveCycles maps these certificates injectively into any graph.
SubdividedFiveAbsorption.subdivided_five_path_to_pentagon proves:
  a single-subdivision K5 plus ANY edge-disjoint touching path
  partitions into a whole pentagon and two paths.
No restriction on the path's length or its other intersections is made.
This is not itself an unconditional three-PATH theorem.

Proof: if no chosen C6 plus P is two-path coverable, the first-visit
predecessor condition holds along EVERY base edge at the first visited core
vertex. For a first visit other than5, choose two neighbors in {0,1,3};
the only possible core predecessor of either on the edge-disjoint path is5,
contradicting unique successor. For first visit5, predecessors of2 and4 must
be4 and2 respectively, contradicting path_no_opposite_steps.

TwoReplacementTransfer supplies arbitrary-graph one-to-two path replacement
and a version retaining a separate subgraph. SubdividedFiveRestoration then
restores this core beside an ordinary partition of size p as a pentagon plus
at most p+1 paths. Smallest-failure pentagon exclusion applies whenever
p+2 is within the Gallai budget. Its support-saving corollary needs connected
residual support, a touching vertex, and a support saving of at least four.

SubdividedFivePairExclusion.failure_no_subdivided_five_rooted_pair excludes
an EXACT closed single-subdivision K5 occupying the defective member plus
one ordinary member in a maximal one-defect family of a smallest failure.
The other k-2 members form the residual path partition. They cannot all avoid
the six core vertices: connectivity and the no-nil-slot lemma give a touching
member. The restoration/pentagon theorem then contradicts failure. No ambient
degree bounds on the six core vertices are assumed.

43 exact declaration reports passed allowed-axiom audits:
  /tmp/subdivided_five_audit1.log             36
  /tmp/subdivided_five_restoration_audit1.log  5
  /tmp/subdivided_five_pair_audit1.log         2
All seven new modules were scanned for proof gaps and forbidden declarations.

Remaining gaps: the full three-edge-tail ordering classification has not
been formalized; the longer-subdivision and continuation variants remain
unresolved by this argument. No arbitrary-subdivision absorption theorem
is claimed. Higher-degree short triangles and arbitrary cycle/tail lengths
remain. Actual Spec is unchanged with the original sole sorry; no complete
proof/disproof or completed submission has been obtained.

### Join-cycle absorption and complementary residues (verified)

Three new proof modules compile warning-free:
  JoinCycleAbsorption
  ComplementCycleResidue
  SubdividedFiveJoinProof

JoinCycleAbsorption.predecessor_of_first_visit_avoids formalizes that the
predecessor of a path's first visit to a set lies outside that set. Its proof
uses injectivity of path positions, not an endpoint-pairing assumption.

join_cycle_absorption_at_first_visit and join_cycle_family_absorb_path give
an UNBOUNDED criterion: let cycles C_i have all vertices inside S=A union B,
where A,B are nonempty, and every edge across A,B belongs to some C_i. If a
simple path P touches S and is edge-disjoint from every C_i, then some
C_i union P has a two-path cover. The cycles need not span S, have equal
lengths, or be pairwise edge-disjoint. No maximum-score or quota hypothesis.

Proof: orient the first visit u to S into A. If no cycle absorbs P, the local
predecessor constraint forces every v in B to occur on P, with its predecessor
in S. Since every A-B edge is on a cycle and P avoids every cycle edge, that
predecessor must be in B. Apply this to P's FIRST visit to B, a contradiction.

cycles_absorb_of_disconnected_complement obtains the join cut from two
components of H's complement, then maps into an arbitrary ambient graph.
cycle_residue_absorption retains any predicate R on the unused core edges:
if each H edge can be put into a candidate cycle with residue satisfying R,
one candidate absorbs P into two paths and its residue is retained separately.
The output is R-residue plus two paths, NOT necessarily just two paths for
the whole core.

SubdividedFiveJoinProof.base_complement_not_preconnected is kernel-checked
by ordinary decide. The complement components are {0,1,3,5} and {2,4}.
subdivided_five_join_path_to_pentagon gives a shorter proof of the previously
verified subdivided-K5 plus touching-path theorem, via the general residue
criterion and the existing three (C5,C6) partitions. The earlier absorption
module is left intact; downstream developments remain unchanged.

Seven exact declaration reports passed allowed-axiom parsing:
  /tmp/join_cycle_absorption_audit1.log       5 declarations
  /tmp/subdivided_five_join_audit1.log        2 declarations
Audit modules: JoinCycleAbsorptionAudit, SubdividedFiveJoinAudit.
Final builds: join_cycle_absorption4.log, complement_cycle_residue2.log,
subdivided_five_join_proof1.log. Only propext, Classical.choice, Quot.sound.

### The unbounded missing-cycle-vertex shortcut is FALSE (structural)

The candidate "a cycle plus an edge-disjoint touching path missing a cycle
vertex always has a two-path cover" is false. This was NOT a search for a
counterexample to Gallai. A preliminary auxiliary check of core-contained
paths on cycles of orders 5 through 9 passed; this was only finite evidence.
Log /tmp/cycle_missing_vertex_probe.log. The process has finished.

A structural 13-vertex obstruction:
  P = 0-2-4-3-5-1-6-8-10-9-11-7
  C = 12-1-4-5-2-3-0-7-10-11-8-9-6-12.
P is a simple path omitting vertex12; C is a spanning simple cycle. Their
edge sets are disjoint and have 24 edges in total. An exact auxiliary
backtracking check using /tmp/triangle_lollipop_two_test.py returns no
2-path cover, consistent with the following structural argument.

Construct the two six-vertex blocks from the two edge-disjoint Hamilton
paths on vertices0..5:
  A=0-2-4-3-5-1, B=0-3-2-5-4-1,
and a copy shifted by6. The block interior is K4 on {2,3,4,5}; ports0,1
have degree2 inside the block. Join the blocks with edges1-6 and0-7.
A_left+A_right and reverse(B_left)+reverse(B_right) are edge-disjoint
Hamilton paths of the twelve-vertex graph, with endpoint pairs (0,7)
and (1,6). Any two-Hamilton-path partition of this graph has exactly this
pairing: each path uses one of the two cut edges, and cannot use a cut edge
incident to either of its endpoints (otherwise it misses the rest of that
side). This ALSO refutes the earlier unproved Hamilton-path endpoint
unpairing candidate, which had passed checks through order9.

Adding vertex12 on a two-edge 1-12-6 connection closes the second Hamilton
path into C. If C union P had two paths, its 24 edges on13 vertices would
force BOTH paths to be Hamiltonian. All vertices except0,7,12 have degree4;
0,7 have degree3 and12 degree2. Thus both paths end at12, and their other
ends are0 and7. Trimming their edges at12 would separate1,6 into different
Hamilton paths, contradicting the forced endpoint pairing above.

These structural obstruction facts have NOT yet been formalized in Lean;
no new theorem assumes them. The Gallai budget here is SEVEN, not two.
They refute auxiliary local assertions only. They do not disprove the
original conjecture. In particular the verified C5/C6/C7 missing-vertex
lemmas cannot be extrapolated to arbitrary lengths by that shortcut.

Actual Submission/Spec.lean is unchanged, with its original sole sorry.
The general high-degree and unbounded cycle/tail cases are still open in
this development. No complete proof/disproof or completed submission exists.

### Missing-cycle-vertex auxiliary obstruction (now Lean-verified)

The earlier thirteen-vertex obstruction is now completely formalized; this
supersedes the earlier note saying its nonabsorbability was still informal.
Modules:
  FinitePathSearch.lean
  MissingCycleVertexObstruction.lean
  MissingCycleVertexNoCover.lean
All compile warning-free. The first module proves soundness of an adjacency-list
simple-path search and derives nonexistence from a `false` certificate. The
second uses ordinary kernel-evaluated `decide` (NOT native_decide) for the
explicit graph, C/P witnesses, and nonexistence of Hamilton paths from12 to0
or7. The successful computational build is missing_cycle_vertex_obstruction2.log.
The proof-only completion is missing_cycle_vertex_no_cover1.log.

The final no_two_path_cover proof uses the 24-edge count to force both paths
Hamiltonian on13 vertices. Degree2 at12 makes12 an endpoint of each. The only
other degree-at-most-three vertices are0,7, so an oriented first Hamilton path
would run from12 to0 or7, contradicting the checked search certificate.
cycle_path_missing_vertex_not_absorbable packages the verified cycle, path,
omitted cycle vertex, edge disjointness, and negated two-path cover.

All seventeen exact-name reports in /tmp/missing_cycle_vertex_audit1.log were
parsed and checked: only propext, Classical.choice, Quot.sound. The three proof
modules also passed comment-stripped gap/forbidden-declaration scans. Audit
module: MissingCycleVertexAudit.lean. Expensive certificates and structural
proof were separated to avoid rerunning the large kernel computation during
proof iterations.

This remains an AUXILIARY obstruction, not a disproof of the conjecture.
Its thirteen-vertex Gallai budget is seven, not two. No new global argument
has eliminated the higher-degree or unbounded attached-tail cases. The actual
Spec.lean remains unchanged, with its original statement and sole sorry.

### Unified minimal-counterexample certificate (verified)

Submission/UnifiedMinimalDefect.lean now combines the compatible global choices
in one explicit package. MinimalFailure stores smallest order and global edge
minimality. OptimizedDefect stores the maximum one-defect score, unrestricted
shortest rooted cycle, shortest tail at that oriented cycle, and the compatible
fixed-anchor carrier-count and carrier-length optima. It deliberately contains
NO quota-energy optimum.

failure_has_unified_certificate obtains such a witness from any actual failure,
using the existing minimal-order, global edge-minimality, and optimization
lemmas. Derived statements apply to that SAME witness:
  - nonnil tail and cycle length strictly below the graph order;
  - every normal component has support size at least twice its member count;
  - at most three normal components, at most two in odd order;
  - anchor-size and outside-component carrier budgets, including odd order;
  - for a triangle with tail length at most two: root quota one, odd root
    degree at least seven, order at least eight, and a nonroot cycle vertex
    of degree at least five.
residual_cases is an exhaustive alternative: cycle length >=4, tail length >=3,
or the above high-degree short-triangle branch. NONE of those alternatives
is proved impossible. This is a consolidation of verified reductions, not a
new proof of the original conjecture or an assertion that compatible quota
energy has been obtained.

Build /tmp/unified_minimal_defect3.log is warning-free. All SIXTEEN exact-name
reports in /tmp/unified_minimal_defect_audit1.log were parsed/matched against
UnifiedMinimalDefectAudit.lean; only propext, Classical.choice, Quot.sound.
The source passed the comment-stripped proof-gap/forbidden-declaration scan.

The global endpoint-pair transport and attached-tail gaps were reconsidered.
No new unconditional transport, avoidance, or normalization lemma was assumed.
In particular, endpoint-owner separation is weaker than path avoidance, and
an unrestricted shortest-cycle choice cannot simply be combined with the
separate quota-energy choice. No complete proof/disproof was obtained.
Actual Spec.lean remains unchanged with its sole original sorry.

### Guarded attached-tail suppression and fresh-tail triangle absorption (verified)

Three new modules compile warning-free:
  RootedCycleNeighborClosure.lean
  LollipopComponentSuppression.lean
  TriangleFreshTail.lean

RootedCycleNeighborClosure.rooted_cycle_avoider_no_chord uses the existing
quota-preserving arbitrary-tail ear exchange. At a shortest rooted cycle
(fixed root and quotas suffice), a path avoiding a NONROOT cycle vertex
cannot own the chord joining that vertex's two cycle neighbors. It does NOT
reroot the lollipop at the removed vertex.

LollipopComponentSuppression.independent_tail_avoiding_shortcuts constructs
fresh distinct suppression edges for a normal component whose support avoids
the ENTIRE attached tail and is independent on the cycle, when cycle length>4.
no_independent_zero_component_away_from_tail applies smaller-order induction
after compression and expands all shortcuts, ruling out such a component
with support size exactly twice its member count. In the unified certificate,
zero_component_tail_hit_or_cycle_edge gives the alternative: a zero-surplus
component meets the tail OR contains both ends of a cycle edge. These guards
have NOT been proved automatically. No unconditional elimination of zero
components follows. Tail length is unrestricted.

TriangleFreshTail proves triangle_fresh_tail_at_last and
triangle_fresh_tail_absorption. A triangular cycle with an arbitrary attached
simple tail can absorb an edge-disjoint path touching its triangle, provided
the ENTIRE tail is VERTEX-DISJOINT from that path. Last-triangle-visit splitting
produces two paths starting at the root; the fresh tail is appended to one.
This is not the false unrestricted lollipop-absorption assertion.
maximum_triangle_tail_avoider_misses_cycle and
maximum_triangle_component_meets_tail imply that every normal component of a
maximal one-defect triangular-lollipop family meets the tail, without an upper
bound on tail length or any Gallai-budget hypothesis. Distinct components
have disjoint supports, giving maximum_triangle_component_count:
  normal component count <= tail length+1.

Build logs: /tmp/rooted_cycle_neighbor_closure2.log,
/tmp/lollipop_component_suppression3.log, /tmp/triangle_fresh_tail4.log.
All NINE exact-name reports were parsed/matched and checked against the
permitted axioms (propext, Classical.choice, Quot.sound):
  /tmp/lollipop_component_suppression_audit1.log   4 reports
  /tmp/triangle_fresh_tail_audit1.log             5 reports
Audit modules: LollipopComponentSuppressionAudit, TriangleFreshTailAudit.
All three proof modules passed comment-stripped forbidden/gap scans.

Potential further extension, NOT proved: compress whole consecutive runs of
cycle visits inside a tail-avoiding zero component. This would require a
long-ear shortcut exchange and a simultaneous expansion certificate; simply
assuming the visits independent would be invalid. If only one or two cycle
vertices survive outside the component, compression creates loops or parallel
edges, so even a run-compression proof cannot ignore those cases. This remains
a research direction, not a new Lean hypothesis.

No complete proof/disproof of the original conjecture was obtained. Spec.lean
is unchanged with its original statement, sole import, and sole sorry.

### Long-ear exchange and simultaneous private path expansion (verified)

LongLollipopEar.lean and PrivatePathExpansion.lean now compile warning-free.
The long-ear exchange replaces an arbitrary cycle arc by a chord owned by a
path avoiding every internal vertex of the arc. When the root lies on the
retained arc, the whole attached tail, root, score, and endpoint quotas are
preserved. A rooted shortest cycle therefore has no such removable long ear.

PrivatePathExpansion expands a finite family of fresh distinct shortcut edges
into paths with private internal vertices. The shortcut edges need NOT belong
to different path members. Privacy is an explicit hypothesis, not inferred
from endpoint-owner separation. The module also proves support connectivity
of compression and a smaller-order compressed partition bound. The pending
Ne-symmetry and already-closed reflexive goal errors were fixed.

All sixteen exact reports from PrivatePathExpansionAudit.lean were parsed and
checked: only propext, Classical.choice, Quot.sound. Both proof modules passed
comment-stripped gap/forbidden-declaration scans. Build/audit logs:
  /tmp/long_lollipop_ear2.log
  /tmp/private_path_expansion3.log
  /tmp/private_path_expansion_audit1.log
The audit's initial missing-docstring style warning was subsequently fixed.

Still needed: a maximal cycle-run certificate connecting these abstract
lemmas to tail-avoiding zero-surplus normal components. The fewer-than-three
surviving-cycle-vertices cases cannot be included without new arguments.
No complete proof/disproof exists; Spec.lean retains the original sorry.

### Maximal cycle-run compression (verified)

CycleRunIntervals.lean constructs all consecutive cycle runs through a set S
using bounded numeric walk intervals. It proves existence of a run covering
every cycle edge incident to S, privacy of interiors, and (when three cycle
vertices remain outside S) distinct nonloop shortcuts absent from the cycle.
The complementary arc of every run contains the literal cycle root.

CycleRunCompression.lean applies the private-path expansion theorem to these
runs. Freshness in the non-cycle base graph remains an explicit hypothesis.
LollipopRunSuppression.lean discharges that hypothesis beside a tail-avoiding
normal component, using the long-ear exchange at the shortest rooted cycle.
Smaller-order induction after compression and selected-group replacement
exclude a zero-surplus component avoiding the tail whenever at least three
cycle vertices survive outside it. No independence-on-the-cycle or cycle
length bound is needed.

zero_component_tail_hit_or_two_survivors applies to the SAME unified minimal
certificate: every zero component meets the tail OR leaves at most two cycle
vertices outside its support. Neither alternative is ruled out globally.
The loop/parallel-shortcut cases are explicitly excluded, not silently treated
as a simple compressed cycle.

All three modules compile warning-free. All TWENTY-SIX exact-name axiom reports
in /tmp/lollipop_run_suppression_audit1.log were parsed and matched against
LollipopRunSuppressionAudit.lean. Only the permitted axioms occur. All proof
modules passed comment-stripped gap/forbidden-declaration scans.
Successful logs: /tmp/cycle_run_intervals7.log,
/tmp/cycle_run_compression5.log, /tmp/lollipop_run_suppression4.log.
This completes the previously pending maximal-run certificate direction.
The original conjecture is still unresolved; Spec.lean remains unchanged.

### Odd-order zero components must meet the tail (verified)

LollipopRunSuppression now additionally proves subset_runs_fresh and
no_zero_component_by_partial_suppression: one may retain selected vertices
of the removed normal component, provided the actual compressed order is
smaller and its ceiling budget does not increase. The original four theorem
statements were retained; tail_avoiding_runs_fresh is now a wrapper.

OddTailComponent.lean eliminates BOTH previously exceptional tail-avoiding
cases on odd order:
- If exactly two cycle vertices survive, retain one additional internal
  cycle vertex. Since the zero component has even support and the ambient
  order is odd, the complementary order is odd. Increasing it by ONE does
  not change ceil(order/2). The compressed cycle is now simple and the
  partial-suppression lemma applies.
- If only the root survives, adjoining the root to the normal component
  gives a nontrivial side with that single boundary vertex. A nonnil tail
  supplies a vertex on the other side. The existing odd cut-vertex budget
  gives the contradiction.

optimized_odd_zero_component_meets_tail therefore proves, for the SAME
unified certificate and Odd F.order, that every zero-surplus normal component
meets the attached tail. Cycle and tail lengths are unrestricted.
This DOES NOT rule out zero components meeting the tail, does not prove that
a smallest global failure has odd order, and does not settle Gallai.

Both updated/new proof modules compile warning-free. All TEN exact-name axiom
reports in /tmp/odd_tail_component_audit1.log were matched and checked against
OddTailComponentAudit.lean; only permitted axioms. Gap/forbidden-declaration
scans passed. Latest builds: /tmp/lollipop_run_suppression6.log and
/tmp/odd_tail_component4.log. The earlier 26-report audit remains valid for
the original declarations, and the updated suppression declarations were
re-audited in the ten-report batch.

Potential next direction (UNPROVED): compress runs through the TAIL as well
as the cycle, using a long-tail ear exchange at the fixed-cycle tail minimum.
This would require retaining any deleted branching root and terminal tail
endpoint, accounting for the resulting order/ceiling cost, and handling
shortcut privacy across both sets of runs. Do not assume these automatically.
Spec.lean is unchanged and still contains its sole original sorry.

### Long-tail ears and path-run freshness (verified)

LongTailEar.lean proves five lemmas, culminating in no_long_tail_ear. An
arbitrary tail segment can be exchanged with a chord owned by an ordinary
path avoiding the segment's internal vertices. The literal oriented cycle,
root, finish, score and endpoint quotas are retained. The length identity is
  newTail.length + removedSegment.length = oldTail.length + 1.
Thus a fixed-cycle shortest tail has no such long removable ear.

The basic Run, RunIndex, runs, runStart, runFinish and runPath definitions in
CycleRunIntervals.lean were generalized from closed walks to arbitrary walks.
Run.internal_mem and Run.intervals_ordered were generalized too; the cycle-
specific theorems keep their original types. ALL affected downstream modules
were rebuilt in order, not merely reused as stale oleans:
  CycleRunCompression, LollipopRunSuppression, OddTailComponent, LongTailEar.
Their successful logs are /tmp/<Module>_generalized_run.log.

PathRunIntervals.lean proves six analogous path-run lemmas: distinct endpoints,
private interiors, injective shortcuts, absence of shortcut edges in the
original path, and coverage of every inside-incident edge when both path
endpoints remain outside the deleted set. Unlike cycles no extra three-mark
hypothesis is needed for simple paths.
TailRunFreshness.subset_tail_runs_fresh proves that tail-run shortcuts through
a subset of a normal component are fresh in the complementary base graph at
a fixed-cycle shortest tail. This is only freshness, NOT yet a combined
cycle-and-tail suppression theorem.

Builds /tmp/path_run_intervals2.log and /tmp/tail_run_freshness1.log are clean.
All THIRTY-TWO exact reports in /tmp/tail_run_freshness_audit1.log were parsed
and matched against TailRunFreshnessAudit.lean, including the generalized
run declarations. Only permitted axioms; comment-stripped gap/forbidden-
declaration scans passed for all four modules.

Suggested next implementation: combine cycle and tail run compression in two
stages, avoiding a bulky tagged-family certificate. Use deleted interior sets
Sc = cycle.verts ∩ S and St = tail.verts ∩ S; they are disjoint when the root
is retained. Compress cycle runs with base H + tail arcs (supported outside
Sc), then tail runs with base H + cycle chords (supported outside St).
Expand in reverse order. Cross-shortcut freshness follows because the cycle
and tail supports meet only at the retained root and shortcut endpoints are
distinct. Retain the tail finish as well so no dangling suffix is deleted.
Account explicitly for the cost of every retained root/finish/cycle vertex.
This plan is UNPROVED. It still does not eliminate all normal-component
configurations or resolve the full conjecture.

The actual Spec check /tmp/spec_cycle_run_checkpoint.log reports ONLY its
original sorry warning. No complete original proof/disproof has been obtained,
no theorem statement/import was altered, and no submission has been made.

### Combined cycle/tail suppression and connected odd normal remainder (verified)

Four new proof modules compile warning-free:
  RunCompressionData.lean
  TwoRunCompression.lean
  LollipopFullRunCompression.lean
  NormalTerminalBudget.lean

RunCompressionData packages the proven privacy/shortcut properties of path
and cycle runs. TwoRunCompression compresses a pair of run families in two
stages when their carrier walks meet only at a retained vertex, and expands
in reverse order. The deleted interior sets are carrier.verts intersect S.
No shortcut-owner separation is assumed. LollipopFullRunCompression applies
this to a lollipop, retaining root and finish and at least three cycle
vertices. no_compressible_normal_component applies smaller-order induction
and group replacement whenever the EXACT retained-vertex budget permits it.
It does not assume that the deleted subset is the whole normal component.

NormalTerminalBudget.component_terminal_budget is the new counting result.
For any terminal set K containing root, finish, and at least three cycle
vertices, every normal component with support S and p path members satisfies
  |S| + 2*ceil(n/2) + 1 <= n + 2*p + |S intersect K|.
Proof: otherwise delete S\K and apply full run suppression. If S\K were
empty, p>=1 already contradicts the failed inequality. Thus no hidden
nonempty/smaller-order condition is assumed.

A set K of at most FOUR vertices suffices. Component supports are disjoint,
so their terminal intersections sum to at most four. For odd n the normal
support is all vertices (existing min-degree result). Summing the terminal
inequality yields 2*c+1<=4, hence at most ONE normal component.

New exact consequences for the SAME unified optimized certificate:
  odd_normal_components_le_one
  odd_component_members            (each component is all normal indices)
  odd_component_surplus_one        (surplus exactly1; no zero components)
  odd_normal_remainder_connected   (the ordinary-path union is connected
                                    and spans the entire vertex type)
  spanning_even_normal_components_le_two (explicit spanning hypothesis)
This supersedes the weaker odd zero-component-tail-intersection result.
It does NOT rule out a connected spanning normal remainder in odd order.
It also does not prove that a smallest global failure has odd order.

All TWENTY-TWO exact reports in /tmp/normal_terminal_budget_audit2.log were
matched against NormalTerminalBudgetAudit.lean; only propext,
Classical.choice, Quot.sound. All four modules passed comment-stripped
proof-gap/forbidden-declaration scans. Successful builds:
  /tmp/run_compression_data2.log
  /tmp/two_run_compression1.log
  /tmp/lollipop_full_run_compression1.log
  /tmp/normal_terminal_budget4.log

The original conjecture remains unresolved; Spec.lean remains unchanged.

### Even-order two-component bound without spanning (verified)

EvenNormalTerminalBudget.lean removes the spanning guard from the even-order
normal-component bound. The SAME optimized certificate already has at most
one missing normal vertex; it lies on the cycle or is the tail finish. Choose
the four-terminal set to contain that vertex as well as root, finish, and
three cycle vertices. The exact sum of component terminal intersections is
|normalSupport intersect K|, and normalSupport union K is all vertices.
Summing component_terminal_budget therefore yields c<=2 in even order,
even when one vertex is absent from the normal remainder.

Five lemmas:
  four_terminals_at_cycle_vertex
  normal_complement_at_most_one
  four_terminals_cover_missing
  terminal_intersections_sum_eq
  even_normal_components_le_two
Build /tmp/even_normal_terminal_budget2.log is warning-free. All FIVE exact
reports in /tmp/even_normal_terminal_budget_audit1.log were parsed/matched
against EvenNormalTerminalBudgetAudit.lean and checked: permitted axioms only.
The source passed the comment-stripped proof-gap/forbidden-declaration scan.

Current strongest normal-component reduction:
  ODD order: one connected spanning ordinary-path remainder, component
             surplus exactly1 (all earlier odd zero-component cases excluded).
  EVEN order: at most two normal components, with at most one missing vertex.
These are reductions, NOT a contradiction. The odd connected spanning case
can still have unbounded cycle and tail lengths. No argument has made a
smallest global failure odd, and no general endpoint-marking theorem for
this connected remainder has been proved.

Potential strategic pivot: the connected odd remainder has n=2p+1 supported
vertices and minimum path number p=(n-1)/2. The old low-degree unmarkability
question (at most one unmarkable vertex of degree<2p) may be relevant, but
remains unproved; DO NOT assume it. The broader claim of at least2p markable
vertices is FALSE (K7 minus a triangle, with three Hamilton paths, has only
three markable vertices). Mere connectedness does not justify arbitrary
endpoint-pair changes or path avoidance.

Latest actual submission check /tmp/spec_normal_terminal_checkpoint.log has
only the expected original sorry warning. Spec.lean is unchanged (24 lines,
original import, original statement, sole sorry); no complete proof/disproof
and no completed submission. No builds remain running.

### Critical remainder edges and universal short-tail root obstruction (verified)

Two new development modules compile warning-free:
  NormalRemainderCritical.lean (13 declarations including 3 abbreviations)
  UniversalNormalEndpoints.lean (6 lemmas)
Latest successful logs:
  /tmp/normal_remainder_critical2.log
  /tmp/universal_normal_endpoints2.log

For the SAME UnifiedMinimalDefect.OptimizedDefect D of F.graph, set
  H = selectedGraph D.family (univ.erase D.rep.index),
  p = (univ.erase D.rep.index).card = budget F.order - 1.
NormalRemainderCritical proves:
- H admits an exact p-path partition with nonempty members;
- every H path partition has at least p members;
- either root-cycle edge raises the p-path budget if added to H;
- the final tail edge likewise raises the p-path budget;
- those edges are absent from H (derived using the exact partition);
- in odd order, n=2*p+1 and H is connected;
- if the optimized tail has length<=1, the root is UNMARKABLE in EVERY
  optimal p-path partition of H, not merely in the chosen family.
The last statement replaces the whole normal group via
GroupActivation.replace_path_group_tracked, retains the literal lollipop
and score, and applies the unrestricted-cycle endpoint rotation theorem.
No quota-energy compatibility is required or asserted.

UniversalNormalEndpoints proves for ANY path TrailFamily U of H of size p:
- all its members are nonnil (otherwise the normal group saves a slot);
- for a tail of length<=1, no member starts or ends at the root;
- consequently the root endpoint quota is zero;
- deg_H(root)+3=deg_G(root);
- at least one U-member avoids the root in all orders;
- at least TWO U-members avoid the root in odd order.
The last counts use the exact degree/quota/avoidance identity and the simple
ambient degree bound. They do not assume markability or any exchange theorem.

NormalRemainderCriticalAudit.lean contains 19 exact axiom reports, including
all abbreviations. /tmp/normal_remainder_critical_audit1.log was parsed and
matched against the exact expected names and count; every report uses only
propext, Classical.choice, Quot.sound. Both sources passed comment-stripped
proof-gap/forbidden-declaration scans.

Lean pitfall encountered: Fintype.card of AvoidIndex can elaborate with
extensionally equal but computationally different Fintype instances. Rewrite
both the incidence hypothesis and goal using <-Nat.card_eq_fintype_card
before omega. The reversal nil lemma is Walk.nil_reverse, not nil_reverse_iff.

Mathematical status is unchanged: these universal restrictions are necessary,
not a contradiction. Root unmarkability and two root-avoiding paths can coexist
in connected graphs; a repair theorem using the additional critical-edge and
lollipop data is still missing. Longer tails and the even-order configurations
also remain. No full proof/disproof has been obtained. Spec.lean is unchanged
and retains its original sole sorry. No completed proof has been submitted.

### Universal critical-edge endpoint capacity (verified)

CriticalEndpointCapacity.lean and ShortTailCriticalStar.lean compile
warning-free. Their latest successful logs are:
  /tmp/critical_endpoint_capacity7.log
  /tmp/short_tail_critical_star4.log

CriticalEndpointCapacity defines EdgeCritical H p r x to mean that H+rx
has no p-path partition. For ANY path TrailFamily T of H with p slots:
- a critical edge is absent from H;
- any member ending at x must contain r (else append rx using the already
  proved DeletionEndpoint.append_new_edge_tracked and keep p paths);
- for a finite set X not containing r, if every rx is critical, then
      sum_{x in X} T.quota x <= deg_H(r).
This is stronger than merely recording which endpoints are forbidden.
Proof: a path with an X-endpoint contains r. Its number of X-endpoints is
at most its local degree at r, by exact path incidence and r notin X. Sum
these inequalities over all members. Thus the number of odd-degree vertices
in such an X is also bounded by deg_H(r).
The module specializes the endpoint containment to either root-cycle edge
and the final tail edge of the unified certificate. No optimization of T
or endpoint-flexibility assumption is used.

ShortTailCriticalStar applies the bound to the THREE DISTINCT ports
  cycle.snd, cycle.penultimate, tail.finish
when the optimized tail has length exactly1. All three missing root edges
are critical, with the tail edge obtained by symmetry. For EVERY optimal
normal path family T:
  quota(cycle.snd)+quota(cycle.penultimate)+quota(tail.finish)+3
      <= deg_G(root).
This has NO cycle-length bound. If all three port degrees in the normal
remainder are odd, the root degree is at least7 (the root is odd by the
existing unrestricted-minimum one-edge-tail quota-one lemma). If the ambient
root is cubic, ALL THREE port quotas are zero in every such T, and their
normal-remainder degrees are even. These are guarded consequences, not a
claim that all three ports must be odd or that cubic cases are eliminated.

CriticalEndpointCapacityAudit.lean prints all TWENTY exact declarations,
including the two definitions/abbreviations. Its log
  /tmp/critical_endpoint_capacity_audit1.log
was parsed and matched against exact names/count; only propext,
Classical.choice, Quot.sound. Both sources passed comment-stripped scans
for proof gaps and forbidden declaration mechanisms. No builds remain.

A new literature fetch from erdosproblems.com failed DNS resolution. No
external theorem was retrieved or assumed. The connected near-saturated
remainder marking candidate is still unproved; the old biconnected and
block-attachment diagnostics were reviewed, not promoted to theorems.

Potential structural continuation, NOT YET FORMALIZED: in the spanning
EVEN-order case with exactly TWO normal components, the terminal budget
inequality is sharp for every four-element K consisting of root, finish,
and two other cycle vertices. If the cycle has length>=4, comparing pairs
of nonroot cycle vertices should show that each component either contains
ALL nonroot cycle vertices or NONE. This follows from equality in the sum
of the two component inequalities; it does not follow when a missing normal
vertex is ignored. Even with the stated spanning guard, this would still
leave several surplus/root/finish configurations and is not a contradiction.

Original status: no complete proof/disproof. Spec.lean is unchanged, with
the same import and theorem statement and the sole original sorry. No
completed proof was submitted.

### Equality and cycle concentration in the even two-component case (verified)

New warning-free modules:
  EvenTerminalEquality.lean (99 lines)
  EvenTwoComponentShape.lean (287 lines)
Latest successful logs:
  /tmp/even_terminal_equality3.log
  /tmp/even_two_component_shape6.log

Namespaces Erdos583EvenTerminalEqualityDevelopment and
Erdos583EvenTwoComponentShapeDevelopment. Local abbreviations:
  NormalComponent F D,
  componentSupport F D A,
  surplus F D A (noncomputable, the existing componentSurplus).

EvenTerminalEquality proves the exact version of the four-terminal budget.
Suppose order is EVEN, the SAME optimized certificate has exactly TWO normal
components, K contains root, finish, and at least three cycle vertices, K has
size<=4, and K contains every missing normal vertex. Then for each component A:
  surplus(A)+1 = |support(A) intersect K|,
and |K|=4. SPANNING IS NOT REQUIRED if the explicit missing-vertex covering
condition holds. The proof sums the nonnegative component inequalities and
uses the exact support/member sums and |N union K|=n.

EvenTwoComponentShape REMOVED the initially planned spanning guard entirely
for cycles of length>=4. Existing free_cycle_minimum_structure gives degree
at least3 at all cycle vertices in this branch. A nonroot cycle vertex absent
from the normal support would satisfy the missing-incidence identity
  degree(v)+quota(v)=2,
a contradiction. Hence every nonroot cycle vertex belongs to the normal
support, and all missing normal vertices are among {root,finish}. Therefore
EVERY allowed four-terminal choice covers the missing vertices.

Comparing K={x,root,z,finish} and K'={y,root,z,finish}, with z a third nonroot
cycle vertex, in the exact terminal equality shows:
- each normal component contains ALL nonroot cycle vertices or NONE;
- there is a component A containing all nonroot cycle vertices;
- every other component avoids them;
- an off-cycle component B satisfies
    surplus(B)+1 <= |support(B) intersect {root,finish}|;
  it has surplus<=1 and contains root or finish;
- A cannot contain BOTH root and finish;
- if an off-cycle component misses either terminal then its surplus is0;
- by the prior zero-component doubling bound its support then has size>=n/2;
- if the cycle component A contains either root or finish, |support(A)|<=n/2.
These statements permit unbounded cycle/tail lengths (cycle length>=4 is the
explicit guard for concentration). They are NOT an elimination of the two-
component case. The triangular case, configurations with both terminals
outside A, and the remaining terminal-split configurations are still open.

EvenTwoComponentShapeAudit.lean prints all TWENTY-THREE exact declarations,
including the three abbreviations. /tmp/even_two_component_shape_audit1.log
was parsed/matched against exact names and count. Only propext,
Classical.choice, Quot.sound. Both sources passed comment-stripped scans for
proof gaps and forbidden declarations. No builds are running.

A possible next repair, NOT FORMALIZED OR ASSUMED: in the spanning even two-
component case where the cycle component A contains root and B contains
finish, B has zero surplus and A has at most half the vertices. Remove B,
compress all complete tail runs through B, and remove the final dangling tail
suffix after its last A-vertex w. The compressed graph on A includes the whole
cycle and has target budget p_A+1=|A|/2. If |A|<n/2, the existing doubled-bridge
marked theorem can mark w at that budget. Append the private dangling suffix,
then expand the other private tail runs, and restore B's p_B paths. This would
exclude that strict-half configuration. The current RunConditions.expand
cannot be used blindly: its interior set includes the dangling suffix if
applied to the whole original tail. One needs prefix-run freshness and an
expansion base avoiding those prefix interiors, or an explicitly tracked
interior set. Marked private-tail extension itself can be obtained by first
appending a fresh edge to the isolated finish and then expanding that edge.
The half-order equality boundary also needs global edge-count control; no
unchecked comparison of the compressed edge count has been made.

The original conjecture is STILL unresolved. Spec.lean is unchanged (same
import and statement, sole original sorry). No complete proof/disproof or
completed submission has been obtained.

## Marked terminal suppression (verified continuation)

The two pending modules `MarkedPrivateTail` and `TailPrefixRunFreshness` now
compile. New modules `MarkedPrefixRunCompression`, `MarkedTailSuppression`,
and `TwoComponentTerminalSuppression` also compile. Axiom audits
`MarkedPrivateTailAudit` and `TerminalSuppressionAudit` give 13 exact reports,
all parsed and checked against the allowed three axioms; gap scan passed.

The generic marked prefix-run partition marks the compressed core, appends
the private final suffix, and then expands the prefix runs. Privacy is
proved with the prefix/suffix support intersection, not an owner-separation
assumption. A strict-half criterion excludes a component containing the
finish but no cycle vertex whenever its complement is the support of a
connected retained core and the exact restore budget holds.

`no_strict_half_cycle_component`: two normal components, spanning normal
support, entire cycle in A, finish in B, surplus(B)=0, and 2|A|<n imply
False. The spanning guard is discharged in the application:
`long_cycle_root_component_balanced`: for even n, two normal components,
cycle length>=4, and a component A containing all nonroot cycle vertices
and root, 2|A|=n. The existing missing-vertex theorem supplies spanning;
no extra spanning assumption remains in this final statement.

Logs: `/tmp/marked_private_tail2.log`,
`/tmp/tail_prefix_run_freshness2.log`,
`/tmp/marked_prefix_run_compression1.log`,
`/tmp/marked_tail_suppression3.log`,
`/tmp/two_component_terminal_suppression2.log`,
`/tmp/marked_private_tail_audit1.log`,
`/tmp/terminal_suppression_audit1.log`.

This is still not a Gallai proof. Balanced even two-component configurations,
the other terminal locations, triangle cases, and the odd connected normal
remainder remain. Spec retains the original sole sorry.

## Balanced terminal boundary (verified continuation)

New verified modules:
- `RunEdgeCount.lean`: exact private-run arc and chord edge counts;
  compression saves at least the number of complete runs.
- `PrefixCompressionEdgeCount.lean`: selected/complement edge-count identity,
  and an additional saving of the private final suffix length.
- `TerminalCoreObstruction.lean`: the compressed terminal core cannot have a
  marked ceiling-budget partition at the suffix join vertex. Also records
  its support/connectivity and the zero-component restore budget.
- `BalancedTerminalBoundary.lean`: at the half-order boundary, a last-hit
  split has suffix length exactly1 and no complete prefix runs. The retained
  core and the deleted normal component have equal edge counts.

`MarkedPrivateTail` now also lifts the half-order/fewer-edges marked theorem.
`MarkedPrefixRunCompression` now factors the expansion through the generic
`prefix_run_partition_of_marked`, with the original strict-half theorem as a
wrapper. Its original statement is unchanged. All affected dependent modules
were rebuilt successfully.

Strongest new result:
`Erdos583BalancedTerminalBoundaryDevelopment.long_cycle_root_component_bridge`.
Assumptions: F minimal failure, D unified optimized defect; even order;
exactly two normal components; cycle length>=4; A contains all nonroot cycle
vertices AND root. Conclusions: a bridge joins a vertex of A to the tail
finish, it is the unique edge crossing the cut support(A), |A| is even,
G has odd edge count, and 4 divides the order. No independent spanning guard
is needed. The earlier balanced theorem still gives 2|A|=n. This is a
bridge reduction, NOT an impossibility proof.

Edge-count argument at equality: write m_B for the deleted component,
m_H for its complement, m_J for the compressed core, and q,r for suffix
length and run count. Verified bounds are
  m_G=m_B+m_H, m_G<=2*m_B+1, m_G<=2*m_J+1,
  m_J+r+q<=m_H, q>=1.
Thus q=1, r=0, m_J=m_B, m_H=m_B+1.

Latest clean build logs:
`/tmp/run_edge_count3.log`, `/tmp/prefix_compression_edge_count2.log`,
`/tmp/terminal_core_obstruction1.log`,
`/tmp/balanced_terminal_boundary4.log`,
`/tmp/marked_private_tail_half1.log`, `/tmp/marked_prefix_general1.log`.

Axiom audits: `/tmp/balanced_terminal_boundary_audit1.log` (20 exact reports,
matched to `/tmp/balanced_terminal_audit_expected.json`), plus rerun
`/tmp/terminal_suppression_audit2.log` (8) and
`/tmp/marked_private_tail_audit2.log` (5). All 33 reports parsed; only the
three allowed axioms occur. The new development files pass gap scans.
No builds are pending or running at this checkpoint.

Actual `Submission/Spec.lean` remains unchanged with the original sole
sorry. `/tmp/spec_balanced_terminal_checkpoint.log` confirms only its
expected sorry warning. The original conjecture is still unresolved. In
particular, the balanced bridge configuration is not excluded, and neither
are the other terminal configurations or the odd connected remainder.

## Balanced bridge is the one-edge tail (verified continuation)

`Submission/TailBridgeLocation.lean` compiles cleanly. On rechecking the
older development, the general parity/bridge tail-shortening argument was
already present in `ShortestTailBridges.lean`; the final new file reuses it
rather than retaining a duplicate proof.

Four results:
- `length_one_walk_eq` represents a length-one walk as a single cons edge.
- `tail_last_bridge_length_one` packages the existing bridge theorem for
  the unified optimized witness.
- `balanced_terminal_root_bridge`: under the explicit spanning two-component,
  cycle-in-A, finish-in-B, zero-B, and half-order assumptions from
  `balanced_terminal_split`, the tail has length1 and root--finish is a bridge.
- `long_cycle_root_component_one_tail`: discharges those extra guards in the
  even-order/two-component/long-cycle/root-in-cycle-component case. Its only
  structural hypotheses are exactly those of
  `long_cycle_root_component_balanced`; no separate spanning guard remains.

This tightens, but does not exclude, the previous balanced bridge residual.
In particular, an arbitrary marked ceiling-budget decomposition at the
boundary vertex of an even-order side is still not available. Ordinary
smaller-order Gallai partitions do not supply that mark. No unproved
endpoint-flexibility assertion has been used.

Build: `/tmp/tail_bridge_location3.log` (clean).
Audit: `Submission/TailBridgeLocationAudit.lean`,
`/tmp/tail_bridge_location_audit1.log`. Four exact reports were parsed and
matched to their names; only permitted axioms occur. Gap scan passed.
The earlier `/tmp/tail_bridge_location1.log` and `2.log` concern a superseded
duplicate implementation, not the final file.

Spec is unchanged. `/tmp/spec_tail_bridge_location_checkpoint.log` shows
only the original sorry warning. No complete proof or disproof has been
obtained, and no build is pending at this checkpoint.

## Fixed normal-remainder energy (verified checkpoint)

`Submission/FixedRemainderEnergy.lean` and its audit compile. The latest clean
logs are `/tmp/fixed_remainder_energy4.log` and
`/tmp/fixed_remainder_energy_audit1.log`; all 13 expected axiom reports matched
`/tmp/fixed_remainder_energy_audit_expected.json` and use only permitted axioms.

The energy optimum is external: the graph `remainder F D` and the slot budget
are held fixed. No global quota-energy minimum is added to `OptimizedDefect`.
The module proves existence, a general pair-energy identity, the terminal-edge
pair slide, and its orientation-independent quota bound. An energy-improving
slide must be blocked; if all members ending at a contain x, then
`2*quota(a) <= degree(x)+quota(x)`. In particular, a terminal edge from a to a
zero-quota vertex of degree at most5 forces quota(a)<=2. The terminal-edge
condition is essential and cannot be replaced by arbitrary adjacency.

For odd order and tail length<=1, one may choose an energy-minimal normal
family which is nonnil in every slot, has root quota0, and has at least two
root-avoiding members. This does not yet imply a contradiction, unrestricted
marking, or quotas<=2. Spec remains unchanged with its original sorry.

## Weighted fixed-remainder optimum and universal endpoint closure

Two new external modules compile warning-free:
`WeightedRemainderEnergy.lean` and `UniversalEndpointClosure.lean`.
Neither changes Spec or the unified optimized-defect certificate.

The weighted module first minimizes quota-square energy, then the natural
potential `sum_v weight(v)*quota(v)` among equal-energy path families of the
SAME fixed graph and slot budget. Existence is by two applications of Nat.find.
For an available terminal-edge pair slide from a to x it proves
  quota(a) <= quota(x)+2,
  quota(a)=quota(x)+2 -> weight(a)<=weight(x).
Thus if quota(a)>=quota(x)+2 and weight(x)<weight(a), all members ending at a
must contain x, and
  2*quota(a)<=degree(x)+quota(x),  quota(x)+4<=degree(x).
The secondary optimum can be chosen for the normal remainder using distance
from the root. In the odd/short-tail case it simultaneously retains nonnil
members, root quota0, and at least two root-avoiding members. This is only a
local obstruction: no argument rules out all of these conditions together.

The universal-closure module extracts an orientation-independent pair slide
that preserves every other member's subgraph. If x has quota0 in EVERY fixed-
slot path family, then a terminal edge a-x forces every member ending at a to
contain x. There is NO quota-gap hypothesis and NO energy optimum in this
statement. For a nonnil family, 2*quota(a)<=degree(x). For the short-tail normal
remainder, this yields 2*quota(a)+3<=degree_G(root) whenever a-root is terminal
in its owning member. Mere adjacency still does not suffice.

Clean builds: `/tmp/weighted_remainder_energy1.log`,
`/tmp/universal_endpoint_closure3.log`.
Audits: `/tmp/weighted_remainder_energy_audit2.log` (11 exact declarations),
`/tmp/universal_endpoint_closure_audit1.log` (5 exact declarations), matched to
the corresponding `_audit_expected.json` files. All16 reports were parsed,
matched in order, and use only propext, Classical.choice, Quot.sound. Both new
sources passed gap scans. The first closure build failed only at the final
simp of an if-True expression; the verified version uses ordinary simp.

The root-distance tie-breaker does not provide endpoint flexibility, all
quotas<=2, or a contradiction. The balanced one-edge bridge, odd connected
normal remainder, and other unbounded cycle/tail cases remain unresolved.
Actual Spec remains the unchanged 24-line original conjecture with its sole
sorry. No completed proof or disproof has been obtained or submitted.

## Global tail minimum across roots and cycle-endpoint tail exchange

New verified modules: `GlobalTailDefect.lean` (112 lines) and
`GlobalTailExchange.lean` (92 lines). The old `OptimizedDefect` is unchanged.

`GloballyTailOptimized G` extends it with a compatible stronger comparison:
for EVERY root s, same-score family U, and rooted representation M with
`M.cycle.length = D.rep.cycle.length`, one has
`D.rep.tail.length <= M.tail.length`. This compares cycle LENGTH, not literal
oriented cycle equality. Existence first minimizes cycle length globally,
then tail length over ALL roots with that cycle length. Invoking the old
joint carrier optimum preserves the chosen tail length: the old fixed-cycle
minimum and the new global minimum give opposite inequalities. No quota-
energy minimum is added. All old certificate consequences remain available
through `D.toOptimizedDefect`.

New APIs in Erdos583GlobalTailDefectDevelopment:
- exists_global_cycle_tail_carrier_optimum
- minimal_failure_has_global_tail_optimum
- failure_has_global_tail_certificate
- GloballyTailOptimized.anchor_length_le_of_cycle_le
- GloballyTailOptimized.no_shorter_tail_at_minimum_cycle
The last two only compare the stated lexicographic objective; they do NOT
assert a global minimum of total anchor length before minimizing cycle length.

`exchange_tail_at_cycle_endpoint` takes a normal member P beginning at s on
C and meeting C ONLY at s. Rotate C to s, replace the old lollipop C+tail and
P by the new lollipop (rotated C)+P and the old tail as an ordinary path.
The indexed family keeps its score, cycle length, and all other subgraphs;
its new tail has length P.length. P need NOT avoid the old tail in vertices:
edge disjointness comes from the original partition. This is not a license
to reroot an open lollipop without exchanging its tail.

Consequences:
- GloballyTailOptimized.tail_le_one_touch_member
- one_edge_cycle_carrier_forces_one_tail
The second rules out longer tails whenever a one-edge normal member has one
endpoint on the cycle and the other outside it. The existence of such a
member is NOT proved and must not be assumed.

Builds: `/tmp/global_tail_defect1.log` and `/tmp/global_tail_exchange2.log`,
both clean. Audit: `GlobalTailDefectAudit.lean`,
`/tmp/global_tail_defect_audit1.log`; all8 exact reports matched
`/tmp/global_tail_defect_audit_expected.json` and use only the allowed axioms.
Both sources passed gap scans. No build remains pending.

The terminal-weight quantitative route was also reviewed. The already
refuted absolute-maximum exposure assertion has NOT been revived; neither
a threshold-preserving augmentation nor a uniform terminal-deficit bound
was proved. No new endpoint-flexibility premise has been used.

Actual Spec is unchanged: 24 lines, original statement/import, sole original
sorry. `/tmp/spec_global_tail_checkpoint.log` has only the expected sorry
warning. This continuation does not settle erdos_583 and no completed proof
or disproof has been submitted.

## Whole-member cycle ears: verified exchange, then a stronger exclusion

New external modules, not inlined into Spec:
- `GlobalCycleEar.lean` (201 lines): two disjoint simple paths with only their
  distinct ends in common form a cycle; whole-normal-member ear exchange;
  its cycle/tail length comparison; the two-edge triangle specialization.
- `CyclePrefixEndpointObstruction.lean` (113 lines): cycle-arc intersection,
  endpoint-prefix obstruction, two-sided visits for a root-avoiding endpoint,
  whole-ear exclusion, and one-touch cycle-endpoint exclusion.

For C=(A+B)+E based at r, with distinct cuts s,t, and a whole ordinary member
P:s->t meeting C only at s,t, the exchange constructs cycle P+reverse(B),
tail reverse(A), and ordinary path E+oldTail. It preserves the score, and its
new lengths are |P|+|B| and |A|. Reversing C gives the symmetric comparison.
The global certificate therefore implies |A|+|E|<=|P|; at equality, old tail
length<=min(|A|,|E|). All these proofs compile and have permitted axioms.

IMPORTANT COURSE CORRECTION: this is NOT a surviving minimal-failure branch.
The already existing `CyclePrefixRepair.cycle_prefix_exchange` gives a
STRONGER repair: A+P and (B+E)+oldTail are two simple paths covering the old
lollipop and P. P may intersect oldTail; those intersections are between the
TWO resulting paths and cause no issue. `maximum_no_whole_cycle_ear` now
formalizes the resulting contradiction under maximum score and one defect,
WITHOUT a cycle or tail minimum. Thus the triangle two-edge-ear corollary
only describes a configuration already impossible, not new progress on the
unresolved cases. Do not pursue this whole-member ear as an active route.
An interior ear does not have this property: its two outside arms remain.

The same correction applies to the previous one-touch-tail-exchange route.
`maximum_no_one_touch_cycle_endpoint` excludes EVERY whole ordinary path
starting on C and meeting C only at that endpoint. If the endpoint differs
from r, prefix repair absorbs it; if it equals r, the earlier shared-start
neighbor lemma forces a second cycle vertex. Consequently the earlier
one-edge-cycle-carrier tail-length consequence is also vacuous in a maximum
one-defect family. No existence of such carriers was ever proved or assumed.

The genuinely useful generic endpoint restriction is explicit now: for a
path starting at a nonroot cycle vertex s, every r-to-s cycle arc meets that
path somewhere besides s. If the path avoids r, it has distinct further
visits on BOTH arcs. This is a necessary restriction, not a contradiction;
it is consistent with the older group-boundary marking obstructions.

Builds: `/tmp/global_cycle_ear5.log` and
`/tmp/cycle_prefix_endpoint_obstruction2.log`, both clean.
The four GlobalCycleEar axiom reports were matched exactly in
`/tmp/global_cycle_ear_audit2.log` against
`/tmp/global_cycle_ear_audit_expected.json`. All use only the permitted axioms.
The endpoint module audit is `CyclePrefixEndpointObstructionAudit.lean`;
its final five-declaration audit is recorded below after compilation.

Actual Spec is still the unchanged 24-line conjecture with the original sole
import, unchanged theorem type, and sole original sorry. The check at
`/tmp/spec_cycle_prefix_endpoint_checkpoint.log` shows only that sorry warning.
The odd connected normal remainder, balanced even bridge, and unbounded
cycle/tail cases remain unresolved. No complete proof or disproof exists.

Final endpoint audit completed cleanly: `/tmp/cycle_prefix_endpoint_obstruction_audit2.log`. All five exact reports matched `_audit_expected.json`, use only the permitted axioms, and both new sources passed gap scans. No build remains pending.

## Critical-edge parity and the odd degree-five one-tail marking obstruction

New verified external module: `Submission/CriticalEvenParity.lean` (220 lines),
namespace `Erdos583CriticalEvenParityDevelopment`. It does not change Spec.

Generic results:
- Adding a missing edge c-x in a one-even graph, with c the unique even
  vertex, moves the unique even label to x. The existing sharp one-even
  partition shows this edge is NOT critical whenever n<=2p+1.
- Adding a missing edge between two even vertices decreases evenCount by2.
  Thus, if n=2p+1 and H admits p paths, a critical even-even missing edge
  forces evenCount(H)>=5. With three even vertices the augmented graph
  would have just one and would admit p paths.
- For a nonnil p-path family and a critical missing edge r-x,
      2*quota(x) <= degree_H(r)+quota(r).
  This is an individual-endpoint bound, distinct from the old sum over
  critical neighbors. It follows by applying the existing endpoint-
  containment capacity theorem, not by imposing a quota-energy optimum.
- A missing edge r-x with r!=x gives degree_H(x)+2<=n.
- Universal zero quota in all fixed-slot path families implies failure of
  the corresponding MarkedPartition property.

Application to the SAME optimized minimal-failure certificate:
`odd_one_tail_degree_five_marking_obstruction` assumes odd order, tail
length1, and original root degree<=5. Odd minimum-degree restrictions force
that degree to be exactly5, so the normal remainder H has root degree2.
The three critical ports cannot all be odd: their quota/degree capacity
would force original root degree>=7. Choose a fixed even port x. In EVERY
optimal remainder family, root quota=0 and 2*quota(x)<=2. Parity forces
quota(x)=0 as well. Consequently the theorem supplies:
- H connected, n=2p+1 as already established, and evenCount(H)>=5;
- x!=root, degree_H(root)=2;
- both root and x have degree<2p;
- neither root nor x is markable in ANY p-path partition of H.
No bound on cycle length is assumed. This extends the explicit marking
obstruction to the odd degree-five one-tail branch, not just the older
cubic/even-order branch.

THIS IS STILL NOT A CONTRADICTION. The candidate assertion excluding two
low-degree universally unmarkable vertices in a connected saturated odd
remainder remains unproved, even in the special case where one has degree2.
The broad n-2p unmarkability bound remains false and is not being used.
Likewise, the one-even nonbridge unoriented-edge-exposure question was
re-examined but not proved: the protected receiver and the unique inactive
vertex can still block the two available exits. No exposure claim was added.

Build: `/tmp/critical_even_parity5.log`, warning-free.
Audit: `Submission/CriticalEvenParityAudit.lean`,
`/tmp/critical_even_parity_audit1.log`. All11 exact declarations matched
`/tmp/critical_even_parity_audit_expected.json`; every dependency is among
propext, Classical.choice, Quot.sound. The source passed the gap/forbidden-
declaration scan. No build remains pending.

Actual Spec remains unchanged: original import and conjecture type, sole
original sorry. `/tmp/spec_critical_even_parity_checkpoint.log` shows only
that expected warning. No complete proof or disproof has been obtained.

## One-edge-tail bypass and critical degree-two carrier (verified)

New external files:
- OneTailBypass.lean: two lemmas, namespace Erdos583OneTailBypassDevelopment.
- CriticalRootCarrier.lean: eight lemmas, namespace
  Erdos583CriticalRootCarrierDevelopment.
- OneTailBypassAudit.lean: all ten exact declarations audited.

The previously proposed tail-bypass surgery is now proved. Write the anchor
cycle as r-s followed by R:s->r, with tail the single edge r-t, t off the
cycle. If an ordinary path P contains edge s-t and avoids r, expand that
edge in P to s-r-t. The other new path is t-s followed by R. Both paths
are simple, are edge-disjoint, and cover precisely the old anchor-plus-P
edge union. Hence maximum one-defect score forbids such a root-avoiding
owner of s-t. No cycle-length or quota-energy minimum is needed for this
local absorption. It is not the rejected whole-member ear configuration.

The obstruction is transported to EVERY optimal fixed-slot path partition
of the ordinary remainder by replace_path_group_tracked, preserving the
literal anchor and maximum score. Thus every member containing a cross-edge
from a root-cycle neighbor to the one-edge tail finish also contains root.

Generic critical-edge consequences, now proved:
- In any all-path family, degree(r)=2 and quota(r)=0 imply a UNIQUE member
  contains r.
- For nonnil members, every critical missing r-x has quota(x)<=1; its quota
  is zero for even x and one for odd x.
- Every positive-quota critical neighbor is an endpoint of the unique
  root carrier.
- If two distinct critical neighbors have positive quota, any member owning
  the edge between them AVOIDS root: their unique endpoint carrier cannot
  contain its endpoint-to-endpoint edge while also containing r internally.

Application one_tail_odd_cross_ports_not_adj: in a minimal-failure
certificate with a one-edge tail and original root degree FIVE, if a cycle
neighbor s and tail finish t both have ODD degree in the normal remainder,
then the ORIGINAL graph has no edge s-t. This holds without an odd-order
assumption. The root's remainder degree is two. Any putative s-t edge is
outside the anchor, so a normal member owns it. Bypass forces that owner
to contain root, while critical endpoint locking forces it to avoid root.
The stated cycle neighbor is represented as the first vertex of a chosen
oriented cycle; reversing the cycle gives the other neighbor. No analogous
claim for the pair of two cycle neighbors has been proved here.

These are additional necessary restrictions, NOT an exclusion of all
minimal-failure configurations. In particular, no general marking theorem,
bridge elimination, longer-tail reduction, or full Gallai proof follows.

Builds: /tmp/one_tail_bypass3.log and /tmp/critical_root_carrier8.log (clean).
Audit: /tmp/one_tail_bypass_audit2.log (clean); exact expected names in
/tmp/one_tail_bypass_audit_expected.json. All ten reports were parsed and
matched, with only propext, Classical.choice, Quot.sound. Gap scan passed.
No builds or diagnostics are pending.

Spec remains the unchanged 24-line conjecture file, its original sole
import and theorem statement intact, and its original sole sorry present.
The actual Spec build /tmp/spec_one_tail_bypass_checkpoint.log contains
only that expected sorry warning. No proof/disproof has been submitted.

## Structural marking-route recheck (no new theorem)

External literature access was attempted via erdosproblems.com/583 and the
Wikipedia page for Gallai's path-decomposition conjecture. Both failed with
DNS resolution errors; no external theorem was obtained or relied upon.

Re-examined the unproved odd saturated marking assertion using bridge
corridors, rather than treating degree two alone as a source of flexibility.
A degree-two cut vertex can indeed be universally unmarkable in a minimum
path partition: if two paths ended there on opposite sides, merging them
would lower the path count. Two odd cliques joined by a two-edge bridge
corridor give sharp odd-order examples with that middle vertex unmarkable.
This does NOT refute the candidate that there is at most one low-degree
unmarkable vertex at n=2p+1.

A more targeted candidate uses A=K3 joined to I4, a triangle B, and a
2-edge corridor from a hub of A to a vertex of B. The order is 11. Trying
to force a SECOND unmarkable hub runs into a concrete simultaneous-marking
partition of A into four paths. Quotas at its three hubs are (2,2,0), and
each independent vertex has quota1:
  3-0-1-4-2-5;
  4-0-5-1-3-2-6;
  0-2-1;
  0-6-1.
The exact diagnostic /tmp/odd_marked_corridor_core.py verified simplicity,
edge disjointness, complete edge coverage, and the endpoint quotas. Log:
/tmp/odd_marked_corridor_core.log. This is only a finite structural check,
not a Lean proof or a Gallai counterexample search. It refutes this proposed
obstruction to simultaneous marking, not the general marking assertion.

Other rechecked routes remain blocked:
- An even-order graph whose prescribed vertex cannot be marked at n/2
  paths yields the balanced-bridge obstruction upon doubling. The existing
  MarkedDouble/bridge results do not supply a proof of that marking claim.
- Minimizing total anchor size or tail length first is NOT interchangeable
  with the current unrestricted shortest-cycle optimum. Root endpoint
  rotation can preserve anchor size while increasing cycle length and
  decreasing tail length. No incompatible optima have been combined.
- A degree-two normal root alone does not justify a new endpoint-repair or
  missing-edge-addition theorem at the sharp odd budget.

No new Lean assertion was added in this recheck. Spec still contains its
original sole sorry. The prior ten-declaration bypass/carrier checkpoint
remains verified; no complete proof/disproof has been obtained or submitted.

## Critical-edge/marking exchange recheck (no new theorem)

Re-examined whether the critical missing edge between the inactive degree-two
root and an even port can activate an endpoint pair without a general marking
claim. The parity calculation is valid: at n=2p+1, adding an even-even edge
increases the odd count by two, so a p-path repair must consume an existing
surplus endpoint pair. The current endpoint-slide lemmas do NOT establish
that this pair can reach the two specified inactive vertices. Terminal-edge
ownership and path-avoidance conditions cannot be dropped.

The attempted repair through merging ordinary paths can create INTERNAL
repetitions, rather than a rooted defect. Existing forest-zero normalization
requires a HasRoot witness (and its stated baseline-forest hypothesis).
Neither a new rootification theorem nor a compatible zero-forest witness
was obtained. The previous counterexamples to unrestricted rootification
remain relevant; no rootification assumption was added.

Also rechecked a mixed path/cycle route. Work.normal_path_cycle_decomposition
provides paths with the odd-vertex endpoint quotas but NO bound on the number
of cycles. It cannot be used as Lovasz's bounded mixed-decomposition theorem.
In fact, demanding both these exact odd endpoint quotas and a general n/2
mixed count would, for odd-order Eulerian graphs, imply the corresponding
Hajos cycle-decomposition bound. Thus that stronger intermediate assertion
must not be treated as an available elementary lemma.

No new Lean lemma, normalization premise, or literature theorem was added.
The original conjecture remains unresolved, and Spec retains its original
sole sorry. No completed proof/disproof has been submitted.


## One-tail cycle-boundary checkpoint (verified)

OneTailCycleBoundary.lean compiles and its 14 exact declarations have been
audited: only propext, Classical.choice, Quot.sound. Build log:
/tmp/one_tail_cycle_boundary8.log; audit log:
/tmp/one_tail_cycle_boundary_audit1.log; expected names:
/tmp/one_tail_cycle_boundary_audit_expected.json. Gap scan passed.

At a maximum one-defect trail family with a one-edge tail r-t, an ordinary
root-avoiding member touching the root cycle has two distinct cycle visits,
neither equal to root nor adjacent to root in the cycle subgraph. They are
obtained as first and last visits. If a boundary visit were a cycle neighbor,
the two cycle arcs can be joined with the path arms to give two simple paths
starting at root. The outside vertex t lies on at most one, so attaching r-t
repairs the defect. The analogous split excludes a single cycle visit.

Consequently every ordinary member touching a cycle of length at most four
contains root. With root quota one, member-incidence dominance gives
  degree(v)+quota(v)+1 <= degree(root)
for every nonroot cycle vertex. In an odd-order minimum failure, minimum
degree five and odd root degree force root degree at least seven. Thus an
odd-order, one-tail optimized defect with root degree at most five must have
cycle length at least five. This is a local restriction, NOT a full proof.

Spec recompiled in /tmp/spec_cycle_boundary_checkpoint.log with only its
original sorry warning. Its import and conjecture statement are unchanged.
No completed proof or disproof has been submitted.


## Four visits in a one-tail defect (verified)

OneTailCycleVisits.lean has seven complete declarations (six lemmas and a
cycle-reversal definition), all compiled and axiom-audited. Only propext,
Classical.choice, Quot.sound occur. Build /tmp/one_tail_cycle_visits2.log;
audit /tmp/one_tail_cycle_visits_audit1.log; exact names in
/tmp/one_tail_cycle_visits_audit_expected.json. Forbidden-declaration/gap
scan passed. No changes to the original conjecture.

New stronger boundary exchange: if P=A++B first meets C at x, and X is a
root-to-x cycle arc, X must meet P at a vertex other than x. Otherwise the
opposite cycle arc followed by reverse(A), and X followed by B, are two
simple paths starting at root. The tail endpoint, outside C, lies on at most
one, so the one tail edge can be attached and the defect repaired. Reversal
gives the analogous assertion for the last cycle visit.

Choose distinct first/last visits x,y, orienting C as root--x--y--root.
The first root--x arc gives another hit u, and the last y--root arc gives
another hit v. Cycle simplicity and root avoidance show x,y,u,v are four
DISTINCT vertices. Thus in ANY maximum one-defect family with tail length
one, an ordinary root-avoiding member touching the cycle meets it in AT
LEAST FOUR vertices. No global cycle minimum is used.

For a pentagon these are all four nonroot cycle vertices:
maximum_one_tail_pentagon_avoider_contains. This does not exclude pentagons.
A local labelled-link diagnostic found the nonabsorbable visit pattern
2--1--4--3 around C=(0,1,2,3,4,0) with tail 0--5. Links overlapping cycle
edges must be subdivided in a simple graph. Requiring the path's exterior
arms to remain attached, these patterns defeat two-path replacement;
subdividing the parallel links does not supply a repair. The diagnostic
/tmp/one_tail_pentagon_routes.py and .log are structural checks only, NOT
Lean assumptions and NOT counterexamples to Gallai. No unrestricted local
pentagon absorption has been asserted.

The original theorem remains unresolved, with its sole sorry still in Spec.

### Explicit local obstruction and final four-visit recheck

The link-model obstruction was checked as an ACTUAL simple graph on eight
vertices, not merely a constrained routing model:
  cycle 0-1-2-3-4-0; tail 0-5; ordinary path 2-6-1-4-7-3.
/tmp/one_tail_pentagon_obstruction.py enumerated all 209 distinct simple-path
edge sets (including the empty set) and found no complementary pair covering
all eleven edges; log /tmp/one_tail_pentagon_obstruction.log.

There is also a direct explanation. Any two-path cover has exactly one
endpoint at each odd vertex 0,2,3,5, so the degree-two vertices 6 and 7 can
be suppressed. The two parallel 12 links must lie on different paths, and
so must the two parallel 34 links. Both paths therefore contain all four
vertices 1,2,3,4 and one of each of those links. Edges 14 and 23 cannot be
on the same path, as that would give a four-cycle. The path using 14 already
uses degree two at both 1 and 4 and can use neither 01 nor 04. The other
path would have to use all three edges 01,04,05 at 0, impossible. This is
NOT a Gallai counterexample (its order-eight budget is four), and it is
not used as a Lean assumption. It refutes the unrestricted two-member
one-tail pentagon absorption shortcut.

Clean exact audits rechecked 14 boundary declarations and seven four-visit
declarations. The boundary audit now includes its module docstring and is
warning-free: /tmp/one_tail_cycle_boundary_audit2.log. The new seven-name
log remains /tmp/one_tail_cycle_visits_audit1.log. Source gap scans passed.
Spec recompiled in /tmp/spec_four_cycle_visits_checkpoint.log, containing
only its original sorry warning. The conjecture is NOT settled; Spec is
unchanged, and no proof or disproof has been submitted. No jobs pending.


## Optimal-remainder four visits and a noncut root (verified)

OneTailRemainderVisits.lean compiles with eight complete lemmas. Build log
/tmp/one_tail_remainder_visits2.log; exact audit log
/tmp/one_tail_remainder_visits_audit1.log; expected declaration names
/tmp/one_tail_remainder_visits_audit_expected.json. All eight axiom reports
were parsed and matched; only propext, Classical.choice, Quot.sound. Source
gap/forbidden-declaration scan passed.

normal_member_realization transports ANY member of ANY optimal fixed-slot
path family of the ordinary remainder to a globally maximal one-defect
family with the original cycle and tail length. It preserves membership of
support vertices, NOT the ordered support list (a path can be reversed).
Thus the four-visit and pentagon all-nonroot-vertices restrictions are now
universal over optimal remainder path partitions, not just properties of
the originally chosen D.family.

At odd order, one-edge tail, and original root degree <=5, there is an
ordinary root-avoiding path through the cycle's second vertex. Otherwise
rooted support incidence dominance forces that vertex's degree <=4,
contradicting the verified minimum-degree-five bound.

For a pentagon this path contains all four nonroot cycle vertices. Transfer
it to the remainder H. Every edge of G after deleting root is either in H
or in the cycle, since the one tail edge touches root. The cycle edges have
endpoints connected in H-root by the root-avoiding carrier. As G-root is
connected in an odd-order minimal failure, so is H-root. Main application:
  odd_one_tail_degree_five_pentagon_root_not_cut.
The universally unmarkable degree-two remainder root is therefore NONCUT
in this residual branch. This excludes the cut-vertex explanation for its
unmarkability, but does NOT prove that a noncut degree-two vertex must be
markable. For example, subdividing one edge of an all-odd graph gives a
unique even degree-two noncut vertex which is necessarily unmarkable at
the exact odd-endpoint budget. A marking contradiction still needs the
other even critical port and the other hypotheses.

Global-bound recheck: AsymptoticAmplification requires arbitrarily accurate
leading coefficient 1/2 with a uniform offset for each coefficient (or an
equivalent asymptotic hypothesis). The available elementary normal path
partition bound is n, not n/2+O(1). Dense-graph or order-dependent bounds
have not been substituted for that missing uniform theorem.

The original conjecture remains unresolved. Spec has not been modified,
and no completed proof or disproof has been submitted.

## Sharp three-even restoration and the five-even critical core (verified)

New standalone modules, not inlined into Spec:

* ThreeEvenSharpRestoration.lean, namespace
  Erdos583ThreeEvenSharpRestorationDevelopment, four lemmas:
  sharp_three_even_forest_edge;
  triple_even_set_of_card_three;
  triple_induce_acyclic_of_nonedge;
  sharp_three_even_edge_nonedge.
  If there are exactly THREE even vertices and their induced graph is a
  nonempty forest, then 2*D.card+1 <= card V. This is the FLOOR-half bound,
  stronger than the old <=5-even ceiling helper, with no connectivity premise.
  Proof: delete an even-even edge, apply the sharp one-even theorem, then
  restore using the existing even-forest normalization. This does NOT cover
  three independent even vertices or a triangle of even vertices.
  Build: /tmp/three_even_sharp_restoration1.log (clean).
  Audit: /tmp/three_even_sharp_restoration_audit1.log.

* CriticalFiveEvenCore.lean, namespace
  Erdos583CriticalFiveEvenCoreDevelopment, four lemmas:
  add_edge_adj_of_away;
  critical_five_even_edge_forces_triangle;
  critical_five_even_triple_homogeneous;
  critical_even_edge_mixed_triple_seven_even.
  Let H have p paths and order 2p+1, and let rx be an even-even critical
  nonedge. If H has exactly five even vertices, the three away from r,x
  induce either a triangle or an independent graph. Indeed adding rx leaves
  exactly those three even; a mixed triple would give the new sharp bound,
  contradicting criticality. Consequently a mixed triple away from such a
  critical edge forces at least SEVEN even vertices.
  Build: /tmp/critical_five_even_core2.log (clean).
  Audit: /tmp/critical_five_even_core_audit1.log.

Exact expected-name JSON files:
  /tmp/ThreeEvenSharpRestoration_audit_expected.json
  /tmp/CriticalFiveEvenCore_audit_expected.json
All eight reports parsed and matched; axioms are only propext,
Classical.choice, Quot.sound. Source gap/forbidden-declaration scans passed.

### Intermediate activity cannot be prescribed merely from an even edge

The stronger possible shortcut in restoring a-w-b was rechecked. A graph J
on seven vertices with edges
  01,03,04,12,13,14,25,26
has even set {1,3,4}; its even-induced graph is the path 3-1-4. The vertex
w=1 has degree4<6, yet no normal three-path partition can make w active
and both3,4 inactive. In fact w cannot be an endpoint in ANY three-path
partition: positive even quota at w gives degree(w)+quota(w)>=6, forcing
all three paths to contain w. But the two leaves5,6 lie beyond the bridge12.
A single simple path containing w cannot contain both leaves, and two such
paths would both use12. Contradiction. Thus merely requiring the desired
active vertex to have an even neighbor and not be universal is insufficient.
It is a cut vertex in this example.

This arises in the actual two-edge restoration pattern: take G=J+edge15,
whose three even vertices {3,4,5} are independent; delete 3-1-5 and then
restore13. The intermediate graph is J, where prescribing activity at1 is
impossible. This is an auxiliary obstruction, NOT a Gallai counterexample.
Targeted exact diagnostic (not a Lean assumption):
  /tmp/three_even_nonisolated_mark.py and .log.
Adding the NONCUT premise passed 606 applicable atlas cases:
  /tmp/three_even_noncut_mark.py and .log.
That narrower marking statement remains UNPROVED and has not been assumed.

The original conjecture is still unresolved. No global normalization,
independent-three-even sharp theorem, odd-remainder marking contradiction,
or balanced even-bridge exclusion was proved. Spec is unchanged and retains
its original sole sorry. No completed proof or disproof has been submitted.

## Guarded path restoration and independent critical triples (verified)

Three new standalone modules compile and have exact permitted-axiom audits:

1. IndependentThreeEvenSharp.lean (four lemmas), namespace
   Erdos583IndependentThreeEvenSharpDevelopment.
   Main result sharp_independent_three_two_neighbors: with exactly three
   independent even vertices a,b,c, an outside vertex w adjacent to a,b but
   NOT c gives a decomposition with 2*card+1 <= |V|. Delete a-w-b to get a
   one-even graph. Restore a-w by exact quota transport (w avoids the sole
   initial inactive c), giving q(a)=0 and q(w)=2. Then restore w-b because
   b avoids both possible inactive labels a,c. This does NOT prescribe an
   intermediate activity when w IS adjacent to c.
   Build: /tmp/independent_three_even_sharp3.log (clean).

2. GuardedPathRestoration.lean (five lemmas), namespace
   Erdos583GuardedPathRestorationDevelopment:
     delete_cons_edge_restoration;
     restore_guarded_path_tracked;
     sharp_three_even_guarded_path;
     shortest_path_guard_of_first_nonadjacent;
     sharp_three_even_common_neighbor_avoidance.
   Generic transport: while restoring a simple path Q from s to b, retain
     q(z)+1[a=z] = 1[z!=c]+1[current=z].
   At each newly restored endpoint z, assume
     not Adj z a OR not Adj z c.
   The actual zero quotas are confined to {a,c}, so at the new root at most
   one neighbor can have quota zero. The existing fixed-quota single-defect
   repair lemma applies. Induction restores the entire path with no extra
   indexed member. This is exact quota transport, not an unproved endpoint
   marking assertion.
   Applying the sharp one-even theorem to a path deleted between two of
   exactly three even vertices gives the floor-half bound under this guard.
   The third even vertex may lie inside the restored path; the balance
   formula correctly gives it quota one only while it is the frontier.
   A shortest path has the guard when its first neighbor avoids c.
   More generally, any a-b connection after removing common neighbors of
   a and c supplies a guarded path and hence the sharp bound.
   Build: /tmp/guarded_path_restoration6.log (clean).

3. CriticalFiveEvenNeighborhood.lean (five lemmas), namespace
   Erdos583CriticalFiveEvenNeighborhoodDevelopment:
     critical_five_even_remaining_set;
     add_edge_adj_to_away;
     critical_five_even_common_neighbor;
     critical_five_even_degree_two_no_pair;
     critical_five_even_common_neighbor_separator.
   In the five-even critical remainder H on 2p+1 vertices, if the remaining
   three even vertices a,b,c are independent, ANY vertex adjacent to two
   must be adjacent to all three. This includes the critical endpoints.
   Hence no degree-at-most-two vertex can be adjacent to two of a,b,c.
   Also common neighbors of a,c separate a from b in H: otherwise the
   same guarded path in H+rx would give p paths, violating criticality.
   The separator theorem only assumes a-b is absent; it does not silently
   add a connectivity or degree hypothesis.
   Build: /tmp/critical_five_even_neighborhood1.log (clean).

Audit logs and exact expected names, for each Module in the above list:
  /tmp/Module_audit1.log
  /tmp/Module_audit_expected.json
All FOURTEEN reports were parsed and matched; all use only propext,
Classical.choice, Quot.sound. No audit warnings/errors. Source gap scans
passed. No build or diagnostic is pending.

Remaining mathematical gap: none of these statements handles the case where
three independent even vertices have only common neighbors adjacent to ALL
three, and those common neighbors separate the three vertices. For example,
this separator pattern itself occurs in K_{3,2}, which is not a counterexample
and does have the sharp two-path bound. Thus the separator restrictions are
not a contradiction. The complete even triple case also remains. No general
marking, internal rootification, or simultaneous optimum has been assumed.

The original Spec statement and import remain untouched; its original sole
sorry is still present. This is NOT a completed proof or disproof of Gallai.

## Regular root flowers and the sharp nontriangle three-even theorem (verified)

This continuation completed the previously tentative regular-flower argument.
FIFTEEN new standalone modules contain FIFTY-ONE audited lemmas. They are not
inlined into Work or Spec. Every module compiles warning-free, and the exact
expected-name axiom audit was parsed and matched. The only axioms in all
reports are propext, Classical.choice, Quot.sound. New-source scans for proof
gaps and forbidden declarations passed.

### Tail and rooted-cut invariants

* RegularTailRearrangement.lean (143 lines, 9 lemmas), namespace
  Erdos583RegularTailRearrangementDevelopment.
  A selected TailFamily with a simple root cycle and path tails at all other
  selected labels is characterized by total tail defect ONE. Rearranged
  preserves total lengths, total vertex incidences, and thus total defect.
  Its root tail is nonempty closed and already consumes one defect, so all
  nonroot tails remain paths and the root remains a simple cycle. Main lemma:
    rearranged_regular.
  This does NOT claim that arbitrary multi-defect tail families remain regular.

* ParallelRootExposures.lean (81 lines, 1 lemma), namespace
  Erdos583ParallelRootExposuresDevelopment.
    parallel_root_exposures.
  Several root-tail selections sharing the SAME nonroot tails are followed
  using one common injective successor function. Their pairwise edge-disjoint
  root tails have distinct root-edge seeds, and distinct seeds give distinct
  first exits. The resulting exit-set cardinal is the SUM of the original
  root-tail degrees. Each exit is separately realizable. No separately chosen
  exposure sets are incorrectly assumed disjoint.

* TrackedRootedCut.lean (242 lines, 2 lemmas), namespace
  Erdos583TrackedRootedCutDevelopment:
    RootedCut.rebuild_tracked;
    RootedCut.rebuild_selected_tracked.
  Stronger copies of the existing reconstruction proofs export tail-vertex
  preservation and unchanged outside members. Work's original APIs are not
  modified.

* RegularRootedCut.lean (105 lines, 4 lemmas), namespace
  Erdos583RegularRootedCutDevelopment.
  RegularTail means a path or a closed root tail with vertex count=length.
  RegularCut requires regular tails, paired tails intersecting only at root,
  and all outside members paths. Main lemma:
    regular_rebuild_selected.
  It proves this invariant survives selected-label rearrangement, rather than
  inferring preservation from the generic score/quotas conclusion.

* AssembleRootedCut.lean (109 lines, 1 lemma), namespace
  Erdos583AssembleRootedCutDevelopment:
    assemble_cut.
  Assemble a whole family from root tails and untouched outside members under
  explicit edge-disjointness and coverage hypotheses.

### The missing regularity-preserving positive surgery

* RootedFlowerSurgery.lean (348 lines, 4 lemmas), namespace
  Erdos583RootedFlowerSurgeryDevelopment:
    move_edge_sets;
    member_endpoint_path;
    regular_improve_outside_rep;
    regular_improve_outside.
  Move an exposed first edge of a simple root cycle to a root-avoiding outside
  path, swapping the two affected endpoint slots. The shortened cycle tail
  is a path with the same vertex set; the outside path acquires the root and
  remains a path. The new cut includes that outside member. All quotas are
  unchanged, the score increases exactly one, and RegularCut is proved for
  the result. This is the explicit preservation previously missing from the
  plan; generic positive surgery alone did not supply it.

* RegularCutDefects.lean (114 lines, 6 lemmas), namespace
  Erdos583RegularCutDefectsDevelopment.
  Per-member defect is the sum of its two tail defects. If only one tail can
  be nonpath, the entire family has total defect at most one. Main lemma:
    regularCut_one_petal_bound.

* RegularFlowerExposures.lean (194 lines, 7 lemmas), namespace
  Erdos583RegularFlowerExposuresDevelopment:
    regular_parallel_exposures;
    exists_max_regular_score;
    regular_exposure_zero_at_max;
    max_regular_petals_bound;
    regularCut_nonpath_root;
    max_regular_three_zeros_deficit;
    normalize_regular_three_zeros.
  Optimize among regular rooted families with FIXED quotas. Every exposed
  outside label must have quota zero, by the regular positive surgery.
  For m distinct nonempty root tails, there are 2m distinct zero labels.
  Thus at most THREE zero labels imply at most ONE petal. If the root has
  quota >=2 and the even-induced graph is a forest, the existing one-defect
  forest normalization repairs the last petal. The FINAL path family need
  not retain the fixed quotas; that is essential (e.g. K_{3,2}).

### Restoring a star through nonpath intermediate families

* AssembleRootedCutGraphs.lean (106 lines, 1 lemma), namespace
  Erdos583AssembleRootedCutGraphsDevelopment:
    assemble_cut_graphs.
  General graph-extension assembly with explicit coverage and cross-edge
  disjointness, and exact endpoint labels.

* PathFamilyRootedCut.lean (73 lines, 1 lemma), namespace
  Erdos583PathFamilyRootedCutDevelopment:
    path_family_regular_rooted.
  Cut each path visiting the prescribed root into its two simple tails.
  Their intersection is exactly that root.

* RegularRootAppend.lean (309 lines, 4 lemmas), namespace
  Erdos583RegularRootAppendDevelopment:
    regularTail_mapLe;
    quota_update_endpoint;
    regular_append_edge;
    regular_append_edge_positive.
  Appending a NEW edge from a positive endpoint to the SAME root preserves
  RegularlyRooted, even if the intermediate family already has petals. If the
  affected member already visits the root, its affected nonroot tail is a
  path and becomes a simple root cycle. Otherwise the root-avoiding path is
  extended and inserted into the cut. Exact quota transport is proved:
    q_new(z)+1[old_endpoint=z] = q_old(z)+1[root=z].
  No unproved endpoint activity assertion is used.

### The completed three-even sharp result

* IndependentTripleCommonNeighbor.lean (139 lines, 2 lemmas), namespace
  Erdos583IndependentTripleCommonNeighborDevelopment:
    star_edges_distinct;
    sharp_independent_three_common_neighbor.
  Given three even vertices a,b,c and a common neighbor w, delete wa,wb,wc.
  The remainder has unique even vertex w. Its sharp one-even partition has
  quotas zero at w and one elsewhere. Restore the three edges using the
  regular-root append theorem. Final quotas at w are THREE and zero labels
  are confined to {a,b,c}. Regular three-zero normalization gives the sharp
  floor-half bound. The final lemma actually needs only a-b to be a NONEDGE:
  a-c and b-c may be edges, since the even-induced triple is still a forest.

* IndependentTripleSharp.lean (101 lines, 4 lemmas), namespace
  Erdos583IndependentTripleSharpDevelopment:
    sharp_independent_three_reachable;
    sharp_at_most_two_even;
    sharp_connected_independent_three;
    sharp_independent_three.
  For independent a,b,c, take a shortest a-b path. If its first neighbor
  avoids c, the previously verified guarded-path restoration applies. If it
  meets c but not b, the previously verified exactly-two-neighbor theorem
  applies (with b,c permuted). Otherwise it is a common neighbor and the
  new star restoration applies. Disconnected graphs are then handled by
  summing component decompositions: components with <=2 evens satisfy half
  the order, and the component with all three, if any, satisfies the new
  connected sharp result. Since the total order is odd, the global result is
    2*D.card+1 <= |V|.

* ThreeEvenNontriangle.lean (52 lines, 2 lemmas), namespace
  Erdos583ThreeEvenNontriangleDevelopment:
    sharp_three_even_nonedge;
    sharp_three_even_not_clique.
  Combine the independent case with the already established nonempty-forest
  restoration. ANY graph with exactly three even vertices whose induced
  graph is NOT a triangle has a decomposition with 2*D.card+1 <= |V|.
  Connectivity is not needed. The triangle exception cannot simply be
  dropped: mathematically K5 minus one edge has three even vertices forming
  a triangle and nine edges, whereas two paths cover at most eight. This is
  an obstruction to the FLOOR bound, not a counterexample to original Gallai.

### Critical five-even remainder improvement

* CriticalFiveEvenClique.lean (68 lines, 3 lemmas), namespace
  Erdos583CriticalFiveEvenCliqueDevelopment:
    critical_five_even_remaining_adj;
    critical_five_even_remaining_triangle;
    critical_even_edge_nonadjacent_remaining_seven_even.
  Let H have p paths and order 2p+1, and let rx be a critical even-even nonedge.
  If H has exactly five even vertices, the other three MUST form a triangle.
  The formerly unresolved independent-triple/separator branch is excluded.
  More generally, just TWO nonadjacent even vertices away from r,x force at
  least SEVEN even vertices (the old lemma required a mixed triple).
  This still does not contradict all critical remainders: the complete even
  triple and the cases with >=7 even vertices remain.

### Build and audit records

Every Module listed above has Submission/ModuleAudit.lean and
/tmp/Module_audit_expected.json. The first five modules have clean parsed
reports /tmp/Module_audit2.log; the other ten have clean parsed reports
/tmp/Module_audit1.log. Exact counts sum to 51 declarations.

Most recent main-build logs:
  /tmp/regular_tail_rearrangement3.log
  /tmp/parallel_root_exposures3.log
  /tmp/tracked_rooted_cut2.log
  /tmp/regular_rooted_cut1.log
  /tmp/assemble_rooted_cut1.log
  /tmp/rooted_flower_surgery6.log
  /tmp/regular_cut_defects2.log
  /tmp/regular_flower_exposures5.log
  /tmp/assemble_rooted_cut_graphs2.log
  /tmp/path_family_rooted_cut2.log
  /tmp/regular_root_append3.log
  /tmp/independent_triple_common_neighbor4.log
  /tmp/independent_triple_sharp3.log
  /tmp/three_even_nontriangle2.log
  /tmp/critical_five_even_clique2.log
All are clean.

Practical fixes encountered:
* Use Walk.ext_support plus congrArg (fun slot => (R.tail slot).support)
  to compare copied selected tails with equal slots. Rewriting directly
  under a dependent Walk.copy can fail even with a simple if_neg hypothesis.
* Give the generic move_edge_sets lemma an explicit [DecidableEq I]. The
  classical equality-decider in a theorem's let-bound conditional otherwise
  differed from the concrete subtype equality-decider in its application.
* For local set-valued functions, simp only [N,...] works where rw [N]
  can misinterpret N as a partially applied predicate instead of a definition.
* Before omega, normalize tuple projections and explicitly change membership
  in {z | q z=0} to the equality q z=0.
* Do not put both Walk.mem_edges_toSubgraph and its reverse into one simp set.

The original conjecture remains UNRESOLVED. Spec is unchanged and still has
its original sole sorry. Its checkpoint build is
  /tmp/spec_regular_flower_checkpoint.log
with only the expected sorry warning. No completed proof or disproof has
been submitted. There is no pending build or diagnostic. These special-case
results must not be mistaken for a proof of the full conjecture; the global
long-tail/high-degree cases, complete even cores, and other previously listed
minimum-failure branches are still open in this development.

## Adjacent endpoint separation and the degree-two triangle case (verified)

The latest continuation adds 22 complete audited declarations in five
standalone modules. None is inlined into Spec, and none settles the original
conjecture.

* CriticalEvenIntersection.lean (124 lines, 5 declarations), namespace
  Erdos583CriticalEvenIntersectionDevelopment:
    disjoint_critical_even_edges_seven_even;
    critical_five_even_edges_intersect;
    pairwise_intersecting_edges_star_or_triangle;
    criticalEvenGraph;
    critical_five_even_star_or_triangle.
  At odd sharp budget p on 2p+1 vertices with exactly five even vertices,
  any two critical even-even nonedges intersect. Otherwise the second
  nonedge lies in the complete remaining even triple forced by the first.
  The auxiliary graph of critical even pairs is therefore empty, a star,
  or supported on a triangle. The graph-theoretic intersecting-edge
  classification is proved independently, including the empty-type case.

* AdjacentEndpointUnpairing.lean (187 lines, 6 lemmas), namespace
  Erdos583AdjacentEndpointUnpairingDevelopment:
    all_paths_maximum;
    singleton_unpair_split;
    singleton_unpair_carrier;
    separate_adjacent_endpoints_of_neighbor;
    connected_edge_has_other_neighbor;
    separate_distinct_endpoints.
  A normal ALL-ODD path family can separate ANY specified distinct pair
  of endpoint owners in a connected graph with more than two vertices.
  This extends EndpointUnpairing.separate_nonadjacent_endpoints to
  adjacent pairs, but does NOT assert simultaneous separation of a
  matching or separation in arbitrary non-normal path families.

  Proof of the new adjacent case: use the already verified prescribed
  first-edge theorem to start a path with ab. If its suffix is nonempty,
  b is internal and already has a different owner. If it is the singleton
  ab, choose another path through a (or symmetrically b). Split that path
  at a and append ab to the half avoiding b. The other half starts at a,
  so a and b now have different owners. The existing
  InducedBuffer.move_stem_to_singleton carries out this last replacement.
  Connectivity and order >2 guarantee that ab is not an isolated edge.

  A diagnostic before the proof checked all 3,610 adjacent pairs in 243
  connected all-odd graphs (224 of order 8 and 19 triangle-free examples
  of order 10), with no failure. This finite computation is NOT used by
  any theorem. Script /tmp/adjacent_odd_unpair.py; completed report
  /tmp/adjacent_odd_unpair.log. Its process has ended.

* TwoSpokeSeparatedLift.lean (137 lines, 2 lemmas), namespace
  Erdos583TwoSpokeSeparatedLiftDevelopment:
    orient_separated_starts;
    lift_two_spokes_separated.
  Given a normal path family on G-r whose two prescribed neighbors have
  distinct owners, orient both neighbor endpoints as starts and prepend
  the two new edges to fresh r. The other members remain untouched.
  This preserves the path count. The graph coverage, path simplicity,
  and disjointness are proved explicitly; no arbitrary endpoint-owner
  separation is assumed for a non-normal family.

* ThreeEvenDegreeTwo.lean (119 lines, 4 lemmas), namespace
  Erdos583ThreeEvenDegreeTwoDevelopment:
    delete_vertex_adjacent_neighbor_card;
    delete_vertex_nonadjacent_neighbor_card;
    sharp_triangle_degree_two;
    sharp_three_even_degree_two.
  Every CONNECTED graph of order >3 with exactly three even vertices,
  one of degree TWO, has a path partition with 2*D.card+1 <= |V|.
  Unlike ThreeEvenNontriangle, this includes the TRIANGLE case.

  In the triangle case, delete the degree-two even vertex r. Its two
  neighbors become odd; all other surviving vertices were odd already.
  The core is connected because the two neighbors are adjacent. Apply
  the all-odd normal path theorem, separate the two neighbor owners using
  the new lemma, then lift the two spokes at no extra path cost.
  The order >3 assumption excludes the genuine K3 floor-bound exception.
  For the nontriangle case, invoke the previous sharp theorem.

* CriticalFiveEvenDegreeTwo.lean (109 lines, 5 lemmas), namespace
  Erdos583CriticalFiveEvenDegreeTwoDevelopment:
    critical_five_even_remaining_not_degree_two;
    critical_five_even_remaining_degree_ge_four;
    degree_two_meets_every_critical_even_edge;
    two_degree_two_critical_edge_unique;
    one_tail_five_even_off_root_degree_ge_four.
  In a CONNECTED five-even sharp remainder, every even vertex away from
  a critical even-even pair has degree >=4. Consequently any degree-two
  vertex meets EVERY critical even-even pair. If there are two distinct
  degree-two vertices, their pair is the sole possible critical even edge.
  In the unified one-edge-tail remainder, two distinct even critical
  ports force all even vertices except the root to have degree >=4.

Build logs (all warning-free):
  /tmp/critical_even_intersection3.log
  /tmp/adjacent_endpoint_unpairing5.log
  /tmp/two_spoke_separated_lift4.log
  /tmp/three_even_degree_two4.log
  /tmp/critical_five_even_degree_two2.log

All five modules have Submission/ModuleAudit.lean and exact expected-name
lists /tmp/Module_audit_expected.json. Clean parsed audits are
/tmp/Module_audit2.log for the first four, and
/tmp/CriticalFiveEvenDegreeTwo_audit1.log for the last. All 22 reports
contain only propext, Classical.choice, Quot.sound. A source scan of all
five new modules found no proof gaps or forbidden declarations.

Important remaining gap: neither the complete high-degree even triple
case nor the full unbounded-tail/high-degree minimal-failure alternatives
are eliminated. The speculative floor-half result with three even
vertices forming a triangle and a CUBIC ODD vertex adjacent to two of them
has NOT been proved. The result above instead concerns a DEGREE-TWO EVEN
vertex. These must not be confused.

Submission/Spec.lean remains unchanged, with its original sole sorry.
The checkpoint /tmp/spec_adjacent_unpairing_checkpoint.log contains only
that expected warning. The conjecture is NOT settled, and no completed
proof/disproof has been submitted. No live build or diagnostic is pending.

## Three-even triangle restoration recheck (no new Lean theorem)

Rechecked the proposed sharp floor-half theorem for connected graphs with
three even vertices when an even vertex is non-universal. This assertion is
still UNPROVED. The earlier 82-case auxiliary diagnostic is not a proof.
The existing non-normal minimum example (K6 plus a degree-three vertex)
precludes assuming normal endpoint quotas merely from optimal cardinality.

The degree-three odd-vertex variant also remains unresolved. If an odd w
has neighbors a,b,x, where a,b are two of the three even triangle vertices
and x is odd, deleting w leaves exactly two even vertices (the third triangle
vertex c and x). Restoring all three spokes by adding fresh w to three
distinct endpoint owners would suffice, but the available single-pair
separation theorem does NOT provide that simultaneous arrangement. Nor may
one assume that a prescribed endpoint pair is disjoint from every other
path carrier.

There is a concrete limitation to that proposed restoration template:
on vertices a=0,b=1,c=2,w=3,x=4 take K5 minus {23,24}. Its even vertices
are a,b,c, forming a triangle, and w has degree three with neighbors a,b,x.
It has the two Hamilton paths
  2-0-3-1-4;
  2-1-0-4-3.
Thus it satisfies the sharp bound. But no two-path system can provide
THREE distinct endpoint owners to receive the three spokes at w. The actual
partition has c as an endpoint twice and w only once. This is an obstruction
to that specific lifting template, NOT to the three-even assertion or to
Gallai. No finite diagnostic or unproved statement was used in Lean.

A conditional mathematical observation, NOT a new Lean theorem: the proposed
non-universal-three-even sharp theorem would imply Gallai for connected
four-even graphs. Attach a fresh leaf at an even vertex r of a four-even
G. The augmented graph has three even vertices, each nonadjacent to the
fresh leaf, and one additional vertex. Its sharp floor budget is precisely
|V(G)|/2. Deleting its pendant edge and projecting paths back to G cannot
increase their number. This clarifies that the proposed auxiliary theorem
would already overcome a substantial remaining parity case; it is not a
consequence established by the earlier at-most-three-even ceiling theorem.

No new Lean declarations were added in this recheck. Spec retains its original
statement, sole import, and sole sorry. No complete proof or disproof has
been obtained or submitted.

## Even cut vertices and single-endpoint edge avoidance (verified)

Three new standalone modules compile warning-free. They have not been inlined
into Work or Spec. Their eleven declarations have exact parsed axiom audits,
all using only propext, Classical.choice, Quot.sound. Comment-stripped scans
found no proof gaps or forbidden declarations.

1. Submission/ThreeEvenCutVertex.lean (namespace
   Erdos583ThreeEvenCutVertexDevelopment), six lemmas:
   boundary_neighbor_card;
   evenCount_induce_le_of_boundary;
   evenCount_induce_le_remove_boundary;
   sharp_three_even_boundary;
   sharp_triangle_even_cut;
   sharp_three_even_cut_vertex.

   Main unconditional result: a connected graph with exactly three even
   vertices satisfies 2*D.card+1 <= |V| if ONE of its even vertices is a cut
   vertex. In the nontriangle case this follows from the previous theorem.
   In the triangle case, separate a branch not containing the other evens.
   If the boundary degree on that branch is odd, both sides have at most two
   evens and their odd endpoint paths merge. If it is even, that branch has
   one even vertex and the main side has at most three; use the existing
   marked ceiling partition on the main side and even-marked double gluing.
   This saves the required one path. No smaller-order Gallai hypothesis is
   used. The proof explicitly tracks both induced-side degree parities and
   the sum of their vertex cardinalities.

2. Submission/CriticalFiveEvenCutVertex.lean (namespace
   Erdos583CriticalFiveEvenCutVertexDevelopment), four lemmas:
   delete_connected_of_sup_edge;
   critical_five_even_remaining_noncut_after_add;
   critical_five_even_reachable_implies_noncut;
   critical_five_even_cut_separates.

   Let connected H have a p-path partition, |V|=2p+1 and exactly five evens,
   and let rx be a critical even-even nonedge. For every OTHER even vertex
   a, (H+rx)-a is connected: otherwise the preceding sharp theorem would
   contradict criticality. If r and x are reachable in H-a, adding rx does
   not change connectivity, so H-a is connected too. Consequently every
   such even cut vertex a of H must SEPARATE r from x. This does not say that
   H-a is always connected, nor that all cut vertices are excluded.

3. Submission/EndpointEdgeAvoidance.lean (namespace
   Erdos583EndpointEdgeAvoidanceDevelopment), one lemma:
   endpoint_owner_avoids_edge_of_nonadjacent.

   In an all-odd normal path system, for edge xy and x != a with x
   nonadjacent to a, there is another normal path system of the same score
   whose endpoint owner of a does NOT carry xy. Force xy as a first edge;
   if that member ends at a, shorten it using the existing nonadjacent-ends
   theorem, keeping its suffix and a's owner at that index. Otherwise edge
   disjointness already gives the result. This is SINGLE-endpoint avoidance.
   It does NOT say the xy carrier avoids a as an internal vertex, and it
   does NOT simultaneously separate two specified owners from that carrier.

Warning-free final builds:
 /tmp/three_even_cut_vertex4.log
 /tmp/critical_five_even_cut_vertex1.log
 /tmp/endpoint_edge_avoidance1.log
Audits (each named ModuleAudit.lean in Submission):
 /tmp/three_even_cut_vertex_audit.log             6 reports
 /tmp/critical_five_even_cut_vertex_audit.log      4 reports
 /tmp/endpoint_edge_avoidance_audit.log            1 report
Exact expected-name JSON files: /tmp/Module_audit_expected.json for each of
these three module names. All eleven names/counts/axiom sets were parsed and
checked, not merely inspected by grep.

A NEW UNPROVED local selection question was examined separately:
 in a connected all-odd graph of order AT LEAST SIX, given disjoint edges
 ab and xy, can the endpoint owners of a and b be distinct, with neither
 carrying xy?
The order restriction is essential: K4 has only two normal path slots,
whereas this assertion needs three. The exact diagnostic
 /tmp/edge_adjacent_endpoint_separation.py
 /tmp/edge_adjacent_endpoint_separation.log
passed all 26,462 ordered choices in 237 graphs: the 13 connected all-odd
atlas graphs of order six and all 224 connected all-odd graphs of order eight.
It took 34.13 seconds and finished; there is no running diagnostic. This is
not a numerical search for an original-conjecture counterexample and is
NOT a Lean proof or hypothesis. The question would support a degree-four
lifting strategy in a three-even graph when the two odd neighbors of the
deleted degree-four even vertex are nonadjacent. Its simultaneous-selection
step remains unproved; no conclusion from that strategy is asserted.

The original conjecture remains unresolved. Spec.lean is still the 24-line
file with the unchanged statement, original import, and sole original sorry.
No completed proof or disproof has been submitted.

## General quota purification and three-endpoint common-neighbor marking (verified)

Three new standalone modules are complete, warning-free, and individually
axiom-audited. They are NOT inlined into Spec or Work. The twelve exact axiom
reports use only propext, Classical.choice, and Quot.sound.

1. Submission/GeneralQuotaPurification.lean, namespace
   Erdos583GeneralQuotaPurificationDevelopment (six lemmas):
     internal_member_of_endpoint_lt_degree;
     split_at_internal_vertex;
     realize_larger_quotas;
     path_family_partition_quota_exact_of_le_degree;
     endpointMultiplicity_le_degree;
     path_family_partition_truncated_quota.

   General endpoint refinement, without the old quota<=2 restriction:
   if a nonempty-path partition has endpoint multiplicities d, and
     d(v) <= q(v) <= deg(v), q(v) == deg(v) mod 2,
   splitting paths at internal vertices realizes EXACTLY q. Strong induction
   on sum(q)-2*|D| gives termination. Each split adds one path and exactly two
   endpoint incidences at its cut vertex; all other multiplicities stay fixed.

   Consequently an indexed all-path family T with k slots has a nonempty
   partition with exactly k members and exactly its quotas whenever
   T.quota(v)<=deg(v). In full generality, it has a partition with <=k members
   and endpoint multiplicities exactly min(T.quota(v),deg(v)). This handles
   nil slots without pretending their indexed endpoints are genuine.

2. Submission/SplitFamilyTracked.lean, namespace
   Erdos583SplitFamilyTrackedDevelopment (four lemmas):
     indexed_path_family_tracked;
     split_family_member;
     one_defect_path_family_preserves_lower_quotas;
     one_defect_marked_partition.

   Splitting one trail L.append R into two simple paths enlarges the indexed
   family from k to k+1 and adds exactly two endpoints at the split vertex.
   All other quotas are preserved. If a family's total incidence deficit is
   at most one, it has a nonempty path partition D with
     |D| <= k+1,
     endpointMultiplicity(D,v) >= min(T.quota(v),deg(v)) for every v.
   The nonpath-cut lemma plus deficit accounting proves that both pieces of
   the chosen split really are simple paths. The preceding truncation result
   is then used to purify nil slots. This is NOT a same-k repair theorem.

3. Submission/ThreeEvenCommonNeighborMarked.lean, namespace
   Erdos583ThreeEvenCommonNeighborMarkedDevelopment (two lemmas):
     regular_three_even_common_neighbor;
     three_even_common_neighbor_marked.

   Main result: if a,b,c are exactly the three even vertices and w is adjacent
   to all three, there is a nonempty-path partition D satisfying
     |D| <= ceil(|V|/2), endpointMultiplicity(D,w) >= 3.
   Neither connectivity nor any missing edge among a,b,c is required.

   Delete wa,wb,wc. The resulting graph has unique even vertex w, so its
   sharp partition has k=(|V|-1)/2 slots and quota0 at w, quota1 elsewhere.
   Restoring the three spokes with regular_append_edge_positive gives a
   regular rooted family with quota3 at w and only a,b,c possibly zero.
   Maximize its regular score at fixed quotas. The existing three-zero petal
   bound leaves total deficit <=1. The new one-defect partition theorem gives
   k+1 paths while preserving at least min(3,deg(w))=3 genuine endpoints at w.
   Distinct neighbors a,b,c supply the required degree>=3 argument.

Warning-free builds:
 /tmp/general_quota_purification3.log
 /tmp/split_family_tracked3.log
 /tmp/three_even_common_neighbor_marked2.log
Each module has a corresponding Submission/ModuleAudit.lean, with logs
 /tmp/GeneralQuotaPurification_audit.log
 /tmp/SplitFamilyTracked_audit.log
 /tmp/ThreeEvenCommonNeighborMarked_audit.log
Exact declaration-name lists are /tmp/Module_audit_expected.json. Parsed
reports matched all 6+4+2 requested names and the allowed axiom sets. The
initial audit files lacked module docstrings; those header-only lint warnings
were corrected and all three audits rerun cleanly.

A narrow auxiliary fixed-quota diagnostic also passed: on connected atlas
graphs through order seven with exactly three even vertices forming a triangle,
every noncut non-universal even r tested admitted a floor-budget partition
with quota2 at r, quota0 at the other evens, quota1 elsewhere. There were 183
choices. Files:
 /tmp/triangle_even_noncut_active.py
 /tmp/triangle_even_noncut_active.log
This is finite evidence only, NOT a Lean theorem or premise. The broader
sharp three-even non-universal result remains UNPROVED, as does the proposed
simultaneous three-owner selection in all-odd systems.

The common-neighbor marking theorem is a CEILING-budget theorem. It does not
supply the missing FLOOR-budget repair and has not eliminated the global
long-tail/high-degree or balanced-even-bridge minimal-failure alternatives.
No complete proof or disproof of the original conjecture has been obtained.
Spec.lean retains its unchanged conjecture and sole original sorry.

## Triangle cut-capacity inequalities (verified)

Submission/TerminalCutCapacity.lean now compiles warning-free. Eight lemmas
in Erdos583TerminalCutCapacityDevelopment were individually axiom-audited:
 boundary_sum_degrees; degree_split_on_set; degree_sum_on_set;
 boundary_parity_of_all_odd; cutCapacity_parity;
 boundary_positive_of_connected; triangle_boundary_ge_three;
 triangle_cutCapacity_ge_three.
The definition cutCapacity(A,U) is
 |delta(U)| + |A\\U| + |U\\A|.
For all-odd G its parity is |A| modulo two. For connected all-odd G of order
at least six and a triangle A, every such cut capacity is at least three.
The proof uses only parity, connectivity, the set degree-sum identity, and
the fact that each triangle vertex has even internal degree two and hence
positive boundary degree. It is NOT a sufficiency theorem for constrained
path partitions. The simultaneous three-owner endpoint selection remains
unproved, as does the original conjecture.

Build: /tmp/terminal_cut_capacity6.log.
Audit: Submission/TerminalCutCapacityAudit.lean;
 /tmp/TerminalCutCapacity_audit.log;
 /tmp/TerminalCutCapacity_audit_expected.json.
All eight exact declaration reports were parsed and matched; permitted
axioms only. No changes to Spec.lean or Work.lean.

## Exactly five even vertices: unconditional ceiling bound (verified)

New module Submission/FiveEvenBound.lean compiles warning-free and all six
lemmas are individually axiom-audited (permitted axioms only):
 delete_even_ends_path_evenCount;
 five_even_bound_of_path;
 five_even_nonclique;
 five_even_clique;
 five_even_path_bound;
 odd_order_at_most_five_even.

The new theorem five_even_path_bound proves the requested ceiling-half path
bound for ANY finite simple graph with exactly five even-degree vertices;
connectivity is not required. Thus the Gallai bound now holds for odd-order
graphs with at most five even vertices. This is NOT yet an at-most-five theorem
for even order: the four-even case is not supplied by this result.

Proof: if two even vertices c,d are nonadjacent, choose two other evens a,b.
If ab is present, delete it; if absent, add it. The modified graph has exactly
three evens, retaining the nonedge cd, so ThreeEvenNontriangle gives the
floor-half budget. Undoing the edge modification costs at most one path.
If the five evens form a clique, choose four distinct evens a,b,c,d and delete
the simple path a-b-c-d. Only a,d change parity, and the remaining even pair
b,c becomes nonadjacent. Apply the same sharp three-even theorem and restore
the one deleted path. This also costs at most one path.

Build: /tmp/five_even_bound2.log.
Audit: Submission/FiveEvenBoundAudit.lean;
 /tmp/FiveEvenBound_audit.log;
 /tmp/FiveEvenBound_audit_expected.json.
All six exact reports matched, with only propext, Classical.choice, Quot.sound.
Spec.lean remains unchanged with its sole original sorry. The earlier
submission attempt was rejected; no complete proof or disproof is available.

FiveEvenFailure.lean adds two verified corollaries: odd_failure_seven_even
and minimal_odd_failure_seven_even. Every odd-order failure (not just a
minimal one) must now have at least seven even-degree vertices. This narrows
but does not eliminate the global failure certificate.
Build /tmp/five_even_failure1.log; audit /tmp/FiveEvenFailure_audit.log;
expected names /tmp/FiveEvenFailure_audit_expected.json. Both exact reports
matched and use only the permitted axioms.
An attempted external status check at erdosproblems.com failed at DNS lookup;
no external mathematical statement was retrieved or used.

## Four even vertices not forming a clique (verified)

Submission/FourEvenNonclique.lean adds three warning-free, axiom-audited lemmas:
 evenCount_leaf_at_even;
 four_even_nonclique;
 four_even_failure_clique.
Attach a fresh leaf at an even vertex r distinct from a nonadjacent even pair
c,d. The augmented graph has exactly three even vertices and retains the
nonedge c,d. Its sharp floor-half partition projects back through the one-leaf
projection without increasing the number of paths. The cardinal identity
|V+leaf|=|V|+1 gives the original ceiling-half bound. No connectivity hypothesis
is required. A four-even failure must therefore have its four evens forming
a clique. That clique case has NOT been proved here.

Build /tmp/four_even_nonclique2.log.
Audit /tmp/FourEvenNonclique_audit.log, expected names
/tmp/FourEvenNonclique_audit_expected.json. All three exact reports parsed
and matched, permitted axioms only. New-source scans found no sorry/admit,
extra axioms, or native_decide. Spec checkpoint
/tmp/spec_five_even_checkpoint.log contains only the original sorry warning.

No complete proof or disproof has been found. Spec remains the original
24-line conjecture file; all new verified results remain auxiliary modules.
Do not submit those partial results as a resolution of erdos_583. The last
submission was rejected, and no corrected complete submission exists yet.

## Four-even clique with a degree-four even vertex (verified)

New modules, all warning-free and individually axiom-audited:
 GeneralTwoSpokeLift.lean (2 lemmas): orient_two_slots;
   lift_two_spokes_at_distinct_slots.
 FourSpokeLift.lean (1 lemma): lift_four_spokes.
 FourEvenDegreeFour.lean (3 lemmas): four_even_clique_degree_four;
   four_even_degree_four; four_even_failure_even_degree_ge_six.

The two-spoke lifting lemma now accepts a general indexed all-path family,
not only a NormalTrailSystem: the two receiving slots must be distinct and
the two neighbor vertices distinct. For four spokes, reserve two for the
simple path c-r-d; prepend the other two at distinct slots in the core,
then restore c-r-d as one extra path. All graph coverage, disjointness,
projection, fresh-vertex simplicity, and cardinal bounds are proved.

Application: if G has exactly four even vertices forming a clique, and r is
one of them with degree four, its neighbors are the other three evens a,b,c
and one odd x. Deleting r leaves exactly one even vertex x. The sharp
one-even core partition has (|V|-2)/2 paths and genuine endpoints at a,b,c.
Three distinct vertices cannot all be endpoints of one path member, so two
of a,b,c have distinct receiving slots. Append their spokes and put the two
remaining spokes into one new path. Total <=|V|/2. No connectivity assumption
is needed. If the four evens were not a clique, the previous theorem already
applies. Consequently in any four-even failure, EVERY even vertex has
degree at least six (and the four evens form a clique).

Builds:
 /tmp/general_two_spoke_lift2.log;
 /tmp/four_spoke_lift2.log;
 /tmp/four_even_degree_four5.log.
Audits: Submission/{GeneralTwoSpokeLift,FourSpokeLift,FourEvenDegreeFour}Audit.lean;
 /tmp/Module_audit.log and /tmp/Module_audit_expected.json for each module.
All six exact requested reports matched and use only propext,
Classical.choice, Quot.sound. A DecidableEq mismatch between Classical and
Subtype ite instances in the quota formula was resolved with split_ifs;
it was not assumed by definitional equality.

The all-degree-four restriction has NOT been removed. In particular, deleting
all six edges of the four-even clique gives an all-odd core, but restoring
that clique at the same path budget remains unproved. Sequential edge
restoration can end with a zero-baseline triangle, outside the available
forest-normalization theorem. Do not apply that theorem to a triangle.

The original conjecture remains unresolved, and Spec.lean is unchanged with
its original sorry. These auxiliary results are not a completed submission.

## Final scope recheck after the five-even development

Re-read `normal_path_cycle_decomposition`, `normalize_one_defect_forest`,
`normalize_zero_root_forest`, and the additive/asymptotic amplification APIs.
The first bounds no cycle count; the forest normalization hypotheses exclude
an induced zero-baseline triangle; and amplification still requires a uniform
or asymptotic upper bound that has not been proved here. None provides the
missing global argument. The all-odd K4 restoration and simultaneous endpoint
selection problems remain unresolved. No new theorem or assumption was added
in this recheck, and no completed proof/disproof of the conjecture was obtained.
Spec.lean is unchanged and still contains its original sorry. The verified
special cases must not be represented as a solution of the general statement.

## Minimal counterexample parity profile (verified)

Submission/MinimalParityProfile.lean supplies five new lemmas:
 degree_sum_lower_of_five;
 odd_minimal_edge_lower;
 odd_minimal_order_ge_nine;
 failure_four_even_or_six;
 failure_parity_profile.

For any graph of minimum degree at least five, degree parity improves the
handshaking bound to 5*|V|+evenCount(G) <= 2*|E|. Thus an odd-order minimal
failure has 5*order+7 <= 2*|E|. Its order is at least nine: an order-seven
failure would have at least 21 edges and therefore be complete, contradicting
the already verified complete-graph theorem.

Every failure (with no connectivity assumption needed for this profile) is
either odd-order with at least seven even vertices, or even-order with at
least six even vertices, or has exactly four even vertices which form a
clique and each have degree at least six. These are necessary conditions,
not a proof that failure is impossible.

Build /tmp/minimal_parity_profile2.log is warning-free. The exact five names
and all axiom sets were parsed from /tmp/minimal_parity_profile_audit.log:
only propext, Classical.choice, Quot.sound. The audit initially had only a
module-docstring linter warning; its missing docstring has been added.

A contemplated global degree-two exclusion was NOT established. In particular,
FreeRootWholeCycleExclusion.minimum_whole_cycle_impossible needs a minimum
cycle across all equal-score rooted families, not just a newly constructed
whole-cycle member. The minimum may instead be an open lollipop; there is
no valid application without the missing comparison hypothesis.

No change to Spec.lean and no completed proof/disproof of the original theorem.

## Eulerian high-girth and edge-budget bounds (verified)

Submission/EulerianGirthBound.lean now supplies eight lemmas:
 maximum_trail_endpoint_edges;
 connected_even_has_eulerian;
 short_trail_isPath;
 trail_path_pieces;
 eulerian_girth_edge_budget;
 eulerian_average_degree_girth_bound;
 eulerian_high_girth_bound;
 eulerian_failure_short_cycle.

The Euler-circuit existence proof is kernel-checked from the maximum-trail
lemma, trail endpoint parity, and connectivity; no unproved converse to the
Eulerian degree theorem is imported. A longest trail is closed by parity.
Rotating it at any visited vertex shows that every incident edge is covered;
connectivity then shows it covers every graph edge.

A trail of length at most d is a path if every cycle has length greater than
d. Inductively split a trail of length at most d*k into at most k paths,
retaining the exact edge union and pairwise edge disjointness. Consequently a
connected Eulerian graph has a k-path partition whenever |E| <= d*k and all
cycles are longer than d. Taking k=ceil(|V|/2) gives Gallai whenever
2*|E| <= d*|V| and all cycles are longer than d. In particular maximum degree
at most d is sufficient under that girth hypothesis. Zero d is harmless and
does not need to be excluded. The contraposition gives a short cycle in an
Eulerian failure under the corresponding average-degree bound.

Final build: /tmp/eulerian_girth_bound4.log, warning-free. Exact eight-name
axiom audit: /tmp/eulerian_girth_bound_audit2.log, only propext,
Classical.choice, Quot.sound. No proof gaps or unsafe declarations were added.

This is an unbounded sufficient family, not a proof for all Eulerian graphs
or for arbitrary graphs. Spec.lean remains unchanged with its original sorry.

## Every connected graph on at most seven vertices (verified)

New final modules:
 * SixVertexCodes.lean: a 15-bit encoding of simple graphs on Fin 6, its
   surjectivity, and a generic checker-to-path-partition theorem.
 * SixVertexCertificateData.lean: explicit three-slot path certificates for
   225 labelled residual graphs, in a binary lookup tree.
 * SixVertexCheck0.lean through SixVertexCheck31.lean: 128 ordinary `decide`
   lemmas, each quantifying over one 256-code block. No native evaluation.
 * SixVertexCertificates.lean: assemble the exhaustive check and prove
   residual_partition.
 * MinimumOrderEight.lean: five lemmas:
     four_even_failure_order_ge_eight;
     failure_order_ge_six;
     minimal_order_ne_six;
     minimal_order_ge_eight;
     connected_at_most_seven.

The finite residual predicate requires all degrees to be two or four, the
neighbors of every degree-two vertex to be adjacent, and no adjacent pair
of degree-two vertices. Exactly 225 edge sets satisfy it (15 with no degree-
two vertices, 90 with two, 120 with three). This count was a diagnostic;
the proof is the exhaustive kernel check over ALL 32768 fifteen-bit codes,
plus the surjective graph encoding. Each returned path list is nonempty and
nodup, its consecutive edges are checked, and all edge unions and disjointness
are checked. The checker-to-decomposition theorem builds actual graph walks.

In a six-vertex minimal failure, the preceding parity profile forces all six
vertices to be even. Connectivity then gives degrees two or four. The old
minimum-order degree-two reductions supply exactly the residual predicate,
so the checked three-path certificate contradicts failure. Combine this with
the odd minimal-order lower bound nine and the new general lower bound six
to obtain minimum counterexample order eight. Extracting the existing smallest-
order witness then proves Gallai for EVERY connected graph of order at most
seven, on arbitrary finite vertex types.

The initial all-in-one certificate build was stopped for memory use. The
successful build used sequential direct Lean invocations for the 32 small
check modules; LEAN_PATH was obtained from `lake env printenv LEAN_PATH`.
Logs:
 /tmp/six_vertex_codes3.log;
 /tmp/six_vertex_certificate_data.log;
 /tmp/six_vertex_check0.log through /tmp/six_vertex_check31.log;
 /tmp/build_six_vertex_checks_direct.log;
 /tmp/six_vertex_certificates_assembled.log;
 /tmp/minimum_order_eight1.log.
All final builds are warning-free. Exact axiom audit:
 /tmp/minimum_order_eight_audit.log;
 /tmp/minimum_order_eight_audit_expected.json;
 Submission/MinimumOrderEightAudit.lean.
All 139 lemma names (including the 128 finite checks) were matched exactly;
every dependency set is contained in propext, Classical.choice, Quot.sound.

Temporary conditional-development and duplicate small-order files were removed
after the unconditional MinimumOrderEight module compiled. None was a dependency
of the final theorem. No check build remains pending.

This does not settle the unbounded conjecture. Spec.lean is unchanged and its
sole original sorry is confirmed by /tmp/spec_at_most_seven_checkpoint.log.
No incomplete file has been resubmitted as a completed proof.

## Sparse-zero regular normalization (verified)

New module: Submission/RegularSparseZeroNormalization.lean. Six lemmas:
 * normalize_regular_one_zero: a regularly rooted family with at most one
   zero-quota vertex admits an all-path family at exactly the original quotas.
 * normalize_regular_zero_baseline_forest: with at most three actual zeros
   and root quota at least two, it is enough that the zero BASELINE graph be
   acyclic. The entire even-induced graph need not be acyclic.
 * acyclic_of_card_le_two: every graph on at most two vertices is acyclic.
 * normalize_regular_two_zeros_large_root: with at most two actual zeros and
   root quota at least three, regular normalization always succeeds.
 * nonacyclic_card_le_three: a nonacyclic graph on at most three vertices
   has exactly three vertices and all possible adjacencies.
 * regular_two_zero_failure_triangle: with at most two actual zeros and
   root quota at least two, failure implies that the root quota is exactly
   two and the zero set is exactly a pair forming a triangle with the root.

The last result is only a NECESSARY obstruction; no existence of a failing
triangle family is asserted, nor is that remaining case normalized.

Final build: /tmp/regular_sparse_zero_normalization4.log (warning-free).
Exact six-name audit: /tmp/regular_sparse_zero_normalization_audit2.log,
via Submission/RegularSparseZeroNormalizationAudit.lean. All names matched,
all dependency sets contained in propext, Classical.choice, Quot.sound.

No unrestricted global argument has been obtained. Spec.lean was not changed
and still has its original sorry, as checked in
/tmp/spec_sparse_zero_checkpoint.log. These auxiliary results are not a
solution of erdos_583, and no completed proof was submitted.

## Local zero-neighbor normalization and the triangle obstruction (verified)

Submission/RegularLocalZeroNormalization.lean proves four lemmas:
 * max_regular_local_petals_bound;
 * normalize_regular_one_zero_neighbor;
 * max_regular_three_zero_neighbors_deficit;
 * normalize_regular_local_zero_forest.

The exposure labels are adjacent to the root, not merely arbitrary zeros.
Consequently 2m distinct exposures for m petals lie in the set of zero-quota
NEIGHBORS of the root. At most one such neighbor gives fixed-quota all-path
normalization; at most three give deficit at most one. Combining with the
zero-baseline forest theorem repairs that defect when a root pair is available.
No restriction is needed on the number of zero labels away from the root.

Build: /tmp/regular_local_zero_normalization.log (warning-free).
Exact four-name axiom audit: /tmp/regular_local_zero_normalization_audit.log,
via Submission/RegularLocalZeroNormalizationAudit.lean.

Submission/RegularTriangleObstruction.lean formalizes why bare triangle
repair is FALSE, and must not be used to close the remaining case. G is K5
minus edge 3-4. Its two trails are:
  p = 0-1-2-3-0-4; q = 0-2-4-1-3.
They partition all nine edges. A regular rooted cut at 0 has tails the cycle
0-1-2-3-0, edge4-0, reverse(q), and nil. Quota at0 is two; zero quotas are
exactly1,2. The graph is connected and the family has exactly one score
defect. No two-path family exists: paths on five vertices have at most four
edges each, whereas G has nine edges. The proof uses the equivalent score
bound. budget_free_triangle_repair_false negates only this overly strong
LOCAL repair claim, NOT the original conjecture. Gallai's budget here is
THREE, so there is no contradiction with erdos_583.

Build: /tmp/regular_triangle_obstruction5.log (warning-free).
Exact eight-name audit: /tmp/regular_triangle_obstruction_audit.log, via
Submission/RegularTriangleObstructionAudit.lean. All twelve audited results
use only propext, Classical.choice, Quot.sound.

The needed global budget-dependent argument is still missing. Neither new
module settles the conjecture. Spec.lean is unchanged with its original sorry.
No completed proof or disproof of erdos_583 has been submitted.

## Final global compatibility recheck (no new theorem)

Rechecked UnifiedMinimalDefect and GlobalTailDefect against the new local
zero-neighbor normalization results. Their globally maximum-score one-defect
families do not come with a bound of at most one zero-quota neighbor, nor with
a zero-baseline forest. The at-most-three-neighbor deficit conclusion only
recovers an already known one-defect bound if its hypothesis is supplied;
it does not eliminate the remaining defect. No such hypothesis was derived.

The compatible certificate deliberately does not contain a quota-energy
minimum. It would be invalid to combine its unrestricted cycle/tail optima
with conclusions requiring a separate global quota-energy minimization.
No contradiction with the parity profile or lower-order bounds was obtained.
This recheck made no change to Spec.lean and produced no full proof/disproof.
