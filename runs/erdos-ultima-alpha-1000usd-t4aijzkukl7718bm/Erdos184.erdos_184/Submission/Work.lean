import FormalConjecturesUtil

/-!
Partial results for Erdős Problem 184. These lemmas do not establish the
conjectured uniform linear bound. The original submission remains unchanged.

A checked exchange now replaces two edge-disjoint cycles with at least three
cycles whenever the original pair shares at least three vertices. Consequently
maximum-cardinality cycle decompositions have pairwise vertex intersections
of size at most two. These statements do not apply to minimum decompositions
without an additional hypothesis; the missing link for minimal cores is not proved.

Deleting an edge from any even graph is now proved to increase the minimum
piece count strictly. More generally, an even-graph decomposition containing
a single-edge piece can be improved by at least two pieces. Every nonempty
even graph consequently has a proper edge-critical subgraph of strictly
larger optimum. These facts do not provide a uniform upper bound.

A seven-vertex even-minimal graph now verifies that an optimal decomposition
can contain a nonseparating rainbow triangle without admitting any improvement.
Its optimum is three and the sparse-union threshold is exactly at equality.
This rules out omitting the quantitative hypothesis from the rainbow-cycle
improvement lemma, not the original conjecture.

Pure multiplicative rounding of the fractional theorem is now disproved.
A family of cubic cyclic-shift graphs has a three-cycle double cover (cost
3/2), while parity forces at least p integral pieces on 2p vertices. Its
integral cost still has the linear upper bound 3p, so this is not a disproof
of Erdős 184. The 15-vertex even obstruction also has a checked four-Hamilton-
cycle double cover of cost two and integral optimum three. A local two-path
completion obstruction is checked for that block. An infinite connected 4-regular family now has a checked exact fractional
cover of cost two and unbounded integral cost. Its integral cost nevertheless
has a separate linear upper bound in the number of vertices.

A fractional exact decomposition is now verified: every finite graph has
nonnegative real coefficients on cycles and single edges, with total weight
at most n-1 and coverage exactly one on each edge. A maximum-weight-path
rotation proves the underlying signed dual inequality, and finite-dimensional
Hahn--Banach separation gives the fractional family. No integral rounding or
pairwise edge-disjointness is obtained from this result; the original
conjecture remains unproved.

An adjacent-neighborhood-transfer example is checked: the five-vertex wheel
is edge-critical with optimum four, while transferring the private neighbors
of one adjacent rim vertex to the other gives optimum three. Thus even
edge-criticality does not justify monotonicity under adjacent compression.
This is not a counterexample to the original conjecture.

The degree-certified case now has an exact characterization: for an even
graph G and specified v, G is even-minimal with degree(v)=2*number(G) if
and only if G-v is acyclic. Within this feedback-vertex class the optimum
is additive across every even edge partition. No such additivity is asserted
for arbitrary even graphs.

A star-core construction retains every edge at a chosen vertex of an even
graph while deleting all cycles avoiding that vertex. Its optimum is exactly
half the retained degree. Consequently a minimal even core whose optimum
saturates a vertex-degree lower bound has a feedback vertex and a vertex of
degree at most two. This does not cover cores whose optimum strictly exceeds
every vertex-degree lower bound. Such a core, if its minimum degree exceeds
two, satisfies degree(v)+2 ≤ 2*number(G) at every vertex.

A nine-vertex example now verifies failure of monotonicity under cycle
deletion even for even graphs: its optimum is two cycles, but deleting a
specified six-cycle leaves three disjoint triangles with optimum three.
This is not a counterexample to Erdős 184. It explains why the minimum-core
argument must not use unrestricted cycle-deletion monotonicity.

A minimum even-core reduction is now checked: every even graph has an
even subgraph with the same optimum that is minimal among even subgraphs.
Deleting any simple cycle from such a core lowers the optimum by exactly
one, so every cycle is exposable in a minimum decomposition. A conditional
induction shows that a uniform low-degree bound for these cores would give
the desired linear estimate for even graphs. That structural low-degree
bound has not been proved or assumed in any unconditional result.

Deleting at most one edge from each piece of a cycle decomposition preserves
all reachability relations. A rainbow cycle is therefore nonseparating. Its
removal followed by a cycle-rank decomposition yields a valid improvement
when the union has sufficiently small edge/vertex excess. The representative
graph also supplies long nonseparating rainbow cycles when the decomposition
is large. These facts alone do not force the sparse-overlap condition.

A new overlap-recombination lemma handles the two-fold independent blow-up
of a simple path: all doubled edges can be partitioned into at most two
cycles, independently of the path length. An embedded doubled path therefore
replaces any larger selected family covering the same edges by at most two
cycles. A general finite-family gluing lemma also shows that a k-path edge
decomposition gives at most 2k cycles in the two-fold blow-up. No unrestricted
linear path decomposition has been formalized here, and arbitrary four-cycle
partitions need not possess the consistent vertex pairs needed by this rule.

Complete bipartite graphs now also have a verified linear bound independent
of their common-neighbor counts: 2*D.card ≤ 3*(|A|+|B|). An explicit cyclic
shift construction partitions K_(2a,2b) into max(a,b) cycles when both shores
are nonempty, and a degree lower bound proves this count optimal. The uniform
coefficient 3/2 for all complete bipartite graphs is optimal. These results
handle unbounded common-neighbor counts for this family, but do not provide
a way to combine overlapping bicliques in arbitrary graphs at linear cost.

The path-rotation upper bound is now generalized beyond the no-four-cycle case.
If every pair of distinct vertices has at most r common neighbors, with r > 0,
there is a decomposition into at most (2*Nat.clog 2 (2*r)+5)*n pieces. The proof
uses an overlap-counting bound, an induced-subgraph density argument, and a
summable sequence of long-cycle removals above density 2*r. The low-density
base is the existing general dyadic bound. This proves a linear bound for
any fixed common-neighbor bound; it does not give an absolute constant when
r grows with n. The common-neighbor condition is verified equivalent to the
absence of an injective homomorphism from K_(2,r+1), so the corresponding
fixed-biclique-free class is also covered.

Further checked results realize every even terminal set as the odd-degree set
of a subgraph in a preconnected graph, using symmetric differences of walks.
When deleting v leaves a preconnected graph, an even subgraph can retain all
edges at v if its degree is even. This gives vertex elimination at a cost of
ceil(degree(v)/2) cycles and edges. Combined with the sparse-cut reduction,
a smallest counterexample to C(n-1) has minimum degree greater than 2C, even
without an even-degree assumption. The remaining bound can be restricted
simultaneously to edge-critical, (C+1)-edge-connected graphs of minimum degree
above 2C; no bound for that class is asserted.

There is also an exact local formula: adding one new edge to an even graph
increases the minimum cycle-and-edge decomposition size by exactly one.
The proof uses a feedback-edge count for edge-disjoint cycle families and
acyclicity after deleting an edge of a connected 2-regular piece. This local
formula does not establish the required uniform linear bound.

Verified bounds include a general `O(n log n)` decomposition, the exact `n - 1`
piece count for trees, and a `6n` decomposition for graphs with no four-cycle.
The four-cycle-free case uses one-step path rotations to establish
`d * d + d ≤ 2 * k` when minimum degree is at least `d` and all cycles
have length at most `k`; the resulting density-scale costs are summable.

The original conjecture is also proved equivalent to a uniform linear bound
restricted to graphs that admit an edge partition into four-cycles. A bound
`Cn` for those graphs yields `(C + 6)n` for arbitrary graphs, by a maximal
four-cycle packing and the four-cycle-free bound. The required constant for
the restricted class has not been established.

A verified local replacement merges a clean three-cycle ring into two cycles.
An explicit grid packing also shows why this rule is insufficient alone:
`K_(2m,2m)` has a partition into `m^2` four-cycles on `4m` vertices whose
nonempty pairwise intersections always contain at least two vertices. This
obstructs the local strategy, not the conjecture itself.

For this same grid graph, an explicit matching-pair construction is now
verified to give at most `m` cycles. Each pair of consecutive cyclic-offset
matchings is connected and 2-regular, and the even-offset pairs partition
all edges. Isomorphism-transport lemmas connect this construction to the
vertex type used by the grid obstruction.

A further checked obstruction rules out extending this fixed factorization
merely by restricting each factor separately: keeping the even cyclic-offset
matchings makes every restricted factor a perfect matching. Any separate
decompositions therefore use `2m^2` pieces on `4m` vertices. This is a lower
bound for that strategy only, not for arbitrary decompositions of the graph.

The cycle-only reduction is also verified: in an even-degree graph, a
cycle-or-edge decomposition with c cycle pieces and e remaining single-edge
pieces can be replaced by at most c + floor(e/3) cycles. Thus every minimum-size
decomposition of an even-degree graph is cycle-only. Exact equivalences now
reduce the conjecture to a uniform linear cycle-only bound either for all
even-degree graphs or just for graphs with a four-cycle partition. These
reductions do not establish the required uniform constant.

A further exact reduction removes low-degree vertices by taking all incident
cycles in an existing decomposition. This costs degree(v)/2 cycles and leaves
an even graph with v isolated. Consequently, a smallest counterexample to a
cycle bound Cn has minimum degree greater than 2C. A fixed Cn bound on even
graphs above this minimum-degree threshold extends to all even graphs; the
existence of such a C is equivalent to the original conjecture and is still
unproved.

A global Hall-type constraint is verified for minimum decompositions in a
smallest counterexample to Cn. Every cycle subfamily supported on a proper
vertex subset has size at most C times that subset's size. Therefore any
subfamily of at most Cn cycles has a capacity-C vertex assignment. If the
minimum decomposition has more than Cn cycles, C distinct cycles can be
assigned to each vertex, each containing that vertex, with an additional
unassigned cycle. No cycle-count-reducing recombination has been proved
from this necessary condition.

A further verified obstruction refutes the proposed strengthening of the
three-cycle replacement rule to arbitrary nonempty pairwise intersections
with no triple intersection. An explicit 15-vertex, 4-regular graph is
partitioned into cycles of lengths 3, 14, and 13, satisfying those intersection
conditions, but it admits no replacement by two simple cycles. A finite SAT
certificate is reconstructed as an ordinary kernel-checked resolution proof
using `lrat_proof`, then connected to graph connectivity and degree constraints.
Only the three permitted axioms are used. This obstructs the proposed local
rule; three pieces on fifteen vertices do not contradict the conjecture.

Further checked reductions cover arbitrary clean rings, incidence forests for
minimum decompositions with singleton pairwise intersections, sparse edge cuts,
and edge-critical graphs. Every graph contains an edge-critical subgraph with
the same minimum decomposition size. Every edge of an edge-critical graph can
be exposed as a single-edge piece in a minimum decomposition; the single-edge
pieces of any minimum decomposition form a forest with the original degree
parities. A nonempty edge-critical graph cannot have all degrees even.

A stronger universal lower bound is now verified: any constant C that bounds
all decomposition sizes by Cn must satisfy C >= 3/2. Unbalanced complete
bipartite graphs yield this restriction. In particular, K_(3,7) needs at least
ten pieces on ten vertices. This refutes an n-1 strengthening, not O(n).
No uniform upper bound on edge-critical, highly edge-connected graphs has
been proved; the original conjecture remains unresolved.

A further obstruction rules out assuming that the even-degree vertices of a
2-connected edge-critical graph induce a forest. The join of a triangle with
an independent four-vertex set is edge-critical, stays connected after every
vertex deletion, and has exactly seven pieces in a minimum decomposition.
Its three even-degree vertices form a triangle. A general parity lower bound
using an independent vertex subset and a generic exposure-orbit criterion
prove these assertions. This is not a counterexample to the original O(n)
conjecture, which remains unresolved.
-/

open Filter SimpleGraph
namespace Erdos184Work

universe u

def IsCycleOrEdge {U : Type*} [Fintype U] (H : SimpleGraph U) : Prop :=
  open scoped Classical in
  (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1

def IsDecomposition {V : Type*} (G : SimpleGraph V) (D : Finset G.Subgraph) : Prop :=
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
  (⋃ H ∈ D, H.edgeSet) = G.edgeSet

open scoped Classical in
lemma exists_single_edge_subgraph {V : Type*} [Fintype V] (G : SimpleGraph V)
    (e : G.edgeSet) :
    ∃ H : G.Subgraph, H.edgeSet = {e.val} ∧ H.coe.edgeFinset.card = 1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with | h u v =>
  let H := G.subgraphOfAdj he
  refine ⟨H, SimpleGraph.edgeSet_subgraphOfAdj he, ?_⟩
  have hi : Function.Injective (Sym2.map (Subtype.val : H.verts → V)) :=
    Sym2.map.injective Subtype.val_injective
  have hc : H.coe.edgeSet = {s(⟨u, by simp [H]⟩, ⟨v, by simp [H]⟩)} := by
    rw [SimpleGraph.Subgraph.edgeSet_coe, SimpleGraph.edgeSet_subgraphOfAdj]
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    change Sym2.map Subtype.val x = Sym2.map (Subtype.val : H.verts → V) s(⟨u, by simp [H]⟩, ⟨v, by simp [H]⟩) ↔ _
    exact hi.eq_iff
  simp [SimpleGraph.edgeFinset, hc]

open scoped Classical in
lemma exists_edge_decomposition {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition G D ∧ D.card ≤ G.edgeFinset.card := by
  classical
  choose h hh using exists_single_edge_subgraph G
  let D : Finset G.Subgraph := Finset.univ.image h
  refine ⟨D, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro H hH
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hH
    exact Or.inr (hh e).2
  · intro H hH J hJ hne
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hJ
    change Disjoint (h e).edgeSet (h f).edgeSet
    rw [(hh e).1, (hh f).1]
    simp only [Set.disjoint_singleton]
    intro hef
    exact hne (congrArg h (Subtype.ext hef))
  · ext e
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨H, hH, he⟩
      exact H.edgeSet_subset he
    · intro he
      refine ⟨h ⟨e, he⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟨e, he⟩, Finset.mem_univ _, rfl⟩
      · rw [(hh ⟨e, he⟩).1]
        exact Set.mem_singleton e
  · calc
      D.card ≤ (Finset.univ : Finset G.edgeSet).card := Finset.card_image_le
      _ = G.edgeFinset.card := by rw [Finset.card_univ, SimpleGraph.card_edgeSet]

open scoped Classical in
lemma acyclic_card_edges_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) : G.edgeFinset.card ≤ Fintype.card V := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    have : G = ⊥ := by ext a; exact isEmptyElim a
    simp [this]
  | inr h =>
    obtain ⟨T, hGT, hT⟩ := {H : SimpleGraph V | H.IsAcyclic}.toFinite.exists_le_maximal hG
    have htree : T.IsTree := SimpleGraph.maximal_isAcyclic_iff_isTree.mp hT
    have hcard := htree.card_edgeFinset
    have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGT)
    omega

open scoped Classical in
lemma degree_sdiff_add {V : Type*} [Fintype V] (G H : SimpleGraph V)
    (hle : H ≤ G) (v : V) : (G \ H).degree v + H.degree v = G.degree v := by
  classical
  have hs : (G \ H).neighborFinset v = G.neighborFinset v \ H.neighborFinset v := by
    ext w
    simp
  rw [SimpleGraph.degree, hs]
  exact Finset.card_sdiff_add_card_eq_card (by
    intro w hw
    exact (G.mem_neighborFinset _ _).mpr (hle ((H.mem_neighborFinset _ _).mp hw)))

open scoped Classical in
lemma cycle_spanning_even {V : Type*} [Fintype V] (G : SimpleGraph V)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) (v : V) :
    Even (p.toSubgraph.spanningCoe.degree v) := by
  classical
  by_cases hv : v ∈ p.support
  · have h := hp.ncard_neighborSet_toSubgraph_eq_two hv
    have he : p.toSubgraph.spanningCoe.degree v = 2 := by
      rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      exact h
    simp [he]
  · have he : p.toSubgraph.spanningCoe.neighborFinset v = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have h := p.toSubgraph.edge_vert ((p.toSubgraph.spanningCoe.mem_neighborFinset _ _).mp hw)
      exact hv (p.mem_verts_toSubgraph.mp h)
    simp [SimpleGraph.degree, he]

open scoped Classical in
lemma exists_even_complement_forest {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      F.edgeFinset.card ≤ Fintype.card V ∧ ∀ v, Even ((G \ F).degree v) := by
  classical
  let P : SimpleGraph V → Prop := fun F =>
    F ≤ G ∧ ∀ v, F.degree v % 2 = G.degree v % 2
  have hGP : P G := ⟨le_rfl, fun _ => rfl⟩
  obtain ⟨F, hFG, hF⟩ := {H | P H}.toFinite.exists_le_minimal hGP
  have hacyclic : F.IsAcyclic := by
    intro u p hp
    let C := p.toSubgraph.spanningCoe
    have hCF : C ≤ F := p.toSubgraph.spanningCoe_le
    have hDC : P (F \ C) := by
      refine ⟨le_trans sdiff_le hFG, ?_⟩
      intro v
      have he := cycle_spanning_even F hp v
      have hd := degree_sdiff_add F C hCF v
      have hv := hF.prop.2 v
      rw [even_iff_two_dvd] at he
      obtain ⟨k, hk⟩ := he
      change C.degree v = 2 * k at hk
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hv hd hk ⊢
      omega
    have hle : F ≤ F \ C := hF.le_of_le hDC sdiff_le
    have hcu := p.toSubgraph_adj_snd hp.not_nil
    have h := hle (hCF hcu)
    exact h.2 hcu
  refine ⟨F, hFG, hacyclic, acyclic_card_edges_le F hacyclic, ?_⟩
  intro v
  have hdeg := degree_sdiff_add G F hFG v
  have hv := hF.prop.2 v
  exact Nat.even_iff.mpr (by omega)

open scoped Classical in
lemma acyclic_card_edges_lt {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) : G.edgeFinset.card < Fintype.card V := by
  classical
  obtain ⟨T, hGT, hT⟩ := {H : SimpleGraph V | H.IsAcyclic}.toFinite.exists_le_maximal hG
  have htree : T.IsTree := SimpleGraph.maximal_isAcyclic_iff_isTree.mp hT
  have hcard := htree.card_edgeFinset
  have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGT)
  omega

open scoped Classical in
lemma acyclic_even_eq_bot {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (heven : ∀ v, Even (G.degree v)) : G = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro u v huv
  have hu : u ∈ G.support := ⟨v, huv⟩
  haveI : Nonempty G.support := ⟨⟨u, hu⟩⟩
  let H := G.induce G.support
  have hlt : H.edgeFinset.card < Fintype.card G.support :=
    acyclic_card_edges_lt H (hG.induce G.support)
  have hdeg : ∀ w : G.support, 2 ≤ H.degree w := by
    intro w
    have hw := heven w
    have hpos := (G.degree_pos_iff_mem_support w).mpr w.property
    have heq : H.degree w = G.degree w :=
      SimpleGraph.degree_induce_of_support_subset Set.Subset.rfl w
    rw [Nat.even_iff] at hw
    omega
  have hs : 2 * Fintype.card G.support ≤ ∑ w : G.support, H.degree w := by
    calc
      2 * Fintype.card G.support = ∑ _w : G.support, 2 := by simp [mul_comm]
      _ ≤ ∑ w : G.support, H.degree w := Finset.sum_le_sum (fun w _ => hdeg w)
  rw [H.sum_degrees_eq_twice_card_edges] at hs
  omega

open scoped Classical in
lemma exists_cycle_of_even_ne_bot {V : Type*} [Fintype V] (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) (hne : G ≠ ⊥) :
    ∃ u : V, ∃ p : G.Walk u u, p.IsCycle := by
  classical
  by_contra h
  apply hne
  apply acyclic_even_eq_bot G _ heven
  intro u p hp
  exact h ⟨u, p, hp⟩

open scoped Classical in
lemma cycle_coe_regular {V : Type*} [Fintype V] (G : SimpleGraph V)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    p.toSubgraph.coe.Connected ∧ p.toSubgraph.coe.IsRegularOfDegree 2 := by
  classical
  refine ⟨p.toSubgraph_connected.coe, ?_⟩
  intro v
  rw [SimpleGraph.Subgraph.coe_degree, SimpleGraph.Subgraph.degree,
    ← Nat.card_eq_fintype_card]
  exact hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp v.property)

def liftSubgraph {V : Type*} {G H : SimpleGraph V} (h : H ≤ G)
    (K : H.Subgraph) : G.Subgraph where
  verts := K.verts
  Adj := K.Adj
  adj_sub hab := h (K.adj_sub hab)
  edge_vert := K.edge_vert
  symm := K.symm

open scoped Classical in
lemma lift_decomposition {V : Type*} [Fintype V] {G H : SimpleGraph V}
    (hHG : H ≤ G) (D : Finset H.Subgraph)
    (hD : ∀ K ∈ D, IsCycleOrEdge K.coe) (hdec : IsDecomposition H D) :
    ∃ D' : Finset G.Subgraph,
      (∀ K ∈ D', IsCycleOrEdge K.coe) ∧
      Set.PairwiseDisjoint (D' : Set G.Subgraph) (fun K => K.edgeSet) ∧
      (⋃ K ∈ D', K.edgeSet) = H.edgeSet ∧ D'.card ≤ D.card := by
  classical
  let D' := D.image (liftSubgraph hHG)
  refine ⟨D', ?_, ?_, ?_, Finset.card_image_le⟩
  · intro K hK
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
    exact hD L hL
  · intro K hK L hL hne
    obtain ⟨K', hK', rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨L', hL', rfl⟩ := Finset.mem_image.mp hL
    exact hdec.1 hK' hL' (fun he => hne (congrArg (liftSubgraph hHG) he))
  · rw [← hdec.2]
    ext e
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨K, hK, he⟩
      obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
      exact ⟨L, hL, he⟩
    · rintro ⟨K, hK, he⟩
      exact ⟨liftSubgraph hHG K, Finset.mem_image.mpr ⟨K, hK, rfl⟩, he⟩

open scoped Classical in
lemma combine_decompositions {V : Type*} [Fintype V] {G H K : SimpleGraph V}
    (hHG : H ≤ G) (hKG : K ≤ G)
    (hdis : Disjoint H.edgeSet K.edgeSet) (hcover : H.edgeSet ∪ K.edgeSet = G.edgeSet)
    (D₁ : Finset H.Subgraph) (D₂ : Finset K.Subgraph)
    (hD₁ : ∀ L ∈ D₁, IsCycleOrEdge L.coe) (hdec₁ : IsDecomposition H D₁)
    (hD₂ : ∀ L ∈ D₂, IsCycleOrEdge L.coe) (hdec₂ : IsDecomposition K D₂) :
    ∃ D : Finset G.Subgraph,
      (∀ L ∈ D, IsCycleOrEdge L.coe) ∧ IsDecomposition G D ∧
      D.card ≤ D₁.card + D₂.card := by
  classical
  obtain ⟨A, hA, hpA, heA, hcA⟩ := lift_decomposition hHG D₁ hD₁ hdec₁
  obtain ⟨B, hB, hpB, heB, hcB⟩ := lift_decomposition hKG D₂ hD₂ hdec₂
  refine ⟨A ∪ B, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro L hL
    rcases Finset.mem_union.mp hL with h | h
    · exact hA L h
    · exact hB L h
  · rw [Finset.coe_union]
    apply hpA.union hpB
    intro L hL M hM _
    apply hdis.mono
    · rw [← heA]
      intro e he
      exact Set.mem_iUnion.mpr ⟨L, Set.mem_iUnion.mpr ⟨hL, he⟩⟩
    · rw [← heB]
      intro e he
      exact Set.mem_iUnion.mpr ⟨M, Set.mem_iUnion.mpr ⟨hM, he⟩⟩
  · rw [← hcover, ← heA, ← heB]
    ext e
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_union, Set.mem_union]
    aesop
  · exact (Finset.card_union_le A B).trans (Nat.add_le_add hcA hcB)

open scoped Classical in
lemma cycle_edge_count {V : Type*} [Fintype V] (G : SimpleGraph V)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    p.toSubgraph.spanningCoe.edgeFinset.card = p.length := by
  classical
  have hfin : p.toSubgraph.spanningCoe.edgeFinset = p.edges.toFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, List.mem_toFinset]
    exact p.mem_edges_toSubgraph
  rw [hfin, List.toFinset_card_of_nodup hp.isTrail.edges_nodup, p.length_edges]

set_option maxHeartbeats 2000000 in
open scoped Classical in
lemma exists_cycle_decomposition {V : Type*} [Fintype V] (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ 3 * D.card ≤ G.edgeFinset.card := by
  classical
  induction hm : G.edgeFinset.card using Nat.strong_induction_on generalizing G with
  | h m ih =>
    by_cases hbot : G = ⊥
    · subst G
      refine ⟨∅, by simp, ?_, by simp⟩
      simp [IsDecomposition]
    obtain ⟨u, p, hp⟩ := exists_cycle_of_even_ne_bot G heven hbot
    let C := p.toSubgraph.spanningCoe
    have hCG : C ≤ G := p.toSubgraph.spanningCoe_le
    have hc3 : 3 ≤ C.edgeFinset.card := by
      change 3 ≤ p.toSubgraph.spanningCoe.edgeFinset.card
      rw [cycle_edge_count G hp]
      exact hp.three_le_length
    have hcount : (G \ C).edgeFinset.card + C.edgeFinset.card = G.edgeFinset.card := by
      rw [SimpleGraph.edgeFinset_sdiff]
      exact Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hCG)
    have hlt : (G \ C).edgeFinset.card < m := by omega
    have hevenR : ∀ v, Even ((G \ C).degree v) := by
      intro v
      have he := heven v
      have hc := cycle_spanning_even G hp v
      have hd := degree_sdiff_add G C hCG v
      rw [Nat.even_iff] at he hc ⊢
      change C.degree v % 2 = 0 at hc
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at he hc hd ⊢
      omega
    obtain ⟨D, hD, hdec, hbound⟩ := ih _ hlt (G \ C) (by
      intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using hevenR v) (by simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card])
    let A : Finset G.Subgraph := D.image (liftSubgraph (show G \ C ≤ G from sdiff_le))
    refine ⟨insert p.toSubgraph A, ?_, ⟨?_, ?_⟩, ?_⟩
    · intro H hH
      rcases Finset.mem_insert.mp hH with rfl | hH
      · exact cycle_coe_regular G hp
      · obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
        simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hD K hK
    · have hpair : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet) := by
        intro H hH K hK hne
        obtain ⟨H', hH', rfl⟩ := Finset.mem_image.mp hH
        obtain ⟨K', hK', rfl⟩ := Finset.mem_image.mp hK
        exact hdec.1 hH' hK' (fun he => hne (congrArg _ he))
      rw [Finset.coe_insert]
      apply hpair.insert
      intro H hH _
      obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
      change Disjoint C.edgeSet K.edgeSet
      have hdis : Disjoint C.edgeSet (G.edgeSet \ C.edgeSet) := disjoint_sdiff_self_right
      apply hdis.mono_right
      simpa only [SimpleGraph.edgeSet_sdiff] using K.edgeSet_subset
    · ext e
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨H, _, he⟩
        exact H.edgeSet_subset he
      · intro he
        by_cases heC : e ∈ C.edgeSet
        · exact ⟨p.toSubgraph, Finset.mem_insert_self _ _, heC⟩
        · have heR : e ∈ (G \ C).edgeSet := by
            rw [SimpleGraph.edgeSet_sdiff]
            exact ⟨he, heC⟩
          rw [← hdec.2] at heR
          obtain ⟨K, heK⟩ := Set.mem_iUnion.mp heR
          obtain ⟨hK, heK⟩ := Set.mem_iUnion.mp heK
          refine ⟨liftSubgraph (show G \ C ≤ G from sdiff_le) K, ?_, heK⟩
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨K, hK, rfl⟩)
    · have hcA : A.card ≤ D.card := Finset.card_image_le
      have hci := Finset.card_insert_le p.toSubgraph A
      omega

open scoped Classical in
lemma exists_decomposition_edge_bound {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      3 * D.card ≤ G.edgeFinset.card + 2 * Fintype.card V := by
  classical
  obtain ⟨F, hFG, hacyclic, hFcard, hpar⟩ := exists_even_complement_forest G
  obtain ⟨D₁, hD₁, hdec₁, hc₁⟩ := exists_cycle_decomposition (G \ F) (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hpar v)
  obtain ⟨D₂, hD₂, hdec₂, hc₂⟩ := exists_edge_decomposition F
  have hdis : Disjoint (G \ F).edgeSet F.edgeSet := by
    rw [SimpleGraph.edgeSet_sdiff]
    exact disjoint_sdiff_self_left
  have hcover : (G \ F).edgeSet ∪ F.edgeSet = G.edgeSet := by
    rw [SimpleGraph.edgeSet_sdiff]
    ext e
    constructor
    · rintro (⟨he, _⟩ | he)
      · exact he
      · exact SimpleGraph.edgeSet_mono hFG he
    · intro he
      by_cases heF : e ∈ F.edgeSet
      · exact Or.inr heF
      · exact Or.inl ⟨he, heF⟩
  obtain ⟨D, hD, hdec, hc⟩ := combine_decompositions
    (G := G) sdiff_le hFG hdis hcover D₁ D₂
    (fun H hH => Or.inl (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hD₁ H hH)) hdec₁ hD₂ hdec₂
  refine ⟨D, hD, hdec, ?_⟩
  have hsum : (G \ F).edgeFinset.card + F.edgeFinset.card = G.edgeFinset.card := by
    rw [SimpleGraph.edgeFinset_sdiff]
    exact Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hFG)
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc₁ hc₂ hFcard hsum ⊢
  omega



lemma take_isPath {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) (j : ℕ) : (p.take j).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.take_support_eq_support_take_succ]
  exact hp.support_nodup.take

lemma endpoint_edge_notMem {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) (hlen : 2 ≤ p.length) : s(u,v) ∉ p.edges := by
  intro h
  have hs := hp.eq_snd_of_mem_edges h
  have heq : p.getVert 1 = p.getVert p.length := by
    simpa [SimpleGraph.Walk.snd] using hs.symm
  have := hp.getVert_injOn (show 1 ≤ p.length by omega) (show p.length ≤ p.length by rfl) heq
  omega

lemma close_prefix_isCycle {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) (j : ℕ) (hj : j ≤ p.length) (hj2 : 2 ≤ j)
    (hadj : G.Adj u (p.getVert j)) :
    (SimpleGraph.Walk.cons hadj (p.take j).reverse).IsCycle := by
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨(take_isPath hp j).reverse, ?_⟩
  rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]
  apply endpoint_edge_notMem (take_isPath hp j)
  simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hj] using hj2

open scoped Classical in
lemma exists_long_cycle_of_min_degree {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k) (hdeg : ∀ v, k ≤ G.degree v) :
    ∃ u : V, ∃ p : G.Walk u u, p.IsCycle ∧ k + 1 ≤ p.length := by
  classical
  obtain ⟨u, v, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hneigh : ∀ w, G.Adj u w → w ∈ p.support := by
    intro w hw
    by_contra hnot
    have hq : (SimpleGraph.Walk.cons hw.symm p).IsPath :=
      (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hp, hnot⟩
    have hlen := hmax w v (.cons hw.symm p) hq
    simp only [SimpleGraph.Walk.length_cons] at hlen
    omega
  have hex : ∃ j, j ≤ p.length ∧ k ≤ j ∧ G.Adj u (p.getVert j) := by
    by_contra! hn
    have hsub : G.neighborFinset u ⊆ (Finset.Ico 1 k).image p.getVert := by
      intro w hw
      have hw' := (G.mem_neighborFinset u w).mp hw
      obtain ⟨j, hjw, hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hneigh w hw')
      have hjpos : 1 ≤ j := by
        by_contra! hjzero
        have hj0 : j = 0 := by omega
        have huw : u = w := by simpa [hj0] using hjw
        exact hw'.ne huw
      have hjlt : j < k := by
        by_contra! hjge
        exact hn j hj hjge (hjw ▸ hw')
      exact Finset.mem_image.mpr ⟨j, Finset.mem_Ico.mpr ⟨hjpos, hjlt⟩, hjw⟩
    have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
    have hdu := hdeg u
    simp only [SimpleGraph.card_neighborFinset_eq_degree, Nat.card_Ico] at hc
    omega
  obtain ⟨j, hj, hjk, hadj⟩ := hex
  refine ⟨u, .cons hadj (p.take j).reverse, close_prefix_isCycle hp j hj (by omega) hadj, ?_⟩
  simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_reverse,
    SimpleGraph.Walk.take_length, Nat.min_eq_left hj]
  omega


open scoped Classical in
lemma edges_le_of_no_long_cycle {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k)
    (hno : ∀ u (p : G.Walk u u), p.IsCycle → p.length ≤ k) :
    G.edgeFinset.card ≤ (k - 1) * Fintype.card V := by
  classical
  have main : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
      Fintype.card W = n →
      (∀ u (p : H.Walk u u), p.IsCycle → p.length ≤ k) →
      H.edgeFinset.card ≤ (k - 1) * n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ H hcard hnoH
      cases isEmpty_or_nonempty W with
      | inl he =>
        have hbot : H = ⊥ := by ext a; exact isEmptyElim a
        subst H
        simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
          SimpleGraph.edgeSet_bot]
        simp
      | inr he =>
        obtain ⟨v, hv⟩ : ∃ v, H.degree v < k := by
          by_contra! hn
          obtain ⟨v, p, hp, hlen⟩ := exists_long_cycle_of_min_degree H k hk hn
          have := hnoH v p hp
          omega
        let S : Set W := {v}ᶜ
        let K := H.induce S
        have hc : Fintype.card S = Fintype.card W - 1 := by
          change Fintype.card ↑({v}ᶜ : Set W) = _
          rw [Fintype.card_compl_set]
          simp only [Fintype.card_unique]
        have hpos : 0 < n := hcard ▸ Fintype.card_pos
        have hsmall : Fintype.card S < n := by omega
        have hnoK : ∀ u (p : K.Walk u u), p.IsCycle → p.length ≤ k := by
          intro u p hp
          let e : K ↪g H := SimpleGraph.Embedding.induce S
          have hp' := SimpleGraph.Walk.IsCycle.map (f := e.toHom) e.injective hp
          have hlen := hnoH (e u) (p.map e.toHom) hp'
          simpa using hlen
        have hb := ih (Fintype.card S) hsmall K rfl hnoK
        have hem : K.edgeFinset.card + H.degree v = H.edgeFinset.card := by
          change (H.induce {v}ᶜ).edgeFinset.card + H.degree v = H.edgeFinset.card
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
            SimpleGraph.card_edgeFinset_deleteIncidenceSet,
            Nat.sub_add_cancel (H.degree_le_card_edgeFinset v)]
        rw [hc, hcard] at hb
        have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hb hem ⊢
        simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hv hem
        have hksub : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
        nlinarith
  exact main _ G rfl hno


open scoped Classical in
lemma add_cycle_to_decomposition {V : Type*} [Fintype V] (G : SimpleGraph V)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle)
    (D : Finset (G \ p.toSubgraph.spanningCoe).Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition (G \ p.toSubgraph.spanningCoe) D) :
    ∃ D' : Finset G.Subgraph,
      (∀ H ∈ D', IsCycleOrEdge H.coe) ∧ IsDecomposition G D' ∧ D'.card ≤ D.card + 1 := by
  classical
  let C := p.toSubgraph.spanningCoe
  let K : C.Subgraph := {
    verts := p.toSubgraph.verts
    Adj := p.toSubgraph.Adj
    adj_sub := fun h => h
    edge_vert := p.toSubgraph.edge_vert
    symm := p.toSubgraph.symm }
  have hK : IsCycleOrEdge K.coe := by
    apply Or.inl
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular G hp
  have hdecK : IsDecomposition C {K} := by
    have hke : K.edgeSet = C.edgeSet := rfl
    simp [IsDecomposition, hke]
  have hCG : C ≤ G := p.toSubgraph.spanningCoe_le
  have hdis : Disjoint (G \ C).edgeSet C.edgeSet := by
    rw [SimpleGraph.edgeSet_sdiff]
    exact disjoint_sdiff_self_left
  have hcover : (G \ C).edgeSet ∪ C.edgeSet = G.edgeSet := by
    rw [SimpleGraph.edgeSet_sdiff]
    exact Set.diff_union_of_subset (SimpleGraph.edgeSet_mono hCG)
  obtain ⟨D', hD', hdec', hcard⟩ := combine_decompositions
    (G := G) sdiff_le hCG hdis hcover D {K} hD hdec
    (by simpa using hK) hdecK
  exact ⟨D', hD', hdec', by simpa using hcard⟩

set_option maxHeartbeats 2000000 in
open scoped Classical in
lemma decomposition_bound_above_threshold {V : Type*} [Fintype V]
    (q a : ℕ) (hq : 0 < q)
    (hbase : ∀ H : SimpleGraph V, H.edgeFinset.card ≤ q * Fintype.card V →
      ∃ D : Finset H.Subgraph,
        (∀ K ∈ D, IsCycleOrEdge K.coe) ∧ IsDecomposition H D ∧ D.card ≤ a)
    (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card ≤ a + G.edgeFinset.card / q := by
  classical
  induction hm : G.edgeFinset.card using Nat.strong_induction_on generalizing G with
  | h m ih =>
    by_cases hsmall : G.edgeFinset.card ≤ q * Fintype.card V
    · obtain ⟨D, hD, hdec, hc⟩ := hbase G (by
        simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hsmall)
      exact ⟨D, hD, hdec, hc.trans (Nat.le_add_right _ _)⟩
    have hex : ∃ u : V, ∃ p : G.Walk u u, p.IsCycle ∧ q + 1 < p.length := by
      by_contra! hn
      have hno : ∀ u (p : G.Walk u u), p.IsCycle → p.length ≤ q + 1 := hn
      have hb := edges_le_of_no_long_cycle G (q + 1) (by omega) hno
      have hb' : G.edgeFinset.card ≤ q * Fintype.card V := by simpa using hb
      exact hsmall hb'
    obtain ⟨u, p, hp, hplen⟩ := hex
    let C := p.toSubgraph.spanningCoe
    have hCG : C ≤ G := p.toSubgraph.spanningCoe_le
    have hcq : q ≤ C.edgeFinset.card := by
      change q ≤ p.toSubgraph.spanningCoe.edgeFinset.card
      rw [cycle_edge_count G hp]
      omega
    have hcount : (G \ C).edgeFinset.card + C.edgeFinset.card = G.edgeFinset.card := by
      rw [SimpleGraph.edgeFinset_sdiff]
      exact Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hCG)
    have hlt : (G \ C).edgeFinset.card < m := by omega
    obtain ⟨D, hD, hdec, hc⟩ := ih _ hlt (G \ C)
      (by simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card])
    obtain ⟨D', hD', hdec', hc'⟩ := add_cycle_to_decomposition G hp D hD hdec
    refine ⟨D', hD', hdec', ?_⟩
    have hdiv : (G \ C).edgeFinset.card / q + 1 ≤ G.edgeFinset.card / q := by
      calc
        (G \ C).edgeFinset.card / q + 1 = ((G \ C).edgeFinset.card + q) / q :=
          (Nat.add_div_right _ hq).symm
        _ ≤ G.edgeFinset.card / q := Nat.div_le_div_right (by omega)
    rw [← hm]
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc hdiv ⊢
    omega

open scoped Classical in
lemma decomposition_dyadic_bound {V : Type*} [Fintype V]
    (s : ℕ) (G : SimpleGraph V) (hm : G.edgeFinset.card ≤ 2 ^ s * Fintype.card V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card ≤ (2 * s + 1) * Fintype.card V := by
  classical
  induction s generalizing G with
  | zero =>
    obtain ⟨D, hD, hdec, hc⟩ := exists_edge_decomposition G
    refine ⟨D, hD, hdec, ?_⟩
    simpa using hc.trans hm
  | succ s ih =>
    obtain ⟨D, hD, hdec, hc⟩ := decomposition_bound_above_threshold
      (2 ^ s) ((2 * s + 1) * Fintype.card V) (by positivity)
      (fun H hH => ih H (by
        simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hH)) G
    refine ⟨D, hD, hdec, ?_⟩
    have hm' : G.edgeFinset.card ≤ 2 ^ s * (2 * Fintype.card V) := by
      simpa only [pow_succ, mul_assoc] using hm
    have hdiv : G.edgeFinset.card / 2 ^ s ≤ 2 * Fintype.card V := Nat.div_le_of_le_mul hm'
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc hdiv ⊢
    nlinarith

open scoped Classical in
lemma exists_decomposition_log_bound {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card ≤ (2 * Nat.clog 2 (Fintype.card V) + 1) * Fintype.card V := by
  classical
  apply decomposition_dyadic_bound
  calc
    G.edgeFinset.card ≤ (Fintype.card V).choose 2 := G.card_edgeFinset_le_card_choose_two
    _ ≤ Fintype.card V ^ 2 := Nat.choose_le_pow _ _
    _ ≤ 2 ^ Nat.clog 2 (Fintype.card V) * Fintype.card V := by
      rw [pow_two]
      exact Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _)

open scoped Classical in
lemma asymptotic_iff_uniform :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C : ℝ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ C * Fintype.card V) := by
  classical
  constructor
  · rintro ⟨f, hf, hG⟩
    obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hf
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hc
    refine ⟨max c (N : ℝ), ?_⟩
    intro V _ _ G
    by_cases hn : N ≤ Fintype.card V
    · obtain ⟨D, hD, hdec, hcard⟩ := hG G
      refine ⟨D, hD, hdec, hcard.trans ?_⟩
      calc
        f (Fintype.card V) ≤ ‖f (Fintype.card V)‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (f (Fintype.card V))
        _ ≤ c * ‖(Fintype.card V : ℝ)‖ := hN _ hn
        _ = c * (Fintype.card V : ℝ) := by rw [Real.norm_natCast]
        _ ≤ max c (N : ℝ) * (Fintype.card V : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
    · obtain ⟨D, hD, hdec, hcard⟩ := exists_edge_decomposition G
      refine ⟨D, hD, hdec, ?_⟩
      have hn' : Fintype.card V ≤ N := (Nat.le_of_not_ge hn)
      have hbound : D.card ≤ N * Fintype.card V := by
        calc
          D.card ≤ G.edgeFinset.card := hcard
          _ ≤ (Fintype.card V).choose 2 := G.card_edgeFinset_le_card_choose_two
          _ ≤ Fintype.card V ^ 2 := Nat.choose_le_pow _ _
          _ ≤ N * Fintype.card V := by
            rw [pow_two]
            exact Nat.mul_le_mul_right _ hn'
      calc
        (D.card : ℝ) ≤ (N : ℝ) * Fintype.card V := by exact_mod_cast hbound
        _ ≤ max c (N : ℝ) * (Fintype.card V : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)
  · rintro ⟨C, hC⟩
    refine ⟨fun n => C * (n : ℝ), ?_, hC⟩
    exact (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).const_mul_left C

open scoped Classical in
lemma uniform_bound_of_even_graphs (C : ℝ)
    (hEven : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ C * Fintype.card V) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ (C + 1) * Fintype.card V := by
  classical
  intro V _ _ G
  obtain ⟨F, hFG, hacyclic, hFcard, hpar⟩ := exists_even_complement_forest G
  obtain ⟨D₁, hD₁, hdec₁, hc₁⟩ := hEven (G \ F) (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hpar v)
  obtain ⟨D₂, hD₂, hdec₂, hc₂⟩ := exists_edge_decomposition F
  have hdis : Disjoint (G \ F).edgeSet F.edgeSet := by
    rw [SimpleGraph.edgeSet_sdiff]
    exact disjoint_sdiff_self_left
  have hcover : (G \ F).edgeSet ∪ F.edgeSet = G.edgeSet := by
    rw [SimpleGraph.edgeSet_sdiff]
    ext e
    constructor
    · rintro (⟨he, _⟩ | he)
      · exact he
      · exact SimpleGraph.edgeSet_mono hFG he
    · intro he
      by_cases heF : e ∈ F.edgeSet
      · exact Or.inr heF
      · exact Or.inl ⟨he, heF⟩
  obtain ⟨D, hD, hdec, hc⟩ := combine_decompositions
    (G := G) sdiff_le hFG hdis hcover D₁ D₂ hD₁ hdec₁ hD₂ hdec₂
  refine ⟨D, hD, hdec, ?_⟩
  have hcr : (D.card : ℝ) ≤ D₁.card + D₂.card := by exact_mod_cast hc
  have hfr : (D₂.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hc₂.trans hFcard
  linarith

open scoped Classical in
lemma asymptotic_iff_even_uniform :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C : ℝ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ C * Fintype.card V) := by
  rw [asymptotic_iff_uniform]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun G _ => hC G⟩
  · rintro ⟨C, hC⟩
    exact ⟨C + 1, uniform_bound_of_even_graphs C hC⟩

/-- The explicit logarithmic upper bound proved above is not itself a linear bound.
This is not a disproof of the conjecture: a better choice of decomposition may be smaller. -/
lemma logarithmic_bound_not_bigO_linear :
    ¬ ((fun n : ℕ => (((2 * Nat.clog 2 n + 1) * n : ℕ) : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ)) := by
  intro h
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hc
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt c
  let k := max N k₀
  have hNk : N ≤ k := le_max_left _ _
  have hkk : k₀ ≤ k := le_max_right _ _
  have hn : N ≤ 2 ^ k := hNk.trans (Nat.le_of_lt Nat.lt_two_pow_self)
  have hb := hN (2 ^ k) hn
  simp only [Real.norm_natCast, Nat.clog_pow 2 k (by decide), Nat.cast_mul,
    Nat.cast_add, Nat.cast_ofNat] at hb
  have hkc : c < (k : ℝ) := hk₀.trans_le (by exact_mod_cast hkk)
  have hpow : 0 < ((2 ^ k : ℕ) : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hb
  simp only [Nat.cast_one] at hb
  have hfactor : c < 2 * (k : ℝ) + 1 := by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  exact (not_lt_of_ge hb) (mul_lt_mul_of_pos_right hfactor hpow)


open scoped Classical in
lemma subgraph_edge_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H : G.Subgraph) : H.spanningCoe.edgeFinset.card = H.coe.edgeFinset.card := by
  classical
  have h := Set.ncard_image_of_injective H.coe.edgeSet
    (Sym2.map.injective (f := (Subtype.val : H.verts → V)) Subtype.val_injective)
  rw [H.image_coe_edgeSet_coe] at h
  simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    ← Set.ncard_def] using h

open scoped Classical in
lemma acyclic_piece_edge_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (H : G.Subgraph) (hH : IsCycleOrEdge H.coe) :
    H.spanningCoe.edgeFinset.card = 1 := by
  classical
  rw [subgraph_edge_card]
  rcases hH with ⟨hconn, hreg⟩ | hcard
  · simp only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hreg
    have hbot : H.coe = ⊥ := by
      apply acyclic_even_eq_bot H.coe (hG.subgraph H)
      intro v
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      rw [hreg v]
      decide
    obtain ⟨v⟩ := hconn.nonempty
    have hv := hreg v
    rw [hbot] at hv
    simp at hv
  · exact hcard

open scoped Classical in
lemma acyclic_decomposition_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D) :
    D.card = G.edgeFinset.card := by
  classical
  have hcover : D.biUnion (fun H => H.spanningCoe.edgeFinset) = G.edgeFinset := by
    ext e
    simpa only [Finset.mem_biUnion, SimpleGraph.mem_edgeFinset,
      Set.mem_iUnion, exists_prop] using Set.ext_iff.mp hdec.2 e
  have hdis : (D : Set G.Subgraph).PairwiseDisjoint
      (fun H => H.spanningCoe.edgeFinset) := by
    intro H hH K hK hne
    apply Finset.disjoint_left.mpr
    intro e heH heK
    have heH' : e ∈ H.edgeSet := SimpleGraph.mem_edgeFinset.mp heH
    have heK' : e ∈ K.edgeSet := SimpleGraph.mem_edgeFinset.mp heK
    exact Set.disjoint_left.mp (hdec.1 hH hK hne) heH' heK'
  rw [← hcover, Finset.card_biUnion hdis]
  have hsum : (∑ H ∈ D, H.spanningCoe.edgeFinset.card) = ∑ _H ∈ D, 1 := by
    apply Finset.sum_congr rfl
    intro H hH
    exact acyclic_piece_edge_card hG H (hD H hH)
  rw [hsum]
  simp

open scoped Classical in
lemma tree_decomposition_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsTree) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D) :
    D.card + 1 = Fintype.card V := by
  rw [acyclic_decomposition_card hG.2 D hD hdec]
  exact hG.card_edgeFinset

open scoped Classical in
lemma universal_bound_ge_tree (f : ℕ → ℝ)
    (hf : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V)) (n : ℕ) :
    (n : ℝ) ≤ f (n + 1) := by
  classical
  let V := ULift.{u} (Fin (n + 1))
  obtain ⟨T, _, hT⟩ := (SimpleGraph.connected_top (V := V)).exists_isTree_le
  obtain ⟨D, hD, hdec, hc⟩ := hf T
  have hcard := tree_decomposition_card hT D hD hdec
  have hV : Fintype.card V = n + 1 := by simp [V]
  rw [hV] at hcard hc
  have hDcard : D.card = n := by omega
  simpa only [hDcard] using hc

open scoped Classical in
lemma universal_linear_constant_ge_one (C : ℝ)
    (hC : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ C * Fintype.card V) : 1 ≤ C := by
  by_contra h
  have hpos : 0 < 1 - C := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (1 - C))
  have hn' : C < (n : ℝ) * (1 - C) := (div_lt_iff₀ hpos).mp hn
  have hb := universal_bound_ge_tree (fun n => C * (n : ℝ)) hC n
  simp only [Nat.cast_add, Nat.cast_one] at hb
  nlinarith

section Rotations
open scoped List

variable {V : Type*} {G : SimpleGraph V} {u v : V}

def rotatePath (p : G.Walk u v) (i : ℕ) (hi : G.Adj u (p.getVert i)) :
    G.Walk (p.getVert (i - 1)) v :=
  (p.take (i - 1)).reverse.append (.cons hi (p.drop i))

lemma rotatePath_length (p : G.Walk u v) (i : ℕ) (hi : G.Adj u (p.getVert i))
    (hi0 : 1 ≤ i) (hil : i ≤ p.length) : (rotatePath p i hi).length = p.length := by
  simp only [rotatePath, Walk.length_append, Walk.length_reverse, Walk.take_length,
    Walk.length_cons, Walk.drop_length]
  omega

lemma rotatePath_support (p : G.Walk u v) (i : ℕ) (hi : G.Adj u (p.getVert i))
    (hi0 : 1 ≤ i) (hil : i ≤ p.length) :
    (rotatePath p i hi).support = (p.support.take i).reverse ++ p.support.drop i := by
  simp only [rotatePath, Walk.support_append, Walk.support_reverse,
    Walk.take_support_eq_support_take_succ, Walk.support_cons, List.tail_cons,
    Walk.drop_support_eq_support_drop_min, Nat.min_eq_left hil,
    Nat.sub_add_cancel hi0]

lemma rotatePath_isPath {p : G.Walk u v} (hp : p.IsPath) (i : ℕ)
    (hi : G.Adj u (p.getVert i)) (hi0 : 1 ≤ i) (hil : i ≤ p.length) :
    (rotatePath p i hi).IsPath := by
  rw [Walk.isPath_def, rotatePath_support p i hi hi0 hil]
  have hperm : (p.support.take i).reverse ++ p.support.drop i ~ p.support := by
    calc
      _ ~ p.support.take i ++ p.support.drop i :=
        (List.reverse_perm _).append_right _
      _ = _ := List.take_append_drop _ _
  exact hperm.nodup_iff.mpr hp.support_nodup

lemma rotatePath_getVert_ge (p : G.Walk u v) (i : ℕ) (hi : G.Adj u (p.getVert i))
    (hi0 : 1 ≤ i) (hil : i ≤ p.length) (j : ℕ) (hij : i ≤ j) :
    (rotatePath p i hi).getVert j = p.getVert j := by
  have ht : i - 1 ≤ p.length := by omega
  simp only [rotatePath, Walk.getVert_append, Walk.length_reverse, Walk.take_length,
    Nat.min_eq_left ht, if_neg (show ¬j < i - 1 by omega)]
  rw [Walk.getVert_cons _ _ (by omega), Walk.drop_getVert]
  congr 1
  omega

open scoped Classical in
lemma pairwise_small_inter_union_bound {α β : Type*} (S : Finset α) (A : α → Finset β)
    (hinter : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (A a ∩ A b).card ≤ 1) :
    2 * (∑ a ∈ S, (A a).card) + S.card ≤
      2 * (S.biUnion A).card + S.card * S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hS : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (A a ∩ A b).card ≤ 1 := by
      intro b hb c hc hbc
      exact hinter b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc) hbc
    have hi := ih hS
    have hinter' : (A a ∩ S.biUnion A).card ≤ S.card := by
      rw [Finset.inter_biUnion]
      simpa using Finset.card_biUnion_le_card_mul S (fun b => A a ∩ A b) 1 (by
        intro b hb
        exact hinter a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb)
          (by intro hab; subst b; exact ha hb))
    have hu := Finset.card_union_add_card_inter (A a) (S.biUnion A)
    simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      Finset.biUnion_insert]
    nlinarith

lemma longest_path_neighbors_mem {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ a b (q : G.Walk a b), q.IsPath → q.length ≤ p.length) :
    ∀ w, G.Adj u w → w ∈ p.support := by
  intro w hw
  by_contra hnot
  have hq : (Walk.cons hw.symm p).IsPath :=
    (Walk.cons_isPath_iff _ _).mpr ⟨hp, hnot⟩
  have hlen := hmax w v (.cons hw.symm p) hq
  simp only [Walk.length_cons] at hlen
  omega

lemma path_neighbor_index_lt {p : G.Walk u v} (hp : p.IsPath) (k : ℕ) (hk : 2 ≤ k)
    (hno : ∀ a (c : G.Walk a a), c.IsCycle → c.length ≤ k)
    (j : ℕ) (hj : j ≤ p.length) (hadj : G.Adj u (p.getVert j)) : j < k := by
  by_contra! hjk
  have hc := hno u (.cons hadj (p.take j).reverse)
    (close_prefix_isCycle hp j hj (by omega) hadj)
  simp only [Walk.length_cons, Walk.length_reverse, Walk.take_length,
    Nat.min_eq_left hj] at hc
  omega

open scoped Classical in
lemma rotation_neighbors_prefix [Fintype V] {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ a b (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    (k : ℕ) (hk : 2 ≤ k)
    (hno : ∀ a (c : G.Walk a a), c.IsCycle → c.length ≤ k)
    (i : ℕ) (hi0 : 1 ≤ i) (hil : i ≤ p.length) (hi : G.Adj u (p.getVert i)) :
    G.neighborFinset (p.getVert (i - 1)) ⊆ (Finset.range k).image p.getVert := by
  classical
  let q := rotatePath p i hi
  have hq : q.IsPath := rotatePath_isPath hp i hi hi0 hil
  have hql : q.length = p.length := rotatePath_length p i hi hi0 hil
  have hqmax : ∀ a b (r : G.Walk a b), r.IsPath → r.length ≤ q.length := by
    simpa only [hql] using hmax
  have hik : i < k := path_neighbor_index_lt hp k hk hno i hil hi
  intro w hw
  have hwAdj : G.Adj (p.getVert (i - 1)) w := G.mem_neighborFinset _ _ |>.mp hw
  have hwq := longest_path_neighbors_mem hq hqmax w hwAdj
  have hwp : w ∈ p.support := by
    rw [rotatePath_support p i hi hi0 hil] at hwq
    simp only [List.mem_append, List.mem_reverse] at hwq
    rcases hwq with h | h
    · exact List.mem_of_mem_take h
    · exact List.mem_of_mem_drop h
  obtain ⟨j, hjw, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hwp
  have hjk : j < k := by
    by_contra! hjk
    have hij : i ≤ j := by omega
    have heq : q.getVert j = w := (rotatePath_getVert_ge p i hi hi0 hil j hij).trans hjw
    have hadj : G.Adj (p.getVert (i - 1)) (q.getVert j) := heq.symm ▸ hwAdj
    have hlt := path_neighbor_index_lt hq k hk hno j (by omega) hadj
    omega
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjk, hjw⟩

open scoped Classical in
lemma min_degree_square_le_of_no_long_cycle [Fintype V] [Nonempty V]
    (d k : ℕ) (hk : 2 ≤ k) (hdeg : ∀ x, d ≤ G.degree x)
    (hinter : ∀ x y, x ≠ y → (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 1)
    (hno : ∀ a (c : G.Walk a a), c.IsCycle → c.length ≤ k) :
    d * d + d ≤ 2 * k := by
  classical
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  let I := (Finset.Icc 1 p.length).filter (fun i => G.Adj u (p.getVert i))
  have hImem : ∀ i, i ∈ I ↔ 1 ≤ i ∧ i ≤ p.length ∧ G.Adj u (p.getVert i) := by
    intro i
    simp only [I, Finset.mem_filter, Finset.mem_Icc, and_assoc]
  have hIcard : I.card = G.degree u := by
    rw [← G.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun i _ => p.getVert i)
    · intro i hi
      exact (G.mem_neighborFinset _ _).mpr ((hImem i).mp hi).2.2
    · intro i hi j hj heq
      exact hp.getVert_injOn ((hImem i).mp hi).2.1 ((hImem j).mp hj).2.1 heq
    · intro w hw
      have hwa : G.Adj u w := (G.mem_neighborFinset _ _).mp hw
      obtain ⟨i, hiw, hil⟩ := Walk.mem_support_iff_exists_getVert.mp
        (longest_path_neighbors_mem hp hmax w hwa)
      have hi0 : 1 ≤ i := by
        by_contra! hi0
        have hi : i = 0 := by omega
        have huw : u = w := by simpa [hi] using hiw
        exact hwa.ne huw
      exact ⟨i, (hImem i).mpr ⟨hi0, hil, hiw.symm ▸ hwa⟩, hiw⟩
  let R := I.image (fun i => p.getVert (i - 1))
  have hRcard : R.card = G.degree u := by
    rw [← hIcard]
    apply Finset.card_image_iff.mpr
    intro i hi j hj heq
    have hi' := (hImem i).mp hi
    have hj' := (hImem j).mp hj
    have he := hp.getVert_injOn (show i - 1 ≤ p.length by omega)
      (show j - 1 ≤ p.length by omega) heq
    omega
  obtain ⟨S, hSR, hScard⟩ := Finset.exists_subset_card_eq
    (show d ≤ R.card by rw [hRcard]; exact hdeg u)
  have hSprefix : S.biUnion (fun x => G.neighborFinset x) ⊆ (Finset.range k).image p.getVert := by
    intro w hw
    obtain ⟨x, hx, hwx⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp (hSR hx)
    have hi' := (hImem i).mp hi
    subst x
    exact rotation_neighbors_prefix hp hmax k hk hno i hi'.1 hi'.2.1 hi'.2.2 hwx
  have hScount : (S.biUnion (fun x => G.neighborFinset x)).card ≤ k := by
    exact (Finset.card_le_card hSprefix).trans (Finset.card_image_le.trans (by simp))
  have hsum : d * d ≤ ∑ x ∈ S, (G.neighborFinset x).card := by
    calc
      d * d = ∑ _x ∈ S, d := by simp [hScard]
      _ ≤ _ := Finset.sum_le_sum (fun x _ => by simpa using hdeg x)
  have hbound := pairwise_small_inter_union_bound S (fun x => G.neighborFinset x)
    (fun x _ y _ hxy => hinter x y hxy)
  rw [hScard] at hbound
  nlinarith

/-- No two distinct vertices have two distinct common neighbors. -/
def UniqueCommonNeighbors (G : SimpleGraph V) : Prop :=
  ∀ {x y z w : V}, x ≠ y → G.Adj x z → G.Adj y z → G.Adj x w → G.Adj y w → z = w

lemma UniqueCommonNeighbors.mono {H : SimpleGraph V} (h : UniqueCommonNeighbors G)
    (hHG : H ≤ G) : UniqueCommonNeighbors H := by
  intro x y z w hxy hxz hyz hxw hyw
  exact h hxy (hHG hxz) (hHG hyz) (hHG hxw) (hHG hyw)

lemma UniqueCommonNeighbors.induce (h : UniqueCommonNeighbors G) (S : Set V) :
    UniqueCommonNeighbors (G.induce S) := by
  intro x y z w hxy hxz hyz hxw hyw
  exact Subtype.ext (h (fun heq => hxy (Subtype.ext heq)) hxz hyz hxw hyw)

open scoped Classical in
lemma UniqueCommonNeighbors.card_inter_le [Fintype V] (h : UniqueCommonNeighbors G)
    (x y : V) (hxy : x ≠ y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro z hz w hw
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz hw
  exact h hxy hz.1 hz.2 hw.1 hw.2


open scoped Classical in
lemma unique_neighbors_edges_le_of_no_long_cycle {V : Type u} [Fintype V]
    (G : SimpleGraph V) (d k : ℕ) (hd : 0 < d) (hk : 2 ≤ k)
    (hdk : 2 * k < d * d + d) (huni : UniqueCommonNeighbors G)
    (hno : ∀ u (p : G.Walk u u), p.IsCycle → p.length ≤ k) :
    G.edgeFinset.card ≤ (d - 1) * Fintype.card V := by
  classical
  have main : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
      Fintype.card W = n → UniqueCommonNeighbors H →
      (∀ u (p : H.Walk u u), p.IsCycle → p.length ≤ k) →
      H.edgeFinset.card ≤ (d - 1) * n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ H hcard huniH hnoH
      cases isEmpty_or_nonempty W with
      | inl he =>
        have hbot : H = ⊥ := by ext a; exact isEmptyElim a
        subst H
        simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
          SimpleGraph.edgeSet_bot]
        simp
      | inr he =>
        obtain ⟨v, hv⟩ : ∃ v, H.degree v < d := by
          by_contra! hn
          have hb := min_degree_square_le_of_no_long_cycle d k hk hn
            huniH.card_inter_le hnoH
          omega
        let S : Set W := {v}ᶜ
        let K := H.induce S
        have hc : Fintype.card S = Fintype.card W - 1 := by
          change Fintype.card ↑({v}ᶜ : Set W) = _
          rw [Fintype.card_compl_set]
          simp only [Fintype.card_unique]
        have hpos : 0 < n := hcard ▸ Fintype.card_pos
        have hsmall : Fintype.card S < n := by omega
        have hnoK : ∀ u (p : K.Walk u u), p.IsCycle → p.length ≤ k := by
          intro u p hp
          let e : K ↪g H := SimpleGraph.Embedding.induce S
          have hp' := SimpleGraph.Walk.IsCycle.map (f := e.toHom) e.injective hp
          have hlen := hnoH (e u) (p.map e.toHom) hp'
          simpa using hlen
        have hb := ih (Fintype.card S) hsmall K rfl (huniH.induce S) hnoK
        have hem : K.edgeFinset.card + H.degree v = H.edgeFinset.card := by
          change (H.induce {v}ᶜ).edgeFinset.card + H.degree v = H.edgeFinset.card
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
            SimpleGraph.card_edgeFinset_deleteIncidenceSet,
            Nat.sub_add_cancel (H.degree_le_card_edgeFinset v)]
        rw [hc, hcard] at hb
        have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hb hem ⊢
        simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hv hem
        have hksub : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
        nlinarith
  exact main _ G rfl huni hno



end Rotations

set_option maxHeartbeats 2000000 in
open scoped Classical in
lemma scaled_decomposition_above_threshold {V : Type*} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hmono : ∀ H K, P H → K ≤ H → P K)
    (q L t a b : ℕ) (hL : 0 < L)
    (hbase : ∀ H : SimpleGraph V, P H → H.edgeFinset.card ≤ q * Fintype.card V →
      ∃ D : Finset H.Subgraph,
        (∀ K ∈ D, IsCycleOrEdge K.coe) ∧ IsDecomposition H D ∧ t * D.card + b ≤ a)
    (hcycle : ∀ H : SimpleGraph V, P H → q * Fintype.card V < H.edgeFinset.card →
      ∃ (u : V) (p : H.Walk u u), p.IsCycle ∧ L ≤ p.length)
    (G : SimpleGraph V) (hPG : P G) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      t * D.card + b ≤ a + t * (G.edgeFinset.card / L) := by
  classical
  induction hm : G.edgeFinset.card using Nat.strong_induction_on generalizing G with
  | h m ih =>
    by_cases hsmall : G.edgeFinset.card ≤ q * Fintype.card V
    · obtain ⟨D, hD, hdec, hc⟩ := hbase G hPG (by
        simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hsmall)
      exact ⟨D, hD, hdec, hc.trans (Nat.le_add_right _ _)⟩
    obtain ⟨u, p, hp, hplen⟩ := hcycle G hPG (lt_of_not_ge hsmall)
    let C := p.toSubgraph.spanningCoe
    have hCG : C ≤ G := p.toSubgraph.spanningCoe_le
    have hcL : L ≤ C.edgeFinset.card := by
      change L ≤ p.toSubgraph.spanningCoe.edgeFinset.card
      rw [cycle_edge_count G hp]
      exact hplen
    have hcount : (G \ C).edgeFinset.card + C.edgeFinset.card = G.edgeFinset.card := by
      rw [SimpleGraph.edgeFinset_sdiff]
      exact Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hCG)
    have hlt : (G \ C).edgeFinset.card < m := by omega
    obtain ⟨D, hD, hdec, hc⟩ := ih _ hlt (G \ C) (hmono _ _ hPG sdiff_le)
      (by simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card])
    obtain ⟨D', hD', hdec', hc'⟩ := add_cycle_to_decomposition G hp D hD hdec
    refine ⟨D', hD', hdec', ?_⟩
    have hdiv : (G \ C).edgeFinset.card / L + 1 ≤ G.edgeFinset.card / L := by
      calc
        (G \ C).edgeFinset.card / L + 1 = ((G \ C).edgeFinset.card + L) / L :=
          (Nat.add_div_right _ hL).symm
        _ ≤ G.edgeFinset.card / L := Nat.div_le_div_right (by omega)
    rw [← hm]
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc hdiv ⊢
    nlinarith [Nat.mul_le_mul_left t hc', Nat.mul_le_mul_left t hdiv]

open scoped Classical in
lemma unique_neighbors_decomposition_scaled {V : Type*} [Fintype V]
    (s : ℕ) (G : SimpleGraph V) (huni : UniqueCommonNeighbors G)
    (hm : G.edgeFinset.card ≤ 2 ^ (s + 1) * Fintype.card V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      2 ^ s * D.card + 4 * Fintype.card V ≤ 6 * 2 ^ s * Fintype.card V := by
  classical
  induction s generalizing G with
  | zero =>
    obtain ⟨D, hD, hdec, hc⟩ := exists_edge_decomposition G
    refine ⟨D, hD, hdec, ?_⟩
    simp only [Nat.zero_add, pow_one] at hm
    simp only [pow_zero, one_mul]
    omega
  | succ s ih =>
    let t := 2 ^ s
    have ht : 0 < t := by positivity
    have hcycles : ∀ H : SimpleGraph V, UniqueCommonNeighbors H →
        (2 * t) * Fintype.card V < H.edgeFinset.card →
        ∃ (u : V) (p : H.Walk u u), p.IsCycle ∧ 2 * t * t ≤ p.length := by
      intro H hH hmH
      by_contra! hn
      have hno : ∀ u (p : H.Walk u u), p.IsCycle → p.length ≤ 2 * t * t := by
        intro u p hp
        exact (hn u p hp).le
      have hb := unique_neighbors_edges_le_of_no_long_cycle H (2 * t + 1) (2 * t * t)
        (by omega) (by nlinarith) (by nlinarith) hH hno
      simp only [Nat.add_sub_cancel] at hb
      omega
    obtain ⟨D, hD, hdec, hc⟩ := scaled_decomposition_above_threshold
      UniqueCommonNeighbors (fun _ _ h hle => h.mono hle)
      (2 * t) (2 * t * t) t (6 * t * Fintype.card V) (4 * Fintype.card V)
      (by positivity)
      (fun H hH hmH => ih H hH (by simpa [t, pow_succ, mul_comm 2] using hmH))
      hcycles G huni
    refine ⟨D, hD, hdec, ?_⟩
    have hm' : G.edgeFinset.card ≤ 4 * t * Fintype.card V := by
      simp only [pow_succ] at hm
      change G.edgeFinset.card ≤ 4 * 2 ^ s * Fintype.card V
      nlinarith
    have hd := Nat.div_mul_le_self G.edgeFinset.card (2 * t * t)
    have hdiv : t * (G.edgeFinset.card / (2 * t * t)) ≤ 2 * Fintype.card V := by
      nlinarith
    change 2 ^ (s + 1) * D.card + 4 * Fintype.card V ≤
      6 * 2 ^ (s + 1) * Fintype.card V
    rw [pow_succ]
    change (t * 2) * D.card + 4 * Fintype.card V ≤ 6 * (t * 2) * Fintype.card V
    nlinarith

open scoped Classical in
lemma unique_neighbors_decomposition_linear {V : Type*} [Fintype V]
    (G : SimpleGraph V) (huni : UniqueCommonNeighbors G) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card ≤ 6 * Fintype.card V := by
  classical
  let s := Fintype.card V
  have hs : Fintype.card V ≤ 2 ^ (s + 1) := by
    exact Nat.le_trans (Nat.le_of_lt Nat.lt_two_pow_self)
      (Nat.pow_le_pow_right (by decide) (Nat.le_succ s))
  have hm : G.edgeFinset.card ≤ 2 ^ (s + 1) * Fintype.card V := by
    calc
      _ ≤ (Fintype.card V).choose 2 := G.card_edgeFinset_le_card_choose_two
      _ ≤ Fintype.card V ^ 2 := Nat.choose_le_pow _ _
      _ ≤ _ := by nlinarith
  obtain ⟨D, hD, hdec, hc⟩ := unique_neighbors_decomposition_scaled s G huni hm
  refine ⟨D, hD, hdec, ?_⟩
  have hpos : 0 < 2 ^ s := by positivity
  nlinarith

lemma uniqueCommonNeighbors_iff_no_four_cycle {V : Type*} (G : SimpleGraph V) :
    UniqueCommonNeighbors G ↔ ∀ u (p : G.Walk u u), p.IsCycle → p.length ≠ 4 := by
  constructor
  · intro huni u p hp hlen
    have h02 : p.getVert 0 ≠ p.getVert 2 := by
      intro h
      have := hp.getVert_injOn' (by omega : 0 ≤ p.length - 1)
        (by omega : 2 ≤ p.length - 1) h
      omega
    have h01 := p.adj_getVert_succ (i := 0) (by omega)
    have h12 := p.adj_getVert_succ (i := 1) (by omega)
    have h23 := p.adj_getVert_succ (i := 2) (by omega)
    have h30 := p.adj_getVert_succ (i := 3) (by omega)
    have heq : p.getVert 4 = p.getVert 0 := by simp [← hlen]
    simp only [show 3 + 1 = 4 from rfl, heq] at h30
    have h13 := huni h02 h01 h12.symm h30.symm h23
    have := hp.getVert_injOn' (by omega : 1 ≤ p.length - 1)
      (by omega : 3 ≤ p.length - 1) h13
    omega
  · intro hno x y z w hxy hxz hyz hxw hyw
    by_contra hzw
    let q : G.Walk z x := .cons hyz.symm (.cons hyw (.cons hxw.symm .nil))
    have hq : q.IsPath := by
      simp [q, SimpleGraph.Walk.isPath_def, hyz.ne.symm, hzw, hxz.ne.symm,
        hyw.ne, hxy.symm, hxw.ne.symm]
    have hc : (SimpleGraph.Walk.cons hxz q).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨hq, ?_⟩
      rw [Sym2.eq_swap]
      exact endpoint_edge_notMem hq (by simp [q])
    exact hno x (.cons hxz q) hc (by simp [q])

open scoped Classical in
lemma no_four_cycle_decomposition_linear {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (hno : ∀ u (p : G.Walk u u), p.IsCycle → p.length ≠ 4) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card ≤ 6 * Fintype.card V :=
  unique_neighbors_decomposition_linear G ((uniqueCommonNeighbors_iff_no_four_cycle G).mpr hno)

open scoped Classical in
lemma lift_decomposition_property
    (P : ∀ {W : Type u} [Fintype W], SimpleGraph W → Prop) {V : Type u} [Fintype V] {G H : SimpleGraph V}
    (hHG : H ≤ G) (D : Finset H.Subgraph)
    (hD : ∀ K ∈ D, P K.coe) (hdec : IsDecomposition H D) :
    ∃ D' : Finset G.Subgraph,
      (∀ K ∈ D', P K.coe) ∧
      Set.PairwiseDisjoint (D' : Set G.Subgraph) (fun K => K.edgeSet) ∧
      (⋃ K ∈ D', K.edgeSet) = H.edgeSet ∧ D'.card ≤ D.card := by
  classical
  let D' := D.image (liftSubgraph hHG)
  refine ⟨D', ?_, ?_, ?_, Finset.card_image_le⟩
  · intro K hK
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
    exact hD L hL
  · intro K hK L hL hne
    obtain ⟨K', hK', rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨L', hL', rfl⟩ := Finset.mem_image.mp hL
    exact hdec.1 hK' hL' (fun he => hne (congrArg (liftSubgraph hHG) he))
  · rw [← hdec.2]
    ext e
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨K, hK, he⟩
      obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
      exact ⟨L, hL, he⟩
    · rintro ⟨K, hK, he⟩
      exact ⟨liftSubgraph hHG K, Finset.mem_image.mpr ⟨K, hK, rfl⟩, he⟩

open scoped Classical in
lemma combine_decompositions_property
    (P : ∀ {W : Type u} [Fintype W], SimpleGraph W → Prop) {V : Type u} [Fintype V] {G H K : SimpleGraph V}
    (hHG : H ≤ G) (hKG : K ≤ G)
    (hdis : Disjoint H.edgeSet K.edgeSet) (hcover : H.edgeSet ∪ K.edgeSet = G.edgeSet)
    (D₁ : Finset H.Subgraph) (D₂ : Finset K.Subgraph)
    (hD₁ : ∀ L ∈ D₁, P L.coe) (hdec₁ : IsDecomposition H D₁)
    (hD₂ : ∀ L ∈ D₂, P L.coe) (hdec₂ : IsDecomposition K D₂) :
    ∃ D : Finset G.Subgraph,
      (∀ L ∈ D, P L.coe) ∧ IsDecomposition G D ∧
      D.card ≤ D₁.card + D₂.card := by
  classical
  obtain ⟨A, hA, hpA, heA, hcA⟩ := lift_decomposition_property P hHG D₁ hD₁ hdec₁
  obtain ⟨B, hB, hpB, heB, hcB⟩ := lift_decomposition_property P hKG D₂ hD₂ hdec₂
  refine ⟨A ∪ B, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro L hL
    rcases Finset.mem_union.mp hL with h | h
    · exact hA L h
    · exact hB L h
  · rw [Finset.coe_union]
    apply hpA.union hpB
    intro L hL M hM _
    apply hdis.mono
    · rw [← heA]
      intro e he
      exact Set.mem_iUnion.mpr ⟨L, Set.mem_iUnion.mpr ⟨hL, he⟩⟩
    · rw [← heB]
      intro e he
      exact Set.mem_iUnion.mpr ⟨M, Set.mem_iUnion.mpr ⟨hM, he⟩⟩
  · rw [← hcover, ← heA, ← heB]
    ext e
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_union, Set.mem_union]
    aesop
  · exact (Finset.card_union_le A B).trans (Nat.add_le_add hcA hcB)

open scoped Classical in
/-- A connected four-edge cycle. -/
def IsFourCycle {W : Type*} [Fintype W] (H : SimpleGraph W) : Prop :=
  H.Connected ∧ H.IsRegularOfDegree 2 ∧ H.edgeFinset.card = 4

open scoped Classical in
/-- The edges already admit a partition into four-cycles. The eventual decomposition
need not retain these four-cycles. -/
def HasFourCyclePartition {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, IsFourCycle H.coe) ∧ IsDecomposition G D

lemma hasFourCyclePartition_bot {V : Type*} [Fintype V] :
    HasFourCyclePartition (⊥ : SimpleGraph V) := by
  refine ⟨∅, by simp, ?_⟩
  simp [IsDecomposition]

open scoped Classical in
lemma hasFourCyclePartition_cycle {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u : V} (p : G.Walk u u) (hp : p.IsCycle) (hlen : p.length = 4) :
    HasFourCyclePartition p.toSubgraph.spanningCoe := by
  classical
  let C := p.toSubgraph.spanningCoe
  let K : C.Subgraph := {
    verts := p.toSubgraph.verts
    Adj := p.toSubgraph.Adj
    adj_sub := fun h => h
    edge_vert := p.toSubgraph.edge_vert
    symm := p.toSubgraph.symm }
  have hKreg : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2 := by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular G hp
  refine ⟨{K}, ?_, ?_⟩
  · intro H hH
    have hHK : H = K := by simpa using hH
    subst H
    refine ⟨hKreg.1, ?_, ?_⟩
    · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hKreg.2
    · rw [← subgraph_edge_card]
      change C.edgeFinset.card = 4
      exact (cycle_edge_count G hp).trans hlen
  · have hke : K.edgeSet = C.edgeSet := rfl
    change IsDecomposition C {K}
    simp [IsDecomposition, hke]

open scoped Classical in
lemma HasFourCyclePartition.sup {V : Type*} [Fintype V] {G H : SimpleGraph V}
    (hG : HasFourCyclePartition G) (hH : HasFourCyclePartition H)
    (hdis : Disjoint G.edgeSet H.edgeSet) : HasFourCyclePartition (G ⊔ H) := by
  obtain ⟨D₁, hD₁, hdec₁⟩ := hG
  obtain ⟨D₂, hD₂, hdec₂⟩ := hH
  obtain ⟨D, hD, hdec, _⟩ := combine_decompositions_property IsFourCycle
    (G := G ⊔ H) le_sup_left le_sup_right hdis (SimpleGraph.edgeSet_sup G H).symm
    D₁ D₂ hD₁ hdec₁ hD₂ hdec₂
  exact ⟨D, hD, hdec⟩

open scoped Classical in
lemma exists_four_cycle_partition_complement {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ HasFourCyclePartition H ∧
      ∀ u (p : (G \ H).Walk u u), p.IsCycle → p.length ≠ 4 := by
  classical
  let P : SimpleGraph V → Prop := fun H => H ≤ G ∧ HasFourCyclePartition H
  have hPbot : P ⊥ := ⟨bot_le, hasFourCyclePartition_bot⟩
  obtain ⟨H, _, hH⟩ := {H | P H}.toFinite.exists_le_maximal hPbot
  refine ⟨H, hH.prop.1, hH.prop.2, ?_⟩
  intro u p hp hlen
  let C := p.toSubgraph.spanningCoe
  have hCsub : C ≤ G \ H := p.toSubgraph.spanningCoe_le
  have hC : HasFourCyclePartition C := hasFourCyclePartition_cycle p hp hlen
  have hdis : Disjoint H.edgeSet C.edgeSet := by
    apply disjoint_sdiff_self_right.mono_right
    simpa only [SimpleGraph.edgeSet_sdiff] using SimpleGraph.edgeSet_mono hCsub
  have hPsup : P (H ⊔ C) :=
    ⟨sup_le hH.prop.1 (hCsub.trans sdiff_le), hH.prop.2.sup hC hdis⟩
  have hsupH : H ⊔ C ≤ H := hH.le_of_ge hPsup le_sup_left
  have hCH : C ≤ H := le_trans le_sup_right hsupH
  have hcu : C.Adj u p.snd := p.toSubgraph_adj_snd hp.not_nil
  exact (hCsub hcu).2 (hCH hcu)

open scoped Classical in
lemma uniform_bound_of_four_cycle_partitions (C : ℝ)
    (hFour : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      HasFourCyclePartition G →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ C * Fintype.card V) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ (C + 6) * Fintype.card V := by
  classical
  intro V _ _ G
  obtain ⟨H, hHG, hH, hno⟩ := exists_four_cycle_partition_complement G
  obtain ⟨D₁, hD₁, hdec₁, hc₁⟩ := no_four_cycle_decomposition_linear (G \ H) hno
  obtain ⟨D₂, hD₂, hdec₂, hc₂⟩ := hFour H hH
  have hdis : Disjoint (G \ H).edgeSet H.edgeSet := by
    rw [SimpleGraph.edgeSet_sdiff]
    exact disjoint_sdiff_self_left
  have hcover : (G \ H).edgeSet ∪ H.edgeSet = G.edgeSet := by
    rw [SimpleGraph.edgeSet_sdiff]
    exact Set.diff_union_of_subset (SimpleGraph.edgeSet_mono hHG)
  obtain ⟨D, hD, hdec, hc⟩ := combine_decompositions
    (G := G) sdiff_le hHG hdis hcover D₁ D₂ hD₁ hdec₁ hD₂ hdec₂
  refine ⟨D, hD, hdec, ?_⟩
  have hcr : (D.card : ℝ) ≤ D₁.card + D₂.card := by exact_mod_cast hc
  have hfr : (D₁.card : ℝ) ≤ 6 * Fintype.card V := by exact_mod_cast hc₁
  linarith

open scoped Classical in
lemma asymptotic_iff_four_cycle_uniform :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C : ℝ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      HasFourCyclePartition G →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ C * Fintype.card V) := by
  rw [asymptotic_iff_uniform]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun G _ => hC G⟩
  · rintro ⟨C, hC⟩
    exact ⟨C + 6, uniform_bound_of_four_cycle_partitions C hC⟩

section Recombination

variable {V : Type*} {G : SimpleGraph V}

lemma path_start_not_mem_tail {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    u ∉ p.support.tail := by
  have h := hp.support_nodup
  rw [p.support_eq_cons, List.nodup_cons] at h
  exact h.1

lemma append_isPath_of_support_inter {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = v) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup.tail, List.disjoint_iff_ne.mp ?_⟩
  intro x hxp hxq
  have hxv := hinter x hxp (List.mem_of_mem_tail hxq)
  exact path_start_not_mem_tail hq (hxv ▸ hxq)

lemma append_isCycle_of_support_inter {u v : V} {p : G.Walk u v} {q : G.Walk v u}
    (hp : p.IsPath) (hq : q.IsPath) (huv : u ≠ v)
    (hedge : p.edges.Disjoint q.edges)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = u ∨ x = v) :
    (p.append q).IsCycle := by
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [Walk.isTrail_def, Walk.edges_append, List.nodup_append]
    exact ⟨hp.isTrail.edges_nodup, hq.isTrail.edges_nodup, List.disjoint_iff_ne.mp hedge⟩
  · intro hnil
    have hzero := congrArg Walk.length hnil
    simp only [Walk.length_append, Walk.length_nil] at hzero
    have hpzero : p.length = 0 := by omega
    exact huv (Walk.eq_of_length_eq_zero hpzero)
  · rw [Walk.tail_support_append, List.nodup_append]
    refine ⟨hp.support_nodup.tail, hq.support_nodup.tail, List.disjoint_iff_ne.mp ?_⟩
    intro x hxp hxq
    rcases hinter x (List.mem_of_mem_tail hxp) (List.mem_of_mem_tail hxq) with hx | hx
    · exact path_start_not_mem_tail hp (hx ▸ hxp)
    · exact path_start_not_mem_tail hq (hx ▸ hxq)

lemma triangle_paths_isCycle {u v w : V}
    {p : G.Walk u v} {q : G.Walk v w} {r : G.Walk w u}
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath) (huw : u ≠ w)
    (hpq : ∀ x, x ∈ p.support → x ∈ q.support → x = v)
    (hqr : ∀ x, x ∈ q.support → x ∈ r.support → x = w)
    (hpr : ∀ x, x ∈ p.support → x ∈ r.support → x = u)
    (hpe : p.edges.Disjoint r.edges) (hqe : q.edges.Disjoint r.edges) :
    ((p.append q).append r).IsCycle := by
  apply append_isCycle_of_support_inter
    (append_isPath_of_support_inter hp hq hpq) hr huw
  · rw [Walk.edges_append]
    exact List.disjoint_append_left.mpr ⟨hpe, hqe⟩
  · intro x hx hxr
    rw [Walk.support_append, List.mem_append] at hx
    rcases hx with hxp | hxq
    · exact Or.inl (hpr x hxp hxr)
    · exact Or.inr (hqr x (List.mem_of_mem_tail hxq) hxr)

lemma cycle_dropUntil_isPath {u v : V} [DecidableEq V] {c : G.Walk u u}
    (hc : c.IsCycle) (hv : v ∈ c.support) (huv : u ≠ v) :
    (c.dropUntil v hv).IsPath := by
  have hc' : ((c.takeUntil v hv).append (c.dropUntil v hv)).IsCycle := by
    simpa only [Walk.take_spec] using hc
  exact hc'.isPath_of_append_right (Walk.not_nil_of_ne huv)

set_option maxHeartbeats 2000000 in
lemma three_cycle_ring_recombine {u v w : V}
    (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (c₁ : G.Walk u u) (c₂ : G.Walk v v) (c₃ : G.Walk w w)
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle) (hc₃ : c₃.IsCycle)
    (hv : v ∈ c₁.support) (hw : w ∈ c₂.support) (hu : u ∈ c₃.support)
    (hs₁₂ : ∀ x, x ∈ c₁.support → x ∈ c₂.support → x = v)
    (hs₂₃ : ∀ x, x ∈ c₂.support → x ∈ c₃.support → x = w)
    (hs₁₃ : ∀ x, x ∈ c₁.support → x ∈ c₃.support → x = u)
    (he₁₂ : c₁.edges.Disjoint c₂.edges)
    (he₂₃ : c₂.edges.Disjoint c₃.edges)
    (he₁₃ : c₁.edges.Disjoint c₃.edges) :
    ∃ a b : G.Walk u u, a.IsCycle ∧ b.IsCycle ∧ a.edges.Disjoint b.edges ∧
      ∀ e, (e ∈ a.edges ∨ e ∈ b.edges) ↔
        (e ∈ c₁.edges ∨ e ∈ c₂.edges ∨ e ∈ c₃.edges) := by
  classical
  let p₁ := c₁.takeUntil v hv
  let p₂ := (c₁.dropUntil v hv).reverse
  let q₁ := c₂.takeUntil w hw
  let q₂ := (c₂.dropUntil w hw).reverse
  let r₁ := c₃.takeUntil u hu
  let r₂ := (c₃.dropUntil u hu).reverse
  have hp₁ : p₁.IsPath := hc₁.isPath_takeUntil hv
  have hp₂ : p₂.IsPath := (cycle_dropUntil_isPath hc₁ hv huv).reverse
  have hq₁ : q₁.IsPath := hc₂.isPath_takeUntil hw
  have hq₂ : q₂.IsPath := (cycle_dropUntil_isPath hc₂ hw hvw).reverse
  have hr₁ : r₁.IsPath := hc₃.isPath_takeUntil hu
  have hr₂ : r₂.IsPath := (cycle_dropUntil_isPath hc₃ hu huw.symm).reverse
  have hsp₁ : p₁.support ⊆ c₁.support := c₁.support_takeUntil_subset hv
  have hsp₂ : p₂.support ⊆ c₁.support := by
    simpa only [p₂, Walk.support_reverse, List.reverse_subset] using c₁.support_dropUntil_subset hv
  have hsq₁ : q₁.support ⊆ c₂.support := c₂.support_takeUntil_subset hw
  have hsq₂ : q₂.support ⊆ c₂.support := by
    simpa only [q₂, Walk.support_reverse, List.reverse_subset] using c₂.support_dropUntil_subset hw
  have hsr₁ : r₁.support ⊆ c₃.support := c₃.support_takeUntil_subset hu
  have hsr₂ : r₂.support ⊆ c₃.support := by
    simpa only [r₂, Walk.support_reverse, List.reverse_subset] using c₃.support_dropUntil_subset hu
  have hep₁ : p₁.edges ⊆ c₁.edges := c₁.edges_takeUntil_subset hv
  have hep₂ : p₂.edges ⊆ c₁.edges := by
    simpa only [p₂, Walk.edges_reverse, List.reverse_subset] using c₁.edges_dropUntil_subset hv
  have heq₁ : q₁.edges ⊆ c₂.edges := c₂.edges_takeUntil_subset hw
  have heq₂ : q₂.edges ⊆ c₂.edges := by
    simpa only [q₂, Walk.edges_reverse, List.reverse_subset] using c₂.edges_dropUntil_subset hw
  have her₁ : r₁.edges ⊆ c₃.edges := c₃.edges_takeUntil_subset hu
  have her₂ : r₂.edges ⊆ c₃.edges := by
    simpa only [r₂, Walk.edges_reverse, List.reverse_subset] using c₃.edges_dropUntil_subset hu
  let a := (p₁.append q₁).append r₁
  let b := (p₂.append q₂).append r₂
  have ha : a.IsCycle := triangle_paths_isCycle hp₁ hq₁ hr₁ huw
    (fun x hx hy => hs₁₂ x (hsp₁ hx) (hsq₁ hy))
    (fun x hx hy => hs₂₃ x (hsq₁ hx) (hsr₁ hy))
    (fun x hx hy => hs₁₃ x (hsp₁ hx) (hsr₁ hy))
    (fun e he hf => he₁₃ (hep₁ he) (her₁ hf))
    (fun e he hf => he₂₃ (heq₁ he) (her₁ hf))
  have hb : b.IsCycle := triangle_paths_isCycle hp₂ hq₂ hr₂ huw
    (fun x hx hy => hs₁₂ x (hsp₂ hx) (hsq₂ hy))
    (fun x hx hy => hs₂₃ x (hsq₂ hx) (hsr₂ hy))
    (fun x hx hy => hs₁₃ x (hsp₂ hx) (hsr₂ hy))
    (fun e he hf => he₁₃ (hep₂ he) (her₂ hf))
    (fun e he hf => he₂₃ (heq₂ he) (her₂ hf))
  have hdp : p₁.edges.Disjoint p₂.edges := by
    simpa only [p₁, p₂, Walk.edges_reverse, List.disjoint_reverse_right] using
      hc₁.isTrail.disjoint_edges_takeUntil_dropUntil hv
  have hdq : q₁.edges.Disjoint q₂.edges := by
    simpa only [q₁, q₂, Walk.edges_reverse, List.disjoint_reverse_right] using
      hc₂.isTrail.disjoint_edges_takeUntil_dropUntil hw
  have hdr : r₁.edges.Disjoint r₂.edges := by
    simpa only [r₁, r₂, Walk.edges_reverse, List.disjoint_reverse_right] using
      hc₃.isTrail.disjoint_edges_takeUntil_dropUntil hu
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · intro e hae hbe
    simp only [a, b, Walk.edges_append, List.mem_append] at hae hbe
    rcases hae with (hpe | hqe) | hre <;>
      rcases hbe with (hpe' | hqe') | hre'
    · exact hdp hpe hpe'
    · exact he₁₂ (hep₁ hpe) (heq₂ hqe')
    · exact he₁₃ (hep₁ hpe) (her₂ hre')
    · exact he₁₂ (hep₂ hpe') (heq₁ hqe)
    · exact hdq hqe hqe'
    · exact he₂₃ (heq₁ hqe) (her₂ hre')
    · exact he₁₃ (hep₂ hpe') (her₁ hre)
    · exact he₂₃ (heq₂ hqe') (her₁ hre)
    · exact hdr hre hre'
  · intro e
    have hcp : (e ∈ p₁.edges ∨ e ∈ p₂.edges) ↔ e ∈ c₁.edges := by
      simp only [p₁, p₂, Walk.edges_reverse, List.mem_reverse]
      rw [← List.mem_append, ← Walk.edges_append, Walk.take_spec]
    have hcq : (e ∈ q₁.edges ∨ e ∈ q₂.edges) ↔ e ∈ c₂.edges := by
      simp only [q₁, q₂, Walk.edges_reverse, List.mem_reverse]
      rw [← List.mem_append, ← Walk.edges_append, Walk.take_spec]
    have hcr : (e ∈ r₁.edges ∨ e ∈ r₂.edges) ↔ e ∈ c₃.edges := by
      simp only [r₁, r₂, Walk.edges_reverse, List.mem_reverse]
      rw [← List.mem_append, ← Walk.edges_append, Walk.take_spec]
    simp only [a, b, Walk.edges_append, List.mem_append]
    tauto


end Recombination

open scoped Classical in
lemma replace_decomposition_subfamily {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D A B : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D)
    (hAD : A ⊆ D) (hB : ∀ H ∈ B, IsCycleOrEdge H.coe)
    (hpairB : Set.PairwiseDisjoint (B : Set G.Subgraph) (fun H => H.edgeSet))
    (hcover : (⋃ H ∈ A, H.edgeSet) = ⋃ H ∈ B, H.edgeSet)
    (hcard : B.card < A.card) :
    ∃ D' : Finset G.Subgraph,
      (∀ H ∈ D', IsCycleOrEdge H.coe) ∧ IsDecomposition G D' ∧ D'.card < D.card := by
  classical
  let D' := (D \ A) ∪ B
  have hpairR : Set.PairwiseDisjoint ((D \ A : Finset G.Subgraph) : Set G.Subgraph)
      (fun H => H.edgeSet) := by
    intro H hH K hK hne
    exact hdec.1 (Finset.mem_sdiff.mp hH).1 (Finset.mem_sdiff.mp hK).1 hne
  refine ⟨D', ?_, ⟨?_, ?_⟩, ?_⟩
  · intro H hH
    rcases Finset.mem_union.mp hH with h | h
    · exact hD H (Finset.mem_sdiff.mp h).1
    · exact hB H h
  · change Set.PairwiseDisjoint (↑((D \ A) ∪ B) : Set G.Subgraph) _
    rw [Finset.coe_union]
    apply hpairR.union hpairB
    intro H hH K hK _
    apply Set.disjoint_left.mpr
    intro e heH heK
    have heU : e ∈ ⋃ K ∈ B, K.edgeSet := Set.mem_iUnion.mpr
      ⟨K, Set.mem_iUnion.mpr ⟨hK, heK⟩⟩
    rw [← hcover] at heU
    obtain ⟨L, heL⟩ := Set.mem_iUnion.mp heU
    obtain ⟨hL, heL⟩ := Set.mem_iUnion.mp heL
    have hHL : H ≠ L := by
      intro heq
      subst L
      exact (Finset.mem_sdiff.mp hH).2 hL
    exact Set.disjoint_left.mp (hdec.1 (Finset.mem_sdiff.mp hH).1 (hAD hL) hHL) heH heL
  · ext e
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨H, _, heH⟩
      exact H.edgeSet_subset heH
    · intro he
      have heD : e ∈ ⋃ H ∈ D, H.edgeSet := hdec.2.symm ▸ he
      obtain ⟨H, heH⟩ := Set.mem_iUnion.mp heD
      obtain ⟨hH, heH⟩ := Set.mem_iUnion.mp heH
      by_cases hHA : H ∈ A
      · have heA : e ∈ ⋃ H ∈ A, H.edgeSet := Set.mem_iUnion.mpr
          ⟨H, Set.mem_iUnion.mpr ⟨hHA, heH⟩⟩
        rw [hcover] at heA
        obtain ⟨K, heK⟩ := Set.mem_iUnion.mp heA
        obtain ⟨hK, heK⟩ := Set.mem_iUnion.mp heK
        exact ⟨K, Finset.mem_union_right _ hK, heK⟩
      · exact ⟨H, Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hH, hHA⟩), heH⟩
  · have hc := Finset.card_union_le (D \ A) B
    rw [Finset.card_sdiff_of_subset hAD] at hc
    have hle := Finset.card_le_card hAD
    change ((D \ A) ∪ B).card < D.card
    omega

lemma cycle_subgraph_ne_of_disjoint {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u u} {q : G.Walk v v} (hp : p.IsCycle)
    (hdis : p.edges.Disjoint q.edges) : p.toSubgraph ≠ q.toSubgraph := by
  intro heq
  have he : s(u, p.snd) ∈ p.toSubgraph.edgeSet := p.toSubgraph_adj_snd hp.not_nil
  have hep := p.mem_edges_toSubgraph.mp he
  rw [heq] at he
  exact hdis hep (q.mem_edges_toSubgraph.mp he)

set_option maxHeartbeats 2000000 in
open scoped Classical in
lemma improve_decomposition_of_three_cycle_ring {V : Type*} [Fintype V]
    {G : SimpleGraph V} (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D)
    {u v w : V} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (c₁ : G.Walk u u) (c₂ : G.Walk v v) (c₃ : G.Walk w w)
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle) (hc₃ : c₃.IsCycle)
    (h₁D : c₁.toSubgraph ∈ D) (h₂D : c₂.toSubgraph ∈ D) (h₃D : c₃.toSubgraph ∈ D)
    (hv : v ∈ c₁.support) (hw : w ∈ c₂.support) (hu : u ∈ c₃.support)
    (hs₁₂ : ∀ x, x ∈ c₁.support → x ∈ c₂.support → x = v)
    (hs₂₃ : ∀ x, x ∈ c₂.support → x ∈ c₃.support → x = w)
    (hs₁₃ : ∀ x, x ∈ c₁.support → x ∈ c₃.support → x = u)
    (he₁₂ : c₁.edges.Disjoint c₂.edges)
    (he₂₃ : c₂.edges.Disjoint c₃.edges)
    (he₁₃ : c₁.edges.Disjoint c₃.edges) :
    ∃ D' : Finset G.Subgraph,
      (∀ H ∈ D', IsCycleOrEdge H.coe) ∧ IsDecomposition G D' ∧ D'.card < D.card := by
  classical
  obtain ⟨a, b, ha, hb, heab, hcover⟩ := three_cycle_ring_recombine
    huv hvw huw c₁ c₂ c₃ hc₁ hc₂ hc₃ hv hw hu hs₁₂ hs₂₃ hs₁₃ he₁₂ he₂₃ he₁₃
  let A : Finset G.Subgraph := {c₁.toSubgraph, c₂.toSubgraph, c₃.toSubgraph}
  let B : Finset G.Subgraph := {a.toSubgraph, b.toSubgraph}
  have hAD : A ⊆ D := by
    simp only [A, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨h₁D, h₂D, h₃D⟩
  have hB : ∀ H ∈ B, IsCycleOrEdge H.coe := by
    intro H hH
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact Or.inl (by
        simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using cycle_coe_regular G ha)
    · exact Or.inl (by
        simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using cycle_coe_regular G hb)
  have hpairB : Set.PairwiseDisjoint (B : Set G.Subgraph) (fun H => H.edgeSet) := by
    have hset : Disjoint a.toSubgraph.edgeSet b.toSubgraph.edgeSet := by
      apply Set.disjoint_left.mpr
      intro e heA heB
      exact heab (a.mem_edges_toSubgraph.mp heA) (b.mem_edges_toSubgraph.mp heB)
    simp only [B, Finset.coe_insert, Finset.coe_singleton]
    apply (Set.pairwiseDisjoint_singleton _ _).insert
    intro H hH _
    have hH' : H = b.toSubgraph := Set.mem_singleton_iff.mp hH
    subst H
    exact hset
  have hcoverAB : (⋃ H ∈ A, H.edgeSet) = ⋃ H ∈ B, H.edgeSet := by
    ext e
    simpa [A, B, Walk.mem_edges_toSubgraph, or_assoc] using (hcover e).symm
  have hAcard : A.card = 3 := by
    have h₁₂ := cycle_subgraph_ne_of_disjoint hc₁ he₁₂
    have h₁₃ := cycle_subgraph_ne_of_disjoint hc₁ he₁₃
    have h₂₃ := cycle_subgraph_ne_of_disjoint hc₂ he₂₃
    simp [A, h₁₂, h₁₃, h₂₃]
  have hBcard : B.card ≤ 2 := by
    have h := Finset.card_insert_le a.toSubgraph {b.toSubgraph}
    simpa only [Finset.card_singleton] using h
  exact replace_decomposition_subfamily D A B hD hdec hAD hB hpairB hcoverAB (by omega)

section GridObstruction

variable {A B : Type*}

def gridGraph (A B : Type*) := completeBipartiteGraph (A × Bool) (B × Bool)

def gridCycle (i : A) (j : B) :
    (gridGraph A B).Walk (.inl (i, false)) (.inl (i, false)) :=
  .cons (v := Sum.inr (j, false)) (by simp [gridGraph])
    (.cons (v := Sum.inl (i, true)) (by simp [gridGraph])
      (.cons (v := Sum.inr (j, true)) (by simp [gridGraph])
        (.cons (by simp [gridGraph]) .nil)))

lemma gridCycle_isCycle (i : A) (j : B) : (gridCycle i j).IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  simp [gridCycle]

lemma gridCycle_length (i : A) (j : B) : (gridCycle i j).length = 4 := rfl

lemma gridCycle_cross_mem (i a : A) (j b : B) (x y : Bool) :
    s(Sum.inl (a,x), Sum.inr (b,y)) ∈ (gridCycle i j).edges ↔ a = i ∧ b = j := by
  cases x <;> cases y <;> simp [gridCycle, eq_comm, and_comm]

lemma gridCycle_edge_mem_iff (i : A) (j : B) (e : Sym2 ((A × Bool) ⊕ (B × Bool))) :
    e ∈ (gridCycle i j).edges ↔
      ∃ x y : Bool, e = s(Sum.inl (i,x), Sum.inr (j,y)) := by
  simp only [gridCycle, Walk.edges_cons, Walk.edges_nil, List.mem_cons,
    List.not_mem_nil, or_false, Bool.exists_bool]
  rw [Sym2.eq_swap (a := Sum.inr (j,false)) (b := Sum.inl (i,true)),
    Sym2.eq_swap (a := Sum.inr (j,true)) (b := Sum.inl (i,false))]
  tauto

lemma gridCycle_subgraph_injective : Function.Injective
    (fun p : A × B => (gridCycle p.1 p.2).toSubgraph) := by
  intro p q heq
  have he : s(Sum.inl (p.1,false), Sum.inr (p.2,false)) ∈ (gridCycle p.1 p.2).toSubgraph.edgeSet := by
    apply (gridCycle p.1 p.2).mem_edges_toSubgraph.mpr
    exact (gridCycle_cross_mem _ _ _ _ _ _).mpr ⟨rfl,rfl⟩
  dsimp only at heq
  rw [heq] at he
  have h := (gridCycle_cross_mem q.1 p.1 q.2 p.2 false false).mp
    ((gridCycle q.1 q.2).mem_edges_toSubgraph.mp he)
  exact Prod.ext h.1 h.2

lemma gridCycle_disjoint (p q : A × B) (hne : p ≠ q) :
    (gridCycle p.1 p.2).edges.Disjoint (gridCycle q.1 q.2).edges := by
  intro e hep heq
  obtain ⟨x,y,rfl⟩ := (gridCycle_edge_mem_iff _ _ _).mp hep
  have h := (gridCycle_cross_mem q.1 p.1 q.2 p.2 x y).mp heq
  exact hne (Prod.ext h.1 h.2)

def flipVertex : (A × Bool) ⊕ (B × Bool) → (A × Bool) ⊕ (B × Bool)
  | .inl (i,b) => .inl (i,!b)
  | .inr (j,b) => .inr (j,!b)

lemma flipVertex_ne (v : (A × Bool) ⊕ (B × Bool)) : flipVertex v ≠ v := by
  rcases v with ⟨i,b⟩ | ⟨j,b⟩ <;> cases b <;> simp [flipVertex]

lemma gridCycle_flip_mem (i : A) (j : B) (v : (A × Bool) ⊕ (B × Bool))
    (hv : v ∈ (gridCycle i j).support) : flipVertex v ∈ (gridCycle i j).support := by
  rcases v with ⟨a,b⟩ | ⟨a,b⟩ <;> cases b <;>
    simp_all [gridCycle, flipVertex]

lemma gridCycle_inter_not_singleton (p q : A × B) (v : (A × Bool) ⊕ (B × Bool))
    (hp : v ∈ (gridCycle p.1 p.2).support) (hq : v ∈ (gridCycle q.1 q.2).support) :
    ¬ (∀ x, x ∈ (gridCycle p.1 p.2).support → x ∈ (gridCycle q.1 q.2).support → x = v) := by
  intro h
  exact flipVertex_ne v (h _ (gridCycle_flip_mem _ _ _ hp) (gridCycle_flip_mem _ _ _ hq))


open scoped Classical in
noncomputable def gridDecomposition (A B : Type*) [Fintype A] [Fintype B] :
    Finset (gridGraph A B).Subgraph :=
  Finset.univ.image (fun p : A × B => (gridCycle p.1 p.2).toSubgraph)

lemma gridDecomposition_card (A B : Type*) [Fintype A] [Fintype B] :
    (gridDecomposition A B).card = Fintype.card A * Fintype.card B := by
  classical
  calc
    _ = (Finset.univ : Finset (A × B)).card :=
      Finset.card_image_iff.mpr gridCycle_subgraph_injective.injOn
    _ = _ := by simp

open scoped Classical in
lemma gridDecomposition_four_cycles (A B : Type*) [Fintype A] [Fintype B] :
    ∀ H ∈ gridDecomposition A B, IsFourCycle H.coe := by
  classical
  intro H hH
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hH
  have hp := gridCycle_isCycle p.1 p.2
  have hreg := cycle_coe_regular (gridGraph A B) hp
  refine ⟨hreg.1, ?_, ?_⟩
  · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hreg.2
  · rw [← subgraph_edge_card]
    exact (cycle_edge_count (gridGraph A B) hp).trans (gridCycle_length p.1 p.2)

lemma gridDecomposition_isDecomposition (A B : Type*) [Fintype A] [Fintype B] :
    IsDecomposition (gridGraph A B) (gridDecomposition A B) := by
  classical
  constructor
  · intro H hH K hK hne
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hK
    apply Set.disjoint_left.mpr
    intro e he₁ he₂
    exact gridCycle_disjoint p q (fun h => hne (congrArg (fun r : A × B => (gridCycle r.1 r.2).toSubgraph) h))
      ((gridCycle p.1 p.2).mem_edges_toSubgraph.mp he₁)
      ((gridCycle q.1 q.2).mem_edges_toSubgraph.mp he₂)
  · ext e
    constructor
    · intro he
      obtain ⟨H, he⟩ := Set.mem_iUnion.mp he
      obtain ⟨_, he⟩ := Set.mem_iUnion.mp he
      exact H.edgeSet_subset he
    · intro he
      have hform : ∃ (i : A) (j : B) (x y : Bool),
          e = s(Sum.inl (i,x), Sum.inr (j,y)) := by
        induction e using Sym2.ind with
        | h a b =>
          cases a with
          | inl a =>
            cases b with
            | inl b => simp [gridGraph] at he
            | inr b => exact ⟨a.1, b.1, a.2, b.2, rfl⟩
          | inr a =>
            cases b with
            | inl b => exact ⟨b.1, a.1, b.2, a.2, Sym2.eq_swap⟩
            | inr b => simp [gridGraph] at he
      obtain ⟨i,j,x,y,rfl⟩ := hform
      refine Set.mem_iUnion.mpr ⟨(gridCycle i j).toSubgraph, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩
      · apply (gridCycle i j).mem_edges_toSubgraph.mpr
        exact (gridCycle_cross_mem _ _ _ _ _ _).mpr ⟨rfl,rfl⟩

lemma gridDecomposition_no_singleton_intersection (A B : Type*) [Fintype A] [Fintype B] :
    ∀ H ∈ gridDecomposition A B, ∀ K ∈ gridDecomposition A B,
      ∀ v, v ∈ H.verts → v ∈ K.verts →
        ∃ w, w ≠ v ∧ w ∈ H.verts ∧ w ∈ K.verts := by
  classical
  intro H hH K hK v hvH hvK
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hH
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hK
  simp only [Walk.mem_verts_toSubgraph] at hvH hvK ⊢
  exact ⟨flipVertex v, flipVertex_ne v,
    gridCycle_flip_mem _ _ _ hvH, gridCycle_flip_mem _ _ _ hvK⟩

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- The clean-ring local rule alone can get stuck on a quadratic-size partition.
This says nothing about the size of a better decomposition of the same graph. -/
lemma gridDecomposition_quadratic (m : ℕ) :
    Fintype.card ((Fin m × Bool) ⊕ (Fin m × Bool)) = 4 * m ∧
    (gridDecomposition (Fin m) (Fin m)).card = m * m ∧
    (∀ H ∈ gridDecomposition (Fin m) (Fin m), IsFourCycle H.coe) ∧
    IsDecomposition (gridGraph (Fin m) (Fin m)) (gridDecomposition (Fin m) (Fin m)) ∧
    (∀ H ∈ gridDecomposition (Fin m) (Fin m),
      ∀ K ∈ gridDecomposition (Fin m) (Fin m),
      ∀ v, v ∈ H.verts → v ∈ K.verts →
        ∃ w, w ≠ v ∧ w ∈ H.verts ∧ w ∈ K.verts) := by
  refine ⟨?_, ?_, gridDecomposition_four_cycles _ _, gridDecomposition_isDecomposition _ _,
    gridDecomposition_no_singleton_intersection _ _⟩
  · simp [Fintype.card_sum, Fintype.card_prod]
    omega
  · simp [gridDecomposition_card]


end GridObstruction

section BipartiteFactors
open scoped Fin.NatCast

variable {n : ℕ} [NeZero n]

def matchingPair (t : Fin n) : SimpleGraph (Fin n ⊕ Fin n) where
  Adj
    | .inl a, .inr b => b = a + t ∨ b = a + t + 1
    | .inr b, .inl a => b = a + t ∨ b = a + t + 1
    | _, _ => False
  symm := by intro a b; cases a <;> cases b <;> simp
  loopless := by intro a; cases a <;> simp

lemma matchingPair_le (t : Fin n) : matchingPair t ≤ completeBipartiteGraph (Fin n) (Fin n) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [matchingPair]

lemma matchingPair_left_step (t a : Fin n) :
    (matchingPair t).Reachable (.inl a) (.inl (a + 1)) := by
  have h₁ : (matchingPair t).Adj (.inl a) (.inr (a + t + 1)) := Or.inr rfl
  have h₂ : (matchingPair t).Adj (.inr (a + t + 1)) (.inl (a + 1)) := by
    exact Or.inl (by abel)
  exact h₁.reachable.trans h₂.reachable

lemma matchingPair_connected (t : Fin n) : (matchingPair t).Connected := by
  have hNat : ∀ k : ℕ, (matchingPair t).Reachable (.inl 0) (.inl (k : Fin n)) := by
    intro k
    induction k with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ k ih =>
      simpa only [Nat.cast_add, Nat.cast_one] using ih.trans (matchingPair_left_step t (k : Fin n))
  have hLeft : ∀ a : Fin n, (matchingPair t).Reachable (.inl 0) (.inl a) := by
    intro a
    simpa only [Fin.cast_val_eq_self] using hNat a.val
  have hRoot : ∀ v, (matchingPair t).Reachable (.inl 0) v := by
    intro v
    cases v with
    | inl a => exact hLeft a
    | inr b =>
      have hEdge : (matchingPair t).Adj (.inl (b - t)) (.inr b) := by
        exact Or.inl (by abel)
      exact (hLeft (b - t)).trans hEdge.reachable
  exact ⟨fun a b => (hRoot a).symm.trans (hRoot b)⟩

open scoped Classical in
lemma matchingPair_regular (hn : 2 ≤ n) (t : Fin n) :
    (matchingPair t).IsRegularOfDegree 2 := by
  classical
  have h10 : (1 : Fin n) ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (show 1 < n by omega)] at hval
    omega
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  cases v with
  | inl a =>
    have hneigh : (matchingPair t).neighborFinset (.inl a) =
        {Sum.inr (a + t), Sum.inr (a + t + 1)} := by
      ext b
      cases b <;> simp [SimpleGraph.mem_neighborFinset, matchingPair]
    rw [hneigh, Finset.card_pair]
    intro heq
    have h := Sum.inr_injective heq
    exact h10 (add_eq_left.mp h.symm)
  | inr b =>
    have hneigh : (matchingPair t).neighborFinset (.inr b) =
        {Sum.inl (b - t), Sum.inl (b - t - 1)} := by
      ext a
      cases a with
      | inl a =>
        simp only [SimpleGraph.mem_neighborFinset, matchingPair,
          Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq]
        constructor
        · rintro (h | h)
          · exact Or.inl (by rw [h]; abel)
          · exact Or.inr (by rw [h]; abel)
        · rintro (rfl | rfl)
          · exact Or.inl (by abel)
          · exact Or.inr (by abel)
      | inr a => simp [SimpleGraph.mem_neighborFinset, matchingPair]
    rw [hneigh, Finset.card_pair]
    intro heq
    have h := Sum.inl_injective heq
    exact h10 (sub_eq_self.mp h.symm)


def evenOffset (m : ℕ) (i : Fin m) : Fin (2 * m) :=
  ⟨2 * i.val, by have := i.isLt; omega⟩

lemma evenOffset_val (m : ℕ) (i : Fin m) : (evenOffset m i).val = 2 * i.val := rfl

lemma evenOffset_succ_val (m : ℕ) [NeZero m] (i : Fin m) :
    (evenOffset m i + 1).val = 2 * i.val + 1 := by
  have hm : 0 < m := NeZero.pos m
  have hi := i.isLt
  rw [Fin.val_add, evenOffset_val, Fin.val_one',
    Nat.mod_eq_of_lt (show 1 < 2 * m by omega), Nat.mod_eq_of_lt (by omega)]

lemma matchingPair_evenOffset_adj (m : ℕ) [NeZero m] (i : Fin m) (a b : Fin (2 * m)) :
    (matchingPair (evenOffset m i)).Adj (.inl a) (.inr b) ↔ (b - a).val / 2 = i.val := by
  constructor
  · rintro (h | h)
    · have heq : b - a = evenOffset m i := by rw [h]; abel
      rw [heq, evenOffset_val]
      omega
    · have heq : b - a = evenOffset m i + 1 := by rw [h]; abel
      rw [heq, evenOffset_succ_val]
      omega
  · intro h
    have hval : (b - a).val = 2 * i.val ∨ (b - a).val = 2 * i.val + 1 := by omega
    rcases hval with h | h
    · have heq : b - a = evenOffset m i := Fin.ext h
      exact Or.inl (by rw [← heq]; abel)
    · have heq : b - a = evenOffset m i + 1 := by
        apply Fin.ext
        rwa [evenOffset_succ_val]
      exact Or.inr (by rw [add_assoc, ← heq]; abel)

lemma matchingPair_evenOffset_unique (m : ℕ) [NeZero m] (i j : Fin m)
    (a b : Fin (2 * m))
    (hi : (matchingPair (evenOffset m i)).Adj (.inl a) (.inr b))
    (hj : (matchingPair (evenOffset m j)).Adj (.inl a) (.inr b)) : i = j := by
  apply Fin.ext
  exact ((matchingPair_evenOffset_adj m i a b).mp hi).symm.trans
    ((matchingPair_evenOffset_adj m j a b).mp hj)

lemma matchingPair_evenOffset_exists (m : ℕ) [NeZero m] (a b : Fin (2 * m)) :
    ∃ i : Fin m, (matchingPair (evenOffset m i)).Adj (.inl a) (.inr b) := by
  have hd := (b - a).isLt
  let i : Fin m := ⟨(b - a).val / 2, by omega⟩
  exact ⟨i, (matchingPair_evenOffset_adj m i a b).mpr rfl⟩

open scoped Classical in
lemma coe_toSubgraph_cycle {V : Type*} [Fintype V] {G H : SimpleGraph V}
    (hHG : H ≤ G) (hconn : H.Connected) (hreg : H.IsRegularOfDegree 2) :
    (SimpleGraph.toSubgraph H hHG).coe.Connected ∧ (SimpleGraph.toSubgraph H hHG).coe.IsRegularOfDegree 2 := by
  classical
  have e : H ≃g (SimpleGraph.toSubgraph H hHG).coe :=
    (SimpleGraph.toSubgraph H hHG).spanningCoeEquivCoeOfSpanning (SimpleGraph.toSubgraph.isSpanning H hHG)
  refine ⟨e.connected_iff.mp hconn, ?_⟩
  intro v
  rw [SimpleGraph.Subgraph.coe_degree, SimpleGraph.degree_toSubgraph]
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hreg v.val

open scoped Classical in
noncomputable def bipartiteFactor (m : ℕ) [NeZero m] (i : Fin m) :
    (completeBipartiteGraph (Fin (2 * m)) (Fin (2 * m))).Subgraph :=
  SimpleGraph.toSubgraph (matchingPair (evenOffset m i)) (matchingPair_le _)

open scoped Classical in
lemma bipartiteFactor_cycle (m : ℕ) [NeZero m] (i : Fin m) :
    (bipartiteFactor m i).coe.Connected ∧ (bipartiteFactor m i).coe.IsRegularOfDegree 2 := by
  apply coe_toSubgraph_cycle
  · exact matchingPair_connected _
  · exact matchingPair_regular (by have := NeZero.pos m; omega) _

open scoped Classical in
lemma balanced_complete_bipartite_decomposition_pos (m : ℕ) [NeZero m] :
    ∃ D : Finset (completeBipartiteGraph (Fin (2 * m)) (Fin (2 * m))).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (completeBipartiteGraph (Fin (2 * m)) (Fin (2 * m))) D ∧
      D.card ≤ m := by
  classical
  let D := Finset.univ.image (bipartiteFactor m)
  refine ⟨D, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro H hH
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using bipartiteFactor_cycle m i
  · intro H hH K hK hne
    change H ∈ Finset.univ.image (bipartiteFactor m) at hH
    change K ∈ Finset.univ.image (bipartiteFactor m) at hK
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hK
    apply Set.disjoint_left.mpr
    intro e hei hej
    induction e using Sym2.ind with
    | h a b =>
      change (matchingPair (evenOffset m i)).Adj a b at hei
      change (matchingPair (evenOffset m j)).Adj a b at hej
      cases a with
      | inl a =>
        cases b with
        | inl b => exact hei
        | inr b => exact hne (congrArg (bipartiteFactor m)
            (matchingPair_evenOffset_unique m i j a b hei hej))
      | inr a =>
        cases b with
        | inl b => exact hne (congrArg (bipartiteFactor m)
            (matchingPair_evenOffset_unique m i j b a hei hej))
        | inr b => exact hei
  · ext e
    constructor
    · intro he
      obtain ⟨H, he⟩ := Set.mem_iUnion.mp he
      obtain ⟨_, he⟩ := Set.mem_iUnion.mp he
      exact H.edgeSet_subset he
    · intro he
      induction e using Sym2.ind with
      | h a b =>
        change (completeBipartiteGraph (Fin (2 * m)) (Fin (2 * m))).Adj a b at he
        cases a with
        | inl a =>
          cases b with
          | inl b => simp at he
          | inr b =>
            obtain ⟨i, hi⟩ := matchingPair_evenOffset_exists m a b
            exact Set.mem_iUnion.mpr ⟨bipartiteFactor m i, Set.mem_iUnion.mpr
              ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩⟩
        | inr a =>
          cases b with
          | inl b =>
            obtain ⟨i, hi⟩ := matchingPair_evenOffset_exists m b a
            exact Set.mem_iUnion.mpr ⟨bipartiteFactor m i, Set.mem_iUnion.mpr
              ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩⟩
          | inr b => simp at he
  · exact Finset.card_image_le.trans (by simp)

open scoped Classical in
lemma balanced_complete_bipartite_decomposition (m : ℕ) :
    ∃ D : Finset (completeBipartiteGraph (Fin (2 * m)) (Fin (2 * m))).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (completeBipartiteGraph (Fin (2 * m)) (Fin (2 * m))) D ∧
      D.card ≤ m := by
  classical
  cases m with
  | zero =>
    refine ⟨∅, by simp, ?_, by simp⟩
    have hbot : completeBipartiteGraph (Fin (2 * 0)) (Fin (2 * 0)) = ⊥ := by
      ext a
      cases a with
      | inl a => exact a.elim0
      | inr a => exact a.elim0
    simp [IsDecomposition, hbot]
  | succ m => exact balanced_complete_bipartite_decomposition_pos (m + 1)


end BipartiteFactors

noncomputable def subgraphMapIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (K : G.Subgraph) : K.coe ≃g (K.map e.toHom).coe where
  toEquiv := Equiv.Set.image e K.verts e.injective
  map_rel_iff' := by
    intro u v
    change Relation.Map K.Adj e e (e u.val) (e v.val) ↔ K.Adj u.val v.val
    simp only [Relation.Map, e.injective.eq_iff]
    simp

open scoped Classical in
lemma cycle_property_map_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (hG : G.Connected ∧ G.IsRegularOfDegree 2) :
    H.Connected ∧ H.IsRegularOfDegree 2 := by
  classical
  refine ⟨e.connected_iff.mp hG.1, ?_⟩
  intro w
  obtain ⟨v, rfl⟩ := e.surjective w
  rw [e.degree_eq]
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hG.2 v

open scoped Classical in
lemma map_isDecomposition_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (D : Finset G.Subgraph) (hdec : IsDecomposition G D) :
    IsDecomposition H (D.image (SimpleGraph.Subgraph.map e.toHom)) := by
  classical
  constructor
  · intro K hK L hL hne
    obtain ⟨K', hK', rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨L', hL', rfl⟩ := Finset.mem_image.mp hL
    change Disjoint (K'.map e.toHom).edgeSet (L'.map e.toHom).edgeSet
    rw [SimpleGraph.Subgraph.edgeSet_map, SimpleGraph.Subgraph.edgeSet_map]
    apply Set.disjoint_left.mpr
    rintro f ⟨g, hg, rfl⟩ ⟨g', hg', heq⟩
    have hgg : g' = g := Sym2.map.injective e.injective heq
    subst g'
    exact Set.disjoint_left.mp (hdec.1 hK' hL'
      (fun heq => hne (congrArg (SimpleGraph.Subgraph.map e.toHom) heq))) hg hg'

  · have hmap : Sym2.map e.toHom '' G.edgeSet = H.edgeSet := by
      have h := congrArg SimpleGraph.Subgraph.edgeSet (SimpleGraph.Subgraph.map_iso_top e)
      simpa only [SimpleGraph.Subgraph.edgeSet_map, SimpleGraph.Subgraph.edgeSet_top] using h
    ext f
    constructor
    · intro hf
      obtain ⟨K, hf⟩ := Set.mem_iUnion.mp hf
      obtain ⟨_, hf⟩ := Set.mem_iUnion.mp hf
      exact K.edgeSet_subset hf
    · intro hf
      rw [← hmap] at hf
      obtain ⟨g, hg, hgf⟩ := hf
      rw [← hdec.2] at hg
      obtain ⟨K, hg⟩ := Set.mem_iUnion.mp hg
      obtain ⟨hK, hgK⟩ := Set.mem_iUnion.mp hg
      refine Set.mem_iUnion.mpr ⟨K.map e.toHom, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_image.mpr ⟨K, hK, rfl⟩
      · rw [SimpleGraph.Subgraph.edgeSet_map]
        exact ⟨g, hgK, hgf⟩

noncomputable def balancedBipartiteIsoGrid (m : ℕ) :
    completeBipartiteGraph (Fin (2 * m)) (Fin (2 * m)) ≃g gridGraph (Fin m) (Fin m) := by
  let e : Fin (2 * m) ≃ Fin m × Bool := Fintype.equivOfCardEq (by simp [mul_comm])
  exact {
    toEquiv := e.sumCongr e
    map_rel_iff' := by intro a b; cases a <;> cases b <;> simp [gridGraph] }

open scoped Classical in
lemma gridGraph_linear_decomposition (m : ℕ) :
    ∃ D : Finset (gridGraph (Fin m) (Fin m)).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (gridGraph (Fin m) (Fin m)) D ∧ D.card ≤ m := by
  classical
  obtain ⟨D, hD, hdec, hc⟩ := balanced_complete_bipartite_decomposition m
  let e := balancedBipartiteIsoGrid m
  refine ⟨D.image (SimpleGraph.Subgraph.map e.toHom), ?_, map_isDecomposition_iso e D hdec,
    Finset.card_image_le.trans hc⟩
  intro K hK
  obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
  have hmapped := cycle_property_map_iso (subgraphMapIso e L) (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD L hL)
  simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using hmapped

section RestrictionObstruction
open scoped Fin.NatCast

variable {n : ℕ} [NeZero n]

def singleMatching (t : Fin n) : SimpleGraph (Fin n ⊕ Fin n) where
  Adj
    | .inl a, .inr b => b = a + t
    | .inr b, .inl a => b = a + t
    | _, _ => False
  symm := by intro a b; cases a <;> cases b <;> simp
  loopless := by intro a; cases a <;> simp

omit [NeZero n] in
lemma singleMatching_adj_unique (t : Fin n) {a b c : Fin n ⊕ Fin n}
    (hab : (singleMatching t).Adj a b) (hac : (singleMatching t).Adj a c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all [singleMatching]

omit [NeZero n] in
lemma singleMatching_acyclic (t : Fin n) : (singleMatching t).IsAcyclic := by
  intro u p hp
  exact hp.snd_ne_penultimate (singleMatching_adj_unique t
    (Walk.adj_snd hp.not_nil) (Walk.adj_penultimate hp.not_nil).symm)

open scoped Classical in
lemma singleMatching_regular (t : Fin n) : (singleMatching t).IsRegularOfDegree 1 := by
  classical
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  cases v with
  | inl a =>
    have hneigh : (singleMatching t).neighborFinset (.inl a) = {Sum.inr (a + t)} := by
      ext b
      cases b <;> simp [SimpleGraph.mem_neighborFinset, singleMatching]
    rw [hneigh, Finset.card_singleton]
  | inr b =>
    have hneigh : (singleMatching t).neighborFinset (.inr b) = {Sum.inl (b - t)} := by
      ext a
      cases a with
      | inl a =>
        simp only [SimpleGraph.mem_neighborFinset, singleMatching,
          Finset.mem_singleton, Sum.inl.injEq]
        constructor
        · intro h; rw [h]; abel
        · rintro rfl; abel
      | inr a => simp [SimpleGraph.mem_neighborFinset, singleMatching]
    rw [hneigh, Finset.card_singleton]

open scoped Classical in
lemma singleMatching_edge_card (t : Fin n) : (singleMatching t).edgeFinset.card = n := by
  classical
  have hdeg := singleMatching_regular t
  have hs := (singleMatching t).sum_degrees_eq_twice_card_edges
  have hsum : (∑ v, (singleMatching t).degree v) = 2 * n := by
    calc
      _ = ∑ _v : Fin n ⊕ Fin n, 1 := by
        apply Finset.sum_congr rfl
        intro v _
        exact hdeg v
      _ = _ := by simp; omega
  rw [hsum] at hs
  omega

def evenMatchingGraph (m : ℕ) [NeZero m] : SimpleGraph (Fin (2 * m) ⊕ Fin (2 * m)) where
  Adj
    | .inl a, .inr b => (b - a).val % 2 = 0
    | .inr b, .inl a => (b - a).val % 2 = 0
    | _, _ => False
  symm := by intro a b; cases a <;> cases b <;> simp
  loopless := by intro a; cases a <;> simp

lemma evenMatchingGraph_le (m : ℕ) [NeZero m] :
    evenMatchingGraph m ≤ completeBipartiteGraph (Fin (2 * m)) (Fin (2 * m)) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [evenMatchingGraph]

lemma even_factor_restriction_cross (m : ℕ) [NeZero m] (i : Fin m) (a b : Fin (2 * m)) :
    ((b - a).val % 2 = 0 ∧
      (b = a + evenOffset m i ∨ b = a + evenOffset m i + 1)) ↔
      b = a + evenOffset m i := by
  constructor
  · rintro ⟨hpar, h | h⟩
    · exact h
    · have heq : b - a = evenOffset m i + 1 := by rw [h]; abel
      rw [heq, evenOffset_succ_val] at hpar
      omega
  · intro h
    refine ⟨?_, Or.inl h⟩
    have heq : b - a = evenOffset m i := by rw [h]; abel
    rw [heq, evenOffset_val]
    omega

lemma even_factor_restriction (m : ℕ) [NeZero m] (i : Fin m) :
    evenMatchingGraph m ⊓ matchingPair (evenOffset m i) = singleMatching (evenOffset m i) := by
  ext a b
  cases a with
  | inl a =>
    cases b with
    | inl b => simp [evenMatchingGraph, matchingPair, singleMatching]
    | inr b => exact even_factor_restriction_cross m i a b
  | inr a =>
    cases b with
    | inl b => exact even_factor_restriction_cross m i b a
    | inr b => simp [evenMatchingGraph, matchingPair, singleMatching]

open scoped Classical in
lemma restricted_factor_decomposition_card (m : ℕ) [NeZero m] (i : Fin m)
    (D : Finset (evenMatchingGraph m ⊓ matchingPair (evenOffset m i)).Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition (evenMatchingGraph m ⊓ matchingPair (evenOffset m i)) D) :
    D.card = 2 * m := by
  classical
  have hacyclic : (evenMatchingGraph m ⊓ matchingPair (evenOffset m i)).IsAcyclic := by
    rw [even_factor_restriction]
    exact singleMatching_acyclic _
  rw [acyclic_decomposition_card hacyclic D hD hdec]
  have heq := even_factor_restriction m i
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  rw [heq]
  simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
    singleMatching_edge_card (evenOffset m i)

open scoped Classical in
/-- Restricting the fixed complete-bipartite factors and decomposing each restriction
separately has quadratic total cost. This is not a lower bound for arbitrary
recombinations of the edges of `evenMatchingGraph m`. -/
lemma sum_restricted_factor_decomposition_cards (m : ℕ) [NeZero m]
    (D : ∀ i : Fin m, Finset (evenMatchingGraph m ⊓ matchingPair (evenOffset m i)).Subgraph)
    (hD : ∀ i H, H ∈ D i → IsCycleOrEdge H.coe)
    (hdec : ∀ i, IsDecomposition (evenMatchingGraph m ⊓ matchingPair (evenOffset m i)) (D i)) :
    (∑ i : Fin m, (D i).card) = 2 * m * m := by
  classical
  calc
    _ = ∑ _i : Fin m, 2 * m := by
      apply Finset.sum_congr rfl
      intro i _
      exact restricted_factor_decomposition_card m i (D i) (hD i) (hdec i)
    _ = _ := by simp; ring

end RestrictionObstruction

#print axioms sum_restricted_factor_decomposition_cards

#print axioms gridGraph_linear_decomposition

#print axioms balanced_complete_bipartite_decomposition
#print axioms gridDecomposition_quadratic
#print axioms improve_decomposition_of_three_cycle_ring

#print axioms asymptotic_iff_four_cycle_uniform

#print axioms no_four_cycle_decomposition_linear

#print axioms unique_neighbors_decomposition_linear

#print axioms universal_linear_constant_ge_one
#print axioms tree_decomposition_card
#print axioms logarithmic_bound_not_bigO_linear
#print axioms exists_decomposition_log_bound
#print axioms decomposition_bound_above_threshold
#print axioms exists_decomposition_edge_bound
#print axioms exists_cycle_decomposition
#print axioms asymptotic_iff_even_uniform
#print axioms exists_even_complement_forest
#print axioms exists_edge_decomposition
#print axioms asymptotic_iff_uniform


open scoped Classical in
lemma regular_two_spanning_even {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H : G.Subgraph) (hH : H.coe.IsRegularOfDegree 2) (v : V) :
    Even (H.spanningCoe.degree v) := by
  classical
  rw [SimpleGraph.Subgraph.degree_spanningCoe]
  by_cases hv : v ∈ H.verts
  · have hd := hH ⟨v, hv⟩
    rw [SimpleGraph.Subgraph.coe_degree] at hd
    rw [hd]
    decide
  · rw [SimpleGraph.Subgraph.degree_of_notMem_verts hv]
    decide

open scoped Classical in
noncomputable def subfamilyGraph {V : Type*} {G : SimpleGraph V}
    (A : Finset G.Subgraph) : SimpleGraph V := A.sup (fun H => H.spanningCoe)

open scoped Classical in
lemma subfamilyGraph_edges {V : Type*} {G : SimpleGraph V}
    (A : Finset G.Subgraph) :
    (subfamilyGraph A).edgeSet = ⋃ H ∈ A, H.edgeSet := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [subfamilyGraph]
  | @insert H A hHA ih =>
    simp only [subfamilyGraph, Finset.sup_insert, SimpleGraph.edgeSet_sup]
    change H.edgeSet ∪ (subfamilyGraph A).edgeSet = _
    rw [ih]
    simp

open scoped Classical in
lemma subfamilyGraph_le {V : Type*} {G : SimpleGraph V}
    (A : Finset G.Subgraph) : subfamilyGraph A ≤ G := by
  classical
  exact Finset.sup_le (fun H _ => H.spanningCoe_le)

open scoped Classical in
lemma subfamilyGraph_degree {V : Type*} [Fintype V] {G : SimpleGraph V}
    (A : Finset G.Subgraph)
    (hp : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet)) (v : V) :
    (subfamilyGraph A).degree v = ∑ H ∈ A, H.spanningCoe.degree v := by
  classical
  have hcover : (subfamilyGraph A).neighborFinset v =
      A.biUnion (fun H => H.spanningCoe.neighborFinset v) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_biUnion]
    have hh := Set.ext_iff.mp (subfamilyGraph_edges A) s(v, w)
    simpa only [SimpleGraph.mem_edgeSet, Set.mem_iUnion, exists_prop,
      SimpleGraph.Subgraph.mem_edgeSet] using hh
  have hdis : (A : Set G.Subgraph).PairwiseDisjoint
      (fun H => H.spanningCoe.neighborFinset v) := by
    intro H hH K hK hne
    apply Finset.disjoint_left.mpr
    intro w hwH hwK
    exact Set.disjoint_left.mp (hp hH hK hne)
      (show s(v, w) ∈ H.edgeSet from (H.spanningCoe.mem_neighborFinset v w).mp hwH)
      (show s(v, w) ∈ K.edgeSet from (K.spanningCoe.mem_neighborFinset v w).mp hwK)
  rw [SimpleGraph.degree, hcover, Finset.card_biUnion hdis]
  rfl

open scoped Classical in
lemma subfamilyGraph_card_edges {V : Type*} [Fintype V] {G : SimpleGraph V}
    (A : Finset G.Subgraph)
    (hp : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet)) :
    (subfamilyGraph A).edgeFinset.card = ∑ H ∈ A, H.coe.edgeFinset.card := by
  classical
  have hcover : (subfamilyGraph A).edgeFinset =
      A.biUnion (fun H => H.spanningCoe.edgeFinset) := by
    ext e
    simpa only [Finset.mem_biUnion, SimpleGraph.mem_edgeFinset,
      Set.mem_iUnion, exists_prop] using Set.ext_iff.mp (subfamilyGraph_edges A) e
  have hdis : (A : Set G.Subgraph).PairwiseDisjoint
      (fun H => H.spanningCoe.edgeFinset) := by
    intro H hH K hK hne
    apply Finset.disjoint_left.mpr
    intro e heH heK
    exact Set.disjoint_left.mp (hp hH hK hne)
      (SimpleGraph.mem_edgeFinset.mp heH) (SimpleGraph.mem_edgeFinset.mp heK)
  rw [hcover, Finset.card_biUnion hdis]
  apply Finset.sum_congr rfl
  intro H _
  exact subgraph_edge_card H

open scoped Classical in
lemma cycle_only_decomposition_scaled {V : Type*} [Fintype V] {G : SimpleGraph V}
    (heven : ∀ v, Even (G.degree v)) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧
      3 * E.card ≤ 2 * (D.filter (fun H =>
        H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)).card + D.card := by
  classical
  let C := D.filter (fun H => H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
  let A := D \ C
  have hCD : C ⊆ D := Finset.filter_subset _ _
  have hAD : A ⊆ D := Finset.sdiff_subset
  have hpA : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet) := by
    intro H hH K hK hne
    exact hdec.1 (hAD hH) (hAD hK) hne
  have hC : ∀ H ∈ C, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    exact (Finset.mem_filter.mp hH).2
  have hA : ∀ H ∈ A, H.coe.edgeFinset.card = 1 := by
    intro H hH
    rcases hD H (hAD hH) with hc | he
    · exact False.elim ((Finset.mem_sdiff.mp hH).2
        (Finset.mem_filter.mpr ⟨hAD hH, by
          simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
            ← Nat.card_eq_fintype_card] using hc⟩))
    · exact he
  have hDG : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  have hR : ∀ v, Even ((subfamilyGraph A).degree v) := by
    intro v
    have hs := Finset.sum_sdiff (f := fun H : G.Subgraph => H.spanningCoe.degree v) hCD
    have hce : Even (∑ H ∈ C, H.spanningCoe.degree v) :=
      Finset.even_sum _ (fun H hH => regular_two_spanning_even H (hC H hH).2 v)
    have he := heven v
    rw [← subfamilyGraph_degree D hdec.1 v, hDG] at hs
    rw [subfamilyGraph_degree A hpA]
    change (∑ H ∈ A, H.spanningCoe.degree v) + _ = _ at hs
    rw [Nat.even_iff] at hce he ⊢
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hs he hce ⊢
    omega
  have hcR : (subfamilyGraph A).edgeFinset.card = A.card := by
    rw [subfamilyGraph_card_edges A hpA]
    calc
      _ = ∑ _H ∈ A, (1 : ℕ) := Finset.sum_congr rfl hA
      _ = A.card := by simp
  obtain ⟨R, hRcyc, hRdec, hRcard⟩ := exists_cycle_decomposition (subfamilyGraph A) (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hR v)
  obtain ⟨B, hB, hpB, heB, hcB⟩ := lift_decomposition_property
    (fun H => H.Connected ∧ H.IsRegularOfDegree 2)
    (subfamilyGraph_le A) R (by
      intro H hH
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hRcyc H hH) hRdec
  have heBA : (⋃ H ∈ B, H.edgeSet) = ⋃ H ∈ A, H.edgeSet :=
    heB.trans (subfamilyGraph_edges A)
  refine ⟨C ∪ B, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · exact hC H hH
    · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hB H hH
  · have hpC : Set.PairwiseDisjoint (C : Set G.Subgraph) (fun H => H.edgeSet) := by
      intro H hH K hK hne
      exact hdec.1 (hCD hH) (hCD hK) hne
    rw [Finset.coe_union]
    apply hpC.union hpB
    intro H hH K hK _
    apply Set.disjoint_left.mpr
    intro e heH heK
    have heU : e ∈ ⋃ K ∈ B, K.edgeSet :=
      Set.mem_iUnion.mpr ⟨K, Set.mem_iUnion.mpr ⟨hK, heK⟩⟩
    rw [heBA] at heU
    obtain ⟨J, heJ⟩ := Set.mem_iUnion.mp heU
    obtain ⟨hJ, heJ⟩ := Set.mem_iUnion.mp heJ
    have hHJ : H ≠ J := by
      intro h
      subst J
      exact (Finset.mem_sdiff.mp hJ).2 hH
    exact Set.disjoint_left.mp (hdec.1 (hCD hH) (hAD hJ) hHJ) heH heJ
  · ext e
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨H, _, heH⟩
      exact H.edgeSet_subset heH
    · intro he
      have heD : e ∈ ⋃ H ∈ D, H.edgeSet := hdec.2.symm ▸ he
      obtain ⟨H, heH⟩ := Set.mem_iUnion.mp heD
      obtain ⟨hH, heH⟩ := Set.mem_iUnion.mp heH
      by_cases hHC : H ∈ C
      · exact ⟨H, Finset.mem_union_left _ hHC, heH⟩
      · have heA : e ∈ ⋃ H ∈ A, H.edgeSet := Set.mem_iUnion.mpr
          ⟨H, Set.mem_iUnion.mpr ⟨Finset.mem_sdiff.mpr ⟨hH, hHC⟩, heH⟩⟩
        rw [← heBA] at heA
        obtain ⟨K, heK⟩ := Set.mem_iUnion.mp heA
        obtain ⟨hK, heK⟩ := Set.mem_iUnion.mp heK
        exact ⟨K, Finset.mem_union_right _ hK, heK⟩
  · have hc := Finset.card_union_le C B
    have hsum : A.card + C.card = D.card := Finset.card_sdiff_add_card_eq_card hCD
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcR hRcard
    change 3 * (C ∪ B).card ≤ 2 * C.card + D.card
    omega

open scoped Classical in
lemma cycle_only_decomposition_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    (heven : ∀ v, Even (G.degree v)) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card ≤ D.card := by
  classical
  obtain ⟨E, hE, hdecE, hcE⟩ := cycle_only_decomposition_scaled heven D hD hdec
  refine ⟨E, hE, hdecE, ?_⟩
  have hc := Finset.card_filter_le D
    (fun H => H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
  omega

open scoped Classical in
lemma minimal_even_decomposition_cycles {V : Type*} [Fintype V] {G : SimpleGraph V}
    (heven : ∀ v, Even (G.degree v)) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D)
    (hmin : ∀ E : Finset G.Subgraph, (∀ H ∈ E, IsCycleOrEdge H.coe) →
      IsDecomposition G E → D.card ≤ E.card) :
    ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
  classical
  obtain ⟨E, hE, hdecE, hcE⟩ := cycle_only_decomposition_scaled heven D hD hdec
  have hle := hmin E (fun H hH => Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hE H hH)) hdecE
  let C := D.filter (fun H => H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
  have hc : D.card ≤ C.card := by
    change 3 * E.card ≤ 2 * C.card + D.card at hcE
    omega
  have heq : C = D := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hc
  intro H hH
  have hHC : H ∈ C := heq.symm ▸ hH
  exact (Finset.mem_filter.mp hHC).2

open scoped Classical in
lemma HasFourCyclePartition.even {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : HasFourCyclePartition G) : ∀ v, Even (G.degree v) := by
  classical
  obtain ⟨D, hD, hdec⟩ := hG
  have hDG : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  intro v
  rw [← hDG, subfamilyGraph_degree D hdec.1]
  apply Finset.even_sum
  intro H hH
  apply regular_two_spanning_even
  simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using (hD H hH).2.1

open scoped Classical in
lemma asymptotic_iff_even_cycle_uniform :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C : ℝ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ C * Fintype.card V) := by
  rw [asymptotic_iff_even_uniform]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro V _ _ G heven
    obtain ⟨D, hD, hdec, hcD⟩ := hC G heven
    obtain ⟨E, hE, hdecE, hcE⟩ := cycle_only_decomposition_le heven D hD hdec
    refine ⟨E, hE, hdecE, le_trans ?_ hcD⟩
    exact_mod_cast hcE
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro V _ _ G heven
    obtain ⟨D, hD, hdec, hcD⟩ := hC G heven
    refine ⟨D, ?_, hdec, hcD⟩
    intro H hH
    apply Or.inl
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD H hH

open scoped Classical in
lemma asymptotic_iff_four_cycle_cycle_uniform :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C : ℝ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      HasFourCyclePartition G →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ C * Fintype.card V) := by
  rw [asymptotic_iff_four_cycle_uniform]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro V _ _ G hfour
    obtain ⟨D, hD, hdec, hcD⟩ := hC G hfour
    obtain ⟨E, hE, hdecE, hcE⟩ := cycle_only_decomposition_le hfour.even D hD hdec
    refine ⟨E, hE, hdecE, le_trans ?_ hcD⟩
    exact_mod_cast hcE
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro V _ _ G hfour
    obtain ⟨D, hD, hdec, hcD⟩ := hC G hfour
    refine ⟨D, ?_, hdec, hcD⟩
    intro H hH
    apply Or.inl
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD H hH

#print axioms cycle_only_decomposition_scaled
#print axioms minimal_even_decomposition_cycles
#print axioms asymptotic_iff_even_cycle_uniform
#print axioms asymptotic_iff_four_cycle_cycle_uniform


open scoped Classical in
lemma regular_two_spanning_degree {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H : G.Subgraph) (hH : H.coe.IsRegularOfDegree 2) (v : V) :
    H.spanningCoe.degree v = if v ∈ H.verts then 2 else 0 := by
  classical
  rw [SimpleGraph.Subgraph.degree_spanningCoe]
  split_ifs with hv
  · have hd := hH ⟨v, hv⟩
    simpa only [SimpleGraph.Subgraph.coe_degree] using hd
  · exact SimpleGraph.Subgraph.degree_of_notMem_verts hv

open scoped Classical in
lemma cycle_subfamily_even {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hp : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    ∀ v, Even ((subfamilyGraph D).degree v) := by
  classical
  intro v
  rw [subfamilyGraph_degree D hp]
  exact Finset.even_sum _ (fun H hH => regular_two_spanning_even H (hD H hH).2 v)

open scoped Classical in
lemma prune_cycles_at_vertex {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) (v : V) :
    ∃ (R : SimpleGraph V) (A : Finset G.Subgraph),
      R ≤ G ∧ (∀ w, Even (R.degree w)) ∧ v ∉ R.support ∧
      (∀ H ∈ A, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet) ∧
      Disjoint (⋃ H ∈ A, H.edgeSet) R.edgeSet ∧
      (⋃ H ∈ A, H.edgeSet) ∪ R.edgeSet = G.edgeSet ∧
      2 * A.card = G.degree v := by
  classical
  let A := D.filter (fun H => v ∈ H.verts)
  let B := D \ A
  have hAD : A ⊆ D := Finset.filter_subset _ _
  have hBD : B ⊆ D := Finset.sdiff_subset
  have hpA : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet) := by
    intro H hH K hK hne
    exact hdec.1 (hAD hH) (hAD hK) hne
  have hpB : Set.PairwiseDisjoint (B : Set G.Subgraph) (fun H => H.edgeSet) := by
    intro H hH K hK hne
    exact hdec.1 (hBD hH) (hBD hK) hne
  refine ⟨subfamilyGraph B, A, subfamilyGraph_le B,
    cycle_subfamily_even B (fun H hH => hD H (hBD hH)) hpB, ?_,
    (fun H hH => hD H (hAD hH)), hpA, ?_, ?_, ?_⟩
  · rintro ⟨w, hvw⟩
    have he : s(v, w) ∈ (subfamilyGraph B).edgeSet := hvw
    rw [subfamilyGraph_edges B] at he
    obtain ⟨H, he⟩ := Set.mem_iUnion.mp he
    obtain ⟨hH, he⟩ := Set.mem_iUnion.mp he
    have hv : v ∈ H.verts := H.edge_vert he
    exact (Finset.mem_sdiff.mp hH).2 (Finset.mem_filter.mpr ⟨hBD hH, hv⟩)
  · rw [subfamilyGraph_edges B]
    apply Set.disjoint_left.mpr
    intro e heA heB
    obtain ⟨H, heA⟩ := Set.mem_iUnion.mp heA
    obtain ⟨hH, heH⟩ := Set.mem_iUnion.mp heA
    obtain ⟨K, heB⟩ := Set.mem_iUnion.mp heB
    obtain ⟨hK, heK⟩ := Set.mem_iUnion.mp heB
    exact Set.disjoint_left.mp (hdec.1 (hAD hH) (hBD hK) (by
      intro h
      subst K
      exact (Finset.mem_sdiff.mp hK).2 hH)) heH heK
  · rw [subfamilyGraph_edges B, ← hdec.2]
    ext e
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop]
    constructor
    · rintro (⟨H, hH, he⟩ | ⟨H, hH, he⟩)
      · exact ⟨H, hAD hH, he⟩
      · exact ⟨H, hBD hH, he⟩
    · rintro ⟨H, hH, he⟩
      by_cases hHA : H ∈ A
      · exact Or.inl ⟨H, hHA, he⟩
      · exact Or.inr ⟨H, Finset.mem_sdiff.mpr ⟨hH, hHA⟩, he⟩
  · have hDG : subfamilyGraph D = G :=
      SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
    have hdeg := subfamilyGraph_degree D hdec.1 v
    rw [hDG] at hdeg
    rw [hdeg]
    calc
      2 * A.card = ∑ _H ∈ A, (2 : ℕ) := by simp [mul_comm]
      _ = ∑ H ∈ D, (if v ∈ H.verts then 2 else 0) := by
        simp only [A, Finset.sum_filter]
      _ = ∑ H ∈ D, H.spanningCoe.degree v := by
        apply Finset.sum_congr rfl
        intro H hH
        exact (regular_two_spanning_degree H (hD H hH).2 v).symm

noncomputable def subgraphMapInjective {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) (K : G.Subgraph) :
    K.coe ≃g (K.map f).coe where
  toEquiv := Equiv.Set.image f K.verts hf
  map_rel_iff' := by
    intro u v
    change Relation.Map K.Adj f f (f u.val) (f v.val) ↔ K.Adj u.val v.val
    simp only [Relation.Map, hf.eq_iff]
    simp

open scoped Classical in
lemma cycle_property_map_injective {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H) (hf : Function.Injective f)
    (K : G.Subgraph) (hK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) :
    (K.map f).coe.Connected ∧ (K.map f).coe.IsRegularOfDegree 2 := by
  classical
  have h := cycle_property_map_iso (subgraphMapInjective f hf K) (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hK)
  simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using h

open scoped Classical in
lemma map_cycle_decomposition_injective {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H) (hf : Function.Injective f)
    (D : Finset G.Subgraph)
    (hD : ∀ K ∈ D, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) :
    ∃ E : Finset H.Subgraph,
      (∀ K ∈ E, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (E : Set H.Subgraph) (fun K => K.edgeSet) ∧
      (⋃ K ∈ E, K.edgeSet) = Sym2.map f '' G.edgeSet ∧ E.card ≤ D.card := by
  classical
  let E := D.image (SimpleGraph.Subgraph.map f)
  refine ⟨E, ?_, ?_, ?_, Finset.card_image_le⟩
  · intro K hK
    obtain ⟨K', hK', rfl⟩ := Finset.mem_image.mp hK
    exact cycle_property_map_injective f hf K' (hD K' hK')
  · intro K hK L hL hne
    obtain ⟨K', hK', rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨L', hL', rfl⟩ := Finset.mem_image.mp hL
    change Disjoint (K'.map f).edgeSet (L'.map f).edgeSet
    rw [SimpleGraph.Subgraph.edgeSet_map, SimpleGraph.Subgraph.edgeSet_map]
    apply Set.disjoint_left.mpr
    rintro e ⟨a, ha, rfl⟩ ⟨b, hb, heq⟩
    have hba : b = a := Sym2.map.injective hf heq
    subst b
    exact Set.disjoint_left.mp (hdec.1 hK' hL' (by
      intro h
      exact hne (congrArg (SimpleGraph.Subgraph.map f) h))) ha hb
  · ext e
    constructor
    · intro he
      obtain ⟨K, he⟩ := Set.mem_iUnion.mp he
      obtain ⟨hK, heK⟩ := Set.mem_iUnion.mp he
      obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
      rw [SimpleGraph.Subgraph.edgeSet_map] at heK
      obtain ⟨a, ha, rfl⟩ := heK
      exact ⟨a, L.edgeSet_subset ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      rw [← hdec.2] at ha
      obtain ⟨K, ha⟩ := Set.mem_iUnion.mp ha
      obtain ⟨hK, ha⟩ := Set.mem_iUnion.mp ha
      refine Set.mem_iUnion.mpr ⟨K.map f, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_image.mpr ⟨K, hK, rfl⟩
      · rw [SimpleGraph.Subgraph.edgeSet_map]
        exact ⟨a, ha, rfl⟩

open scoped Classical in
lemma lift_cycle_decomposition_induce_support {V : Type*} [Fintype V]
    (G : SimpleGraph V) (s : Set V) (hs : G.support ⊆ s)
    (D : Finset (G.induce s).Subgraph)
    (hD : ∀ K ∈ D, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition (G.induce s) D) :
    ∃ E : Finset G.Subgraph,
      (∀ K ∈ E, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card ≤ D.card := by
  classical
  let f := (SimpleGraph.Embedding.induce (G := G) s).toHom
  have hf : Function.Injective f := Subtype.val_injective
  obtain ⟨E, hE, hpE, heE, hcE⟩ := map_cycle_decomposition_injective f hf D hD hdec
  refine ⟨E, hE, ⟨hpE, heE.trans ?_⟩, hcE⟩
  ext e
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact f.map_mem_edgeSet ha
  · intro he
    induction e using Sym2.ind with | h u v =>
    have hu : u ∈ s := hs ⟨v, he⟩
    have hv : v ∈ s := hs ⟨u, he.symm⟩
    exact ⟨s(⟨u, hu⟩, ⟨v, hv⟩), he, rfl⟩


set_option maxHeartbeats 300000 in
open scoped Classical in
/-- Eliminate a vertex of an even graph by taking its incident cycles.  The
remaining even graph has one fewer vertex.  This is an extension lemma, not a
uniform bound: its cost still depends on the eliminated vertex's degree. -/
lemma even_vertex_elimination {V : Type u} [Fintype V] (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) (v : V) (C : ℕ)
    (hsmall : ∀ (R : SimpleGraph {w : V // w ≠ v}),
      (∀ w, Even (R.degree w)) →
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition R D ∧ D.card ≤ C * Fintype.card {w : V // w ≠ v}) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧
      2 * E.card ≤ G.degree v + 2 * C * (Fintype.card V - 1) := by
  classical
  obtain ⟨D, hD, hdec, _⟩ := exists_cycle_decomposition G heven
  obtain ⟨R, A, hRG, hReven, hvR, hA, hpA, hdis, hcover, hcardA⟩ :=
    prune_cycles_at_vertex D hD hdec v
  let s : Set V := {w | w ≠ v}
  have hs : R.support ⊆ s := by
    intro w hw h
    subst w
    exact hvR hw
  have hevenI : ∀ w, Even ((R.induce s).degree w) := by
    intro w
    rw [SimpleGraph.degree_induce_of_support_subset hs]
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hReven w
  obtain ⟨I, hI, hdecI, hcI⟩ := hsmall (R.induce s) (by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hevenI w)
  obtain ⟨B, hB, hdecB, hcB⟩ := lift_cycle_decomposition_induce_support R s hs I (by
    intro H hH
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hI H hH) hdecI
  obtain ⟨B', hB', hpB', heB', hcB'⟩ := lift_decomposition_property
    (fun H => H.Connected ∧ H.IsRegularOfDegree 2) hRG B (by
      intro H hH
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hB H hH) hdecB
  refine ⟨A ∪ B', ?_, ⟨?_, ?_⟩, ?_⟩
  · intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · exact hA H hH
    · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hB' H hH
  · rw [Finset.coe_union]
    apply hpA.union hpB'
    intro H hH K hK _
    apply hdis.mono
    · intro e he
      exact Set.mem_iUnion.mpr ⟨H, Set.mem_iUnion.mpr ⟨hH, he⟩⟩
    · intro e he
      rw [← heB']
      exact Set.mem_iUnion.mpr ⟨K, Set.mem_iUnion.mpr ⟨hK, he⟩⟩
  · apply Set.Subset.antisymm
    · intro e he
      obtain ⟨H, he⟩ := Set.mem_iUnion.mp he
      obtain ⟨_, he⟩ := Set.mem_iUnion.mp he
      exact H.edgeSet_subset he
    · intro e he
      have heU := hcover.symm ▸ he
      rcases heU with heA | heR
      · obtain ⟨H, heA⟩ := Set.mem_iUnion.mp heA
        obtain ⟨hH, heH⟩ := Set.mem_iUnion.mp heA
        exact Set.mem_iUnion.mpr ⟨H, Set.mem_iUnion.mpr
          ⟨Finset.mem_union_left B' hH, heH⟩⟩
      · rw [← heB'] at heR
        obtain ⟨H, heR⟩ := Set.mem_iUnion.mp heR
        obtain ⟨hH, heH⟩ := Set.mem_iUnion.mp heR
        exact Set.mem_iUnion.mpr ⟨H, Set.mem_iUnion.mpr
          ⟨Finset.mem_union_right A hH, heH⟩⟩
  · have hc := Finset.card_union_le A B'
    have hn : Fintype.card {w : V // w ≠ v} = Fintype.card V - 1 := by
      rw [Fintype.card_subtype_compl (fun w : V => w = v)]
      simp
    rw [hn] at hcI
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hcardA hcI ⊢
    nlinarith only [hc, hcardA, hcI, hcB, hcB']

open scoped Classical in
lemma even_smallest_counterexample_min_degree {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : ℕ) (heven : ∀ v, Even (G.degree v))
    (hbad : ∀ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G D → C * Fintype.card V < D.card)
    (hsmall : ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      Fintype.card W < Fintype.card V → (∀ w, Even (R.degree w)) →
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition R D ∧ D.card ≤ C * Fintype.card W) :
    ∀ v, 2 * C < G.degree v := by
  classical
  intro v
  obtain ⟨E, hE, hdecE, hcE⟩ := even_vertex_elimination G heven v C (by
    intro R hR
    apply hsmall R (Fintype.card_subtype_lt (x := v) (by simp))
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hR)
  have hbig := hbad E hE hdecE
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hn : Fintype.card V - 1 + 1 = Fintype.card V := by omega
  have hmul : C * (Fintype.card V - 1) + C = C * Fintype.card V := by
    nlinarith [congrArg (fun n => C * n) hn]
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hcE hmul hbig ⊢
  nlinarith only [hcE, hmul, hbig]

#print axioms prune_cycles_at_vertex
#print axioms even_vertex_elimination
#print axioms even_smallest_counterexample_min_degree


open scoped Classical in
/-- A fixed linear bound for even graphs need only be established above the
corresponding minimum-degree threshold. This is an exact reduction, not the
missing high-minimum-degree theorem. -/
lemma uniform_even_bound_of_high_min_degree (C : ℕ)
    (hhigh : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) → (∀ v, 2 * C < G.degree v) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ D.card ≤ C * Fintype.card V) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ D.card ≤ C * Fintype.card V := by
  classical
  have main : ∀ n : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      Fintype.card V = n → (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ D.card ≤ C * Fintype.card V := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ _ G hn heven
      by_contra hbad
      have hd : ∀ v, 2 * C < G.degree v := by
        apply even_smallest_counterexample_min_degree G C heven
        · intro D hD hdec
          by_contra hcard
          exact hbad ⟨D, hD, hdec, Nat.le_of_not_gt hcard⟩
        · intro W _ _ R hcard hReven
          apply ih (Fintype.card W) (hcard.trans_eq hn) R rfl
          simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
            using hReven
      exact hbad (hhigh G heven hd)
  intro V _ _ G heven
  exact main (Fintype.card V) G rfl heven

#print axioms uniform_even_bound_of_high_min_degree

open scoped Classical in
lemma asymptotic_iff_high_min_degree_cycle_uniform :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) → (∀ v, 2 * C < G.degree v) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ D.card ≤ C * Fintype.card V) := by
  rw [asymptotic_iff_even_cycle_uniform]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨⌈C⌉₊, ?_⟩
    intro V _ _ G heven _
    obtain ⟨D, hD, hdec, hcard⟩ := hC G heven
    refine ⟨D, hD, hdec, ?_⟩
    have hle : (D.card : ℝ) ≤ (⌈C⌉₊ : ℝ) * Fintype.card V :=
      hcard.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (Nat.cast_nonneg _))
    exact_mod_cast hle
  · rintro ⟨C, hC⟩
    refine ⟨(C : ℝ), ?_⟩
    intro V _ _ G heven
    obtain ⟨D, hD, hdec, hcard⟩ := uniform_even_bound_of_high_min_degree C hC G heven
    refine ⟨D, hD, hdec, ?_⟩
    exact_mod_cast hcard

#print axioms asymptotic_iff_high_min_degree_cycle_uniform
open scoped Classical in
lemma exists_minimal_even_decomposition {V : Type*} [Fintype V]
    (G : SimpleGraph V) (heven : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧
      ∀ E : Finset G.Subgraph, (∀ H ∈ E, IsCycleOrEdge H.coe) →
        IsDecomposition G E → D.card ≤ E.card := by
  classical
  let P : ℕ → Prop := fun n => ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ D.card = n
  have hex : ∃ n, P n := by
    obtain ⟨D, hD, hdec, _⟩ := exists_edge_decomposition G
    exact ⟨D.card, D, hD, hdec, rfl⟩
  obtain ⟨D, hD, hdec, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ E : Finset G.Subgraph, (∀ H ∈ E, IsCycleOrEdge H.coe) →
      IsDecomposition G E → D.card ≤ E.card := by
    intro E hE hdecE
    rw [hcard]
    exact Nat.find_min' hex ⟨E, hE, hdecE, rfl⟩
  exact ⟨D, minimal_even_decomposition_cycles heven D hD hdec hmin, hdec, hmin⟩

open scoped Classical in
lemma minimal_cycle_subfamily_card {V : Type u} [Fintype V] {G : SimpleGraph V}
    (C : ℕ) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D)
    (hmin : ∀ E : Finset G.Subgraph, (∀ H ∈ E, IsCycleOrEdge H.coe) →
      IsDecomposition G E → D.card ≤ E.card)
    (hsmall : ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      Fintype.card W < Fintype.card V → (∀ w, Even (R.degree w)) →
      ∃ E : Finset R.Subgraph,
        (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition R E ∧ E.card ≤ C * Fintype.card W)
    (A : Finset G.Subgraph) (hAD : A ⊆ D) (s : Finset V)
    (hs : s.card < Fintype.card V)
    (hAs : ∀ H ∈ A, H.verts ⊆ (s : Set V)) :
    A.card ≤ C * s.card := by
  classical
  by_contra hbad
  let R := subfamilyGraph A
  have hpA : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet) := by
    intro H hH K hK hne
    exact hdec.1 (hAD hH) (hAD hK) hne
  have hReven : ∀ v, Even (R.degree v) :=
    cycle_subfamily_even A (fun H hH => hD H (hAD hH)) hpA
  have hRs : R.support ⊆ (s : Set V) := by
    rintro v ⟨w, hvw⟩
    have he : s(v, w) ∈ R.edgeSet := hvw
    rw [subfamilyGraph_edges A] at he
    obtain ⟨H, he⟩ := Set.mem_iUnion.mp he
    obtain ⟨hH, he⟩ := Set.mem_iUnion.mp he
    exact hAs H hH (H.edge_vert he)
  have hIeven : ∀ w, Even ((R.induce (s : Set V)).degree w) := by
    intro w
    have hd := SimpleGraph.degree_induce_of_support_subset hRs w
    have he := hReven w
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd he ⊢
    rw [hd]
    exact he
  obtain ⟨I, hI, hdecI, hcI⟩ := hsmall (R.induce (s : Set V)) (by simpa using hs) (by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hIeven w)
  obtain ⟨B, hB, hdecB, hcB⟩ := lift_cycle_decomposition_induce_support R (s : Set V) hRs I (by
    intro H hH
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hI H hH) hdecI
  obtain ⟨B', hB', hpB', heB', hcB'⟩ := lift_decomposition_property
    (fun H => H.Connected ∧ H.IsRegularOfDegree 2) (subfamilyGraph_le A) B (by
      intro H hH
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hB H hH) hdecB
  have hDmixed : ∀ H ∈ D, IsCycleOrEdge H.coe := by
    intro H hH
    apply Or.inl
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD H hH
  have hBmixed : ∀ H ∈ B', IsCycleOrEdge H.coe := by
    intro H hH
    exact Or.inl (hB' H hH)
  have hreplace : (⋃ H ∈ A, H.edgeSet) = ⋃ H ∈ B', H.edgeSet := by
    rw [heB']
    exact (subfamilyGraph_edges A).symm
  have hc : B'.card < A.card := by
    have hIcard : I.card ≤ C * s.card := by simpa using hcI
    omega
  obtain ⟨E, hE, hdecE, hcE⟩ := replace_decomposition_subfamily D A B'
    hDmixed hdec hAD hBmixed hpB' hreplace hc
  exact Nat.not_lt_of_ge (hmin E hE hdecE) hcE

open scoped Classical in
lemma capacity_matching {ι V : Type*} (I : Finset ι) (S : ι → Finset V) (C : ℕ)
    (hcap : ∀ A ⊆ I, A.card ≤ C * (A.biUnion S).card) :
    ∃ f : I → V × Fin C, Function.Injective f ∧ ∀ i : I, (f i).1 ∈ S i := by
  classical
  let T : I → Finset (V × Fin C) := fun i => S i ×ˢ Finset.univ
  have hall : ∀ A : Finset I, A.card ≤ (A.biUnion T).card := by
    intro A
    let B := A.image (Subtype.val : I → ι)
    have hBI : B ⊆ I := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact j.property
    have hcard : B.card = A.card := Finset.card_image_of_injective _ Subtype.val_injective
    have heq : A.biUnion T = B.biUnion S ×ˢ (Finset.univ : Finset (Fin C)) := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_product, Finset.mem_univ, and_true,
        T, B, Finset.mem_image]
      constructor
      · rintro ⟨i, hi, hx⟩
        exact ⟨i.val, ⟨i, hi, rfl⟩, hx⟩
      · rintro ⟨i, ⟨j, hj, rfl⟩, hx⟩
        exact ⟨j, hj, hx⟩
    rw [heq, Finset.card_product, Finset.card_univ, Fintype.card_fin, ← hcard]
    simpa only [mul_comm] using hcap B hBI
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' T).mp hall
  exact ⟨f, hf, fun i => (Finset.mem_product.mp (hmem i)).1⟩

#print axioms minimal_cycle_subfamily_card
#print axioms capacity_matching

open scoped Classical in
lemma critical_cycle_capacity_assignment {V : Type u} [Fintype V] {G : SimpleGraph V}
    (C : ℕ) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D)
    (hmin : ∀ E : Finset G.Subgraph, (∀ H ∈ E, IsCycleOrEdge H.coe) →
      IsDecomposition G E → D.card ≤ E.card)
    (hsmall : ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      Fintype.card W < Fintype.card V → (∀ w, Even (R.degree w)) →
      ∃ E : Finset R.Subgraph,
        (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition R E ∧ E.card ≤ C * Fintype.card W)
    (F : Finset G.Subgraph) (hFD : F ⊆ D) (hF : F.card ≤ C * Fintype.card V) :
    ∃ f : F → V × Fin C,
      Function.Injective f ∧ ∀ H : F, (f H).1 ∈ H.val.verts := by
  classical
  let S : G.Subgraph → Finset V := fun H => H.verts.toFinset
  have hcap : ∀ A ⊆ F, A.card ≤ C * (A.biUnion S).card := by
    intro A hAF
    let s := A.biUnion S
    by_cases hs : s = Finset.univ
    · have hle := (Finset.card_le_card hAF).trans hF
      change A.card ≤ C * s.card
      simpa only [hs, Finset.card_univ] using hle
    · have hlt : s.card < Fintype.card V := by
        simpa only [Finset.card_univ] using
          Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hs)
      apply minimal_cycle_subfamily_card C D hD hdec hmin hsmall A
        (hAF.trans hFD) s hlt
      intro H hH v hv
      exact Finset.mem_biUnion.mpr ⟨H, hH, Set.mem_toFinset.mpr hv⟩
  obtain ⟨f, hf, hmem⟩ := capacity_matching F S C hcap
  exact ⟨f, hf, fun H => Set.mem_toFinset.mp (hmem H)⟩

open scoped Classical in
/-- A smallest counterexample has a globally balanced rooted cycle system:
C distinct cycles can be assigned to each vertex, with every assigned cycle
containing its assigned vertex, and with at least one further unassigned cycle.
This necessary condition is not by itself a contradiction. -/
lemma critical_cycle_ownership {V : Type u} [Fintype V] {G : SimpleGraph V}
    (C : ℕ) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D)
    (hmin : ∀ E : Finset G.Subgraph, (∀ H ∈ E, IsCycleOrEdge H.coe) →
      IsDecomposition G E → D.card ≤ E.card)
    (hsmall : ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      Fintype.card W < Fintype.card V → (∀ w, Even (R.degree w)) →
      ∃ E : Finset R.Subgraph,
        (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition R E ∧ E.card ≤ C * Fintype.card W)
    (hbad : C * Fintype.card V < D.card) :
    ∃ owner : V × Fin C → D, Function.Injective owner ∧
      (∀ p, p.1 ∈ (owner p).val.verts) ∧
      ∃ H₀ : D, ∀ p, owner p ≠ H₀ := by
  classical
  obtain ⟨F, hFD, hcardF⟩ := Finset.exists_subset_card_eq (Nat.le_of_lt hbad)
  obtain ⟨f, hf, hmem⟩ := critical_cycle_capacity_assignment C D hD hdec hmin hsmall
    F hFD (Nat.le_of_eq hcardF)
  have hbij : Function.Bijective f := by
    apply (Fintype.bijective_iff_injective_and_card f).mpr
    refine ⟨hf, ?_⟩
    simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, hcardF, mul_comm]
  let e : F ≃ V × Fin C := Equiv.ofBijective f hbij
  let incl : F → D := fun H => ⟨H.val, hFD H.property⟩
  have hincl : Function.Injective incl := by
    intro H K h
    apply Subtype.ext
    exact congrArg (fun H : D => H.val) h
  let owner : V × Fin C → D := fun p => incl (e.symm p)
  have howner : Function.Injective owner := hincl.comp e.symm.injective
  refine ⟨owner, howner, ?_, ?_⟩
  · intro p
    have h := hmem (e.symm p)
    change (e (e.symm p)).1 ∈ (e.symm p).val.verts at h
    simpa only [Equiv.apply_symm_apply] using h
  · have hn : ¬ Function.Surjective owner := by
      intro hs
      have hc := Fintype.card_le_of_surjective owner hs
      simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, mul_comm] at hc
      omega
    obtain ⟨H₀, hH₀⟩ := not_forall.mp hn
    refine ⟨H₀, ?_⟩
    intro p hp
    exact hH₀ ⟨p, hp⟩

#print axioms exists_minimal_even_decomposition
#print axioms critical_cycle_capacity_assignment
#print axioms critical_cycle_ownership

namespace ThreeCycleObstruction
open scoped Fin.NatCast

def edgeEnds : Fin 30 → Fin 15 × Fin 15 :=
  ![(0, 1), (0, 7), (0, 8), (0, 9), (1, 5), (1, 8), (1, 12), (2, 3), (2, 4), (2, 12), (2, 14), (3, 7), (3, 12), (3, 13), (4, 9), (4, 11), (4, 14), (5, 6), (5, 11), (5, 12), (6, 10), (6, 11), (6, 13), (7, 9), (7, 13), (8, 10), (8, 14), (9, 11), (10, 13), (10, 14)]

-- Kernel-reconstructed resolution proof. Unlike the default `bv_decide`
-- implementation, this does not depend on compiler-trust axioms.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lrat_proof no_two_regular_cut_connected_clauses
"p cnf 30 524
1 2 3 0
-1 -2 -3 0
1 2 4 0
-1 -2 -4 0
1 3 4 0
-1 -3 -4 0
2 3 4 0
-2 -3 -4 0
1 5 6 0
-1 -5 -6 0
1 5 7 0
-1 -5 -7 0
1 6 7 0
-1 -6 -7 0
5 6 7 0
-5 -6 -7 0
8 9 10 0
-8 -9 -10 0
8 9 11 0
-8 -9 -11 0
8 10 11 0
-8 -10 -11 0
9 10 11 0
-9 -10 -11 0
8 12 13 0
-8 -12 -13 0
8 12 14 0
-8 -12 -14 0
8 13 14 0
-8 -13 -14 0
12 13 14 0
-12 -13 -14 0
9 15 16 0
-9 -15 -16 0
9 15 17 0
-9 -15 -17 0
9 16 17 0
-9 -16 -17 0
15 16 17 0
-15 -16 -17 0
5 18 19 0
-5 -18 -19 0
5 18 20 0
-5 -18 -20 0
5 19 20 0
-5 -19 -20 0
18 19 20 0
-18 -19 -20 0
18 21 22 0
-18 -21 -22 0
18 21 23 0
-18 -21 -23 0
18 22 23 0
-18 -22 -23 0
21 22 23 0
-21 -22 -23 0
2 12 24 0
-2 -12 -24 0
2 12 25 0
-2 -12 -25 0
2 24 25 0
-2 -24 -25 0
12 24 25 0
-12 -24 -25 0
3 6 26 0
-3 -6 -26 0
3 6 27 0
-3 -6 -27 0
3 26 27 0
-3 -26 -27 0
6 26 27 0
-6 -26 -27 0
4 15 24 0
-4 -15 -24 0
4 15 28 0
-4 -15 -28 0
4 24 28 0
-4 -24 -28 0
15 24 28 0
-15 -24 -28 0
21 26 29 0
-21 -26 -29 0
21 26 30 0
-21 -26 -30 0
21 29 30 0
-21 -29 -30 0
26 29 30 0
-26 -29 -30 0
16 19 22 0
-16 -19 -22 0
16 19 28 0
-16 -19 -28 0
16 22 28 0
-16 -22 -28 0
19 22 28 0
-19 -22 -28 0
7 10 13 0
-7 -10 -13 0
7 10 20 0
-7 -10 -20 0
7 13 20 0
-7 -13 -20 0
10 13 20 0
-10 -13 -20 0
14 23 25 0
-14 -23 -25 0
14 23 29 0
-14 -23 -29 0
14 25 29 0
-14 -25 -29 0
23 25 29 0
-23 -25 -29 0
11 17 27 0
-11 -17 -27 0
11 17 30 0
-11 -17 -30 0
11 27 30 0
-11 -27 -30 0
17 27 30 0
-17 -27 -30 0
2 4 10 11 13 14 16 17 25 28 0
-2 -4 -10 -11 -13 -14 -16 -17 -25 -28 0
1 3 7 19 20 22 23 27 29 30 0
-1 -3 -7 -19 -20 -22 -23 -27 -29 -30 0
5 16 20 21 23 28 0
-5 -16 -20 -21 -23 -28 0
4 9 17 19 22 24 0
-4 -9 -17 -19 -22 -24 0
2 4 10 11 13 14 17 19 22 25 0
-2 -4 -10 -11 -13 -14 -17 -19 -22 -25 0
1 3 7 16 20 23 27 28 29 30 0
-1 -3 -7 -16 -20 -23 -27 -28 -29 -30 0
7 9 11 12 14 20 0
-7 -9 -11 -12 -14 -20 0
1 6 10 13 18 19 0
-1 -6 -10 -13 -18 -19 0
2 4 7 11 14 16 17 20 25 28 0
-2 -4 -7 -11 -14 -16 -17 -20 -25 -28 0
1 3 10 13 19 22 23 27 29 30 0
-1 -3 -10 -13 -19 -22 -23 -27 -29 -30 0
5 7 8 11 13 15 17 18 22 28 0
-5 -7 -8 -11 -13 -15 -17 -18 -22 -28 0
1 6 8 11 13 15 17 18 22 28 0
-1 -6 -8 -11 -13 -15 -17 -18 -22 -28 0
5 7 11 12 14 15 17 18 22 28 0
-5 -7 -11 -12 -14 -15 -17 -18 -22 -28 0
1 6 11 12 14 15 17 18 22 28 0
-1 -6 -11 -12 -14 -15 -17 -18 -22 -28 0
5 7 8 11 13 15 17 21 23 28 0
-5 -7 -8 -11 -13 -15 -17 -21 -23 -28 0
1 6 8 11 13 15 17 21 23 28 0
-1 -6 -8 -11 -13 -15 -17 -21 -23 -28 0
5 7 11 12 14 15 17 21 23 28 0
-5 -7 -11 -12 -14 -15 -17 -21 -23 -28 0
1 6 11 12 14 15 17 21 23 28 0
-1 -6 -11 -12 -14 -15 -17 -21 -23 -28 0
4 5 7 8 11 13 17 18 22 24 0
-4 -5 -7 -8 -11 -13 -17 -18 -22 -24 0
1 4 6 8 11 13 17 18 22 24 0
-1 -4 -6 -8 -11 -13 -17 -18 -22 -24 0
4 5 7 11 12 14 17 18 22 24 0
-4 -5 -7 -11 -12 -14 -17 -18 -22 -24 0
1 4 6 11 12 14 17 18 22 24 0
-1 -4 -6 -11 -12 -14 -17 -18 -22 -24 0
4 5 7 8 11 13 17 21 23 24 0
-4 -5 -7 -8 -11 -13 -17 -21 -23 -24 0
1 4 6 8 11 13 17 21 23 24 0
-1 -4 -6 -8 -11 -13 -17 -21 -23 -24 0
4 5 7 11 12 14 17 21 23 24 0
-4 -5 -7 -11 -12 -14 -17 -21 -23 -24 0
1 4 6 11 12 14 17 21 23 24 0
-1 -4 -6 -11 -12 -14 -17 -21 -23 -24 0
2 4 7 11 14 17 19 20 22 25 0
-2 -4 -7 -11 -14 -17 -19 -20 -22 -25 0
1 3 10 13 16 23 27 28 29 30 0
-1 -3 -10 -13 -16 -23 -27 -28 -29 -30 0
2 8 13 23 24 29 0
-2 -8 -13 -23 -24 -29 0
2 4 10 11 13 16 17 23 28 29 0
-2 -4 -10 -11 -13 -16 -17 -23 -28 -29 0
14 18 22 25 26 30 0
-14 -18 -22 -25 -26 -30 0
1 3 7 14 19 20 22 25 27 30 0
-1 -3 -7 -14 -19 -20 -22 -25 -27 -30 0
2 4 10 11 13 17 19 22 23 29 0
-2 -4 -10 -11 -13 -17 -19 -22 -23 -29 0
2 4 12 14 15 16 18 19 21 29 0
-2 -4 -12 -14 -15 -16 -18 -19 -21 -29 0
2 4 8 13 15 16 18 19 21 29 0
-2 -4 -8 -13 -15 -16 -18 -19 -21 -29 0
2 4 9 12 14 17 18 19 21 29 0
-2 -4 -9 -12 -14 -17 -18 -19 -21 -29 0
2 4 8 9 13 17 18 19 21 29 0
-2 -4 -8 -9 -13 -17 -18 -19 -21 -29 0
2 4 5 12 14 15 16 20 21 29 0
-2 -4 -5 -12 -14 -15 -16 -20 -21 -29 0
2 4 5 8 13 15 16 20 21 29 0
-2 -4 -5 -8 -13 -15 -16 -20 -21 -29 0
2 4 5 9 12 14 17 20 21 29 0
-2 -4 -5 -9 -12 -14 -17 -20 -21 -29 0
2 4 5 8 9 13 17 20 21 29 0
-2 -4 -5 -8 -9 -13 -17 -20 -21 -29 0
1 3 7 14 16 20 25 27 28 30 0
-1 -3 -7 -14 -16 -20 -25 -27 -28 -30 0
2 4 12 14 15 16 18 19 26 30 0
-2 -4 -12 -14 -15 -16 -18 -19 -26 -30 0
2 4 8 13 15 16 18 19 26 30 0
-2 -4 -8 -13 -15 -16 -18 -19 -26 -30 0
2 4 9 12 14 17 18 19 26 30 0
-2 -4 -9 -12 -14 -17 -18 -19 -26 -30 0
2 4 8 9 13 17 18 19 26 30 0
-2 -4 -8 -9 -13 -17 -18 -19 -26 -30 0
2 4 5 12 14 15 16 20 26 30 0
-2 -4 -5 -12 -14 -15 -16 -20 -26 -30 0
2 4 5 8 13 15 16 20 26 30 0
-2 -4 -5 -8 -13 -15 -16 -20 -26 -30 0
2 4 5 9 12 14 17 20 26 30 0
-2 -4 -5 -9 -12 -14 -17 -20 -26 -30 0
2 4 5 8 9 13 17 20 26 30 0
-2 -4 -5 -8 -9 -13 -17 -20 -26 -30 0
5 7 8 10 12 19 21 22 25 29 0
-5 -7 -8 -10 -12 -19 -21 -22 -25 -29 0
1 6 8 10 12 19 21 22 25 29 0
-1 -6 -8 -10 -12 -19 -21 -22 -25 -29 0
5 7 9 11 12 19 21 22 25 29 0
-5 -7 -9 -11 -12 -19 -21 -22 -25 -29 0
1 6 9 11 12 19 21 22 25 29 0
-1 -6 -9 -11 -12 -19 -21 -22 -25 -29 0
2 5 7 8 10 19 21 22 24 29 0
-2 -5 -7 -8 -10 -19 -21 -22 -24 -29 0
1 2 6 8 10 19 21 22 24 29 0
-1 -2 -6 -8 -10 -19 -21 -22 -24 -29 0
2 5 7 9 11 19 21 22 24 29 0
-2 -5 -7 -9 -11 -19 -21 -22 -24 -29 0
1 2 6 9 11 19 21 22 24 29 0
-1 -2 -6 -9 -11 -19 -21 -22 -24 -29 0
2 4 7 11 16 17 20 23 28 29 0
-2 -4 -7 -11 -16 -17 -20 -23 -28 -29 0
5 7 8 10 12 19 22 25 26 30 0
-5 -7 -8 -10 -12 -19 -22 -25 -26 -30 0
1 6 8 10 12 19 22 25 26 30 0
-1 -6 -8 -10 -12 -19 -22 -25 -26 -30 0
5 7 9 11 12 19 22 25 26 30 0
-5 -7 -9 -11 -12 -19 -22 -25 -26 -30 0
1 6 9 11 12 19 22 25 26 30 0
-1 -6 -9 -11 -12 -19 -22 -25 -26 -30 0
2 5 7 8 10 19 22 24 26 30 0
-2 -5 -7 -8 -10 -19 -22 -24 -26 -30 0
1 2 6 8 10 19 22 24 26 30 0
-1 -2 -6 -8 -10 -19 -22 -24 -26 -30 0
2 5 7 9 11 19 22 24 26 30 0
-2 -5 -7 -9 -11 -19 -22 -24 -26 -30 0
1 2 6 9 11 19 22 24 26 30 0
-1 -2 -6 -9 -11 -19 -22 -24 -26 -30 0
1 3 10 13 14 19 22 25 27 30 0
-1 -3 -10 -13 -14 -19 -22 -25 -27 -30 0
5 7 8 10 12 16 21 25 28 29 0
-5 -7 -8 -10 -12 -16 -21 -25 -28 -29 0
1 6 8 10 12 16 21 25 28 29 0
-1 -6 -8 -10 -12 -16 -21 -25 -28 -29 0
5 7 9 11 12 16 21 25 28 29 0
-5 -7 -9 -11 -12 -16 -21 -25 -28 -29 0
1 6 9 11 12 16 21 25 28 29 0
-1 -6 -9 -11 -12 -16 -21 -25 -28 -29 0
2 5 7 8 10 16 21 24 28 29 0
-2 -5 -7 -8 -10 -16 -21 -24 -28 -29 0
1 2 6 8 10 16 21 24 28 29 0
-1 -2 -6 -8 -10 -16 -21 -24 -28 -29 0
2 5 7 9 11 16 21 24 28 29 0
-2 -5 -7 -9 -11 -16 -21 -24 -28 -29 0
1 2 6 9 11 16 21 24 28 29 0
-1 -2 -6 -9 -11 -16 -21 -24 -28 -29 0
2 4 7 11 17 19 20 22 23 29 0
-2 -4 -7 -11 -17 -19 -20 -22 -23 -29 0
5 7 8 10 12 16 25 26 28 30 0
-5 -7 -8 -10 -12 -16 -25 -26 -28 -30 0
1 6 8 10 12 16 25 26 28 30 0
-1 -6 -8 -10 -12 -16 -25 -26 -28 -30 0
5 7 9 11 12 16 25 26 28 30 0
-5 -7 -9 -11 -12 -16 -25 -26 -28 -30 0
1 6 9 11 12 16 25 26 28 30 0
-1 -6 -9 -11 -12 -16 -25 -26 -28 -30 0
2 5 7 8 10 16 24 26 28 30 0
-2 -5 -7 -8 -10 -16 -24 -26 -28 -30 0
1 2 6 8 10 16 24 26 28 30 0
-1 -2 -6 -8 -10 -16 -24 -26 -28 -30 0
2 5 7 9 11 16 24 26 28 30 0
-2 -5 -7 -9 -11 -16 -24 -26 -28 -30 0
1 2 6 9 11 16 24 26 28 30 0
-1 -2 -6 -9 -11 -16 -24 -26 -28 -30 0
1 3 10 13 14 16 25 27 28 30 0
-1 -3 -10 -13 -14 -16 -25 -27 -28 -30 0
8 10 15 16 27 30 0
-8 -10 -15 -16 -27 -30 0
2 4 10 13 14 16 25 27 28 30 0
-2 -4 -10 -13 -14 -16 -25 -27 -28 -30 0
3 6 11 17 21 29 0
-3 -6 -11 -17 -21 -29 0
1 3 7 11 17 19 20 22 23 29 0
-1 -3 -7 -11 -17 -19 -20 -22 -23 -29 0
2 4 10 13 14 19 22 25 27 30 0
-2 -4 -10 -13 -14 -19 -22 -25 -27 -30 0
9 11 15 18 19 23 26 27 28 29 0
-9 -11 -15 -18 -19 -23 -26 -27 -28 -29 0
8 10 15 18 19 23 26 27 28 29 0
-8 -10 -15 -18 -19 -23 -26 -27 -28 -29 0
5 9 11 15 20 23 26 27 28 29 0
-5 -9 -11 -15 -20 -23 -26 -27 -28 -29 0
5 8 10 15 20 23 26 27 28 29 0
-5 -8 -10 -15 -20 -23 -26 -27 -28 -29 0
3 6 9 11 15 18 19 23 28 29 0
-3 -6 -9 -11 -15 -18 -19 -23 -28 -29 0
3 6 8 10 15 18 19 23 28 29 0
-3 -6 -8 -10 -15 -18 -19 -23 -28 -29 0
1 3 7 11 16 17 20 23 28 29 0
-1 -3 -7 -11 -16 -17 -20 -23 -28 -29 0
3 5 6 9 11 15 20 23 28 29 0
-3 -5 -6 -9 -11 -15 -20 -23 -28 -29 0
3 5 6 8 10 15 20 23 28 29 0
-3 -5 -6 -8 -10 -15 -20 -23 -28 -29 0
4 9 11 18 19 23 24 26 27 29 0
-4 -9 -11 -18 -19 -23 -24 -26 -27 -29 0
4 8 10 18 19 23 24 26 27 29 0
-4 -8 -10 -18 -19 -23 -24 -26 -27 -29 0
4 5 9 11 20 23 24 26 27 29 0
-4 -5 -9 -11 -20 -23 -24 -26 -27 -29 0
4 5 8 10 20 23 24 26 27 29 0
-4 -5 -8 -10 -20 -23 -24 -26 -27 -29 0
3 4 6 9 11 18 19 23 24 29 0
-3 -4 -6 -9 -11 -18 -19 -23 -24 -29 0
3 4 6 8 10 18 19 23 24 29 0
-3 -4 -6 -8 -10 -18 -19 -23 -24 -29 0
3 4 5 6 9 11 20 23 24 29 0
-3 -4 -5 -6 -9 -11 -20 -23 -24 -29 0
3 4 5 6 8 10 20 23 24 29 0
-3 -4 -5 -6 -8 -10 -20 -23 -24 -29 0
1 3 5 8 9 13 17 20 26 30 0
-1 -3 -5 -8 -9 -13 -17 -20 -26 -30 0
1 3 5 9 12 14 17 20 26 30 0
-1 -3 -5 -9 -12 -14 -17 -20 -26 -30 0
1 3 5 8 13 15 16 20 26 30 0
-1 -3 -5 -8 -13 -15 -16 -20 -26 -30 0
1 3 5 12 14 15 16 20 26 30 0
-1 -3 -5 -12 -14 -15 -16 -20 -26 -30 0
1 3 8 9 13 17 18 19 26 30 0
-1 -3 -8 -9 -13 -17 -18 -19 -26 -30 0
1 3 9 12 14 17 18 19 26 30 0
-1 -3 -9 -12 -14 -17 -18 -19 -26 -30 0
1 3 8 13 15 16 18 19 26 30 0
-1 -3 -8 -13 -15 -16 -18 -19 -26 -30 0
1 3 12 14 15 16 18 19 26 30 0
-1 -3 -12 -14 -15 -16 -18 -19 -26 -30 0
2 4 7 14 16 20 25 27 28 30 0
-2 -4 -7 -14 -16 -20 -25 -27 -28 -30 0
1 3 5 8 9 13 17 20 21 29 0
-1 -3 -5 -8 -9 -13 -17 -20 -21 -29 0
1 3 5 9 12 14 17 20 21 29 0
-1 -3 -5 -9 -12 -14 -17 -20 -21 -29 0
1 3 5 8 13 15 16 20 21 29 0
-1 -3 -5 -8 -13 -15 -16 -20 -21 -29 0
1 3 5 12 14 15 16 20 21 29 0
-1 -3 -5 -12 -14 -15 -16 -20 -21 -29 0
1 3 8 9 13 17 18 19 21 29 0
-1 -3 -8 -9 -13 -17 -18 -19 -21 -29 0
1 3 9 12 14 17 18 19 21 29 0
-1 -3 -9 -12 -14 -17 -18 -19 -21 -29 0
1 3 8 13 15 16 18 19 21 29 0
-1 -3 -8 -13 -15 -16 -18 -19 -21 -29 0
1 3 12 14 15 16 18 19 21 29 0
-1 -3 -12 -14 -15 -16 -18 -19 -21 -29 0
1 3 10 11 13 17 19 22 23 29 0
-1 -3 -10 -11 -13 -17 -19 -22 -23 -29 0
5 7 8 13 15 18 22 27 28 30 0
-5 -7 -8 -13 -15 -18 -22 -27 -28 -30 0
1 6 8 13 15 18 22 27 28 30 0
-1 -6 -8 -13 -15 -18 -22 -27 -28 -30 0
5 7 12 14 15 18 22 27 28 30 0
-5 -7 -12 -14 -15 -18 -22 -27 -28 -30 0
1 6 12 14 15 18 22 27 28 30 0
-1 -6 -12 -14 -15 -18 -22 -27 -28 -30 0
5 7 8 13 15 21 23 27 28 30 0
-5 -7 -8 -13 -15 -21 -23 -27 -28 -30 0
1 6 8 13 15 21 23 27 28 30 0
-1 -6 -8 -13 -15 -21 -23 -27 -28 -30 0
5 7 12 14 15 21 23 27 28 30 0
-5 -7 -12 -14 -15 -21 -23 -27 -28 -30 0
1 6 12 14 15 21 23 27 28 30 0
-1 -6 -12 -14 -15 -21 -23 -27 -28 -30 0
4 5 7 8 13 18 22 24 27 30 0
-4 -5 -7 -8 -13 -18 -22 -24 -27 -30 0
1 4 6 8 13 18 22 24 27 30 0
-1 -4 -6 -8 -13 -18 -22 -24 -27 -30 0
4 5 7 12 14 18 22 24 27 30 0
-4 -5 -7 -12 -14 -18 -22 -24 -27 -30 0
1 4 6 12 14 18 22 24 27 30 0
-1 -4 -6 -12 -14 -18 -22 -24 -27 -30 0
4 5 7 8 13 21 23 24 27 30 0
-4 -5 -7 -8 -13 -21 -23 -24 -27 -30 0
1 4 6 8 13 21 23 24 27 30 0
-1 -4 -6 -8 -13 -21 -23 -24 -27 -30 0
4 5 7 12 14 21 23 24 27 30 0
-4 -5 -7 -12 -14 -21 -23 -24 -27 -30 0
1 4 6 12 14 21 23 24 27 30 0
-1 -4 -6 -12 -14 -21 -23 -24 -27 -30 0
2 4 7 14 19 20 22 25 27 30 0
-2 -4 -7 -14 -19 -20 -22 -25 -27 -30 0
1 3 10 11 13 16 17 23 28 29 0
-1 -3 -10 -11 -13 -16 -17 -23 -28 -29 0
2 4 10 13 16 23 27 28 29 30 0
-2 -4 -10 -13 -16 -23 -27 -28 -29 -30 0
9 10 12 13 17 21 23 25 26 27 0
-9 -10 -12 -13 -17 -21 -23 -25 -26 -27 0
10 12 13 15 16 21 23 25 26 27 0
-10 -12 -13 -15 -16 -21 -23 -25 -26 -27 0
9 10 12 13 17 18 22 25 26 27 0
-9 -10 -12 -13 -17 -18 -22 -25 -26 -27 0
10 12 13 15 16 18 22 25 26 27 0
-10 -12 -13 -15 -16 -18 -22 -25 -26 -27 0
2 9 10 13 17 21 23 24 26 27 0
-2 -9 -10 -13 -17 -21 -23 -24 -26 -27 0
2 10 13 15 16 21 23 24 26 27 0
-2 -10 -13 -15 -16 -21 -23 -24 -26 -27 0
2 9 10 13 17 18 22 24 26 27 0
-2 -9 -10 -13 -17 -18 -22 -24 -26 -27 0
2 10 13 15 16 18 22 24 26 27 0
-2 -10 -13 -15 -16 -18 -22 -24 -26 -27 0
3 6 9 10 12 13 17 21 23 25 0
-3 -6 -9 -10 -12 -13 -17 -21 -23 -25 0
3 6 10 12 13 15 16 21 23 25 0
-3 -6 -10 -12 -13 -15 -16 -21 -23 -25 0
3 6 9 10 12 13 17 18 22 25 0
-3 -6 -9 -10 -12 -13 -17 -18 -22 -25 0
3 6 10 12 13 15 16 18 22 25 0
-3 -6 -10 -12 -13 -15 -16 -18 -22 -25 0
1 3 7 11 14 17 19 20 22 25 0
-1 -3 -7 -11 -14 -17 -19 -20 -22 -25 0
2 3 6 9 10 13 17 21 23 24 0
-2 -3 -6 -9 -10 -13 -17 -21 -23 -24 0
2 3 6 10 13 15 16 21 23 24 0
-2 -3 -6 -10 -13 -15 -16 -21 -23 -24 0
2 3 6 9 10 13 17 18 22 24 0
-2 -3 -6 -9 -10 -13 -17 -18 -22 -24 0
2 3 6 10 13 15 16 18 22 24 0
-2 -3 -6 -10 -13 -15 -16 -18 -22 -24 0
2 4 10 13 19 22 23 27 29 30 0
-2 -4 -10 -13 -19 -22 -23 -27 -29 -30 0
9 11 14 15 18 19 25 26 27 28 0
-9 -11 -14 -15 -18 -19 -25 -26 -27 -28 0
8 10 14 15 18 19 25 26 27 28 0
-8 -10 -14 -15 -18 -19 -25 -26 -27 -28 0
5 9 11 14 15 20 25 26 27 28 0
-5 -9 -11 -14 -15 -20 -25 -26 -27 -28 0
5 8 10 14 15 20 25 26 27 28 0
-5 -8 -10 -14 -15 -20 -25 -26 -27 -28 0
3 6 9 11 14 15 18 19 25 28 0
-3 -6 -9 -11 -14 -15 -18 -19 -25 -28 0
3 6 8 10 14 15 18 19 25 28 0
-3 -6 -8 -10 -14 -15 -18 -19 -25 -28 0
1 3 7 11 14 16 17 20 25 28 0
-1 -3 -7 -11 -14 -16 -17 -20 -25 -28 0
3 5 6 9 11 14 15 20 25 28 0
-3 -5 -6 -9 -11 -14 -15 -20 -25 -28 0
3 5 6 8 10 14 15 20 25 28 0
-3 -5 -6 -8 -10 -14 -15 -20 -25 -28 0
4 9 11 14 18 19 24 25 26 27 0
-4 -9 -11 -14 -18 -19 -24 -25 -26 -27 0
4 8 10 14 18 19 24 25 26 27 0
-4 -8 -10 -14 -18 -19 -24 -25 -26 -27 0
4 5 9 11 14 20 24 25 26 27 0
-4 -5 -9 -11 -14 -20 -24 -25 -26 -27 0
4 5 8 10 14 20 24 25 26 27 0
-4 -5 -8 -10 -14 -20 -24 -25 -26 -27 0
3 4 6 9 11 14 18 19 24 25 0
-3 -4 -6 -9 -11 -14 -18 -19 -24 -25 0
3 4 6 8 10 14 18 19 24 25 0
-3 -4 -6 -8 -10 -14 -18 -19 -24 -25 0
3 4 5 6 9 11 14 20 24 25 0
-3 -4 -5 -6 -9 -11 -14 -20 -24 -25 0
3 4 5 6 8 10 14 20 24 25 0
-3 -4 -5 -6 -8 -10 -14 -20 -24 -25 0
2 4 7 16 20 23 27 28 29 30 0
-2 -4 -7 -16 -20 -23 -27 -28 -29 -30 0
7 9 12 17 20 21 23 25 26 27 0
-7 -9 -12 -17 -20 -21 -23 -25 -26 -27 0
7 12 15 16 20 21 23 25 26 27 0
-7 -12 -15 -16 -20 -21 -23 -25 -26 -27 0
7 9 12 17 18 20 22 25 26 27 0
-7 -9 -12 -17 -18 -20 -22 -25 -26 -27 0
7 12 15 16 18 20 22 25 26 27 0
-7 -12 -15 -16 -18 -20 -22 -25 -26 -27 0
2 7 9 17 20 21 23 24 26 27 0
-2 -7 -9 -17 -20 -21 -23 -24 -26 -27 0
2 7 15 16 20 21 23 24 26 27 0
-2 -7 -15 -16 -20 -21 -23 -24 -26 -27 0
2 7 9 17 18 20 22 24 26 27 0
-2 -7 -9 -17 -18 -20 -22 -24 -26 -27 0
2 7 15 16 18 20 22 24 26 27 0
-2 -7 -15 -16 -18 -20 -22 -24 -26 -27 0
3 6 7 9 12 17 20 21 23 25 0
-3 -6 -7 -9 -12 -17 -20 -21 -23 -25 0
3 6 7 12 15 16 20 21 23 25 0
-3 -6 -7 -12 -15 -16 -20 -21 -23 -25 0
3 6 7 9 12 17 18 20 22 25 0
-3 -6 -7 -9 -12 -17 -18 -20 -22 -25 0
3 6 7 12 15 16 18 20 22 25 0
-3 -6 -7 -12 -15 -16 -18 -20 -22 -25 0
1 3 10 11 13 14 17 19 22 25 0
-1 -3 -10 -11 -13 -14 -17 -19 -22 -25 0
2 3 6 7 9 17 20 21 23 24 0
-2 -3 -6 -7 -9 -17 -20 -21 -23 -24 0
2 3 6 7 15 16 20 21 23 24 0
-2 -3 -6 -7 -15 -16 -20 -21 -23 -24 0
2 3 6 7 9 17 18 20 22 24 0
-2 -3 -6 -7 -9 -17 -18 -20 -22 -24 0
2 3 6 7 15 16 18 20 22 24 0
-2 -3 -6 -7 -15 -16 -18 -20 -22 -24 0
2 4 7 19 20 22 23 27 29 30 0
-2 -4 -7 -19 -20 -22 -23 -27 -29 -30 0
1 3 10 11 13 14 16 17 25 28 0
-1 -3 -10 -11 -13 -14 -16 -17 -25 -28 0
1 3 12 15 25 28 0
-1 -3 -12 -15 -25 -28 0
2 4 5 7 26 27 0
-2 -4 -5 -7 -26 -27 0
"
"525 -13 -20 24 4 23 14 17 11 21 0 51 44 102 104 169 21 26 0
526 -12 -15 -25 -28 0 76 60 3 7 522 0
527 -25 -27 -28 -29 -30 0 120 118 86 110 112 51 55 94 96 37 39 76 80 526 27 31 18 525 99 45 374 0
528 -22 20 -23 -28 0 54 96 47 0
529 -13 -23 -12 -15 11 -28 21 0 26 19 21 34 98 104 528 49 89 42 11 15 136 0
530 -10 -8 -15 -27 -30 0 120 294 18 37 0
531 22 16 -20 21 0 49 89 48 0
532 14 -15 25 -27 -28 21 -30 0 80 63 118 105 529 29 530 23 97 103 34 531 54 96 41 12 16 135 0
533 -20 13 8 23 24 4 17 11 21 0 21 51 44 100 165 0
534 -15 -27 -28 -29 -30 0 527 120 118 86 76 80 63 532 108 28 32 51 55 96 533 101 45 378 0
535 24 13 -27 -28 -29 -30 0 120 534 35 86 39 94 55 108 29 18 103 97 527 61 73 482 0
536 13 -27 -28 -29 -30 0 86 120 534 39 94 55 108 92 35 527 118 29 31 18 535 78 58 129 0
536 d 535 0
537 2 4 -27 -28 -29 -30 0 536 86 120 534 39 94 55 527 118 3 7 59 176 26 21 0
538 -24 -27 -28 -29 -30 0 536 86 120 534 39 94 55 108 78 537 58 178 27 0
539 -27 -28 -29 -30 0 86 118 120 527 534 39 94 55 536 538 61 63 73 26 410 21 0
539 d 538 537 536 534 527 0
540 -4 24 -13 -28 -29 -30 0 88 539 71 69 86 76 8 61 57 112 26 51 55 94 39 33 116 432 21 0
541 2 4 24 -3 -28 0 73 3 61 57 522 0
542 -22 10 14 8 25 4 24 27 -28 26 0 105 54 96 467 0
543 10 -11 14 8 25 4 24 27 -28 26 21 -29 0 105 73 71 69 17 34 542 49 89 312 0
544 -12 24 -13 -28 -29 -30 0 88 539 69 540 541 73 86 60 26 32 105 529 116 543 24 104 37 528 92 127 0
545 -10 14 12 -13 0 27 22 98 104 18 133 0
546 11 10 -15 27 0 113 23 36 0
547 24 -13 -28 -29 -30 0 539 86 540 73 544 63 110 112 27 55 94 545 546 116 20 37 0
547 d 544 540 0
548 -11 -8 15 -30 0 116 20 35 0
549 2 4 27 26 0 71 3 14 10 523 0
550 14 12 -2 -24 -13 -29 0 62 27 178 105 0
551 -14 -13 -28 -29 -30 0 88 539 547 78 549 80 71 69 86 108 30 51 55 94 39 33 116 442 21 0
552 -13 -28 -29 -30 0 539 88 547 78 549 551 58 550 0
552 d 551 547 0
553 -24 13 27 -28 26 21 -29 0 78 80 549 62 58 31 25 108 55 94 33 413 18 0
554 12 24 13 -29 0 31 63 110 0
555 -9 -14 -15 -12 13 27 0 36 113 24 97 103 134 0
556 -14 -15 -28 -29 -30 0 552 86 88 539 553 554 108 28 55 94 555 19 37 116 0
557 17 9 4 24 -28 0 37 92 94 127 0
558 22 -10 16 -8 -23 -15 -6 -3 -28 21 -29 0 49 89 314 0
559 9 -2 -28 -29 -30 0 552 86 88 539 553 69 8 73 556 29 554 60 105 71 557 116 40 546 558 54 96 465 0
560 -2 -28 -29 -30 0 86 88 539 552 553 69 8 73 556 29 559 20 36 113 0
560 d 559 0
561 -28 -29 -30 0 88 86 539 552 553 554 560 61 110 112 526 29 55 94 33 421 18 0
561 d 560 556 552 0
562 -9 -8 27 -15 0 20 36 113 0
563 16 23 28 21 0 51 91 48 42 125 0
564 -8 17 23 2 27 -15 24 26 21 0 113 57 26 562 419 22 0
565 27 24 28 26 21 -29 0 79 77 69 71 8 61 57 110 112 51 55 563 40 564 34 29 17 434 0
566 9 -27 -15 -30 0 118 19 23 530 0
567 -8 1 3 -12 25 14 -27 -15 28 -30 0 566 34 120 118 530 26 519 0
568 24 -29 -30 0 561 88 86 77 79 565 118 566 34 91 93 563 108 112 61 63 8 4 567 29 21 446 0
569 8 17 11 25 14 16 4 -24 28 0 27 29 21 58 98 104 137 0
570 2 10 -8 17 11 25 14 16 4 28 0 121 59 26 0
571 -27 16 -15 -29 -30 0 86 561 563 112 108 568 74 118 120 569 530 570 58 178 31 0
572 16 -15 -29 -30 0 568 74 561 88 86 563 108 571 549 58 31 550 0
572 d 571 0
573 14 -2 -24 -29 0 58 31 550 0
574 -13 -22 -18 -14 -2 -6 -3 -16 -15 -24 0 34 30 444 17 0
575 -15 -29 -30 0 568 88 86 74 572 40 34 566 69 71 549 113 62 58 573 108 51 55 574 25 411 22 0
575 d 572 0
576 9 8 15 -30 0 35 19 116 0
577 -14 13 -16 27 -29 -30 0 561 575 75 88 69 8 110 59 28 576 38 113 24 97 103 134 0
578 13 23 27 -29 -30 0 86 561 563 568 577 105 31 64 0
579 14 23 27 -29 -30 0 578 86 561 563 575 568 105 64 27 545 548 113 23 38 0
580 23 27 -29 -30 0 561 575 75 88 69 8 578 579 110 32 59 0
580 d 579 578 0
581 -20 -11 -9 -13 -23 -6 -3 -4 -24 -29 0 6 102 334 11 0
582 -11 -9 -13 -23 27 15 -24 28 26 -29 0 75 69 8 112 59 26 108 71 24 581 453 99 16 0
583 -13 27 -29 -30 0 561 575 75 88 69 8 580 112 59 568 26 576 582 113 38 91 93 128 0
584 -9 -17 -4 -24 28 0 38 91 93 128 0
585 -22 9 11 25 14 -23 27 15 28 26 0 33 54 90 447 0
586 27 -29 -30 0 561 575 75 568 88 86 69 71 580 108 112 583 29 548 113 584 23 585 95 49 332 0
586 d 583 580 577 0
587 -8 -12 20 -9 0 26 18 103 0
588 22 -9 11 -24 28 21 -29 0 95 49 55 48 42 108 112 573 59 587 29 21 98 11 15 136 0
589 12 25 15 28 0 75 59 8 4 521 0
590 1 13 23 2 8 17 11 -27 15 28 21 0 1 151 68 0
591 -18 25 8 -29 -30 0 568 561 575 589 58 86 586 118 120 35 588 75 88 54 105 32 590 396 6 65 0
592 18 -10 8 19 21 -29 0 51 47 108 104 29 0
593 8 -29 -30 0 575 586 120 39 86 561 568 118 35 588 90 21 592 591 110 64 27 0
593 d 591 0
594 -20 12 23 -18 14 17 11 15 28 21 0 31 44 102 153 0
595 -18 14 -29 -30 0 575 586 120 35 593 18 39 86 561 568 118 588 90 75 54 105 64 31 594 45 99 390 0
596 18 10 -8 19 15 28 21 -29 0 51 41 112 589 26 97 12 16 135 0
597 -29 -30 0 86 561 568 575 586 118 120 35 39 588 90 593 18 596 595 110 28 589 0
597 d 86 0
598 17 11 21 29 0 81 113 70 72 297 0
599 6 19 27 11 12 22 25 21 29 0 89 598 38 59 67 227 2 0
600 19 11 -8 -28 12 22 25 21 -30 0 597 598 120 63 78 59 81 89 38 23 599 66 286 5 0
601 -8 15 12 25 21 -18 -14 -30 0 589 597 111 54 548 30 600 92 48 33 103 18 0
602 11 -13 -9 8 22 21 -18 29 0 598 21 38 98 89 42 11 15 136 0
603 -6 -16 -11 -9 -28 -2 -24 -26 -30 0 78 66 290 5 0
604 15 12 25 21 -18 -14 -30 0 59 63 597 111 54 81 589 601 576 25 602 118 116 24 39 92 603 67 223 2 0
604 d 601 0
605 8 9 -19 12 -18 0 42 25 17 98 15 11 136 0
606 12 25 21 -18 -14 -30 0 597 111 54 63 604 80 93 95 40 34 48 598 605 22 30 103 0
606 d 604 0
607 -24 5 20 17 9 -15 13 8 -12 21 29 0 58 74 201 0
608 28 9 -15 25 21 -18 -14 -30 0 606 28 19 116 37 32 597 111 54 81 95 48 42 607 77 61 206 0
609 9 -15 25 21 -18 -14 -30 0 606 28 19 116 608 80 76 557 0
609 d 608 0
610 -15 25 21 -18 -14 -30 0 606 32 597 609 36 555 598 118 0
610 d 609 0
611 -11 -9 -12 -14 0 32 24 103 97 134 0
612 24 -17 15 -12 25 -26 -18 -14 -30 0 597 111 54 28 576 38 89 61 73 210 0
613 25 21 -18 -14 -30 0 597 81 111 54 606 28 32 610 576 611 598 38 93 89 531 42 612 58 78 197 0
613 d 610 606 0
614 21 -18 -14 -30 0 597 81 613 106 182 55 0
614 d 613 0
615 -12 23 -14 29 0 111 60 64 28 32 177 0
616 24 -3 15 12 0 57 73 8 0
617 -17 -9 15 12 -25 22 26 -30 0 120 38 69 93 616 78 62 549 0
618 13 11 19 4 2 17 -9 12 23 22 29 0 25 185 18 0
619 4 2 -9 15 -18 -14 -30 0 614 84 50 597 52 111 615 617 39 75 549 7 3 92 118 618 30 292 21 0
620 -13 11 -19 -18 -14 0 42 30 21 98 15 11 136 0
621 13 20 -9 12 0 25 103 18 0
622 28 -9 15 -18 -14 -30 0 597 614 52 615 50 84 95 48 42 621 30 620 118 24 309 0
623 -24 -9 15 -18 -14 -30 0 622 597 614 52 111 62 78 619 0
624 -13 -27 -4 -2 -28 -16 -25 -14 -30 0 118 30 296 21 0
625 -9 15 -18 -14 -30 0 597 614 52 615 111 50 84 617 39 622 92 623 57 73 616 4 69 118 624 371 25 18 0
625 d 623 622 619 0
626 15 -18 -14 -30 0 597 614 52 615 111 50 84 625 35 576 116 120 23 69 71 616 62 549 78 476 95 0
626 d 625 612 0
627 28 27 9 -15 12 22 -18 -14 0 93 95 40 48 605 113 22 30 103 0
628 9 -18 -14 -30 0 626 597 614 52 615 111 50 84 566 69 71 627 80 76 557 116 40 546 19 89 458 0
629 -18 -14 -30 0 597 614 84 50 52 615 626 628 34 93 89 80 76 48 42 621 30 620 118 24 327 0
629 d 628 626 614 0
630 8 19 23 4 24 12 18 -30 0 47 51 84 597 25 104 21 323 118 0
631 -15 -28 -9 12 -14 -30 0 629 80 76 63 106 53 96 41 630 30 18 97 12 16 135 0
632 19 10 13 18 0 97 41 12 16 135 0
633 -8 -28 -9 12 -14 -30 0 631 629 30 18 621 632 92 96 39 531 53 120 84 106 417 0
634 -16 -28 18 0 94 92 49 53 41 47 126 0
635 -28 -9 12 -14 -30 0 629 631 633 25 634 39 116 120 21 98 104 47 96 49 53 84 106 489 0
635 d 633 631 0
636 15 -19 28 -9 12 18 -14 0 589 75 79 106 584 53 39 90 0
637 20 11 2 4 23 16 17 28 18 29 0 3 43 237 12 0
638 -24 23 16 17 -15 -19 28 -14 -30 0 629 51 84 597 111 93 74 62 7 549 3 68 118 637 46 184 15 0
639 -20 -27 -2 -4 -25 -22 -19 -14 -30 0 4 406 46 11 0
640 23 16 17 -15 -19 28 12 -14 -30 0 93 629 597 111 51 84 638 77 57 8 4 69 65 118 639 43 315 16 0
641 20 -2 -24 -11 -26 -22 -19 -9 18 -30 0 24 43 99 252 0
642 -19 -9 12 -14 -30 0 635 629 597 636 36 34 93 640 56 106 81 598 63 59 20 24 25 641 46 102 257 0
643 -11 23 19 28 -9 18 -30 0 51 84 91 34 597 118 20 24 305 0
644 10 7 11 -14 0 21 97 30 0
645 -10 -20 -9 12 0 18 104 25 0
646 -9 12 -14 -30 0 629 635 642 91 47 34 589 106 643 645 21 632 30 0
646 d 642 635 0
647 15 23 28 11 19 9 18 -30 0 51 84 597 303 35 120 0
648 -15 -16 11 9 -30 0 40 566 113 0
649 28 11 19 12 -14 -30 0 646 629 91 648 589 647 106 0
650 11 19 12 -14 -30 0 646 629 597 649 634 33 80 76 566 63 106 51 321 84 0
650 d 649 0
651 24 -3 28 12 0 77 57 8 0
652 23 28 -15 27 12 18 -30 0 597 111 51 84 69 651 74 62 549 0
653 -7 19 18 0 47 100 102 632 0
654 10 19 9 18 -14 0 17 632 30 0
655 19 12 -14 -30 0 646 629 47 650 654 22 104 25 0
655 d 650 0
656 -16 28 11 12 -14 -30 0 655 646 629 90 648 53 589 106 0
657 28 7 5 11 12 -14 -30 0 646 629 597 656 93 33 566 652 56 106 261 0
658 -28 -19 9 12 18 -14 0 634 96 33 53 80 106 63 0
659 7 11 13 12 -14 -30 0 629 646 655 658 101 657 46 0
660 13 -10 12 -14 -30 0 629 646 655 658 597 25 22 656 93 33 566 652 56 106 81 63 59 659 100 248 43 0
661 -10 12 -14 -30 0 629 646 655 658 660 30 104 98 576 19 566 652 116 106 37 90 49 487 84 0
661 d 660 0
662 12 -14 -30 0 629 646 655 658 661 17 23 30 118 116 548 37 652 90 106 49 415 84 0
662 d 661 659 657 656 655 646 0
663 -7 -6 -10 18 0 100 16 43 0
664 -11 -19 -14 -30 0 662 32 28 629 118 116 611 37 17 90 49 84 69 71 663 101 46 11 2 6 549 0
665 26 27 -10 -19 13 18 0 69 71 663 101 46 11 2 6 549 0
666 27 -19 -14 -30 0 662 28 664 21 19 32 629 555 113 665 84 49 96 75 79 584 0
667 7 28 22 17 11 -19 13 8 18 0 19 93 34 101 141 46 0
668 28 -4 -19 -14 -30 0 597 662 615 664 666 120 598 56 28 21 19 32 629 93 34 79 667 100 402 43 0
669 -4 -19 -14 -30 0 666 120 629 668 634 76 39 0
669 d 668 0
670 -7 -28 -19 -14 -30 0 666 120 629 634 39 597 664 598 662 28 21 615 386 100 43 0
671 -28 -19 -14 -30 0 669 597 662 615 664 666 120 598 56 32 28 629 634 39 80 670 101 157 46 0
671 d 670 0
672 -19 -14 -30 0 597 662 615 28 664 19 666 120 598 56 669 671 75 93 34 0
672 d 671 669 666 664 0
673 4 -15 21 28 19 13 8 -12 18 29 0 91 40 34 193 77 58 0
674 -15 28 -14 -30 0 597 662 615 672 95 56 81 91 629 47 41 106 32 28 673 214 74 61 0
675 28 -14 -30 0 672 597 662 615 28 91 95 56 674 576 611 38 598 0
675 d 674 0
676 -4 15 -14 -30 0 629 675 634 39 33 597 662 615 672 89 56 81 47 41 106 218 78 61 0
677 15 -14 -30 0 597 662 615 672 629 675 634 89 56 32 28 676 189 73 58 0
677 d 676 0
678 -17 -14 -30 0 677 662 28 116 36 19 0
679 -14 -30 0 597 629 662 615 672 675 634 89 56 678 37 598 611 0
679 d 678 677 675 672 662 0
680 16 19 -12 17 -25 0 91 39 526 0
681 -20 21 22 -18 19 24 2 -13 10 8 29 0 44 102 229 0
682 21 -16 19 -11 -9 -30 0 597 679 109 20 27 64 34 79 94 634 60 29 24 81 681 45 99 280 0
683 19 -11 -9 17 -30 0 597 679 109 20 27 64 107 680 34 79 634 682 52 0
684 -16 -19 24 -9 0 92 34 79 0
685 20 -22 -19 -11 -9 -30 0 597 679 107 56 81 54 20 27 24 109 43 99 244 0
686 -11 -9 17 -30 0 597 679 109 107 20 24 27 29 60 64 683 684 39 526 93 56 685 46 102 265 0
686 d 683 0
687 16 -12 22 17 -25 0 39 93 526 0
688 -12 22 18 -9 17 -25 0 64 687 34 634 79 0
689 -20 28 15 12 22 18 11 17 14 0 95 31 46 102 145 0
690 -16 -9 17 -30 0 679 597 109 107 686 598 52 56 688 31 545 27 113 34 634 75 79 689 43 99 398 0
691 20 -28 -15 10 -8 -13 -27 -21 -30 0 597 679 107 52 43 99 382 0
692 -9 17 -30 0 597 679 109 107 686 598 113 52 56 688 31 27 545 690 89 39 93 76 80 691 46 102 161 0
692 d 690 686 0
693 -28 9 17 0 37 35 94 92 76 80 127 0
694 24 22 12 17 -30 0 692 693 95 679 27 31 35 566 37 57 651 77 69 208 84 49 0
695 22 12 17 -30 0 679 27 31 692 693 35 566 37 597 109 95 694 74 62 549 3 7 84 350 49 0
695 d 694 0
696 -24 12 17 -30 0 597 679 107 695 56 54 692 37 90 35 109 74 62 191 0
697 12 17 -30 0 692 693 37 35 597 679 107 31 27 695 90 54 56 41 47 81 696 57 77 216 0
697 d 696 695 0
698 -13 -20 -12 9 0 26 104 17 0
699 19 17 -30 0 697 692 693 35 37 648 597 679 107 95 54 47 698 29 632 22 0
700 13 26 18 -19 24 2 27 9 17 0 37 90 665 423 0
701 18 17 -30 0 692 37 699 90 597 679 109 697 64 60 35 566 107 49 84 69 71 700 26 430 17 0
702 -13 -18 -19 -12 9 0 42 26 17 98 11 15 136 0
703 17 -30 0 679 692 35 37 648 697 699 701 48 702 29 103 22 0
703 d 701 699 697 692 0
704 -15 22 -12 -30 0 703 597 679 109 40 526 93 0
705 -18 -12 -19 -30 0 597 679 109 64 703 116 107 52 54 48 704 79 92 33 587 29 602 0
706 -13 -21 -9 -12 -30 0 703 120 84 71 69 116 597 679 109 107 26 428 21 0
707 15 -12 -19 -30 0 705 597 679 109 64 60 703 120 79 634 96 33 49 84 706 665 425 0
708 -6 -12 -19 -30 0 597 679 107 707 704 56 81 703 116 36 19 120 546 109 60 66 242 1 0
709 -12 -19 -30 0 703 120 116 597 679 109 107 60 64 707 40 36 526 704 77 56 708 67 271 6 0
709 d 708 707 705 0
710 28 15 -9 -17 0 79 584 75 0
711 -24 -19 -30 0 703 116 679 709 31 545 23 120 546 710 96 597 109 617 84 49 42 38 531 62 78 195 0
712 -19 -30 0 703 120 116 597 679 109 709 31 27 545 23 546 710 96 617 84 49 711 57 73 212 0
712 d 711 709 0
713 12 24 15 -30 0 73 712 703 120 116 597 679 107 31 545 57 616 23 4 69 38 84 89 369 54 0
714 10 18 -12 -30 0 712 703 116 632 21 26 0
715 -22 -12 -28 15 -30 0 597 679 107 94 54 528 33 714 18 104 29 0
716 -20 21 22 2 24 -30 0 49 703 116 712 89 38 23 597 44 100 233 0
717 21 22 -12 24 -28 -30 0 703 116 712 89 38 19 26 23 597 679 109 60 81 716 45 101 276 0
718 24 -28 15 -30 0 712 597 679 107 713 715 89 717 634 52 0
719 -28 15 -30 0 712 703 120 116 597 679 109 107 718 62 64 78 31 545 549 23 84 38 187 89 54 0
719 d 718 715 0
720 15 -30 0 703 116 597 679 109 719 79 710 64 23 31 545 0
720 d 719 713 0
721 -30 0 597 679 107 109 703 116 120 712 720 40 546 89 91 528 526 104 31 0
722 -22 9 11 23 29 4 -28 24 0 721 87 117 70 72 85 96 50 329 0
723 13 -10 -28 12 24 -15 0 721 76 63 554 31 25 87 106 22 18 117 115 40 722 53 89 450 0
724 22 16 9 8 23 12 0 53 89 605 0
725 -22 -21 20 -28 0 96 50 47 0
726 9 22 8 23 -28 12 -15 0 693 724 40 0
727 -10 -28 12 24 -15 0 721 63 723 104 545 110 106 30 85 725 726 36 24 115 0
727 d 723 0
728 22 -14 -9 -28 -25 -15 0 721 110 87 106 36 119 115 34 53 89 448 0
729 -9 -28 12 24 -15 0 721 727 76 63 36 115 119 20 27 110 106 85 87 72 70 728 96 50 331 0
730 -21 -29 -11 -17 0 114 82 69 71 298 0
731 -3 21 23 14 27 4 12 24 0 721 83 57 66 2 403 0
732 23 -22 -13 -28 12 24 -15 0 727 729 17 30 693 23 114 76 107 730 51 731 5 67 144 0
733 -22 -13 -28 12 24 -15 0 721 63 732 112 56 85 0
733 d 732 0
734 3 -21 -23 -13 -8 -11 -17 -28 -15 0 114 76 5 67 152 0
735 -23 -13 -28 12 24 -15 0 721 733 727 729 17 30 693 23 114 76 63 57 112 85 87 52 734 66 2 395 0
736 -13 -28 12 24 -15 0 727 729 17 23 693 30 733 735 107 55 730 0
736 d 735 733 0
737 22 23 -20 16 0 89 53 48 0
738 -28 12 24 -15 0 721 63 727 729 693 40 736 554 31 103 85 106 737 96 50 654 0
738 d 736 729 727 0
739 10 -22 -19 9 -17 -14 13 -4 -25 -2 0 97 103 23 174 0
740 -27 -26 -4 -2 0 4 72 13 9 524 0
741 13 23 12 24 -15 0 721 57 738 77 4 651 554 25 87 740 117 119 22 40 175 0
742 29 -11 -13 23 -4 28 -25 -2 12 -15 0 721 87 107 740 30 119 40 36 91 724 17 130 0
743 -17 -29 -11 23 28 -15 0 40 730 563 0
744 -22 26 17 9 14 1 3 12 0 721 83 37 90 50 347 0
745 -11 -13 23 3 -4 28 -25 -2 12 -15 0 721 4 742 110 27 20 743 119 37 740 83 744 95 53 190 0
746 -13 23 -15 3 -4 28 -25 -2 12 0 721 745 117 115 740 36 87 23 110 545 0
746 d 745 0
747 23 12 24 -15 0 738 651 77 63 57 741 746 0
747 d 741 0
748 12 24 -15 0 721 57 63 738 77 747 112 85 87 56 740 93 119 40 0
748 d 747 738 0
749 29 -23 -2 -4 28 -15 0 721 85 87 56 740 93 119 40 0
750 13 16 27 14 1 3 25 28 0 721 117 29 291 22 0
751 27 -23 -2 -4 28 -12 -15 0 721 749 108 4 8 60 117 119 40 36 91 93 750 26 186 17 0
752 -23 -2 -4 28 -12 -15 0 721 60 749 108 751 740 83 52 56 181 0
752 d 751 0
753 22 -21 -2 -4 28 -12 -15 0 60 752 105 111 95 93 53 188 0
754 -16 -22 26 13 8 1 3 -15 0 721 83 50 34 40 90 345 0
755 17 16 -14 -12 0 721 115 37 611 0
756 -27 -2 -4 28 -12 -15 0 721 60 752 105 32 28 4 8 740 83 753 754 755 36 114 19 0
757 -2 -4 28 -12 -15 0 721 60 752 111 756 117 119 743 0
757 d 756 753 752 0
758 23 -11 -17 28 -12 -15 0 743 107 615 0
759 -23 -22 -25 0 721 112 56 85 0
760 3 -8 -10 -21 -22 -19 -25 2 -12 0 759 28 107 82 1 65 224 0
761 -17 28 24 -15 0 721 748 77 757 61 40 36 91 93 759 563 758 117 23 19 28 107 82 760 68 6 289 0
762 -3 26 8 10 16 -27 2 28 24 0 721 77 68 6 285 0
763 16 -22 -29 23 17 2 28 -12 24 0 721 119 115 61 680 37 563 24 20 82 762 1 65 228 0
764 18 19 9 14 -11 -12 0 47 653 698 29 97 22 0
765 -8 21 9 23 17 2 -12 24 0 721 119 83 72 70 115 26 22 437 0
766 -22 -29 23 28 24 -15 0 721 748 77 757 61 110 761 119 115 763 34 90 764 50 83 765 29 17 418 0
767 -29 23 28 24 -15 0 721 761 115 748 77 757 61 110 766 95 93 53 34 48 702 29 103 22 0
767 d 766 0
768 23 28 24 -15 0 748 767 107 615 0
768 d 767 0
769 -8 9 6 3 18 22 17 2 -12 24 0 721 115 26 22 441 0
770 28 24 -15 0 721 748 77 757 61 761 119 768 112 106 759 85 87 93 52 70 72 34 769 29 17 414 0
770 d 768 761 0
771 -16 -28 -15 0 34 40 693 0
772 -13 -19 22 -11 -17 9 25 -12 0 32 702 109 49 730 0
773 3 -14 -11 -17 -23 24 -15 0 721 108 85 114 770 76 748 5 67 156 0
774 22 8 9 -23 24 -15 0 721 770 693 19 114 771 748 526 61 76 89 772 29 108 85 87 52 773 66 2 391 0
775 8 9 -23 24 -15 0 721 770 17 774 96 54 56 85 592 0
775 d 774 0
776 -22 -26 9 -23 24 -15 0 721 748 770 526 775 28 109 26 96 528 54 632 41 764 310 117 0
777 21 9 -23 24 -15 0 721 748 770 526 775 28 109 26 771 83 776 89 49 531 103 22 306 117 0
778 9 -23 24 -15 0 721 748 770 526 775 28 109 777 52 56 82 181 0
778 d 777 776 775 0
779 -21 14 -23 25 0 721 109 52 56 82 181 0
780 22 21 -29 -9 -23 -28 -15 0 721 83 36 119 115 771 89 49 304 0
781 -23 24 -15 0 721 770 771 76 748 526 778 36 115 119 755 24 20 109 779 83 70 72 780 96 54 475 0
781 d 778 773 0
782 3 24 -15 0 781 748 770 526 111 771 105 755 28 36 19 730 55 51 114 76 5 67 148 0
783 24 -15 0 721 748 770 526 76 61 771 781 111 105 28 32 755 36 19 114 730 83 782 66 2 399 0
783 d 748 0
784 -23 -22 -14 0 721 108 56 85 0
785 8 -3 -1 -25 12 -22 -19 9 -17 -11 -14 0 25 17 508 0
786 27 -11 -14 -15 0 721 783 74 80 119 40 36 91 93 784 758 743 111 62 3 7 785 22 30 409 0
787 29 23 -27 -15 0 721 783 74 87 111 70 62 7 0
788 -8 9 6 21 3 25 23 12 17 -11 -14 0 22 30 427 0
789 -26 3 23 12 -11 -14 -15 0 786 787 110 59 114 783 80 82 72 51 563 55 34 788 25 17 426 0
790 8 9 5 12 0 25 17 104 45 43 605 0
791 -8 7 -11 -14 0 22 30 97 0
792 3 23 12 -11 -14 -15 0 721 786 787 110 783 74 80 5 789 65 14 10 791 790 34 24 275 0
792 d 789 0
793 -9 1 6 26 25 12 -11 -15 0 721 783 80 34 24 20 277 0
794 8 9 -7 12 0 25 17 98 0
795 23 12 -11 -14 -15 0 786 787 110 59 792 70 68 2 13 9 793 794 22 30 103 46 44 654 0
795 d 792 0
796 -8 9 6 3 18 22 25 12 17 -11 -14 0 22 30 431 0
797 12 -11 -14 -15 0 721 786 114 783 80 795 106 108 784 59 85 87 93 52 70 72 34 796 25 17 422 0
797 d 795 0
798 18 23 26 -16 9 13 8 2 17 4 0 721 53 211 90 0
799 -11 -14 -15 0 721 783 74 80 786 114 797 58 28 32 611 755 3 7 70 83 87 108 798 50 370 95 0
799 d 797 786 0
800 -3 26 25 12 9 16 11 28 0 721 59 117 68 2 281 0
801 -14 -15 0 721 783 74 80 799 117 115 40 36 91 93 19 23 784 28 787 563 110 82 59 800 5 65 232 0
801 d 799 0
802 -22 26 9 12 -15 0 721 83 801 31 545 23 87 730 37 783 550 74 90 50 209 0
803 26 9 12 -15 0 721 801 31 545 23 27 783 74 80 83 87 550 730 59 3 7 37 112 802 95 53 368 0
803 d 802 0
804 -2 -15 0 801 783 62 573 109 0
805 9 12 -15 0 721 804 59 801 31 545 783 74 7 80 23 803 70 119 40 93 759 743 107 0
805 d 803 0
806 12 -15 0 721 801 27 805 36 20 115 0
806 d 805 793 0
807 -8 -15 0 721 783 74 804 7 806 64 801 105 779 83 70 119 40 117 80 26 22 295 0
808 -24 -15 0 721 80 74 801 804 3 7 806 64 109 105 779 83 70 117 119 40 36 91 93 807 17 29 372 0
808 d 80 0
809 -15 0 783 808 0
810 16 8 -11 0 721 809 39 33 114 24 293 0
811 2 19 -28 7 20 27 25 14 0 721 105 528 61 405 78 0
812 -28 27 25 8 -11 -12 14 0 721 809 29 810 119 38 17 98 698 105 109 92 811 58 180 73 0
813 19 28 9 -23 -11 -12 14 0 95 764 54 0
814 27 25 8 -11 -12 14 0 721 105 810 29 119 38 812 813 90 772 0
814 d 812 0
815 -19 28 -27 21 -23 -29 -16 -11 0 721 809 75 79 114 35 83 90 322 49 0
816 28 -27 25 8 -11 14 0 721 809 114 35 24 105 779 83 72 70 109 810 815 95 457 54 0
817 -4 -28 -27 -26 25 0 78 740 61 0
818 25 8 -11 -12 14 0 721 809 105 779 83 814 70 816 817 73 7 58 0
818 d 814 0
819 21 22 -25 0 721 85 55 112 0
820 3 -9 -29 -25 -16 -11 -12 0 809 64 79 94 819 82 60 65 1 264 0
821 -27 -29 -25 8 -11 -12 0 809 721 810 64 79 94 819 82 92 73 60 114 35 24 820 6 68 249 0
822 8 -11 -12 14 0 809 721 810 818 64 79 634 94 819 52 107 821 730 119 0
822 d 818 0
823 16 9 0 809 33 0
823 d 33 34 0
824 9 17 0 809 35 0
824 d 35 36 0
825 16 17 0 809 39 0
825 d 39 40 0
826 4 24 0 809 73 0
826 d 73 74 0
827 4 28 0 809 75 0
827 d 75 76 0
828 28 24 0 809 79 0
828 d 79 0
829 21 26 0 721 83 0
829 d 83 84 0
830 21 29 0 721 85 0
830 d 85 0
831 29 26 0 721 87 0
831 d 87 88 0
832 17 11 0 721 115 0
832 d 115 116 0
833 11 27 0 721 117 0
833 d 117 118 0
834 17 27 0 721 119 0
834 d 119 120 0
835 23 29 20 3 1 7 19 22 27 0 721 123 0
835 d 123 124 0
836 1 7 27 16 20 3 23 28 29 0 721 131 0
836 d 131 132 0
837 29 3 22 10 1 13 23 27 19 0 721 139 0
837 d 139 140 0
838 18 8 11 13 28 7 17 5 22 0 809 141 0
838 d 141 142 0
839 6 22 8 11 13 17 18 1 28 0 809 143 0
839 d 143 144 0
840 7 18 11 28 14 5 17 22 12 0 809 145 0
840 d 145 146 0
841 1 18 11 12 14 17 6 22 28 0 809 147 0
841 d 147 148 0
842 7 5 17 21 11 8 13 23 28 0 809 149 0
842 d 149 150 0
843 6 1 8 11 13 17 21 23 28 0 809 151 0
843 d 151 152 0
844 5 17 7 23 11 14 21 12 28 0 809 153 0
844 d 153 154 0
845 6 1 11 12 14 17 21 23 28 0 809 155 0
845 d 155 156 0
846 1 23 27 29 3 10 13 28 16 0 721 175 0
846 d 175 176 0
847 18 22 14 25 26 0 721 181 0
847 d 181 182 0
848 1 7 20 14 22 3 19 25 27 0 721 183 0
848 d 183 184 0
849 21 29 4 14 18 12 16 19 2 0 809 187 0
849 d 187 188 0
850 18 19 16 4 2 13 8 21 29 0 809 189 0
850 d 189 190 0
851 5 4 16 12 14 20 2 21 29 0 809 195 0
851 d 195 196 0
852 5 29 21 16 4 13 20 8 2 0 809 197 0
852 d 197 198 0
853 1 7 27 14 16 20 25 3 28 0 721 203 0
853 d 203 204 0
854 18 2 4 14 12 16 19 26 0 809 721 205 0
854 d 205 206 0
855 19 26 4 13 2 8 18 16 0 809 721 207 0
855 d 207 208 0
856 18 19 4 2 17 14 12 9 26 0 721 209 0
856 d 209 210 0
857 18 19 4 2 13 8 17 26 9 0 721 211 0
857 d 211 212 0
858 5 2 4 12 14 16 20 26 0 809 721 213 0
858 d 213 214 0
859 5 13 4 2 16 8 20 26 0 809 721 215 0
859 d 215 216 0
860 5 2 4 20 9 14 17 12 26 0 721 217 0
860 d 217 218 0
861 20 5 4 2 26 13 9 17 8 0 721 219 0
861 d 219 220 0
862 5 7 26 10 12 8 22 25 19 0 721 239 0
862 d 239 240 0
863 1 26 22 19 12 6 8 25 10 0 721 241 0
863 d 241 242 0
864 5 19 7 9 12 11 22 25 26 0 721 243 0
864 d 243 244 0
865 1 6 9 11 12 26 19 25 22 0 721 245 0
865 d 245 246 0
866 5 7 24 26 8 2 10 22 19 0 721 247 0
866 d 247 248 0
867 1 6 2 8 10 19 26 24 22 0 721 249 0
867 d 249 250 0
868 5 19 24 7 9 2 11 22 26 0 721 251 0
868 d 251 252 0
869 1 6 24 9 11 2 22 19 26 0 721 253 0
869 d 253 254 0
870 22 19 10 3 1 14 13 25 27 0 721 255 0
870 d 255 256 0
871 5 7 8 26 12 10 25 16 28 0 721 275 0
871 d 275 276 0
872 16 8 10 6 12 26 25 1 28 0 721 277 0
872 d 277 278 0
873 5 7 26 9 12 16 25 11 28 0 721 279 0
873 d 279 280 0
874 1 6 16 11 9 12 25 26 28 0 721 281 0
874 d 281 282 0
875 5 26 7 2 16 8 24 10 28 0 721 283 0
875 d 283 284 0
876 1 16 2 8 6 10 24 26 28 0 721 285 0
876 d 285 286 0
877 5 2 26 7 9 16 24 11 28 0 721 287 0
877 d 287 288 0
878 1 6 2 9 11 16 24 26 28 0 721 289 0
878 d 289 290 0
879 3 1 16 13 10 14 25 27 28 0 721 291 0
879 d 291 292 0
880 27 16 8 10 0 809 721 293 0
880 d 293 294 0
881 16 2 4 27 14 13 10 25 28 0 721 295 0
881 d 295 296 0
882 2 4 19 13 14 10 22 25 27 0 721 301 0
882 d 301 302 0
883 23 28 19 9 11 18 26 27 29 0 809 303 0
883 d 303 304 0
884 18 23 27 8 10 19 26 28 29 0 809 305 0
884 d 305 306 0
885 5 26 9 11 20 23 27 28 29 0 809 307 0
885 d 307 308 0
886 5 26 28 10 20 23 8 27 29 0 809 309 0
886 d 309 310 0
887 6 18 23 11 3 9 19 28 29 0 809 311 0
887 d 311 312 0
888 18 19 10 8 3 6 23 28 29 0 809 313 0
888 d 313 314 0
889 20 5 29 9 11 6 23 28 3 0 809 317 0
889 d 317 318 0
890 6 20 5 8 10 3 23 28 29 0 809 319 0
890 d 319 320 0
891 1 5 20 3 9 13 8 17 26 0 721 337 0
891 d 337 338 0
892 5 1 20 9 12 3 17 14 26 0 721 339 0
892 d 339 340 0
893 5 20 3 1 13 8 16 26 0 809 721 341 0
893 d 341 342 0
894 5 1 3 12 16 14 20 26 0 809 721 343 0
894 d 343 344 0
895 1 18 3 17 19 9 8 13 26 0 721 345 0
895 d 345 346 0
896 3 1 18 12 26 14 9 17 19 0 721 347 0
896 d 347 348 0
897 1 18 13 3 8 19 16 26 0 809 721 349 0
897 d 349 350 0
898 18 26 12 14 3 1 19 16 0 809 721 351 0
898 d 351 352 0
899 28 4 2 14 16 20 25 27 7 0 721 353 0
899 d 353 354 0
900 20 1 16 3 13 5 8 21 29 0 809 359 0
900 d 359 360 0
901 5 1 20 12 16 14 3 21 29 0 809 361 0
901 d 361 362 0
902 18 1 19 13 3 21 16 8 29 0 809 367 0
902 d 367 368 0
903 18 1 12 14 3 16 19 21 29 0 809 369 0
903 d 369 370 0
904 5 18 7 13 27 22 8 28 0 809 721 373 0
904 d 373 374 0
905 6 18 28 1 13 8 27 22 0 809 721 375 0
905 d 375 376 0
906 22 5 28 14 18 12 27 7 0 809 721 377 0
906 d 377 378 0
907 1 18 12 14 6 22 27 28 0 809 721 379 0
907 d 379 380 0
908 5 21 7 13 8 23 27 28 0 809 721 381 0
908 d 381 382 0
909 6 1 21 8 13 23 27 28 0 809 721 383 0
909 d 383 384 0
910 5 23 7 14 21 12 27 28 0 809 721 385 0
910 d 385 386 0
911 6 1 12 14 21 23 27 28 0 809 721 387 0
911 d 387 388 0
912 5 18 24 4 7 13 22 8 27 0 721 389 0
912 d 389 390 0
913 1 18 4 8 22 13 6 24 27 0 721 391 0
913 d 391 392 0
914 5 18 24 12 4 14 22 7 27 0 721 393 0
914 d 393 394 0
915 18 1 4 12 14 6 22 24 27 0 721 395 0
915 d 395 396 0
916 5 7 4 27 13 21 23 24 8 0 721 397 0
916 d 397 398 0
917 6 1 4 8 13 21 23 24 27 0 721 399 0
917 d 399 400 0
918 7 5 4 12 14 21 23 24 27 0 721 401 0
918 d 401 402 0
919 6 1 4 12 21 14 23 24 27 0 721 403 0
919 d 403 404 0
920 20 4 22 14 7 19 2 25 27 0 721 405 0
920 d 405 406 0
921 23 28 4 2 16 13 10 27 29 0 721 409 0
921 d 409 410 0
922 21 26 12 16 13 10 25 23 27 0 809 413 0
922 d 413 414 0
923 22 18 12 25 16 13 10 26 27 0 809 417 0
923 d 417 418 0
924 21 26 24 13 10 16 2 23 27 0 809 421 0
924 d 421 422 0
925 22 18 16 2 27 10 24 13 26 0 809 425 0
925 d 425 426 0
926 3 6 12 10 13 16 21 23 25 0 809 429 0
926 d 429 430 0
927 3 6 12 10 13 16 18 22 25 0 809 433 0
927 d 433 434 0
928 6 16 2 10 3 13 21 23 24 0 809 439 0
928 d 439 440 0
929 6 16 2 10 3 13 18 22 24 0 809 443 0
929 d 443 444 0
930 23 29 4 10 13 19 2 22 27 0 721 445 0
930 d 445 446 0
931 26 18 11 19 14 9 25 27 28 0 809 447 0
931 d 447 448 0
932 26 18 25 14 8 10 19 27 28 0 809 449 0
932 d 449 450 0
933 5 28 9 14 11 25 26 27 20 0 809 451 0
933 d 451 452 0
934 5 26 20 14 10 8 25 27 28 0 809 453 0
934 d 453 454 0
935 6 28 3 11 14 9 18 19 25 0 809 455 0
935 d 455 456 0
936 18 19 3 8 14 6 10 28 25 0 809 457 0
936 d 457 458 0
937 5 20 28 9 11 14 6 25 3 0 809 461 0
937 d 461 462 0
938 20 5 28 8 10 14 3 25 6 0 809 463 0
938 d 463 464 0
939 7 2 4 23 20 16 27 28 29 0 721 481 0
939 d 481 482 0
940 26 20 25 23 12 16 21 7 27 0 809 485 0
940 d 485 486 0
941 7 26 16 22 12 18 20 25 27 0 809 489 0
941 d 489 490 0
942 26 7 2 24 21 23 20 16 27 0 809 493 0
942 d 493 494 0
943 18 26 2 24 16 22 20 7 27 0 809 497 0
943 d 497 498 0
944 7 3 23 6 20 12 21 16 25 0 809 501 0
944 d 501 502 0
945 22 7 25 6 3 12 16 18 20 0 809 505 0
945 d 505 506 0
946 6 7 2 3 16 20 21 23 24 0 809 511 0
946 d 511 512 0
947 6 7 2 3 16 18 20 22 24 0 809 515 0
947 d 515 516 0
948 23 29 4 20 2 7 19 22 27 0 721 517 0
948 d 517 518 0
949 3 1 12 25 28 0 809 521 0
949 d 521 522 526 529 530 532 539 546 548 555 558 561 562 564 566 567 568 574 575 576 0
950 -24 28 -13 -23 -29 -9 27 26 -11 0 809 582 0
950 d 582 0
951 -22 28 9 11 25 -23 14 27 26 0 809 585 0
951 d 585 586 0
952 28 25 12 0 809 589 0
952 d 589 0
953 1 23 2 8 13 11 -27 17 28 21 0 809 590 0
953 d 590 593 0
954 -20 12 23 -18 14 17 21 11 28 0 809 594 0
954 d 594 595 0
955 18 28 -8 19 -29 21 10 0 809 596 0
955 d 596 600 603 607 0
956 -3 12 24 0 809 616 0
956 d 616 617 624 627 629 630 0
957 28 -14 -19 -9 12 18 0 809 636 0
957 d 636 638 639 640 641 643 647 648 652 673 682 685 0
958 -20 11 12 28 22 18 17 14 0 809 689 0
958 d 689 691 704 706 0
959 28 -9 -17 0 809 710 0
959 d 710 714 716 717 726 728 734 742 743 746 749 754 757 758 770 771 780 781 782 787 808 597 679 703 712 720 783 801 804 806 807 0
960 -25 -11 -12 14 0 822 20 823 824 64 828 634 94 819 730 52 107 0
961 24 -28 -23 -29 25 -16 -17 -20 -7 -11 0 826 61 238 0
962 22 -11 -12 14 0 822 20 824 960 109 730 105 114 823 26 22 103 97 49 48 95 961 78 58 882 0
963 -11 -12 14 0 822 22 20 824 823 960 109 105 730 962 94 90 54 955 0
963 d 822 0
964 -22 -16 25 11 14 0 832 38 833 105 779 829 72 70 94 90 54 935 0
965 28 -18 22 -10 -8 -26 -23 -29 -27 0 828 827 95 324 0
966 4 3 -12 0 826 7 58 0
967 25 -12 14 0 963 832 833 109 105 779 829 70 966 817 959 823 19 23 964 49 965 0
968 -10 -23 -26 -12 14 0 967 64 828 759 819 52 634 823 963 832 833 18 412 29 0
969 -23 -26 -12 14 0 963 833 72 70 967 64 828 60 759 819 52 634 968 21 929 26 0
969 d 968 0
970 10 21 23 6 3 24 2 11 -12 0 828 55 94 21 928 26 0
971 -26 -12 14 0 967 64 828 60 963 832 833 70 72 969 107 82 51 55 94 823 970 18 416 29 0
971 d 969 0
972 8 -10 -12 14 0 967 971 831 112 829 64 828 963 832 19 29 38 104 98 725 53 89 42 15 11 136 0
973 -6 -8 -10 -29 -21 -25 -27 -12 0 18 823 64 828 60 68 260 1 0
974 -10 -12 14 0 971 831 829 967 64 828 826 60 963 833 972 18 823 92 94 973 65 869 6 0
974 d 972 0
975 -12 14 0 963 832 967 64 828 971 829 831 112 974 21 23 26 38 587 737 96 50 632 0
975 d 963 0
976 24 -22 -29 11 -21 14 0 50 832 975 31 545 23 959 96 41 725 27 826 57 202 0
977 -22 26 11 -21 14 0 831 832 975 31 545 23 38 959 96 50 976 78 550 854 0
978 -24 5 20 26 11 14 0 831 832 975 31 545 23 38 959 78 550 858 0
979 26 -25 11 -21 14 0 832 975 31 545 23 38 27 831 112 977 53 89 737 42 978 826 57 194 0
980 24 -26 -27 12 0 826 57 740 0
981 -25 11 -21 14 0 832 975 31 545 23 959 833 979 70 980 78 62 7 0
981 d 979 0
982 25 -21 14 0 105 779 0
983 3 -21 14 0 982 975 27 981 20 823 824 730 107 52 634 828 62 827 114 31 67 1 168 0
984 -21 14 0 975 27 982 981 20 824 823 114 730 831 107 759 52 634 827 983 6 66 907 0
984 d 983 982 981 977 976 0
985 25 14 0 984 830 975 31 63 59 550 0
985 d 967 964 0
986 -3 -11 14 0 975 27 20 823 984 985 819 94 827 824 114 830 112 829 6 66 911 0
987 -11 14 0 984 830 985 112 51 819 975 27 31 20 824 823 114 94 828 827 550 986 67 1 160 0
987 d 986 0
988 -13 12 14 0 545 984 829 830 987 833 832 23 70 980 959 78 550 7 0
988 d 545 0
989 12 14 0 31 988 0
989 d 31 988 0
990 14 0 975 989 0
991 21 23 25 3 16 7 20 -27 12 0 829 944 72 0
992 23 25 3 11 -13 12 0 990 832 30 19 38 959 21 98 645 833 991 725 53 89 620 0
993 3 4 11 -13 12 0 990 826 30 19 21 832 833 7 62 992 108 830 831 420 0
994 -3 7 -27 12 0 990 70 68 831 13 110 2 59 0
995 11 -13 12 0 990 30 833 832 21 19 98 959 994 993 78 63 980 110 831 0
995 d 993 992 0
996 7 -4 -25 -24 -26 -27 -11 0 990 72 114 824 24 99 15 470 0
997 -25 -24 29 3 -27 -11 -13 0 990 831 72 114 824 24 30 106 62 7 1 78 996 102 12 890 0
998 29 3 -27 -13 12 0 990 30 995 810 830 831 980 997 952 111 634 52 0
999 3 -27 -13 12 0 990 995 114 824 30 810 998 110 108 63 59 952 94 78 55 5 82 272 65 0
999 d 998 0
1000 -27 -13 12 0 990 30 995 810 114 824 999 956 70 68 994 829 831 110 59 952 2 270 9 0
1000 d 999 0
1001 -29 -13 12 0 990 1000 834 30 995 810 110 108 730 952 55 94 0
1002 -3 -13 12 0 990 1001 831 30 995 810 1000 834 38 794 17 66 13 2 6 59 827 520 0
1003 -25 -4 -2 -17 -11 -13 0 990 30 810 38 17 62 122 828 0
1004 -13 12 0 990 30 995 810 1000 834 38 790 1002 67 10 1 5 1003 63 952 78 0
1004 d 1002 1001 1000 995 0
1005 3 4 27 -7 0 67 5 14 0
1006 26 -17 -11 0 829 831 730 0
1007 -29 -11 12 0 990 1004 25 20 823 824 110 108 730 952 55 94 0
1008 -28 6 -24 -3 29 27 -16 10 13 0 830 103 92 634 94 78 44 52 9 930 2 0
1009 -5 -20 10 9 0 990 46 44 654 0
1010 6 -11 12 0 1004 25 20 22 103 1009 1007 824 114 823 67 9 956 6 1008 827 0
1011 28 -2 12 0 828 952 62 0
1012 -11 12 0 990 1004 25 791 20 22 824 823 114 1006 1007 830 1010 66 14 1 1011 92 634 94 52 837 0
1012 d 1010 1007 0
1013 3 -28 1 12 0 1012 833 1004 1 5 740 78 831 554 0
1014 10 -5 13 0 103 46 44 632 0
1015 -28 1 12 0 1012 833 1004 25 1013 956 70 68 994 78 829 831 9 3 1014 18 266 823 0
1015 d 1013 0
1016 1 12 0 990 1012 833 1015 952 1011 110 1 831 70 0
1016 d 1015 0
1017 -5 28 12 0 990 952 110 831 1012 832 959 23 827 828 1016 833 1004 25 12 472 101 0
1018 28 12 0 990 1016 1012 832 833 827 952 959 6 110 106 23 831 72 1017 15 889 100 0
1018 d 1017 1011 0
1019 5 19 -10 6 0 15 45 100 0
1020 -10 6 12 0 1018 1016 1004 25 18 823 92 634 1019 12 44 101 0
1021 19 -26 12 0 990 1012 832 833 72 1020 23 38 1004 103 644 70 1018 980 78 7 89 632 496 0
1022 -26 12 0 1018 1012 832 833 1004 70 72 980 78 7 62 1020 23 103 38 1021 96 48 927 0
1022 d 1021 0
1023 13 12 0 990 25 1012 1016 1018 1022 829 831 554 110 59 2 65 14 644 18 268 823 0
1023 d 25 0
1024 12 0 1004 1023 0
1025 -8 0 1024 990 28 0
1026 -13 0 1024 990 32 0
1027 7 -24 16 26 0 1025 1026 990 1024 810 833 825 823 959 78 966 68 58 3 831 829 101 15 358 0
1028 -24 16 -10 26 0 1024 1026 1025 825 823 959 58 78 3 1027 100 12 859 0
1029 -7 16 -10 26 0 990 1024 1028 826 831 110 61 8 65 823 825 829 663 100 16 192 45 0
1030 16 -10 26 0 1026 990 1024 831 110 829 825 823 1028 826 61 4 1029 101 11 200 0
1030 d 1029 1028 0
1031 -9 28 0 990 1024 959 611 832 0
1031 d 959 0
1032 9 26 0 1025 824 19 1006 0
1033 26 0 1024 990 1025 1032 611 832 21 38 1030 0
1034 -25 0 990 1024 110 106 615 0
1035 -9 0 990 1034 1033 1024 1031 611 833 70 817 966 0
1036 17 0 1035 824 0
1037 16 0 1035 823 0
1038 11 0 1035 1025 19 0
1039 10 0 1035 1025 17 0
1040 -27 0 1036 1038 114 0
1041 7 -28 0 1037 1026 1033 1024 1034 634 101 44 15 11 66 966 78 4 61 0
1042 2 -28 0 1039 1037 1034 1041 92 100 45 12 61 3 78 0
1043 -28 0 1037 1039 1040 1024 92 1041 100 45 16 67 1042 58 8 826 0
1044 24 0 1043 828 0
1045 4 0 1043 827 0
1046 -2 0 1044 1024 58 0
1047 -18 1 0 1046 1033 1024 1036 990 1038 1045 1044 1043 1 66 9 13 42 162 95 0
1048 6 1 0 1037 1026 1025 1040 1043 1039 13 100 1047 47 905 90 0
1048 d 13 0
1049 1 0 1046 1033 1 66 1048 0
1050 -3 0 1049 1045 6 0
1051 6 0 1050 1040 67 0
1052 -5 0 1051 1049 10 0
1053 -7 0 1051 1049 14 0
1054 20 0 1053 1026 101 0
1055 18 0 1043 1025 1040 1026 1053 1052 1037 904 41 90 0
1056 -19 0 1055 1054 48 0
1057 -22 0 1055 1045 1038 1044 990 1036 1049 1024 1051 164 0
1058 0 1056 1057 1043 95 0
"

#print axioms no_two_regular_cut_connected_clauses

def cnfProp (p : Fin 30 → Prop) : Prop :=
  ((((((((((p 0 ∨ p 1 ∨ p 2) ∧
  (¬ p 0 ∨ ¬ p 1 ∨ ¬ p 2)) ∧
  ((p 0 ∨ p 1 ∨ p 3) ∧
  (¬ p 0 ∨ ¬ p 1 ∨ ¬ p 3))) ∧
  (((p 0 ∨ p 2 ∨ p 3) ∧
  (¬ p 0 ∨ ¬ p 2 ∨ ¬ p 3)) ∧
  ((p 1 ∨ p 2 ∨ p 3) ∧
  (¬ p 1 ∨ ¬ p 2 ∨ ¬ p 3)))) ∧
  ((((p 0 ∨ p 4 ∨ p 5) ∧
  (¬ p 0 ∨ ¬ p 4 ∨ ¬ p 5)) ∧
  ((p 0 ∨ p 4 ∨ p 6) ∧
  (¬ p 0 ∨ ¬ p 4 ∨ ¬ p 6))) ∧
  (((p 0 ∨ p 5 ∨ p 6) ∧
  (¬ p 0 ∨ ¬ p 5 ∨ ¬ p 6)) ∧
  ((p 4 ∨ p 5 ∨ p 6) ∧
  (¬ p 4 ∨ ¬ p 5 ∨ ¬ p 6))))) ∧
  (((((p 7 ∨ p 8 ∨ p 9) ∧
  (¬ p 7 ∨ ¬ p 8 ∨ ¬ p 9)) ∧
  ((p 7 ∨ p 8 ∨ p 10) ∧
  (¬ p 7 ∨ ¬ p 8 ∨ ¬ p 10))) ∧
  (((p 7 ∨ p 9 ∨ p 10) ∧
  (¬ p 7 ∨ ¬ p 9 ∨ ¬ p 10)) ∧
  ((p 8 ∨ p 9 ∨ p 10) ∧
  (¬ p 8 ∨ ¬ p 9 ∨ ¬ p 10)))) ∧
  ((((p 7 ∨ p 11 ∨ p 12) ∧
  (¬ p 7 ∨ ¬ p 11 ∨ ¬ p 12)) ∧
  ((p 7 ∨ p 11 ∨ p 13) ∧
  (¬ p 7 ∨ ¬ p 11 ∨ ¬ p 13))) ∧
  (((p 7 ∨ p 12 ∨ p 13) ∧
  (¬ p 7 ∨ ¬ p 12 ∨ ¬ p 13)) ∧
  ((p 11 ∨ p 12 ∨ p 13) ∧
  (¬ p 11 ∨ ¬ p 12 ∨ ¬ p 13)))))) ∧
  ((((((p 8 ∨ p 14 ∨ p 15) ∧
  (¬ p 8 ∨ ¬ p 14 ∨ ¬ p 15)) ∧
  ((p 8 ∨ p 14 ∨ p 16) ∧
  (¬ p 8 ∨ ¬ p 14 ∨ ¬ p 16))) ∧
  (((p 8 ∨ p 15 ∨ p 16) ∧
  (¬ p 8 ∨ ¬ p 15 ∨ ¬ p 16)) ∧
  ((p 14 ∨ p 15 ∨ p 16) ∧
  (¬ p 14 ∨ ¬ p 15 ∨ ¬ p 16)))) ∧
  ((((p 4 ∨ p 17 ∨ p 18) ∧
  (¬ p 4 ∨ ¬ p 17 ∨ ¬ p 18)) ∧
  ((p 4 ∨ p 17 ∨ p 19) ∧
  (¬ p 4 ∨ ¬ p 17 ∨ ¬ p 19))) ∧
  (((p 4 ∨ p 18 ∨ p 19) ∧
  (¬ p 4 ∨ ¬ p 18 ∨ ¬ p 19)) ∧
  ((p 17 ∨ p 18 ∨ p 19) ∧
  (¬ p 17 ∨ ¬ p 18 ∨ ¬ p 19))))) ∧
  (((((p 17 ∨ p 20 ∨ p 21) ∧
  (¬ p 17 ∨ ¬ p 20 ∨ ¬ p 21)) ∧
  ((p 17 ∨ p 20 ∨ p 22) ∧
  (¬ p 17 ∨ ¬ p 20 ∨ ¬ p 22))) ∧
  (((p 17 ∨ p 21 ∨ p 22) ∧
  (¬ p 17 ∨ ¬ p 21 ∨ ¬ p 22)) ∧
  ((p 20 ∨ p 21 ∨ p 22) ∧
  (¬ p 20 ∨ ¬ p 21 ∨ ¬ p 22)))) ∧
  ((((p 1 ∨ p 11 ∨ p 23) ∧
  (¬ p 1 ∨ ¬ p 11 ∨ ¬ p 23)) ∧
  ((p 1 ∨ p 11 ∨ p 24) ∧
  (¬ p 1 ∨ ¬ p 11 ∨ ¬ p 24))) ∧
  (((p 1 ∨ p 23 ∨ p 24) ∧
  (¬ p 1 ∨ ¬ p 23 ∨ ¬ p 24)) ∧
  ((p 11 ∨ p 23 ∨ p 24) ∧
  ((¬ p 11 ∨ ¬ p 23 ∨ ¬ p 24) ∧
  (p 2 ∨ p 5 ∨ p 25)))))))) ∧
  (((((((¬ p 2 ∨ ¬ p 5 ∨ ¬ p 25) ∧
  (p 2 ∨ p 5 ∨ p 26)) ∧
  ((¬ p 2 ∨ ¬ p 5 ∨ ¬ p 26) ∧
  (p 2 ∨ p 25 ∨ p 26))) ∧
  (((¬ p 2 ∨ ¬ p 25 ∨ ¬ p 26) ∧
  (p 5 ∨ p 25 ∨ p 26)) ∧
  ((¬ p 5 ∨ ¬ p 25 ∨ ¬ p 26) ∧
  (p 3 ∨ p 14 ∨ p 23)))) ∧
  ((((¬ p 3 ∨ ¬ p 14 ∨ ¬ p 23) ∧
  (p 3 ∨ p 14 ∨ p 27)) ∧
  ((¬ p 3 ∨ ¬ p 14 ∨ ¬ p 27) ∧
  (p 3 ∨ p 23 ∨ p 27))) ∧
  (((¬ p 3 ∨ ¬ p 23 ∨ ¬ p 27) ∧
  (p 14 ∨ p 23 ∨ p 27)) ∧
  ((¬ p 14 ∨ ¬ p 23 ∨ ¬ p 27) ∧
  (p 20 ∨ p 25 ∨ p 28))))) ∧
  (((((¬ p 20 ∨ ¬ p 25 ∨ ¬ p 28) ∧
  (p 20 ∨ p 25 ∨ p 29)) ∧
  ((¬ p 20 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 20 ∨ p 28 ∨ p 29))) ∧
  (((¬ p 20 ∨ ¬ p 28 ∨ ¬ p 29) ∧
  (p 25 ∨ p 28 ∨ p 29)) ∧
  ((¬ p 25 ∨ ¬ p 28 ∨ ¬ p 29) ∧
  (p 15 ∨ p 18 ∨ p 21)))) ∧
  ((((¬ p 15 ∨ ¬ p 18 ∨ ¬ p 21) ∧
  (p 15 ∨ p 18 ∨ p 27)) ∧
  ((¬ p 15 ∨ ¬ p 18 ∨ ¬ p 27) ∧
  (p 15 ∨ p 21 ∨ p 27))) ∧
  (((¬ p 15 ∨ ¬ p 21 ∨ ¬ p 27) ∧
  (p 18 ∨ p 21 ∨ p 27)) ∧
  ((¬ p 18 ∨ ¬ p 21 ∨ ¬ p 27) ∧
  ((p 6 ∨ p 9 ∨ p 12) ∧
  (¬ p 6 ∨ ¬ p 9 ∨ ¬ p 12))))))) ∧
  ((((((p 6 ∨ p 9 ∨ p 19) ∧
  (¬ p 6 ∨ ¬ p 9 ∨ ¬ p 19)) ∧
  ((p 6 ∨ p 12 ∨ p 19) ∧
  (¬ p 6 ∨ ¬ p 12 ∨ ¬ p 19))) ∧
  (((p 9 ∨ p 12 ∨ p 19) ∧
  (¬ p 9 ∨ ¬ p 12 ∨ ¬ p 19)) ∧
  ((p 13 ∨ p 22 ∨ p 24) ∧
  (¬ p 13 ∨ ¬ p 22 ∨ ¬ p 24)))) ∧
  ((((p 13 ∨ p 22 ∨ p 28) ∧
  (¬ p 13 ∨ ¬ p 22 ∨ ¬ p 28)) ∧
  ((p 13 ∨ p 24 ∨ p 28) ∧
  (¬ p 13 ∨ ¬ p 24 ∨ ¬ p 28))) ∧
  (((p 22 ∨ p 24 ∨ p 28) ∧
  (¬ p 22 ∨ ¬ p 24 ∨ ¬ p 28)) ∧
  ((p 10 ∨ p 16 ∨ p 26) ∧
  (¬ p 10 ∨ ¬ p 16 ∨ ¬ p 26))))) ∧
  (((((p 10 ∨ p 16 ∨ p 29) ∧
  (¬ p 10 ∨ ¬ p 16 ∨ ¬ p 29)) ∧
  ((p 10 ∨ p 26 ∨ p 29) ∧
  (¬ p 10 ∨ ¬ p 26 ∨ ¬ p 29))) ∧
  (((p 16 ∨ p 26 ∨ p 29) ∧
  (¬ p 16 ∨ ¬ p 26 ∨ ¬ p 29)) ∧
  ((p 1 ∨ p 3 ∨ p 9 ∨ p 10 ∨ p 12 ∨ p 13 ∨ p 15 ∨ p 16 ∨ p 24 ∨ p 27) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 9 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 13 ∨ ¬ p 15 ∨ ¬ p 16 ∨ ¬ p 24 ∨ ¬ p 27)))) ∧
  ((((p 0 ∨ p 2 ∨ p 6 ∨ p 18 ∨ p 19 ∨ p 21 ∨ p 22 ∨ p 26 ∨ p 28 ∨ p 29) ∧
  (¬ p 0 ∨ ¬ p 2 ∨ ¬ p 6 ∨ ¬ p 18 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 22 ∨ ¬ p 26 ∨ ¬ p 28 ∨ ¬ p 29)) ∧
  ((p 4 ∨ p 15 ∨ p 19 ∨ p 20 ∨ p 22 ∨ p 27) ∧
  (¬ p 4 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 27))) ∧
  (((p 3 ∨ p 8 ∨ p 16 ∨ p 18 ∨ p 21 ∨ p 23) ∧
  (¬ p 3 ∨ ¬ p 8 ∨ ¬ p 16 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 23)) ∧
  ((p 1 ∨ p 3 ∨ p 9 ∨ p 10 ∨ p 12 ∨ p 13 ∨ p 16 ∨ p 18 ∨ p 21 ∨ p 24) ∧
  ((¬ p 1 ∨ ¬ p 3 ∨ ¬ p 9 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 24) ∧
  (p 0 ∨ p 2 ∨ p 6 ∨ p 15 ∨ p 19 ∨ p 22 ∨ p 26 ∨ p 27 ∨ p 28 ∨ p 29))))))))) ∧
  ((((((((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 6 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 22 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 28 ∨ ¬ p 29) ∧
  (p 6 ∨ p 8 ∨ p 10 ∨ p 11 ∨ p 13 ∨ p 19)) ∧
  ((¬ p 6 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 19) ∧
  (p 0 ∨ p 5 ∨ p 9 ∨ p 12 ∨ p 17 ∨ p 18))) ∧
  (((¬ p 0 ∨ ¬ p 5 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 17 ∨ ¬ p 18) ∧
  (p 1 ∨ p 3 ∨ p 6 ∨ p 10 ∨ p 13 ∨ p 15 ∨ p 16 ∨ p 19 ∨ p 24 ∨ p 27)) ∧
  ((¬ p 1 ∨ ¬ p 3 ∨ ¬ p 6 ∨ ¬ p 10 ∨ ¬ p 13 ∨ ¬ p 15 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 24 ∨ ¬ p 27) ∧
  (p 0 ∨ p 2 ∨ p 9 ∨ p 12 ∨ p 18 ∨ p 21 ∨ p 22 ∨ p 26 ∨ p 28 ∨ p 29)))) ∧
  ((((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 22 ∨ ¬ p 26 ∨ ¬ p 28 ∨ ¬ p 29) ∧
  (p 4 ∨ p 6 ∨ p 7 ∨ p 10 ∨ p 12 ∨ p 14 ∨ p 16 ∨ p 17 ∨ p 21 ∨ p 27)) ∧
  ((¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 27) ∧
  (p 0 ∨ p 5 ∨ p 7 ∨ p 10 ∨ p 12 ∨ p 14 ∨ p 16 ∨ p 17 ∨ p 21 ∨ p 27))) ∧
  (((¬ p 0 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 27) ∧
  (p 4 ∨ p 6 ∨ p 10 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 16 ∨ p 17 ∨ p 21 ∨ p 27)) ∧
  ((¬ p 4 ∨ ¬ p 6 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 27) ∧
  (p 0 ∨ p 5 ∨ p 10 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 16 ∨ p 17 ∨ p 21 ∨ p 27))))) ∧
  (((((¬ p 0 ∨ ¬ p 5 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 27) ∧
  (p 4 ∨ p 6 ∨ p 7 ∨ p 10 ∨ p 12 ∨ p 14 ∨ p 16 ∨ p 20 ∨ p 22 ∨ p 27)) ∧
  ((¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 16 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 27) ∧
  (p 0 ∨ p 5 ∨ p 7 ∨ p 10 ∨ p 12 ∨ p 14 ∨ p 16 ∨ p 20 ∨ p 22 ∨ p 27))) ∧
  (((¬ p 0 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 16 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 27) ∧
  (p 4 ∨ p 6 ∨ p 10 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 16 ∨ p 20 ∨ p 22 ∨ p 27)) ∧
  ((¬ p 4 ∨ ¬ p 6 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 16 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 27) ∧
  (p 0 ∨ p 5 ∨ p 10 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 16 ∨ p 20 ∨ p 22 ∨ p 27)))) ∧
  ((((¬ p 0 ∨ ¬ p 5 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 16 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 27) ∧
  (p 3 ∨ p 4 ∨ p 6 ∨ p 7 ∨ p 10 ∨ p 12 ∨ p 16 ∨ p 17 ∨ p 21 ∨ p 23)) ∧
  ((¬ p 3 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 23) ∧
  (p 0 ∨ p 3 ∨ p 5 ∨ p 7 ∨ p 10 ∨ p 12 ∨ p 16 ∨ p 17 ∨ p 21 ∨ p 23))) ∧
  (((¬ p 0 ∨ ¬ p 3 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 23) ∧
  (p 3 ∨ p 4 ∨ p 6 ∨ p 10 ∨ p 11 ∨ p 13 ∨ p 16 ∨ p 17 ∨ p 21 ∨ p 23)) ∧
  ((¬ p 3 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 23) ∧
  (p 0 ∨ p 3 ∨ p 5 ∨ p 10 ∨ p 11 ∨ p 13 ∨ p 16 ∨ p 17 ∨ p 21 ∨ p 23)))))) ∧
  ((((((¬ p 0 ∨ ¬ p 3 ∨ ¬ p 5 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 23) ∧
  (p 3 ∨ p 4 ∨ p 6 ∨ p 7 ∨ p 10 ∨ p 12 ∨ p 16 ∨ p 20 ∨ p 22 ∨ p 23)) ∧
  ((¬ p 3 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23) ∧
  (p 0 ∨ p 3 ∨ p 5 ∨ p 7 ∨ p 10 ∨ p 12 ∨ p 16 ∨ p 20 ∨ p 22 ∨ p 23))) ∧
  (((¬ p 0 ∨ ¬ p 3 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23) ∧
  (p 3 ∨ p 4 ∨ p 6 ∨ p 10 ∨ p 11 ∨ p 13 ∨ p 16 ∨ p 20 ∨ p 22 ∨ p 23)) ∧
  ((¬ p 3 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23) ∧
  (p 0 ∨ p 3 ∨ p 5 ∨ p 10 ∨ p 11 ∨ p 13 ∨ p 16 ∨ p 20 ∨ p 22 ∨ p 23)))) ∧
  ((((¬ p 0 ∨ ¬ p 3 ∨ ¬ p 5 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23) ∧
  (p 1 ∨ p 3 ∨ p 6 ∨ p 10 ∨ p 13 ∨ p 16 ∨ p 18 ∨ p 19 ∨ p 21 ∨ p 24)) ∧
  ((¬ p 1 ∨ ¬ p 3 ∨ ¬ p 6 ∨ ¬ p 10 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 18 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 24) ∧
  (p 0 ∨ p 2 ∨ p 9 ∨ p 12 ∨ p 15 ∨ p 22 ∨ p 26 ∨ p 27 ∨ p 28 ∨ p 29))) ∧
  (((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 15 ∨ ¬ p 22 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 28 ∨ ¬ p 29) ∧
  (p 1 ∨ p 7 ∨ p 12 ∨ p 22 ∨ p 23 ∨ p 28)) ∧
  ((¬ p 1 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 28) ∧
  (p 1 ∨ p 3 ∨ p 9 ∨ p 10 ∨ p 12 ∨ p 15 ∨ p 16 ∨ p 22 ∨ p 27 ∨ p 28))))) ∧
  (((((¬ p 1 ∨ ¬ p 3 ∨ ¬ p 9 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 15 ∨ ¬ p 16 ∨ ¬ p 22 ∨ ¬ p 27 ∨ ¬ p 28) ∧
  (p 13 ∨ p 17 ∨ p 21 ∨ p 24 ∨ p 25 ∨ p 29)) ∧
  ((¬ p 13 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 0 ∨ p 2 ∨ p 6 ∨ p 13 ∨ p 18 ∨ p 19 ∨ p 21 ∨ p 24 ∨ p 26 ∨ p 29))) ∧
  (((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 6 ∨ ¬ p 13 ∨ ¬ p 18 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 26 ∨ ¬ p 29) ∧
  (p 1 ∨ p 3 ∨ p 9 ∨ p 10 ∨ p 12 ∨ p 16 ∨ p 18 ∨ p 21 ∨ p 22 ∨ p 28)) ∧
  ((¬ p 1 ∨ ¬ p 3 ∨ ¬ p 9 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 22 ∨ ¬ p 28) ∧
  (p 1 ∨ p 3 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 18 ∨ p 20 ∨ p 28)))) ∧
  ((((¬ p 1 ∨ ¬ p 3 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 28) ∧
  (p 1 ∨ p 3 ∨ p 7 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 18 ∨ p 20 ∨ p 28)) ∧
  ((¬ p 1 ∨ ¬ p 3 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 28) ∧
  (p 1 ∨ p 3 ∨ p 8 ∨ p 11 ∨ p 13 ∨ p 16 ∨ p 17 ∨ p 18 ∨ p 20 ∨ p 28))) ∧
  (((¬ p 1 ∨ ¬ p 3 ∨ ¬ p 8 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 28) ∧
  (p 1 ∨ p 3 ∨ p 7 ∨ p 8 ∨ p 12 ∨ p 16 ∨ p 17 ∨ p 18 ∨ p 20 ∨ p 28)) ∧
  ((¬ p 1 ∨ ¬ p 3 ∨ ¬ p 7 ∨ ¬ p 8 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 28) ∧
  ((p 1 ∨ p 3 ∨ p 4 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 15 ∨ p 19 ∨ p 20 ∨ p 28) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 4 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 28)))))))) ∧
  (((((((p 1 ∨ p 3 ∨ p 4 ∨ p 7 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 19 ∨ p 20 ∨ p 28) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 4 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 28)) ∧
  ((p 1 ∨ p 3 ∨ p 4 ∨ p 8 ∨ p 11 ∨ p 13 ∨ p 16 ∨ p 19 ∨ p 20 ∨ p 28) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 4 ∨ ¬ p 8 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 28))) ∧
  (((p 1 ∨ p 3 ∨ p 4 ∨ p 7 ∨ p 8 ∨ p 12 ∨ p 16 ∨ p 19 ∨ p 20 ∨ p 28) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 4 ∨ ¬ p 7 ∨ ¬ p 8 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 28)) ∧
  ((p 0 ∨ p 2 ∨ p 6 ∨ p 13 ∨ p 15 ∨ p 19 ∨ p 24 ∨ p 26 ∨ p 27 ∨ p 29) ∧
  (¬ p 0 ∨ ¬ p 2 ∨ ¬ p 6 ∨ ¬ p 13 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 24 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 29)))) ∧
  ((((p 1 ∨ p 3 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 18 ∨ p 25 ∨ p 29) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 25 ∨ ¬ p 29)) ∧
  ((p 1 ∨ p 3 ∨ p 7 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 18 ∨ p 25 ∨ p 29) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 25 ∨ ¬ p 29))) ∧
  (((p 1 ∨ p 3 ∨ p 8 ∨ p 11 ∨ p 13 ∨ p 16 ∨ p 17 ∨ p 18 ∨ p 25 ∨ p 29) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 8 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 25 ∨ ¬ p 29)) ∧
  ((p 1 ∨ p 3 ∨ p 7 ∨ p 8 ∨ p 12 ∨ p 16 ∨ p 17 ∨ p 18 ∨ p 25 ∨ p 29) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 7 ∨ ¬ p 8 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 25 ∨ ¬ p 29))))) ∧
  (((((p 1 ∨ p 3 ∨ p 4 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 15 ∨ p 19 ∨ p 25 ∨ p 29) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 4 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 25 ∨ ¬ p 29)) ∧
  ((p 1 ∨ p 3 ∨ p 4 ∨ p 7 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 19 ∨ p 25 ∨ p 29) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 4 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 25 ∨ ¬ p 29))) ∧
  (((p 1 ∨ p 3 ∨ p 4 ∨ p 8 ∨ p 11 ∨ p 13 ∨ p 16 ∨ p 19 ∨ p 25 ∨ p 29) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 4 ∨ ¬ p 8 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 25 ∨ ¬ p 29)) ∧
  ((p 1 ∨ p 3 ∨ p 4 ∨ p 7 ∨ p 8 ∨ p 12 ∨ p 16 ∨ p 19 ∨ p 25 ∨ p 29) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 4 ∨ ¬ p 7 ∨ ¬ p 8 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 25 ∨ ¬ p 29)))) ∧
  ((((p 4 ∨ p 6 ∨ p 7 ∨ p 9 ∨ p 11 ∨ p 18 ∨ p 20 ∨ p 21 ∨ p 24 ∨ p 28) ∧
  (¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 11 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 28)) ∧
  ((p 0 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 11 ∨ p 18 ∨ p 20 ∨ p 21 ∨ p 24 ∨ p 28) ∧
  (¬ p 0 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 11 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 28))) ∧
  (((p 4 ∨ p 6 ∨ p 8 ∨ p 10 ∨ p 11 ∨ p 18 ∨ p 20 ∨ p 21 ∨ p 24 ∨ p 28) ∧
  (¬ p 4 ∨ ¬ p 6 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 28)) ∧
  ((p 0 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 11 ∨ p 18 ∨ p 20 ∨ p 21 ∨ p 24 ∨ p 28) ∧
  ((¬ p 0 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 28) ∧
  (p 1 ∨ p 4 ∨ p 6 ∨ p 7 ∨ p 9 ∨ p 18 ∨ p 20 ∨ p 21 ∨ p 23 ∨ p 28))))))) ∧
  ((((((¬ p 1 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 28) ∧
  (p 0 ∨ p 1 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 18 ∨ p 20 ∨ p 21 ∨ p 23 ∨ p 28)) ∧
  ((¬ p 0 ∨ ¬ p 1 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 28) ∧
  (p 1 ∨ p 4 ∨ p 6 ∨ p 8 ∨ p 10 ∨ p 18 ∨ p 20 ∨ p 21 ∨ p 23 ∨ p 28))) ∧
  (((¬ p 1 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 28) ∧
  (p 0 ∨ p 1 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 18 ∨ p 20 ∨ p 21 ∨ p 23 ∨ p 28)) ∧
  ((¬ p 0 ∨ ¬ p 1 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 28) ∧
  (p 1 ∨ p 3 ∨ p 6 ∨ p 10 ∨ p 15 ∨ p 16 ∨ p 19 ∨ p 22 ∨ p 27 ∨ p 28)))) ∧
  ((((¬ p 1 ∨ ¬ p 3 ∨ ¬ p 6 ∨ ¬ p 10 ∨ ¬ p 15 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 22 ∨ ¬ p 27 ∨ ¬ p 28) ∧
  (p 4 ∨ p 6 ∨ p 7 ∨ p 9 ∨ p 11 ∨ p 18 ∨ p 21 ∨ p 24 ∨ p 25 ∨ p 29)) ∧
  ((¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 11 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 0 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 11 ∨ p 18 ∨ p 21 ∨ p 24 ∨ p 25 ∨ p 29))) ∧
  (((¬ p 0 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 11 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 4 ∨ p 6 ∨ p 8 ∨ p 10 ∨ p 11 ∨ p 18 ∨ p 21 ∨ p 24 ∨ p 25 ∨ p 29)) ∧
  ((¬ p 4 ∨ ¬ p 6 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 0 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 11 ∨ p 18 ∨ p 21 ∨ p 24 ∨ p 25 ∨ p 29))))) ∧
  (((((¬ p 0 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 1 ∨ p 4 ∨ p 6 ∨ p 7 ∨ p 9 ∨ p 18 ∨ p 21 ∨ p 23 ∨ p 25 ∨ p 29)) ∧
  ((¬ p 1 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 0 ∨ p 1 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 18 ∨ p 21 ∨ p 23 ∨ p 25 ∨ p 29))) ∧
  (((¬ p 0 ∨ ¬ p 1 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 1 ∨ p 4 ∨ p 6 ∨ p 8 ∨ p 10 ∨ p 18 ∨ p 21 ∨ p 23 ∨ p 25 ∨ p 29)) ∧
  ((¬ p 1 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 0 ∨ p 1 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 18 ∨ p 21 ∨ p 23 ∨ p 25 ∨ p 29)))) ∧
  ((((¬ p 0 ∨ ¬ p 1 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 0 ∨ p 2 ∨ p 9 ∨ p 12 ∨ p 13 ∨ p 18 ∨ p 21 ∨ p 24 ∨ p 26 ∨ p 29)) ∧
  ((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 13 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 26 ∨ ¬ p 29) ∧
  (p 4 ∨ p 6 ∨ p 7 ∨ p 9 ∨ p 11 ∨ p 15 ∨ p 20 ∨ p 24 ∨ p 27 ∨ p 28))) ∧
  (((¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 11 ∨ ¬ p 15 ∨ ¬ p 20 ∨ ¬ p 24 ∨ ¬ p 27 ∨ ¬ p 28) ∧
  (p 0 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 11 ∨ p 15 ∨ p 20 ∨ p 24 ∨ p 27 ∨ p 28)) ∧
  ((¬ p 0 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 11 ∨ ¬ p 15 ∨ ¬ p 20 ∨ ¬ p 24 ∨ ¬ p 27 ∨ ¬ p 28) ∧
  ((p 4 ∨ p 6 ∨ p 8 ∨ p 10 ∨ p 11 ∨ p 15 ∨ p 20 ∨ p 24 ∨ p 27 ∨ p 28) ∧
  (¬ p 4 ∨ ¬ p 6 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 15 ∨ ¬ p 20 ∨ ¬ p 24 ∨ ¬ p 27 ∨ ¬ p 28)))))))))) ∧
  (((((((((p 0 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 11 ∨ p 15 ∨ p 20 ∨ p 24 ∨ p 27 ∨ p 28) ∧
  (¬ p 0 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 15 ∨ ¬ p 20 ∨ ¬ p 24 ∨ ¬ p 27 ∨ ¬ p 28)) ∧
  ((p 1 ∨ p 4 ∨ p 6 ∨ p 7 ∨ p 9 ∨ p 15 ∨ p 20 ∨ p 23 ∨ p 27 ∨ p 28) ∧
  (¬ p 1 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 15 ∨ ¬ p 20 ∨ ¬ p 23 ∨ ¬ p 27 ∨ ¬ p 28))) ∧
  (((p 0 ∨ p 1 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 15 ∨ p 20 ∨ p 23 ∨ p 27 ∨ p 28) ∧
  (¬ p 0 ∨ ¬ p 1 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 15 ∨ ¬ p 20 ∨ ¬ p 23 ∨ ¬ p 27 ∨ ¬ p 28)) ∧
  ((p 1 ∨ p 4 ∨ p 6 ∨ p 8 ∨ p 10 ∨ p 15 ∨ p 20 ∨ p 23 ∨ p 27 ∨ p 28) ∧
  (¬ p 1 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 15 ∨ ¬ p 20 ∨ ¬ p 23 ∨ ¬ p 27 ∨ ¬ p 28)))) ∧
  ((((p 0 ∨ p 1 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 15 ∨ p 20 ∨ p 23 ∨ p 27 ∨ p 28) ∧
  (¬ p 0 ∨ ¬ p 1 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 15 ∨ ¬ p 20 ∨ ¬ p 23 ∨ ¬ p 27 ∨ ¬ p 28)) ∧
  ((p 1 ∨ p 3 ∨ p 6 ∨ p 10 ∨ p 16 ∨ p 18 ∨ p 19 ∨ p 21 ∨ p 22 ∨ p 28) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 6 ∨ ¬ p 10 ∨ ¬ p 16 ∨ ¬ p 18 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 22 ∨ ¬ p 28))) ∧
  (((p 4 ∨ p 6 ∨ p 7 ∨ p 9 ∨ p 11 ∨ p 15 ∨ p 24 ∨ p 25 ∨ p 27 ∨ p 29) ∧
  (¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 11 ∨ ¬ p 15 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 27 ∨ ¬ p 29)) ∧
  ((p 0 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 11 ∨ p 15 ∨ p 24 ∨ p 25 ∨ p 27 ∨ p 29) ∧
  (¬ p 0 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 11 ∨ ¬ p 15 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 27 ∨ ¬ p 29))))) ∧
  (((((p 4 ∨ p 6 ∨ p 8 ∨ p 10 ∨ p 11 ∨ p 15 ∨ p 24 ∨ p 25 ∨ p 27 ∨ p 29) ∧
  (¬ p 4 ∨ ¬ p 6 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 15 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 27 ∨ ¬ p 29)) ∧
  ((p 0 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 11 ∨ p 15 ∨ p 24 ∨ p 25 ∨ p 27 ∨ p 29) ∧
  (¬ p 0 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 11 ∨ ¬ p 15 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 27 ∨ ¬ p 29))) ∧
  (((p 1 ∨ p 4 ∨ p 6 ∨ p 7 ∨ p 9 ∨ p 15 ∨ p 23 ∨ p 25 ∨ p 27 ∨ p 29) ∧
  (¬ p 1 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 15 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 27 ∨ ¬ p 29)) ∧
  ((p 0 ∨ p 1 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 15 ∨ p 23 ∨ p 25 ∨ p 27 ∨ p 29) ∧
  (¬ p 0 ∨ ¬ p 1 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 15 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 27 ∨ ¬ p 29)))) ∧
  ((((p 1 ∨ p 4 ∨ p 6 ∨ p 8 ∨ p 10 ∨ p 15 ∨ p 23 ∨ p 25 ∨ p 27 ∨ p 29) ∧
  (¬ p 1 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 15 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 27 ∨ ¬ p 29)) ∧
  ((p 0 ∨ p 1 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 15 ∨ p 23 ∨ p 25 ∨ p 27 ∨ p 29) ∧
  (¬ p 0 ∨ ¬ p 1 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 15 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 27 ∨ ¬ p 29))) ∧
  (((p 0 ∨ p 2 ∨ p 9 ∨ p 12 ∨ p 13 ∨ p 15 ∨ p 24 ∨ p 26 ∨ p 27 ∨ p 29) ∧
  (¬ p 0 ∨ ¬ p 2 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 13 ∨ ¬ p 15 ∨ ¬ p 24 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 29)) ∧
  ((p 7 ∨ p 9 ∨ p 14 ∨ p 15 ∨ p 26 ∨ p 29) ∧
  (¬ p 7 ∨ ¬ p 9 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 26 ∨ ¬ p 29)))))) ∧
  ((((((p 1 ∨ p 3 ∨ p 9 ∨ p 12 ∨ p 13 ∨ p 15 ∨ p 24 ∨ p 26 ∨ p 27 ∨ p 29) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 13 ∨ ¬ p 15 ∨ ¬ p 24 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 29)) ∧
  ((p 2 ∨ p 5 ∨ p 10 ∨ p 16 ∨ p 20 ∨ p 28) ∧
  (¬ p 2 ∨ ¬ p 5 ∨ ¬ p 10 ∨ ¬ p 16 ∨ ¬ p 20 ∨ ¬ p 28))) ∧
  (((p 0 ∨ p 2 ∨ p 6 ∨ p 10 ∨ p 16 ∨ p 18 ∨ p 19 ∨ p 21 ∨ p 22 ∨ p 28) ∧
  (¬ p 0 ∨ ¬ p 2 ∨ ¬ p 6 ∨ ¬ p 10 ∨ ¬ p 16 ∨ ¬ p 18 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 22 ∨ ¬ p 28)) ∧
  ((p 1 ∨ p 3 ∨ p 9 ∨ p 12 ∨ p 13 ∨ p 18 ∨ p 21 ∨ p 24 ∨ p 26 ∨ p 29) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 13 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 26 ∨ ¬ p 29)))) ∧
  ((((p 8 ∨ p 10 ∨ p 14 ∨ p 17 ∨ p 18 ∨ p 22 ∨ p 25 ∨ p 26 ∨ p 27 ∨ p 28) ∧
  (¬ p 8 ∨ ¬ p 10 ∨ ¬ p 14 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 22 ∨ ¬ p 25 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 28)) ∧
  ((p 7 ∨ p 9 ∨ p 14 ∨ p 17 ∨ p 18 ∨ p 22 ∨ p 25 ∨ p 26 ∨ p 27 ∨ p 28) ∧
  (¬ p 7 ∨ ¬ p 9 ∨ ¬ p 14 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 22 ∨ ¬ p 25 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 28))) ∧
  (((p 4 ∨ p 8 ∨ p 10 ∨ p 14 ∨ p 19 ∨ p 22 ∨ p 25 ∨ p 26 ∨ p 27 ∨ p 28) ∧
  (¬ p 4 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 14 ∨ ¬ p 19 ∨ ¬ p 22 ∨ ¬ p 25 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 28)) ∧
  ((p 4 ∨ p 7 ∨ p 9 ∨ p 14 ∨ p 19 ∨ p 22 ∨ p 25 ∨ p 26 ∨ p 27 ∨ p 28) ∧
  (¬ p 4 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 14 ∨ ¬ p 19 ∨ ¬ p 22 ∨ ¬ p 25 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 28))))) ∧
  (((((p 2 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 14 ∨ p 17 ∨ p 18 ∨ p 22 ∨ p 27 ∨ p 28) ∧
  (¬ p 2 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 14 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 22 ∨ ¬ p 27 ∨ ¬ p 28)) ∧
  ((p 2 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 14 ∨ p 17 ∨ p 18 ∨ p 22 ∨ p 27 ∨ p 28) ∧
  (¬ p 2 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 14 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 22 ∨ ¬ p 27 ∨ ¬ p 28))) ∧
  (((p 0 ∨ p 2 ∨ p 6 ∨ p 10 ∨ p 15 ∨ p 16 ∨ p 19 ∨ p 22 ∨ p 27 ∨ p 28) ∧
  (¬ p 0 ∨ ¬ p 2 ∨ ¬ p 6 ∨ ¬ p 10 ∨ ¬ p 15 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 22 ∨ ¬ p 27 ∨ ¬ p 28)) ∧
  ((p 2 ∨ p 4 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 14 ∨ p 19 ∨ p 22 ∨ p 27 ∨ p 28) ∧
  (¬ p 2 ∨ ¬ p 4 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 14 ∨ ¬ p 19 ∨ ¬ p 22 ∨ ¬ p 27 ∨ ¬ p 28)))) ∧
  ((((p 2 ∨ p 4 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 14 ∨ p 19 ∨ p 22 ∨ p 27 ∨ p 28) ∧
  (¬ p 2 ∨ ¬ p 4 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 14 ∨ ¬ p 19 ∨ ¬ p 22 ∨ ¬ p 27 ∨ ¬ p 28)) ∧
  ((p 3 ∨ p 8 ∨ p 10 ∨ p 17 ∨ p 18 ∨ p 22 ∨ p 23 ∨ p 25 ∨ p 26 ∨ p 28) ∧
  (¬ p 3 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 26 ∨ ¬ p 28))) ∧
  (((p 3 ∨ p 7 ∨ p 9 ∨ p 17 ∨ p 18 ∨ p 22 ∨ p 23 ∨ p 25 ∨ p 26 ∨ p 28) ∧
  (¬ p 3 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 26 ∨ ¬ p 28)) ∧
  ((p 3 ∨ p 4 ∨ p 8 ∨ p 10 ∨ p 19 ∨ p 22 ∨ p 23 ∨ p 25 ∨ p 26 ∨ p 28) ∧
  ((¬ p 3 ∨ ¬ p 4 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 19 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 26 ∨ ¬ p 28) ∧
  (p 3 ∨ p 4 ∨ p 7 ∨ p 9 ∨ p 19 ∨ p 22 ∨ p 23 ∨ p 25 ∨ p 26 ∨ p 28)))))))) ∧
  (((((((¬ p 3 ∨ ¬ p 4 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 19 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 26 ∨ ¬ p 28) ∧
  (p 2 ∨ p 3 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 17 ∨ p 18 ∨ p 22 ∨ p 23 ∨ p 28)) ∧
  ((¬ p 2 ∨ ¬ p 3 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 28) ∧
  (p 2 ∨ p 3 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 17 ∨ p 18 ∨ p 22 ∨ p 23 ∨ p 28))) ∧
  (((¬ p 2 ∨ ¬ p 3 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 28) ∧
  (p 2 ∨ p 3 ∨ p 4 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 19 ∨ p 22 ∨ p 23 ∨ p 28)) ∧
  ((¬ p 2 ∨ ¬ p 3 ∨ ¬ p 4 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 19 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 28) ∧
  (p 2 ∨ p 3 ∨ p 4 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 19 ∨ p 22 ∨ p 23 ∨ p 28)))) ∧
  ((((¬ p 2 ∨ ¬ p 3 ∨ ¬ p 4 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 19 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 28) ∧
  (p 0 ∨ p 2 ∨ p 4 ∨ p 7 ∨ p 8 ∨ p 12 ∨ p 16 ∨ p 19 ∨ p 25 ∨ p 29)) ∧
  ((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 4 ∨ ¬ p 7 ∨ ¬ p 8 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 0 ∨ p 2 ∨ p 4 ∨ p 8 ∨ p 11 ∨ p 13 ∨ p 16 ∨ p 19 ∨ p 25 ∨ p 29))) ∧
  (((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 4 ∨ ¬ p 8 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 0 ∨ p 2 ∨ p 4 ∨ p 7 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 19 ∨ p 25 ∨ p 29)) ∧
  ((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 4 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 0 ∨ p 2 ∨ p 4 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 15 ∨ p 19 ∨ p 25 ∨ p 29))))) ∧
  (((((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 4 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 0 ∨ p 2 ∨ p 7 ∨ p 8 ∨ p 12 ∨ p 16 ∨ p 17 ∨ p 18 ∨ p 25 ∨ p 29)) ∧
  ((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 7 ∨ ¬ p 8 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 0 ∨ p 2 ∨ p 8 ∨ p 11 ∨ p 13 ∨ p 16 ∨ p 17 ∨ p 18 ∨ p 25 ∨ p 29))) ∧
  (((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 8 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 0 ∨ p 2 ∨ p 7 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 18 ∨ p 25 ∨ p 29)) ∧
  ((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 0 ∨ p 2 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 18 ∨ p 25 ∨ p 29)))) ∧
  ((((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 25 ∨ ¬ p 29) ∧
  (p 1 ∨ p 3 ∨ p 6 ∨ p 13 ∨ p 15 ∨ p 19 ∨ p 24 ∨ p 26 ∨ p 27 ∨ p 29)) ∧
  ((¬ p 1 ∨ ¬ p 3 ∨ ¬ p 6 ∨ ¬ p 13 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 24 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 29) ∧
  (p 0 ∨ p 2 ∨ p 4 ∨ p 7 ∨ p 8 ∨ p 12 ∨ p 16 ∨ p 19 ∨ p 20 ∨ p 28))) ∧
  (((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 4 ∨ ¬ p 7 ∨ ¬ p 8 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 28) ∧
  (p 0 ∨ p 2 ∨ p 4 ∨ p 8 ∨ p 11 ∨ p 13 ∨ p 16 ∨ p 19 ∨ p 20 ∨ p 28)) ∧
  ((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 4 ∨ ¬ p 8 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 28) ∧
  ((p 0 ∨ p 2 ∨ p 4 ∨ p 7 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 19 ∨ p 20 ∨ p 28) ∧
  (¬ p 0 ∨ ¬ p 2 ∨ ¬ p 4 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 28))))))) ∧
  ((((((p 0 ∨ p 2 ∨ p 4 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 15 ∨ p 19 ∨ p 20 ∨ p 28) ∧
  (¬ p 0 ∨ ¬ p 2 ∨ ¬ p 4 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 28)) ∧
  ((p 0 ∨ p 2 ∨ p 7 ∨ p 8 ∨ p 12 ∨ p 16 ∨ p 17 ∨ p 18 ∨ p 20 ∨ p 28) ∧
  (¬ p 0 ∨ ¬ p 2 ∨ ¬ p 7 ∨ ¬ p 8 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 28))) ∧
  (((p 0 ∨ p 2 ∨ p 8 ∨ p 11 ∨ p 13 ∨ p 16 ∨ p 17 ∨ p 18 ∨ p 20 ∨ p 28) ∧
  (¬ p 0 ∨ ¬ p 2 ∨ ¬ p 8 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 28)) ∧
  ((p 0 ∨ p 2 ∨ p 7 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 18 ∨ p 20 ∨ p 28) ∧
  (¬ p 0 ∨ ¬ p 2 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 28)))) ∧
  ((((p 0 ∨ p 2 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 18 ∨ p 20 ∨ p 28) ∧
  (¬ p 0 ∨ ¬ p 2 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 20 ∨ ¬ p 28)) ∧
  ((p 0 ∨ p 2 ∨ p 9 ∨ p 10 ∨ p 12 ∨ p 16 ∨ p 18 ∨ p 21 ∨ p 22 ∨ p 28) ∧
  (¬ p 0 ∨ ¬ p 2 ∨ ¬ p 9 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 22 ∨ ¬ p 28))) ∧
  (((p 4 ∨ p 6 ∨ p 7 ∨ p 12 ∨ p 14 ∨ p 17 ∨ p 21 ∨ p 26 ∨ p 27 ∨ p 29) ∧
  (¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 29)) ∧
  ((p 0 ∨ p 5 ∨ p 7 ∨ p 12 ∨ p 14 ∨ p 17 ∨ p 21 ∨ p 26 ∨ p 27 ∨ p 29) ∧
  (¬ p 0 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 29))))) ∧
  (((((p 4 ∨ p 6 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 17 ∨ p 21 ∨ p 26 ∨ p 27 ∨ p 29) ∧
  (¬ p 4 ∨ ¬ p 6 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 29)) ∧
  ((p 0 ∨ p 5 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 17 ∨ p 21 ∨ p 26 ∨ p 27 ∨ p 29) ∧
  (¬ p 0 ∨ ¬ p 5 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 29))) ∧
  (((p 4 ∨ p 6 ∨ p 7 ∨ p 12 ∨ p 14 ∨ p 20 ∨ p 22 ∨ p 26 ∨ p 27 ∨ p 29) ∧
  (¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 29)) ∧
  ((p 0 ∨ p 5 ∨ p 7 ∨ p 12 ∨ p 14 ∨ p 20 ∨ p 22 ∨ p 26 ∨ p 27 ∨ p 29) ∧
  (¬ p 0 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 29)))) ∧
  ((((p 4 ∨ p 6 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 20 ∨ p 22 ∨ p 26 ∨ p 27 ∨ p 29) ∧
  (¬ p 4 ∨ ¬ p 6 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 29)) ∧
  ((p 0 ∨ p 5 ∨ p 11 ∨ p 13 ∨ p 14 ∨ p 20 ∨ p 22 ∨ p 26 ∨ p 27 ∨ p 29) ∧
  (¬ p 0 ∨ ¬ p 5 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 29))) ∧
  (((p 3 ∨ p 4 ∨ p 6 ∨ p 7 ∨ p 12 ∨ p 17 ∨ p 21 ∨ p 23 ∨ p 26 ∨ p 29) ∧
  (¬ p 3 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 26 ∨ ¬ p 29)) ∧
  ((p 0 ∨ p 3 ∨ p 5 ∨ p 7 ∨ p 12 ∨ p 17 ∨ p 21 ∨ p 23 ∨ p 26 ∨ p 29) ∧
  ((¬ p 0 ∨ ¬ p 3 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 26 ∨ ¬ p 29) ∧
  (p 3 ∨ p 4 ∨ p 6 ∨ p 11 ∨ p 13 ∨ p 17 ∨ p 21 ∨ p 23 ∨ p 26 ∨ p 29))))))))) ∧
  ((((((((¬ p 3 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 26 ∨ ¬ p 29) ∧
  (p 0 ∨ p 3 ∨ p 5 ∨ p 11 ∨ p 13 ∨ p 17 ∨ p 21 ∨ p 23 ∨ p 26 ∨ p 29)) ∧
  ((¬ p 0 ∨ ¬ p 3 ∨ ¬ p 5 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 26 ∨ ¬ p 29) ∧
  (p 3 ∨ p 4 ∨ p 6 ∨ p 7 ∨ p 12 ∨ p 20 ∨ p 22 ∨ p 23 ∨ p 26 ∨ p 29))) ∧
  (((¬ p 3 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 26 ∨ ¬ p 29) ∧
  (p 0 ∨ p 3 ∨ p 5 ∨ p 7 ∨ p 12 ∨ p 20 ∨ p 22 ∨ p 23 ∨ p 26 ∨ p 29)) ∧
  ((¬ p 0 ∨ ¬ p 3 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 12 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 26 ∨ ¬ p 29) ∧
  (p 3 ∨ p 4 ∨ p 6 ∨ p 11 ∨ p 13 ∨ p 20 ∨ p 22 ∨ p 23 ∨ p 26 ∨ p 29)))) ∧
  ((((¬ p 3 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 26 ∨ ¬ p 29) ∧
  (p 0 ∨ p 3 ∨ p 5 ∨ p 11 ∨ p 13 ∨ p 20 ∨ p 22 ∨ p 23 ∨ p 26 ∨ p 29)) ∧
  ((¬ p 0 ∨ ¬ p 3 ∨ ¬ p 5 ∨ ¬ p 11 ∨ ¬ p 13 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 26 ∨ ¬ p 29) ∧
  (p 1 ∨ p 3 ∨ p 6 ∨ p 13 ∨ p 18 ∨ p 19 ∨ p 21 ∨ p 24 ∨ p 26 ∨ p 29))) ∧
  (((¬ p 1 ∨ ¬ p 3 ∨ ¬ p 6 ∨ ¬ p 13 ∨ ¬ p 18 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 26 ∨ ¬ p 29) ∧
  (p 0 ∨ p 2 ∨ p 9 ∨ p 10 ∨ p 12 ∨ p 15 ∨ p 16 ∨ p 22 ∨ p 27 ∨ p 28)) ∧
  ((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 9 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 15 ∨ ¬ p 16 ∨ ¬ p 22 ∨ ¬ p 27 ∨ ¬ p 28) ∧
  (p 1 ∨ p 3 ∨ p 9 ∨ p 12 ∨ p 15 ∨ p 22 ∨ p 26 ∨ p 27 ∨ p 28 ∨ p 29))))) ∧
  (((((¬ p 1 ∨ ¬ p 3 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 15 ∨ ¬ p 22 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 28 ∨ ¬ p 29) ∧
  (p 8 ∨ p 9 ∨ p 11 ∨ p 12 ∨ p 16 ∨ p 20 ∨ p 22 ∨ p 24 ∨ p 25 ∨ p 26)) ∧
  ((¬ p 8 ∨ ¬ p 9 ∨ ¬ p 11 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26) ∧
  (p 9 ∨ p 11 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 20 ∨ p 22 ∨ p 24 ∨ p 25 ∨ p 26))) ∧
  (((¬ p 9 ∨ ¬ p 11 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26) ∧
  (p 8 ∨ p 9 ∨ p 11 ∨ p 12 ∨ p 16 ∨ p 17 ∨ p 21 ∨ p 24 ∨ p 25 ∨ p 26)) ∧
  ((¬ p 8 ∨ ¬ p 9 ∨ ¬ p 11 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26) ∧
  (p 9 ∨ p 11 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 21 ∨ p 24 ∨ p 25 ∨ p 26)))) ∧
  ((((¬ p 9 ∨ ¬ p 11 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26) ∧
  (p 1 ∨ p 8 ∨ p 9 ∨ p 12 ∨ p 16 ∨ p 20 ∨ p 22 ∨ p 23 ∨ p 25 ∨ p 26)) ∧
  ((¬ p 1 ∨ ¬ p 8 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 26) ∧
  (p 1 ∨ p 9 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 20 ∨ p 22 ∨ p 23 ∨ p 25 ∨ p 26))) ∧
  (((¬ p 1 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 26) ∧
  (p 1 ∨ p 8 ∨ p 9 ∨ p 12 ∨ p 16 ∨ p 17 ∨ p 21 ∨ p 23 ∨ p 25 ∨ p 26)) ∧
  ((¬ p 1 ∨ ¬ p 8 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 26) ∧
  (p 1 ∨ p 9 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 21 ∨ p 23 ∨ p 25 ∨ p 26)))))) ∧
  ((((((¬ p 1 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 26) ∧
  (p 2 ∨ p 5 ∨ p 8 ∨ p 9 ∨ p 11 ∨ p 12 ∨ p 16 ∨ p 20 ∨ p 22 ∨ p 24)) ∧
  ((¬ p 2 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 9 ∨ ¬ p 11 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 24) ∧
  (p 2 ∨ p 5 ∨ p 9 ∨ p 11 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 20 ∨ p 22 ∨ p 24))) ∧
  (((¬ p 2 ∨ ¬ p 5 ∨ ¬ p 9 ∨ ¬ p 11 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 24) ∧
  (p 2 ∨ p 5 ∨ p 8 ∨ p 9 ∨ p 11 ∨ p 12 ∨ p 16 ∨ p 17 ∨ p 21 ∨ p 24)) ∧
  ((¬ p 2 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 9 ∨ ¬ p 11 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 24) ∧
  (p 2 ∨ p 5 ∨ p 9 ∨ p 11 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 21 ∨ p 24)))) ∧
  ((((¬ p 2 ∨ ¬ p 5 ∨ ¬ p 9 ∨ ¬ p 11 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 24) ∧
  (p 0 ∨ p 2 ∨ p 6 ∨ p 10 ∨ p 13 ∨ p 16 ∨ p 18 ∨ p 19 ∨ p 21 ∨ p 24)) ∧
  ((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 6 ∨ ¬ p 10 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 18 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 24) ∧
  (p 1 ∨ p 2 ∨ p 5 ∨ p 8 ∨ p 9 ∨ p 12 ∨ p 16 ∨ p 20 ∨ p 22 ∨ p 23))) ∧
  (((¬ p 1 ∨ ¬ p 2 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23) ∧
  (p 1 ∨ p 2 ∨ p 5 ∨ p 9 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 20 ∨ p 22 ∨ p 23)) ∧
  ((¬ p 1 ∨ ¬ p 2 ∨ ¬ p 5 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23) ∧
  (p 1 ∨ p 2 ∨ p 5 ∨ p 8 ∨ p 9 ∨ p 12 ∨ p 16 ∨ p 17 ∨ p 21 ∨ p 23))))) ∧
  (((((¬ p 1 ∨ ¬ p 2 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 23) ∧
  (p 1 ∨ p 2 ∨ p 5 ∨ p 9 ∨ p 12 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 21 ∨ p 23)) ∧
  ((¬ p 1 ∨ ¬ p 2 ∨ ¬ p 5 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 21 ∨ ¬ p 23) ∧
  (p 1 ∨ p 3 ∨ p 9 ∨ p 12 ∨ p 18 ∨ p 21 ∨ p 22 ∨ p 26 ∨ p 28 ∨ p 29))) ∧
  (((¬ p 1 ∨ ¬ p 3 ∨ ¬ p 9 ∨ ¬ p 12 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 22 ∨ ¬ p 26 ∨ ¬ p 28 ∨ ¬ p 29) ∧
  (p 8 ∨ p 10 ∨ p 13 ∨ p 14 ∨ p 17 ∨ p 18 ∨ p 24 ∨ p 25 ∨ p 26 ∨ p 27)) ∧
  ((¬ p 8 ∨ ¬ p 10 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26 ∨ ¬ p 27) ∧
  (p 7 ∨ p 9 ∨ p 13 ∨ p 14 ∨ p 17 ∨ p 18 ∨ p 24 ∨ p 25 ∨ p 26 ∨ p 27)))) ∧
  ((((¬ p 7 ∨ ¬ p 9 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26 ∨ ¬ p 27) ∧
  (p 4 ∨ p 8 ∨ p 10 ∨ p 13 ∨ p 14 ∨ p 19 ∨ p 24 ∨ p 25 ∨ p 26 ∨ p 27)) ∧
  ((¬ p 4 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 19 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26 ∨ ¬ p 27) ∧
  (p 4 ∨ p 7 ∨ p 9 ∨ p 13 ∨ p 14 ∨ p 19 ∨ p 24 ∨ p 25 ∨ p 26 ∨ p 27))) ∧
  (((¬ p 4 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 19 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26 ∨ ¬ p 27) ∧
  (p 2 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 13 ∨ p 14 ∨ p 17 ∨ p 18 ∨ p 24 ∨ p 27)) ∧
  ((¬ p 2 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 24 ∨ ¬ p 27) ∧
  ((p 2 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 13 ∨ p 14 ∨ p 17 ∨ p 18 ∨ p 24 ∨ p 27) ∧
  (¬ p 2 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 24 ∨ ¬ p 27)))))))) ∧
  (((((((p 0 ∨ p 2 ∨ p 6 ∨ p 10 ∨ p 13 ∨ p 15 ∨ p 16 ∨ p 19 ∨ p 24 ∨ p 27) ∧
  (¬ p 0 ∨ ¬ p 2 ∨ ¬ p 6 ∨ ¬ p 10 ∨ ¬ p 13 ∨ ¬ p 15 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 24 ∨ ¬ p 27)) ∧
  ((p 2 ∨ p 4 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 13 ∨ p 14 ∨ p 19 ∨ p 24 ∨ p 27) ∧
  (¬ p 2 ∨ ¬ p 4 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 19 ∨ ¬ p 24 ∨ ¬ p 27))) ∧
  (((p 2 ∨ p 4 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 13 ∨ p 14 ∨ p 19 ∨ p 24 ∨ p 27) ∧
  (¬ p 2 ∨ ¬ p 4 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 13 ∨ ¬ p 14 ∨ ¬ p 19 ∨ ¬ p 24 ∨ ¬ p 27)) ∧
  ((p 3 ∨ p 8 ∨ p 10 ∨ p 13 ∨ p 17 ∨ p 18 ∨ p 23 ∨ p 24 ∨ p 25 ∨ p 26) ∧
  (¬ p 3 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 13 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 23 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26)))) ∧
  ((((p 3 ∨ p 7 ∨ p 9 ∨ p 13 ∨ p 17 ∨ p 18 ∨ p 23 ∨ p 24 ∨ p 25 ∨ p 26) ∧
  (¬ p 3 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 13 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 23 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26)) ∧
  ((p 3 ∨ p 4 ∨ p 8 ∨ p 10 ∨ p 13 ∨ p 19 ∨ p 23 ∨ p 24 ∨ p 25 ∨ p 26) ∧
  (¬ p 3 ∨ ¬ p 4 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 13 ∨ ¬ p 19 ∨ ¬ p 23 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26))) ∧
  (((p 3 ∨ p 4 ∨ p 7 ∨ p 9 ∨ p 13 ∨ p 19 ∨ p 23 ∨ p 24 ∨ p 25 ∨ p 26) ∧
  (¬ p 3 ∨ ¬ p 4 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 13 ∨ ¬ p 19 ∨ ¬ p 23 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26)) ∧
  ((p 2 ∨ p 3 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 13 ∨ p 17 ∨ p 18 ∨ p 23 ∨ p 24) ∧
  (¬ p 2 ∨ ¬ p 3 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 13 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 23 ∨ ¬ p 24))))) ∧
  (((((p 2 ∨ p 3 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 13 ∨ p 17 ∨ p 18 ∨ p 23 ∨ p 24) ∧
  (¬ p 2 ∨ ¬ p 3 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 13 ∨ ¬ p 17 ∨ ¬ p 18 ∨ ¬ p 23 ∨ ¬ p 24)) ∧
  ((p 2 ∨ p 3 ∨ p 4 ∨ p 5 ∨ p 8 ∨ p 10 ∨ p 13 ∨ p 19 ∨ p 23 ∨ p 24) ∧
  (¬ p 2 ∨ ¬ p 3 ∨ ¬ p 4 ∨ ¬ p 5 ∨ ¬ p 8 ∨ ¬ p 10 ∨ ¬ p 13 ∨ ¬ p 19 ∨ ¬ p 23 ∨ ¬ p 24))) ∧
  (((p 2 ∨ p 3 ∨ p 4 ∨ p 5 ∨ p 7 ∨ p 9 ∨ p 13 ∨ p 19 ∨ p 23 ∨ p 24) ∧
  (¬ p 2 ∨ ¬ p 3 ∨ ¬ p 4 ∨ ¬ p 5 ∨ ¬ p 7 ∨ ¬ p 9 ∨ ¬ p 13 ∨ ¬ p 19 ∨ ¬ p 23 ∨ ¬ p 24)) ∧
  ((p 1 ∨ p 3 ∨ p 6 ∨ p 15 ∨ p 19 ∨ p 22 ∨ p 26 ∨ p 27 ∨ p 28 ∨ p 29) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 6 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 22 ∨ ¬ p 26 ∨ ¬ p 27 ∨ ¬ p 28 ∨ ¬ p 29)))) ∧
  ((((p 6 ∨ p 8 ∨ p 11 ∨ p 16 ∨ p 19 ∨ p 20 ∨ p 22 ∨ p 24 ∨ p 25 ∨ p 26) ∧
  (¬ p 6 ∨ ¬ p 8 ∨ ¬ p 11 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26)) ∧
  ((p 6 ∨ p 11 ∨ p 14 ∨ p 15 ∨ p 19 ∨ p 20 ∨ p 22 ∨ p 24 ∨ p 25 ∨ p 26) ∧
  (¬ p 6 ∨ ¬ p 11 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26))) ∧
  (((p 6 ∨ p 8 ∨ p 11 ∨ p 16 ∨ p 17 ∨ p 19 ∨ p 21 ∨ p 24 ∨ p 25 ∨ p 26) ∧
  (¬ p 6 ∨ ¬ p 8 ∨ ¬ p 11 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26)) ∧
  ((p 6 ∨ p 11 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 19 ∨ p 21 ∨ p 24 ∨ p 25 ∨ p 26) ∧
  ((¬ p 6 ∨ ¬ p 11 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 24 ∨ ¬ p 25 ∨ ¬ p 26) ∧
  (p 1 ∨ p 6 ∨ p 8 ∨ p 16 ∨ p 19 ∨ p 20 ∨ p 22 ∨ p 23 ∨ p 25 ∨ p 26))))))) ∧
  ((((((¬ p 1 ∨ ¬ p 6 ∨ ¬ p 8 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 26) ∧
  (p 1 ∨ p 6 ∨ p 14 ∨ p 15 ∨ p 19 ∨ p 20 ∨ p 22 ∨ p 23 ∨ p 25 ∨ p 26)) ∧
  ((¬ p 1 ∨ ¬ p 6 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 26) ∧
  (p 1 ∨ p 6 ∨ p 8 ∨ p 16 ∨ p 17 ∨ p 19 ∨ p 21 ∨ p 23 ∨ p 25 ∨ p 26))) ∧
  (((¬ p 1 ∨ ¬ p 6 ∨ ¬ p 8 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 26) ∧
  (p 1 ∨ p 6 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 19 ∨ p 21 ∨ p 23 ∨ p 25 ∨ p 26)) ∧
  ((¬ p 1 ∨ ¬ p 6 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 23 ∨ ¬ p 25 ∨ ¬ p 26) ∧
  (p 2 ∨ p 5 ∨ p 6 ∨ p 8 ∨ p 11 ∨ p 16 ∨ p 19 ∨ p 20 ∨ p 22 ∨ p 24)))) ∧
  ((((¬ p 2 ∨ ¬ p 5 ∨ ¬ p 6 ∨ ¬ p 8 ∨ ¬ p 11 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 24) ∧
  (p 2 ∨ p 5 ∨ p 6 ∨ p 11 ∨ p 14 ∨ p 15 ∨ p 19 ∨ p 20 ∨ p 22 ∨ p 24)) ∧
  ((¬ p 2 ∨ ¬ p 5 ∨ ¬ p 6 ∨ ¬ p 11 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 24) ∧
  (p 2 ∨ p 5 ∨ p 6 ∨ p 8 ∨ p 11 ∨ p 16 ∨ p 17 ∨ p 19 ∨ p 21 ∨ p 24))) ∧
  (((¬ p 2 ∨ ¬ p 5 ∨ ¬ p 6 ∨ ¬ p 8 ∨ ¬ p 11 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 24) ∧
  (p 2 ∨ p 5 ∨ p 6 ∨ p 11 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 19 ∨ p 21 ∨ p 24)) ∧
  ((¬ p 2 ∨ ¬ p 5 ∨ ¬ p 6 ∨ ¬ p 11 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 24) ∧
  (p 0 ∨ p 2 ∨ p 9 ∨ p 10 ∨ p 12 ∨ p 13 ∨ p 16 ∨ p 18 ∨ p 21 ∨ p 24))))) ∧
  (((((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 9 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 13 ∨ ¬ p 16 ∨ ¬ p 18 ∨ ¬ p 21 ∨ ¬ p 24) ∧
  (p 1 ∨ p 2 ∨ p 5 ∨ p 6 ∨ p 8 ∨ p 16 ∨ p 19 ∨ p 20 ∨ p 22 ∨ p 23)) ∧
  ((¬ p 1 ∨ ¬ p 2 ∨ ¬ p 5 ∨ ¬ p 6 ∨ ¬ p 8 ∨ ¬ p 16 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23) ∧
  (p 1 ∨ p 2 ∨ p 5 ∨ p 6 ∨ p 14 ∨ p 15 ∨ p 19 ∨ p 20 ∨ p 22 ∨ p 23))) ∧
  (((¬ p 1 ∨ ¬ p 2 ∨ ¬ p 5 ∨ ¬ p 6 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 19 ∨ ¬ p 20 ∨ ¬ p 22 ∨ ¬ p 23) ∧
  (p 1 ∨ p 2 ∨ p 5 ∨ p 6 ∨ p 8 ∨ p 16 ∨ p 17 ∨ p 19 ∨ p 21 ∨ p 23)) ∧
  ((¬ p 1 ∨ ¬ p 2 ∨ ¬ p 5 ∨ ¬ p 6 ∨ ¬ p 8 ∨ ¬ p 16 ∨ ¬ p 17 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 23) ∧
  (p 1 ∨ p 2 ∨ p 5 ∨ p 6 ∨ p 14 ∨ p 15 ∨ p 17 ∨ p 19 ∨ p 21 ∨ p 23)))) ∧
  ((((¬ p 1 ∨ ¬ p 2 ∨ ¬ p 5 ∨ ¬ p 6 ∨ ¬ p 14 ∨ ¬ p 15 ∨ ¬ p 17 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 23) ∧
  (p 1 ∨ p 3 ∨ p 6 ∨ p 18 ∨ p 19 ∨ p 21 ∨ p 22 ∨ p 26 ∨ p 28 ∨ p 29)) ∧
  ((¬ p 1 ∨ ¬ p 3 ∨ ¬ p 6 ∨ ¬ p 18 ∨ ¬ p 19 ∨ ¬ p 21 ∨ ¬ p 22 ∨ ¬ p 26 ∨ ¬ p 28 ∨ ¬ p 29) ∧
  (p 0 ∨ p 2 ∨ p 9 ∨ p 10 ∨ p 12 ∨ p 13 ∨ p 15 ∨ p 16 ∨ p 24 ∨ p 27))) ∧
  (((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 9 ∨ ¬ p 10 ∨ ¬ p 12 ∨ ¬ p 13 ∨ ¬ p 15 ∨ ¬ p 16 ∨ ¬ p 24 ∨ ¬ p 27) ∧
  (p 0 ∨ p 2 ∨ p 11 ∨ p 14 ∨ p 24 ∨ p 27)) ∧
  ((¬ p 0 ∨ ¬ p 2 ∨ ¬ p 11 ∨ ¬ p 14 ∨ ¬ p 24 ∨ ¬ p 27) ∧
  ((p 1 ∨ p 3 ∨ p 4 ∨ p 6 ∨ p 25 ∨ p 26) ∧
  (¬ p 1 ∨ ¬ p 3 ∨ ¬ p 4 ∨ ¬ p 6 ∨ ¬ p 25 ∨ ¬ p 26)))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma no_cnfProp (p : Fin 30 → Prop) : ¬ cnfProp p := by
  have h := no_two_regular_cut_connected_clauses (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) (p 8) (p 9) (p 10) (p 11) (p 12) (p 13) (p 14) (p 15) (p 16) (p 17) (p 18) (p 19) (p 20) (p 21) (p 22) (p 23) (p 24) (p 25) (p 26) (p 27) (p 28) (p 29)
  simpa only [cnfProp, not_and_or, not_or, not_not] using h

def tripleAt : Fin 60 → Fin 15 × Fin 30 × Fin 30 × Fin 30 :=
  ![(0, 0, 1, 2),
    (0, 0, 1, 3),
    (0, 0, 2, 3),
    (0, 1, 2, 3),
    (1, 0, 4, 5),
    (1, 0, 4, 6),
    (1, 0, 5, 6),
    (1, 4, 5, 6),
    (2, 7, 8, 9),
    (2, 7, 8, 10),
    (2, 7, 9, 10),
    (2, 8, 9, 10),
    (3, 7, 11, 12),
    (3, 7, 11, 13),
    (3, 7, 12, 13),
    (3, 11, 12, 13),
    (4, 8, 14, 15),
    (4, 8, 14, 16),
    (4, 8, 15, 16),
    (4, 14, 15, 16),
    (5, 4, 17, 18),
    (5, 4, 17, 19),
    (5, 4, 18, 19),
    (5, 17, 18, 19),
    (6, 17, 20, 21),
    (6, 17, 20, 22),
    (6, 17, 21, 22),
    (6, 20, 21, 22),
    (7, 1, 11, 23),
    (7, 1, 11, 24),
    (7, 1, 23, 24),
    (7, 11, 23, 24),
    (8, 2, 5, 25),
    (8, 2, 5, 26),
    (8, 2, 25, 26),
    (8, 5, 25, 26),
    (9, 3, 14, 23),
    (9, 3, 14, 27),
    (9, 3, 23, 27),
    (9, 14, 23, 27),
    (10, 20, 25, 28),
    (10, 20, 25, 29),
    (10, 20, 28, 29),
    (10, 25, 28, 29),
    (11, 15, 18, 21),
    (11, 15, 18, 27),
    (11, 15, 21, 27),
    (11, 18, 21, 27),
    (12, 6, 9, 12),
    (12, 6, 9, 19),
    (12, 6, 12, 19),
    (12, 9, 12, 19),
    (13, 13, 22, 24),
    (13, 13, 22, 28),
    (13, 13, 24, 28),
    (13, 22, 24, 28),
    (14, 10, 16, 26),
    (14, 10, 16, 29),
    (14, 10, 26, 29),
    (14, 16, 26, 29)]

def cutAt : Fin 202 → BitVec 15 × Fin 15 × List (Fin 30) :=
  ![(668, 2, [1, 3, 9, 10, 12, 13, 15, 16, 24, 27]),
    (1378, 1, [0, 2, 6, 18, 19, 21, 22, 26, 28, 29]),
    (2144, 5, [4, 15, 19, 20, 22, 27]),
    (2576, 4, [3, 8, 16, 18, 21, 23]),
    (2716, 2, [1, 3, 9, 10, 12, 13, 16, 18, 21, 24]),
    (3426, 1, [0, 2, 6, 15, 19, 22, 26, 27, 28, 29]),
    (4108, 2, [6, 8, 10, 11, 13, 19]),
    (4130, 1, [0, 5, 9, 12, 17, 18]),
    (4764, 2, [1, 3, 6, 10, 13, 15, 16, 19, 24, 27]),
    (5474, 1, [0, 2, 9, 12, 18, 21, 22, 26, 28, 29]),
    (6196, 2, [4, 6, 7, 10, 12, 14, 16, 17, 21, 27]),
    (6198, 1, [0, 5, 7, 10, 12, 14, 16, 17, 21, 27]),
    (6204, 2, [4, 6, 10, 11, 13, 14, 16, 17, 21, 27]),
    (6206, 1, [0, 5, 10, 11, 13, 14, 16, 17, 21, 27]),
    (6260, 2, [4, 6, 7, 10, 12, 14, 16, 20, 22, 27]),
    (6262, 1, [0, 5, 7, 10, 12, 14, 16, 20, 22, 27]),
    (6268, 2, [4, 6, 10, 11, 13, 14, 16, 20, 22, 27]),
    (6270, 1, [0, 5, 10, 11, 13, 14, 16, 20, 22, 27]),
    (6708, 2, [3, 4, 6, 7, 10, 12, 16, 17, 21, 23]),
    (6710, 1, [0, 3, 5, 7, 10, 12, 16, 17, 21, 23]),
    (6716, 2, [3, 4, 6, 10, 11, 13, 16, 17, 21, 23]),
    (6718, 1, [0, 3, 5, 10, 11, 13, 16, 17, 21, 23]),
    (6772, 2, [3, 4, 6, 7, 10, 12, 16, 20, 22, 23]),
    (6774, 1, [0, 3, 5, 7, 10, 12, 16, 20, 22, 23]),
    (6780, 2, [3, 4, 6, 10, 11, 13, 16, 20, 22, 23]),
    (6782, 1, [0, 3, 5, 10, 11, 13, 16, 20, 22, 23]),
    (6812, 2, [1, 3, 6, 10, 13, 16, 18, 19, 21, 24]),
    (7522, 1, [0, 2, 9, 12, 15, 22, 26, 27, 28, 29]),
    (8328, 3, [1, 7, 12, 22, 23, 28]),
    (8860, 2, [1, 3, 9, 10, 12, 15, 16, 22, 27, 28]),
    (9280, 6, [13, 17, 21, 24, 25, 29]),
    (9570, 1, [0, 2, 6, 13, 18, 19, 21, 24, 26, 29]),
    (10908, 2, [1, 3, 9, 10, 12, 16, 18, 21, 22, 28]),
    (10944, 6, [1, 3, 11, 13, 14, 15, 17, 18, 20, 28]),
    (10952, 3, [1, 3, 7, 12, 14, 15, 17, 18, 20, 28]),
    (10960, 4, [1, 3, 8, 11, 13, 16, 17, 18, 20, 28]),
    (10968, 3, [1, 3, 7, 8, 12, 16, 17, 18, 20, 28]),
    (10976, 5, [1, 3, 4, 11, 13, 14, 15, 19, 20, 28]),
    (10984, 3, [1, 3, 4, 7, 12, 14, 15, 19, 20, 28]),
    (10992, 4, [1, 3, 4, 8, 11, 13, 16, 19, 20, 28]),
    (11000, 3, [1, 3, 4, 7, 8, 12, 16, 19, 20, 28]),
    (11618, 1, [0, 2, 6, 13, 15, 19, 24, 26, 27, 29]),
    (11968, 6, [1, 3, 11, 13, 14, 15, 17, 18, 25, 29]),
    (11976, 3, [1, 3, 7, 12, 14, 15, 17, 18, 25, 29]),
    (11984, 4, [1, 3, 8, 11, 13, 16, 17, 18, 25, 29]),
    (11992, 3, [1, 3, 7, 8, 12, 16, 17, 18, 25, 29]),
    (12000, 5, [1, 3, 4, 11, 13, 14, 15, 19, 25, 29]),
    (12008, 3, [1, 3, 4, 7, 12, 14, 15, 19, 25, 29]),
    (12016, 4, [1, 3, 4, 8, 11, 13, 16, 19, 25, 29]),
    (12024, 3, [1, 3, 4, 7, 8, 12, 16, 19, 25, 29]),
    (12392, 3, [4, 6, 7, 9, 11, 18, 20, 21, 24, 28]),
    (12394, 1, [0, 5, 7, 9, 11, 18, 20, 21, 24, 28]),
    (12396, 2, [4, 6, 8, 10, 11, 18, 20, 21, 24, 28]),
    (12398, 1, [0, 5, 8, 10, 11, 18, 20, 21, 24, 28]),
    (12520, 3, [1, 4, 6, 7, 9, 18, 20, 21, 23, 28]),
    (12522, 1, [0, 1, 5, 7, 9, 18, 20, 21, 23, 28]),
    (12524, 2, [1, 4, 6, 8, 10, 18, 20, 21, 23, 28]),
    (12526, 1, [0, 1, 5, 8, 10, 18, 20, 21, 23, 28]),
    (12956, 2, [1, 3, 6, 10, 15, 16, 19, 22, 27, 28]),
    (13416, 3, [4, 6, 7, 9, 11, 18, 21, 24, 25, 29]),
    (13418, 1, [0, 5, 7, 9, 11, 18, 21, 24, 25, 29]),
    (13420, 2, [4, 6, 8, 10, 11, 18, 21, 24, 25, 29]),
    (13422, 1, [0, 5, 8, 10, 11, 18, 21, 24, 25, 29]),
    (13544, 3, [1, 4, 6, 7, 9, 18, 21, 23, 25, 29]),
    (13546, 1, [0, 1, 5, 7, 9, 18, 21, 23, 25, 29]),
    (13548, 2, [1, 4, 6, 8, 10, 18, 21, 23, 25, 29]),
    (13550, 1, [0, 1, 5, 8, 10, 18, 21, 23, 25, 29]),
    (13666, 1, [0, 2, 9, 12, 13, 18, 21, 24, 26, 29]),
    (14440, 3, [4, 6, 7, 9, 11, 15, 20, 24, 27, 28]),
    (14442, 1, [0, 5, 7, 9, 11, 15, 20, 24, 27, 28]),
    (14444, 2, [4, 6, 8, 10, 11, 15, 20, 24, 27, 28]),
    (14446, 1, [0, 5, 8, 10, 11, 15, 20, 24, 27, 28]),
    (14568, 3, [1, 4, 6, 7, 9, 15, 20, 23, 27, 28]),
    (14570, 1, [0, 1, 5, 7, 9, 15, 20, 23, 27, 28]),
    (14572, 2, [1, 4, 6, 8, 10, 15, 20, 23, 27, 28]),
    (14574, 1, [0, 1, 5, 8, 10, 15, 20, 23, 27, 28]),
    (15004, 2, [1, 3, 6, 10, 16, 18, 19, 21, 22, 28]),
    (15464, 3, [4, 6, 7, 9, 11, 15, 24, 25, 27, 29]),
    (15466, 1, [0, 5, 7, 9, 11, 15, 24, 25, 27, 29]),
    (15468, 2, [4, 6, 8, 10, 11, 15, 24, 25, 27, 29]),
    (15470, 1, [0, 5, 8, 10, 11, 15, 24, 25, 27, 29]),
    (15592, 3, [1, 4, 6, 7, 9, 15, 23, 25, 27, 29]),
    (15594, 1, [0, 1, 5, 7, 9, 15, 23, 25, 27, 29]),
    (15596, 2, [1, 4, 6, 8, 10, 15, 23, 25, 27, 29]),
    (15598, 1, [0, 1, 5, 8, 10, 15, 23, 25, 27, 29]),
    (15714, 1, [0, 2, 9, 12, 13, 15, 24, 26, 27, 29]),
    (16404, 2, [7, 9, 14, 15, 26, 29]),
    (17052, 2, [1, 3, 9, 12, 13, 15, 24, 26, 27, 29]),
    (17664, 8, [2, 5, 10, 16, 20, 28]),
    (17762, 1, [0, 2, 6, 10, 16, 18, 19, 21, 22, 28]),
    (19100, 2, [1, 3, 9, 12, 13, 18, 21, 24, 26, 29]),
    (19536, 4, [8, 10, 14, 17, 18, 22, 25, 26, 27, 28]),
    (19540, 2, [7, 9, 14, 17, 18, 22, 25, 26, 27, 28]),
    (19568, 4, [4, 8, 10, 14, 19, 22, 25, 26, 27, 28]),
    (19572, 2, [4, 7, 9, 14, 19, 22, 25, 26, 27, 28]),
    (19792, 4, [2, 5, 8, 10, 14, 17, 18, 22, 27, 28]),
    (19796, 2, [2, 5, 7, 9, 14, 17, 18, 22, 27, 28]),
    (19810, 1, [0, 2, 6, 10, 15, 16, 19, 22, 27, 28]),
    (19824, 4, [2, 4, 5, 8, 10, 14, 19, 22, 27, 28]),
    (19828, 2, [2, 4, 5, 7, 9, 14, 19, 22, 27, 28]),
    (20048, 4, [3, 8, 10, 17, 18, 22, 23, 25, 26, 28]),
    (20052, 2, [3, 7, 9, 17, 18, 22, 23, 25, 26, 28]),
    (20080, 4, [3, 4, 8, 10, 19, 22, 23, 25, 26, 28]),
    (20084, 2, [3, 4, 7, 9, 19, 22, 23, 25, 26, 28]),
    (20304, 4, [2, 3, 5, 8, 10, 17, 18, 22, 23, 28]),
    (20308, 2, [2, 3, 5, 7, 9, 17, 18, 22, 23, 28]),
    (20336, 4, [2, 3, 4, 5, 8, 10, 19, 22, 23, 28]),
    (20340, 2, [2, 3, 4, 5, 7, 9, 19, 22, 23, 28]),
    (20742, 1, [0, 2, 4, 7, 8, 12, 16, 19, 25, 29]),
    (20750, 1, [0, 2, 4, 8, 11, 13, 16, 19, 25, 29]),
    (20758, 1, [0, 2, 4, 7, 12, 14, 15, 19, 25, 29]),
    (20766, 1, [0, 2, 4, 11, 13, 14, 15, 19, 25, 29]),
    (20774, 1, [0, 2, 7, 8, 12, 16, 17, 18, 25, 29]),
    (20782, 1, [0, 2, 8, 11, 13, 16, 17, 18, 25, 29]),
    (20790, 1, [0, 2, 7, 12, 14, 15, 17, 18, 25, 29]),
    (20798, 1, [0, 2, 11, 13, 14, 15, 17, 18, 25, 29]),
    (21148, 2, [1, 3, 6, 13, 15, 19, 24, 26, 27, 29]),
    (21766, 1, [0, 2, 4, 7, 8, 12, 16, 19, 20, 28]),
    (21774, 1, [0, 2, 4, 8, 11, 13, 16, 19, 20, 28]),
    (21782, 1, [0, 2, 4, 7, 12, 14, 15, 19, 20, 28]),
    (21790, 1, [0, 2, 4, 11, 13, 14, 15, 19, 20, 28]),
    (21798, 1, [0, 2, 7, 8, 12, 16, 17, 18, 20, 28]),
    (21806, 1, [0, 2, 8, 11, 13, 16, 17, 18, 20, 28]),
    (21814, 1, [0, 2, 7, 12, 14, 15, 17, 18, 20, 28]),
    (21822, 1, [0, 2, 11, 13, 14, 15, 17, 18, 20, 28]),
    (21858, 1, [0, 2, 9, 10, 12, 16, 18, 21, 22, 28]),
    (22580, 2, [4, 6, 7, 12, 14, 17, 21, 26, 27, 29]),
    (22582, 1, [0, 5, 7, 12, 14, 17, 21, 26, 27, 29]),
    (22588, 2, [4, 6, 11, 13, 14, 17, 21, 26, 27, 29]),
    (22590, 1, [0, 5, 11, 13, 14, 17, 21, 26, 27, 29]),
    (22644, 2, [4, 6, 7, 12, 14, 20, 22, 26, 27, 29]),
    (22646, 1, [0, 5, 7, 12, 14, 20, 22, 26, 27, 29]),
    (22652, 2, [4, 6, 11, 13, 14, 20, 22, 26, 27, 29]),
    (22654, 1, [0, 5, 11, 13, 14, 20, 22, 26, 27, 29]),
    (23092, 2, [3, 4, 6, 7, 12, 17, 21, 23, 26, 29]),
    (23094, 1, [0, 3, 5, 7, 12, 17, 21, 23, 26, 29]),
    (23100, 2, [3, 4, 6, 11, 13, 17, 21, 23, 26, 29]),
    (23102, 1, [0, 3, 5, 11, 13, 17, 21, 23, 26, 29]),
    (23156, 2, [3, 4, 6, 7, 12, 20, 22, 23, 26, 29]),
    (23158, 1, [0, 3, 5, 7, 12, 20, 22, 23, 26, 29]),
    (23164, 2, [3, 4, 6, 11, 13, 20, 22, 23, 26, 29]),
    (23166, 1, [0, 3, 5, 11, 13, 20, 22, 23, 26, 29]),
    (23196, 2, [1, 3, 6, 13, 18, 19, 21, 24, 26, 29]),
    (23906, 1, [0, 2, 9, 10, 12, 15, 16, 22, 27, 28]),
    (25244, 2, [1, 3, 9, 12, 15, 22, 26, 27, 28, 29]),
    (25612, 2, [8, 9, 11, 12, 16, 20, 22, 24, 25, 26]),
    (25628, 2, [9, 11, 12, 14, 15, 20, 22, 24, 25, 26]),
    (25676, 2, [8, 9, 11, 12, 16, 17, 21, 24, 25, 26]),
    (25692, 2, [9, 11, 12, 14, 15, 17, 21, 24, 25, 26]),
    (25740, 2, [1, 8, 9, 12, 16, 20, 22, 23, 25, 26]),
    (25756, 2, [1, 9, 12, 14, 15, 20, 22, 23, 25, 26]),
    (25804, 2, [1, 8, 9, 12, 16, 17, 21, 23, 25, 26]),
    (25820, 2, [1, 9, 12, 14, 15, 17, 21, 23, 25, 26]),
    (25868, 2, [2, 5, 8, 9, 11, 12, 16, 20, 22, 24]),
    (25884, 2, [2, 5, 9, 11, 12, 14, 15, 20, 22, 24]),
    (25932, 2, [2, 5, 8, 9, 11, 12, 16, 17, 21, 24]),
    (25948, 2, [2, 5, 9, 11, 12, 14, 15, 17, 21, 24]),
    (25954, 1, [0, 2, 6, 10, 13, 16, 18, 19, 21, 24]),
    (25996, 2, [1, 2, 5, 8, 9, 12, 16, 20, 22, 23]),
    (26012, 2, [1, 2, 5, 9, 12, 14, 15, 20, 22, 23]),
    (26060, 2, [1, 2, 5, 8, 9, 12, 16, 17, 21, 23]),
    (26076, 2, [1, 2, 5, 9, 12, 14, 15, 17, 21, 23]),
    (27292, 2, [1, 3, 9, 12, 18, 21, 22, 26, 28, 29]),
    (27728, 4, [8, 10, 13, 14, 17, 18, 24, 25, 26, 27]),
    (27732, 2, [7, 9, 13, 14, 17, 18, 24, 25, 26, 27]),
    (27760, 4, [4, 8, 10, 13, 14, 19, 24, 25, 26, 27]),
    (27764, 2, [4, 7, 9, 13, 14, 19, 24, 25, 26, 27]),
    (27984, 4, [2, 5, 8, 10, 13, 14, 17, 18, 24, 27]),
    (27988, 2, [2, 5, 7, 9, 13, 14, 17, 18, 24, 27]),
    (28002, 1, [0, 2, 6, 10, 13, 15, 16, 19, 24, 27]),
    (28016, 4, [2, 4, 5, 8, 10, 13, 14, 19, 24, 27]),
    (28020, 2, [2, 4, 5, 7, 9, 13, 14, 19, 24, 27]),
    (28240, 4, [3, 8, 10, 13, 17, 18, 23, 24, 25, 26]),
    (28244, 2, [3, 7, 9, 13, 17, 18, 23, 24, 25, 26]),
    (28272, 4, [3, 4, 8, 10, 13, 19, 23, 24, 25, 26]),
    (28276, 2, [3, 4, 7, 9, 13, 19, 23, 24, 25, 26]),
    (28496, 4, [2, 3, 5, 8, 10, 13, 17, 18, 23, 24]),
    (28500, 2, [2, 3, 5, 7, 9, 13, 17, 18, 23, 24]),
    (28528, 4, [2, 3, 4, 5, 8, 10, 13, 19, 23, 24]),
    (28532, 2, [2, 3, 4, 5, 7, 9, 13, 19, 23, 24]),
    (29340, 2, [1, 3, 6, 15, 19, 22, 26, 27, 28, 29]),
    (29708, 2, [6, 8, 11, 16, 19, 20, 22, 24, 25, 26]),
    (29724, 2, [6, 11, 14, 15, 19, 20, 22, 24, 25, 26]),
    (29772, 2, [6, 8, 11, 16, 17, 19, 21, 24, 25, 26]),
    (29788, 2, [6, 11, 14, 15, 17, 19, 21, 24, 25, 26]),
    (29836, 2, [1, 6, 8, 16, 19, 20, 22, 23, 25, 26]),
    (29852, 2, [1, 6, 14, 15, 19, 20, 22, 23, 25, 26]),
    (29900, 2, [1, 6, 8, 16, 17, 19, 21, 23, 25, 26]),
    (29916, 2, [1, 6, 14, 15, 17, 19, 21, 23, 25, 26]),
    (29964, 2, [2, 5, 6, 8, 11, 16, 19, 20, 22, 24]),
    (29980, 2, [2, 5, 6, 11, 14, 15, 19, 20, 22, 24]),
    (30028, 2, [2, 5, 6, 8, 11, 16, 17, 19, 21, 24]),
    (30044, 2, [2, 5, 6, 11, 14, 15, 17, 19, 21, 24]),
    (30050, 1, [0, 2, 9, 10, 12, 13, 16, 18, 21, 24]),
    (30092, 2, [1, 2, 5, 6, 8, 16, 19, 20, 22, 23]),
    (30108, 2, [1, 2, 5, 6, 14, 15, 19, 20, 22, 23]),
    (30156, 2, [1, 2, 5, 6, 8, 16, 17, 19, 21, 23]),
    (30172, 2, [1, 2, 5, 6, 14, 15, 17, 19, 21, 23]),
    (31388, 2, [1, 3, 6, 18, 19, 21, 22, 26, 28, 29]),
    (32098, 1, [0, 2, 9, 10, 12, 13, 15, 16, 24, 27]),
    (32126, 1, [0, 2, 11, 14, 24, 27]),
    (32508, 2, [1, 3, 4, 6, 25, 26])]

def clauseProp (p : Fin 30 → Prop) : List (Fin 30) → Prop
  | [] => False
  | [i] => p i
  | i :: j :: is => p i ∨ clauseProp p (j :: is)

lemma exists_mem_clauseProp (p : Fin 30 → Prop) (is : List (Fin 30)) :
    (∃ i ∈ is, p i) ↔ clauseProp p is := by
  induction is with
  | nil => simp [clauseProp]
  | cons i is ih =>
    cases is with
    | nil => simp [clauseProp]
    | cons j js => simpa [clauseProp] using (or_congr (Iff.rfl : p i ↔ p i) ih)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma no_constraint_assignment (p : Fin 30 → Prop)
    (hR : ∀ t : Fin 60,
      (p (tripleAt t).2.1 ∨ p (tripleAt t).2.2.1 ∨ p (tripleAt t).2.2.2) ∧
      (¬p (tripleAt t).2.1 ∨ ¬p (tripleAt t).2.2.1 ∨ ¬p (tripleAt t).2.2.2))
    (hC : ∀ c : Fin 202,
      (∃ i ∈ (cutAt c).2.2, p i) ∧ (∃ i ∈ (cutAt c).2.2, ¬p i)) : False := by
  apply no_cnfProp p
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨(hR 0).1, (hR 0).2⟩, ⟨(hR 1).1, (hR 1).2⟩⟩, ⟨⟨(hR 2).1, (hR 2).2⟩, ⟨(hR 3).1, (hR 3).2⟩⟩⟩, ⟨⟨⟨(hR 4).1, (hR 4).2⟩, ⟨(hR 5).1, (hR 5).2⟩⟩, ⟨⟨(hR 6).1, (hR 6).2⟩, ⟨(hR 7).1, (hR 7).2⟩⟩⟩⟩, ⟨⟨⟨⟨(hR 8).1, (hR 8).2⟩, ⟨(hR 9).1, (hR 9).2⟩⟩, ⟨⟨(hR 10).1, (hR 10).2⟩, ⟨(hR 11).1, (hR 11).2⟩⟩⟩, ⟨⟨⟨(hR 12).1, (hR 12).2⟩, ⟨(hR 13).1, (hR 13).2⟩⟩, ⟨⟨(hR 14).1, (hR 14).2⟩, ⟨(hR 15).1, (hR 15).2⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨(hR 16).1, (hR 16).2⟩, ⟨(hR 17).1, (hR 17).2⟩⟩, ⟨⟨(hR 18).1, (hR 18).2⟩, ⟨(hR 19).1, (hR 19).2⟩⟩⟩, ⟨⟨⟨(hR 20).1, (hR 20).2⟩, ⟨(hR 21).1, (hR 21).2⟩⟩, ⟨⟨(hR 22).1, (hR 22).2⟩, ⟨(hR 23).1, (hR 23).2⟩⟩⟩⟩, ⟨⟨⟨⟨(hR 24).1, (hR 24).2⟩, ⟨(hR 25).1, (hR 25).2⟩⟩, ⟨⟨(hR 26).1, (hR 26).2⟩, ⟨(hR 27).1, (hR 27).2⟩⟩⟩, ⟨⟨⟨(hR 28).1, (hR 28).2⟩, ⟨(hR 29).1, (hR 29).2⟩⟩, ⟨⟨(hR 30).1, (hR 30).2⟩, ⟨(hR 31).1, ⟨(hR 31).2, (hR 32).1⟩⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨⟨(hR 32).2, (hR 33).1⟩, ⟨(hR 33).2, (hR 34).1⟩⟩, ⟨⟨(hR 34).2, (hR 35).1⟩, ⟨(hR 35).2, (hR 36).1⟩⟩⟩, ⟨⟨⟨(hR 36).2, (hR 37).1⟩, ⟨(hR 37).2, (hR 38).1⟩⟩, ⟨⟨(hR 38).2, (hR 39).1⟩, ⟨(hR 39).2, (hR 40).1⟩⟩⟩⟩, ⟨⟨⟨⟨(hR 40).2, (hR 41).1⟩, ⟨(hR 41).2, (hR 42).1⟩⟩, ⟨⟨(hR 42).2, (hR 43).1⟩, ⟨(hR 43).2, (hR 44).1⟩⟩⟩, ⟨⟨⟨(hR 44).2, (hR 45).1⟩, ⟨(hR 45).2, (hR 46).1⟩⟩, ⟨⟨(hR 46).2, (hR 47).1⟩, ⟨(hR 47).2, ⟨(hR 48).1, (hR 48).2⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨(hR 49).1, (hR 49).2⟩, ⟨(hR 50).1, (hR 50).2⟩⟩, ⟨⟨(hR 51).1, (hR 51).2⟩, ⟨(hR 52).1, (hR 52).2⟩⟩⟩, ⟨⟨⟨(hR 53).1, (hR 53).2⟩, ⟨(hR 54).1, (hR 54).2⟩⟩, ⟨⟨(hR 55).1, (hR 55).2⟩, ⟨(hR 56).1, (hR 56).2⟩⟩⟩⟩, ⟨⟨⟨⟨(hR 57).1, (hR 57).2⟩, ⟨(hR 58).1, (hR 58).2⟩⟩, ⟨⟨(hR 59).1, (hR 59).2⟩, ⟨((exists_mem_clauseProp p _).mp (hC 0).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 0).2)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 1).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 1).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 2).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 2).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 3).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 3).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 4).1), ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 4).2), ((exists_mem_clauseProp p _).mp (hC 5).1)⟩⟩⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 5).2), ((exists_mem_clauseProp p _).mp (hC 6).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 6).2), ((exists_mem_clauseProp p _).mp (hC 7).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 7).2), ((exists_mem_clauseProp p _).mp (hC 8).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 8).2), ((exists_mem_clauseProp p _).mp (hC 9).1)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 9).2), ((exists_mem_clauseProp p _).mp (hC 10).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 10).2), ((exists_mem_clauseProp p _).mp (hC 11).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 11).2), ((exists_mem_clauseProp p _).mp (hC 12).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 12).2), ((exists_mem_clauseProp p _).mp (hC 13).1)⟩⟩⟩⟩, ⟨⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 13).2), ((exists_mem_clauseProp p _).mp (hC 14).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 14).2), ((exists_mem_clauseProp p _).mp (hC 15).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 15).2), ((exists_mem_clauseProp p _).mp (hC 16).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 16).2), ((exists_mem_clauseProp p _).mp (hC 17).1)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 17).2), ((exists_mem_clauseProp p _).mp (hC 18).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 18).2), ((exists_mem_clauseProp p _).mp (hC 19).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 19).2), ((exists_mem_clauseProp p _).mp (hC 20).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 20).2), ((exists_mem_clauseProp p _).mp (hC 21).1)⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 21).2), ((exists_mem_clauseProp p _).mp (hC 22).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 22).2), ((exists_mem_clauseProp p _).mp (hC 23).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 23).2), ((exists_mem_clauseProp p _).mp (hC 24).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 24).2), ((exists_mem_clauseProp p _).mp (hC 25).1)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 25).2), ((exists_mem_clauseProp p _).mp (hC 26).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 26).2), ((exists_mem_clauseProp p _).mp (hC 27).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 27).2), ((exists_mem_clauseProp p _).mp (hC 28).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 28).2), ((exists_mem_clauseProp p _).mp (hC 29).1)⟩⟩⟩⟩, ⟨⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 29).2), ((exists_mem_clauseProp p _).mp (hC 30).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 30).2), ((exists_mem_clauseProp p _).mp (hC 31).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 31).2), ((exists_mem_clauseProp p _).mp (hC 32).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 32).2), ((exists_mem_clauseProp p _).mp (hC 33).1)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 33).2), ((exists_mem_clauseProp p _).mp (hC 34).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 34).2), ((exists_mem_clauseProp p _).mp (hC 35).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 35).2), ((exists_mem_clauseProp p _).mp (hC 36).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 36).2), ⟨((exists_mem_clauseProp p _).mp (hC 37).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 37).2)⟩⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 38).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 38).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 39).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 39).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 40).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 40).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 41).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 41).2)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 42).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 42).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 43).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 43).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 44).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 44).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 45).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 45).2)⟩⟩⟩⟩, ⟨⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 46).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 46).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 47).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 47).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 48).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 48).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 49).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 49).2)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 50).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 50).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 51).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 51).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 52).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 52).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 53).1), ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 53).2), ((exists_mem_clauseProp p _).mp (hC 54).1)⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 54).2), ((exists_mem_clauseProp p _).mp (hC 55).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 55).2), ((exists_mem_clauseProp p _).mp (hC 56).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 56).2), ((exists_mem_clauseProp p _).mp (hC 57).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 57).2), ((exists_mem_clauseProp p _).mp (hC 58).1)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 58).2), ((exists_mem_clauseProp p _).mp (hC 59).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 59).2), ((exists_mem_clauseProp p _).mp (hC 60).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 60).2), ((exists_mem_clauseProp p _).mp (hC 61).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 61).2), ((exists_mem_clauseProp p _).mp (hC 62).1)⟩⟩⟩⟩, ⟨⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 62).2), ((exists_mem_clauseProp p _).mp (hC 63).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 63).2), ((exists_mem_clauseProp p _).mp (hC 64).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 64).2), ((exists_mem_clauseProp p _).mp (hC 65).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 65).2), ((exists_mem_clauseProp p _).mp (hC 66).1)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 66).2), ((exists_mem_clauseProp p _).mp (hC 67).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 67).2), ((exists_mem_clauseProp p _).mp (hC 68).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 68).2), ((exists_mem_clauseProp p _).mp (hC 69).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 69).2), ⟨((exists_mem_clauseProp p _).mp (hC 70).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 70).2)⟩⟩⟩⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 71).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 71).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 72).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 72).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 73).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 73).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 74).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 74).2)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 75).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 75).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 76).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 76).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 77).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 77).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 78).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 78).2)⟩⟩⟩⟩, ⟨⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 79).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 79).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 80).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 80).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 81).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 81).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 82).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 82).2)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 83).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 83).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 84).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 84).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 85).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 85).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 86).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 86).2)⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 87).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 87).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 88).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 88).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 89).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 89).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 90).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 90).2)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 91).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 91).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 92).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 92).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 93).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 93).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 94).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 94).2)⟩⟩⟩⟩, ⟨⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 95).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 95).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 96).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 96).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 97).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 97).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 98).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 98).2)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 99).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 99).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 100).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 100).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 101).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 101).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 102).1), ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 102).2), ((exists_mem_clauseProp p _).mp (hC 103).1)⟩⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 103).2), ((exists_mem_clauseProp p _).mp (hC 104).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 104).2), ((exists_mem_clauseProp p _).mp (hC 105).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 105).2), ((exists_mem_clauseProp p _).mp (hC 106).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 106).2), ((exists_mem_clauseProp p _).mp (hC 107).1)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 107).2), ((exists_mem_clauseProp p _).mp (hC 108).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 108).2), ((exists_mem_clauseProp p _).mp (hC 109).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 109).2), ((exists_mem_clauseProp p _).mp (hC 110).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 110).2), ((exists_mem_clauseProp p _).mp (hC 111).1)⟩⟩⟩⟩, ⟨⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 111).2), ((exists_mem_clauseProp p _).mp (hC 112).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 112).2), ((exists_mem_clauseProp p _).mp (hC 113).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 113).2), ((exists_mem_clauseProp p _).mp (hC 114).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 114).2), ((exists_mem_clauseProp p _).mp (hC 115).1)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 115).2), ((exists_mem_clauseProp p _).mp (hC 116).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 116).2), ((exists_mem_clauseProp p _).mp (hC 117).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 117).2), ((exists_mem_clauseProp p _).mp (hC 118).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 118).2), ⟨((exists_mem_clauseProp p _).mp (hC 119).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 119).2)⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 120).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 120).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 121).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 121).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 122).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 122).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 123).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 123).2)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 124).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 124).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 125).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 125).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 126).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 126).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 127).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 127).2)⟩⟩⟩⟩, ⟨⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 128).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 128).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 129).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 129).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 130).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 130).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 131).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 131).2)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 132).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 132).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 133).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 133).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 134).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 134).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 135).1), ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 135).2), ((exists_mem_clauseProp p _).mp (hC 136).1)⟩⟩⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 136).2), ((exists_mem_clauseProp p _).mp (hC 137).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 137).2), ((exists_mem_clauseProp p _).mp (hC 138).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 138).2), ((exists_mem_clauseProp p _).mp (hC 139).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 139).2), ((exists_mem_clauseProp p _).mp (hC 140).1)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 140).2), ((exists_mem_clauseProp p _).mp (hC 141).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 141).2), ((exists_mem_clauseProp p _).mp (hC 142).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 142).2), ((exists_mem_clauseProp p _).mp (hC 143).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 143).2), ((exists_mem_clauseProp p _).mp (hC 144).1)⟩⟩⟩⟩, ⟨⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 144).2), ((exists_mem_clauseProp p _).mp (hC 145).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 145).2), ((exists_mem_clauseProp p _).mp (hC 146).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 146).2), ((exists_mem_clauseProp p _).mp (hC 147).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 147).2), ((exists_mem_clauseProp p _).mp (hC 148).1)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 148).2), ((exists_mem_clauseProp p _).mp (hC 149).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 149).2), ((exists_mem_clauseProp p _).mp (hC 150).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 150).2), ((exists_mem_clauseProp p _).mp (hC 151).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 151).2), ((exists_mem_clauseProp p _).mp (hC 152).1)⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 152).2), ((exists_mem_clauseProp p _).mp (hC 153).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 153).2), ((exists_mem_clauseProp p _).mp (hC 154).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 154).2), ((exists_mem_clauseProp p _).mp (hC 155).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 155).2), ((exists_mem_clauseProp p _).mp (hC 156).1)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 156).2), ((exists_mem_clauseProp p _).mp (hC 157).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 157).2), ((exists_mem_clauseProp p _).mp (hC 158).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 158).2), ((exists_mem_clauseProp p _).mp (hC 159).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 159).2), ((exists_mem_clauseProp p _).mp (hC 160).1)⟩⟩⟩⟩, ⟨⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 160).2), ((exists_mem_clauseProp p _).mp (hC 161).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 161).2), ((exists_mem_clauseProp p _).mp (hC 162).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 162).2), ((exists_mem_clauseProp p _).mp (hC 163).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 163).2), ((exists_mem_clauseProp p _).mp (hC 164).1)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 164).2), ((exists_mem_clauseProp p _).mp (hC 165).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 165).2), ((exists_mem_clauseProp p _).mp (hC 166).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 166).2), ((exists_mem_clauseProp p _).mp (hC 167).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 167).2), ⟨((exists_mem_clauseProp p _).mp (hC 168).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 168).2)⟩⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 169).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 169).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 170).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 170).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 171).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 171).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 172).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 172).2)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 173).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 173).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 174).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 174).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 175).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 175).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 176).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 176).2)⟩⟩⟩⟩, ⟨⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 177).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 177).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 178).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 178).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 179).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 179).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 180).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 180).2)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp p _).mp (hC 181).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 181).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 182).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 182).2)⟩⟩, ⟨⟨((exists_mem_clauseProp p _).mp (hC 183).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 183).2)⟩, ⟨((exists_mem_clauseProp p _).mp (hC 184).1), ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 184).2), ((exists_mem_clauseProp p _).mp (hC 185).1)⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 185).2), ((exists_mem_clauseProp p _).mp (hC 186).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 186).2), ((exists_mem_clauseProp p _).mp (hC 187).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 187).2), ((exists_mem_clauseProp p _).mp (hC 188).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 188).2), ((exists_mem_clauseProp p _).mp (hC 189).1)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 189).2), ((exists_mem_clauseProp p _).mp (hC 190).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 190).2), ((exists_mem_clauseProp p _).mp (hC 191).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 191).2), ((exists_mem_clauseProp p _).mp (hC 192).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 192).2), ((exists_mem_clauseProp p _).mp (hC 193).1)⟩⟩⟩⟩, ⟨⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 193).2), ((exists_mem_clauseProp p _).mp (hC 194).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 194).2), ((exists_mem_clauseProp p _).mp (hC 195).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 195).2), ((exists_mem_clauseProp p _).mp (hC 196).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 196).2), ((exists_mem_clauseProp p _).mp (hC 197).1)⟩⟩⟩, ⟨⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 197).2), ((exists_mem_clauseProp p _).mp (hC 198).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 198).2), ((exists_mem_clauseProp p _).mp (hC 199).1)⟩⟩, ⟨⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 199).2), ((exists_mem_clauseProp p _).mp (hC 200).1)⟩, ⟨((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 200).2), ⟨((exists_mem_clauseProp p _).mp (hC 201).1), ((exists_mem_clauseProp (fun i => ¬ p i) _).mp (hC 201).2)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

#print axioms no_constraint_assignment

open SimpleGraph

lemma edgeEnds_distinct (i : Fin 30) : (edgeEnds i).1 ≠ (edgeEnds i).2 := by
  revert i
  decide

def exampleGraph : SimpleGraph (Fin 15) where
  Adj u v := ∃ i : Fin 30, edgeEnds i = (u, v) ∨ edgeEnds i = (v, u)
  symm := by
    intro u v h
    obtain ⟨i, h⟩ := h
    exact ⟨i, h.symm⟩
  loopless := by
    intro v h
    obtain ⟨i, h | h⟩ := h
    all_goals
      have hd := edgeEnds_distinct i
      rw [h] at hd
      exact hd rfl

instance : DecidableRel exampleGraph.Adj := fun u v =>
  inferInstanceAs (Decidable (∃ i : Fin 30, edgeEnds i = (u, v) ∨ edgeEnds i = (v, u)))

lemma edgeEnds_adj (i : Fin 30) : exampleGraph.Adj (edgeEnds i).1 (edgeEnds i).2 :=
  ⟨i, Or.inl (Prod.eta (edgeEnds i)).symm⟩

def otherEnd (v : Fin 15) (i : Fin 30) : Fin 15 :=
  if (edgeEnds i).1 = v then (edgeEnds i).2 else (edgeEnds i).1

lemma edge_color_at_vertex (H : SimpleGraph (Fin 15)) (v : Fin 15) (i : Fin 30)
    (hi : (edgeEnds i).1 = v ∨ (edgeEnds i).2 = v) :
    H.Adj (edgeEnds i).1 (edgeEnds i).2 ↔ H.Adj v (otherEnd v i) := by
  rcases hi with hi | hi
  · subst v
    simp [otherEnd]
  · subst v
    simp [otherEnd, edgeEnds_distinct, SimpleGraph.adj_comm]

lemma triple_valid (t : Fin 60) :
    let v := (tripleAt t).1
    let i := (tripleAt t).2.1
    let j := (tripleAt t).2.2.1
    let k := (tripleAt t).2.2.2
    ((edgeEnds i).1 = v ∨ (edgeEnds i).2 = v) ∧
    ((edgeEnds j).1 = v ∨ (edgeEnds j).2 = v) ∧
    ((edgeEnds k).1 = v ∨ (edgeEnds k).2 = v) ∧
    otherEnd v i ≠ otherEnd v j ∧ otherEnd v i ≠ otherEnd v k ∧
    otherEnd v j ≠ otherEnd v k := by
  revert t
  decide

set_option maxRecDepth 100000 in
lemma cut_valid (c : Fin 202) :
    let S := (cutAt c).1
    S.getLsbD (cutAt c).2.1.val = true ∧ S.getLsbD 0 = false ∧
    ∀ i : Fin 30, i ∈ (cutAt c).2.2 ↔
      S.getLsbD (edgeEnds i).1.val ≠ S.getLsbD (edgeEnds i).2.val := by
  revert c
  decide

open scoped Classical in
lemma degree_two_not_three {V : Type*} [Fintype V] (H : SimpleGraph V)
    (hH : H.IsRegularOfDegree 2) (v a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : H.Adj v a) (hb : H.Adj v b) (hc : H.Adj v c) : False := by
  classical
  have hsub : ({a, b, c} : Finset V) ⊆ H.neighborFinset v := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact (H.mem_neighborFinset v _).mpr ha
    · exact (H.mem_neighborFinset v _).mpr hb
    · exact (H.mem_neighborFinset v _).mpr hc
  have hcount := Finset.card_le_card hsub
  rw [H.card_neighborFinset_eq_degree, hH v] at hcount
  simp [hab, hac, hbc] at hcount

lemma connected_crosses_cut (H : SimpleGraph (Fin 15)) (hHG : H ≤ exampleGraph)
    (hH : H.Connected) (c : Fin 202) :
    ∃ i ∈ (cutAt c).2.2, H.Adj (edgeEnds i).1 (edgeEnds i).2 := by
  classical
  by_contra hn
  have hvalid := cut_valid c
  let S := (cutAt c).1
  have hcol : ∀ u v, H.Adj u v → S.getLsbD u.val = S.getLsbD v.val := by
    intro u v huv
    obtain ⟨i, hi | hi⟩ := hHG huv
    · have h1 := congrArg Prod.fst hi
      have h2 := congrArg Prod.snd hi
      have hip : H.Adj (edgeEnds i).1 (edgeEnds i).2 := by simpa only [h1, h2] using huv
      have hni : i ∉ (cutAt c).2.2 := fun hmem => hn ⟨i, hmem, hip⟩
      have he := not_ne_iff.mp (hni ∘ (hvalid.2.2 i).mpr)
      simpa only [h1, h2] using he
    · have h1 := congrArg Prod.fst hi
      have h2 := congrArg Prod.snd hi
      have hip : H.Adj (edgeEnds i).1 (edgeEnds i).2 := by simpa only [h1, h2] using huv.symm
      have hni : i ∉ (cutAt c).2.2 := fun hmem => hn ⟨i, hmem, hip⟩
      have he := not_ne_iff.mp (hni ∘ (hvalid.2.2 i).mpr)
      simpa only [h1, h2] using he.symm
  have hpath : ∀ {u v : Fin 15} (p : H.Walk u v), S.getLsbD u.val = S.getLsbD v.val := by
    intro u v p
    induction p with
    | nil => rfl
    | cons h p ih => exact (hcol _ _ h).trans ih
  obtain ⟨p⟩ := hH.preconnected (cutAt c).2.1 0
  have he := hpath p
  change (cutAt c).1.getLsbD (cutAt c).2.1.val = (cutAt c).1.getLsbD 0 at he
  rw [hvalid.1, hvalid.2.1] at he
  cases he

open scoped Classical in
lemma no_two_connected_regular_subgraphs (H K : SimpleGraph (Fin 15))
    (hHG : H ≤ exampleGraph) (hKG : K ≤ exampleGraph)
    (hHc : H.Connected) (hKc : K.Connected)
    (hHr : H.IsRegularOfDegree 2) (hKr : K.IsRegularOfDegree 2)
    (hdis : Disjoint H.edgeSet K.edgeSet)
    (hcover : exampleGraph.edgeSet ⊆ H.edgeSet ∪ K.edgeSet) : False := by
  classical
  apply no_constraint_assignment (fun i => H.Adj (edgeEnds i).1 (edgeEnds i).2)
  · intro t
    obtain ⟨hi, hj, hk, hij, hik, hjk⟩ := triple_valid t
    have hnotH : ¬ (H.Adj (edgeEnds (tripleAt t).2.1).1 (edgeEnds (tripleAt t).2.1).2 ∧
        H.Adj (edgeEnds (tripleAt t).2.2.1).1 (edgeEnds (tripleAt t).2.2.1).2 ∧
        H.Adj (edgeEnds (tripleAt t).2.2.2).1 (edgeEnds (tripleAt t).2.2.2).2) := by
      rintro ⟨ha, hb, hc⟩
      exact degree_two_not_three H hHr (tripleAt t).1 _ _ _ hij hik hjk
        ((edge_color_at_vertex H _ _ hi).mp ha)
        ((edge_color_at_vertex H _ _ hj).mp hb)
        ((edge_color_at_vertex H _ _ hk).mp hc)
    refine ⟨?_, by tauto⟩
    by_contra hn
    push_neg at hn
    have hK : ∀ i : Fin 30, ¬ H.Adj (edgeEnds i).1 (edgeEnds i).2 →
        K.Adj (edgeEnds i).1 (edgeEnds i).2 := by
      intro i hni
      exact (hcover (show s((edgeEnds i).1, (edgeEnds i).2) ∈ exampleGraph.edgeSet from
        edgeEnds_adj i)).resolve_left hni
    exact degree_two_not_three K hKr (tripleAt t).1 _ _ _ hij hik hjk
      ((edge_color_at_vertex K _ _ hi).mp (hK _ hn.1))
      ((edge_color_at_vertex K _ _ hj).mp (hK _ hn.2.1))
      ((edge_color_at_vertex K _ _ hk).mp (hK _ hn.2.2))
  · intro c
    refine ⟨connected_crosses_cut H hHG hHc c, ?_⟩
    obtain ⟨i, hi, hKi⟩ := connected_crosses_cut K hKG hKc c
    refine ⟨i, hi, ?_⟩
    intro hHi
    exact Set.disjoint_left.mp hdis
      (show s((edgeEnds i).1, (edgeEnds i).2) ∈ H.edgeSet from hHi) hKi

#print axioms no_two_connected_regular_subgraphs
end ThreeCycleObstruction

open SimpleGraph
namespace ThreeCycleObstruction
open scoped Fin.NatCast

lemma exampleGraph_regular : exampleGraph.IsRegularOfDegree 4 := by
  unfold SimpleGraph.IsRegularOfDegree
  decide

def c0 : exampleGraph.Walk 0 0 :=
  .cons (show exampleGraph.Adj 0 1 by decide) (.cons (show exampleGraph.Adj 1 8 by decide) (.cons (show exampleGraph.Adj 8 0 by decide) (.nil)))

lemma c0_cycle : c0.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def c1 : exampleGraph.Walk 0 0 :=
  .cons (show exampleGraph.Adj 0 7 by decide) (.cons (show exampleGraph.Adj 7 3 by decide) (.cons (show exampleGraph.Adj 3 2 by decide) (.cons (show exampleGraph.Adj 2 12 by decide) (.cons (show exampleGraph.Adj 12 1 by decide) (.cons (show exampleGraph.Adj 1 5 by decide) (.cons (show exampleGraph.Adj 5 6 by decide) (.cons (show exampleGraph.Adj 6 13 by decide) (.cons (show exampleGraph.Adj 13 10 by decide) (.cons (show exampleGraph.Adj 10 14 by decide) (.cons (show exampleGraph.Adj 14 4 by decide) (.cons (show exampleGraph.Adj 4 11 by decide) (.cons (show exampleGraph.Adj 11 9 by decide) (.cons (show exampleGraph.Adj 9 0 by decide) (.nil))))))))))))))

lemma c1_cycle : c1.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def c2 : exampleGraph.Walk 2 2 :=
  .cons (show exampleGraph.Adj 2 4 by decide) (.cons (show exampleGraph.Adj 4 9 by decide) (.cons (show exampleGraph.Adj 9 7 by decide) (.cons (show exampleGraph.Adj 7 13 by decide) (.cons (show exampleGraph.Adj 13 3 by decide) (.cons (show exampleGraph.Adj 3 12 by decide) (.cons (show exampleGraph.Adj 12 5 by decide) (.cons (show exampleGraph.Adj 5 11 by decide) (.cons (show exampleGraph.Adj 11 6 by decide) (.cons (show exampleGraph.Adj 6 10 by decide) (.cons (show exampleGraph.Adj 10 8 by decide) (.cons (show exampleGraph.Adj 8 14 by decide) (.cons (show exampleGraph.Adj 14 2 by decide) (.nil)))))))))))))

lemma c2_cycle : c2.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

lemma cycles_edge_disjoint :
    c0.edges.Disjoint c1.edges ∧ c0.edges.Disjoint c2.edges ∧ c1.edges.Disjoint c2.edges := by
  simp only [List.disjoint_iff_ne, c0, c1, c2, Walk.edges_cons, Walk.edges_nil,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  repeat' apply And.intro
  all_goals decide

lemma cycles_cover : ∀ u v : Fin 15, exampleGraph.Adj u v ↔
    s(u, v) ∈ c0.edges ∨ s(u, v) ∈ c1.edges ∨ s(u, v) ∈ c2.edges := by decide

lemma cycles_pairwise_intersect :
    (∃ v, v ∈ c0.support ∧ v ∈ c1.support) ∧
    (∃ v, v ∈ c0.support ∧ v ∈ c2.support) ∧
    (∃ v, v ∈ c1.support ∧ v ∈ c2.support) := by decide

lemma cycles_no_triple_intersection :
    ∀ v : Fin 15, ¬ (v ∈ c0.support ∧ v ∈ c1.support ∧ v ∈ c2.support) := by decide

set_option maxHeartbeats 1000000 in
open scoped Classical in
lemma no_two_cycle_subgraphs (H K : exampleGraph.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hdis : Disjoint H.edgeSet K.edgeSet)
    (hcover : H.edgeSet ∪ K.edgeSet = exampleGraph.edgeSet) : False := by
  classical
  have hdiff : exampleGraph \ H.spanningCoe = K.spanningCoe := by
    apply SimpleGraph.edgeSet_injective
    rw [SimpleGraph.edgeSet_sdiff]
    change exampleGraph.edgeSet \ H.edgeSet = K.edgeSet
    rw [← hcover]
    apply Set.Subset.antisymm
    · rintro e ⟨heH | heK, he⟩
      · exact False.elim (he heH)
      · exact heK
    · intro e heK
      exact ⟨Or.inr heK, fun heH => Set.disjoint_left.mp hdis heH heK⟩
  have hverts : ∀ v, v ∈ H.verts ∧ v ∈ K.verts := by
    intro v
    have hs := degree_sdiff_add exampleGraph H.spanningCoe H.spanningCoe_le v
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hs
    rw [hdiff] at hs
    have hHdeg := regular_two_spanning_degree H (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hH.2) v
    have hKdeg := regular_two_spanning_degree K (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hK.2) v
    have hGdeg := exampleGraph_regular v
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      at hs hHdeg hKdeg hGdeg
    by_cases hvH : v ∈ H.verts <;> by_cases hvK : v ∈ K.verts
    · exact ⟨hvH, hvK⟩
    all_goals simp only [hvH, hvK, if_true, if_false] at hHdeg hKdeg; omega
  have hHC : H.spanningCoe.Connected ∧ H.spanningCoe.IsRegularOfDegree 2 := by
    apply cycle_property_map_iso (H.spanningCoeEquivCoeOfSpanning (fun v => (hverts v).1)).symm
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hH
  have hKC : K.spanningCoe.Connected ∧ K.spanningCoe.IsRegularOfDegree 2 := by
    apply cycle_property_map_iso (K.spanningCoeEquivCoeOfSpanning (fun v => (hverts v).2)).symm
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hK
  apply no_two_connected_regular_subgraphs H.spanningCoe K.spanningCoe
    H.spanningCoe_le K.spanningCoe_le hHC.1 hKC.1
  · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hHC.2
  · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hKC.2
  · exact hdis
  · exact hcover.ge

lemma no_two_cycle_walks {u v : Fin 15} (a : exampleGraph.Walk u u)
    (b : exampleGraph.Walk v v) (ha : a.IsCycle) (hb : b.IsCycle)
    (hdis : a.edges.Disjoint b.edges)
    (hcover : ∀ e, (e ∈ a.edges ∨ e ∈ b.edges) ↔
      (e ∈ c0.edges ∨ e ∈ c1.edges ∨ e ∈ c2.edges)) : False := by
  classical
  apply no_two_cycle_subgraphs a.toSubgraph b.toSubgraph
    (by simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular exampleGraph ha)
    (by simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular exampleGraph hb)
  · apply Set.disjoint_left.mpr
    intro e hea heb
    exact hdis ((a.mem_edges_toSubgraph).mp hea) ((b.mem_edges_toSubgraph).mp heb)
  · ext e
    induction e using Sym2.ind with | h x y =>
    change (s(x, y) ∈ a.toSubgraph.edgeSet ∨ s(x, y) ∈ b.toSubgraph.edgeSet) ↔ _
    rw [a.mem_edges_toSubgraph, b.mem_edges_toSubgraph, hcover]
    exact (cycles_cover x y).symm

/-- The three supplied edge-disjoint cycles have nonempty pairwise intersections
and no triple intersection, yet cannot be replaced by two cycles with the same
edge union. This refutes only that proposed local rule, not the linear-bound
conjecture. -/
theorem three_cycle_pairwise_rule_obstruction :
    c0.IsCycle ∧ c1.IsCycle ∧ c2.IsCycle ∧
    c0.edges.Disjoint c1.edges ∧ c0.edges.Disjoint c2.edges ∧ c1.edges.Disjoint c2.edges ∧
    (∃ x, x ∈ c0.support ∧ x ∈ c1.support) ∧
    (∃ x, x ∈ c0.support ∧ x ∈ c2.support) ∧
    (∃ x, x ∈ c1.support ∧ x ∈ c2.support) ∧
    (∀ x, ¬ (x ∈ c0.support ∧ x ∈ c1.support ∧ x ∈ c2.support)) ∧
    ¬ ∃ (u v : Fin 15) (a : exampleGraph.Walk u u) (b : exampleGraph.Walk v v),
      a.IsCycle ∧ b.IsCycle ∧ a.edges.Disjoint b.edges ∧
      ∀ e, (e ∈ a.edges ∨ e ∈ b.edges) ↔
        (e ∈ c0.edges ∨ e ∈ c1.edges ∨ e ∈ c2.edges) := by
  refine ⟨c0_cycle, c1_cycle, c2_cycle, cycles_edge_disjoint.1,
    cycles_edge_disjoint.2.1, cycles_edge_disjoint.2.2,
    cycles_pairwise_intersect.1, cycles_pairwise_intersect.2.1,
    cycles_pairwise_intersect.2.2, cycles_no_triple_intersection, ?_⟩
  rintro ⟨u, v, a, b, ha, hb, hdis, hcover⟩
  exact no_two_cycle_walks a b ha hb hdis hcover

#print axioms three_cycle_pairwise_rule_obstruction
end ThreeCycleObstruction

end Erdos184Work



/- Unbounded clean-ring recombination. This is a partial structural result,
not a proof of the uniform linear decomposition conjecture. -/

open SimpleGraph
namespace Erdos184Work
namespace LongRing
variable {V : Type*} {G : SimpleGraph V}

lemma split_cycle_paths {u v : V} (c : G.Walk u u) (hc : c.IsCycle)
    (hv : v ∈ c.support) (huv : u ≠ v) :
    ∃ p q : G.Walk u v,
      p.IsPath ∧ q.IsPath ∧ p.edges.Disjoint q.edges ∧
      (∀ e, (e ∈ p.edges ∨ e ∈ q.edges) ↔ e ∈ c.edges) ∧
      (∀ x, (x ∈ p.support ∨ x ∈ q.support) ↔ x ∈ c.support) := by
  classical
  let p := c.takeUntil v hv
  let q := (c.dropUntil v hv).reverse
  refine ⟨p, q, hc.isPath_takeUntil hv,
    (cycle_dropUntil_isPath hc hv huv).reverse, ?_, ?_, ?_⟩
  · simpa only [p, q, Walk.edges_reverse, List.disjoint_reverse_right] using
      hc.isTrail.disjoint_edges_takeUntil_dropUntil hv
  · intro e
    simp only [p, q, Walk.edges_reverse, List.mem_reverse]
    rw [← List.mem_append, ← Walk.edges_append, Walk.take_spec]
  · intro x
    simp only [p, q, Walk.support_reverse, List.mem_reverse]
    rw [← Walk.mem_support_append_iff, Walk.take_spec]

/-- An open chain in which a new cycle meets the previous union only at the
joining vertex. The edge-disjointness field is explicit for convenient use
inside a given decomposition. -/
inductive CleanCycleChain (G : SimpleGraph V) : V → V → List G.Subgraph → Prop
  | single {u v : V} (c : G.Walk u u) (hc : c.IsCycle)
      (hv : v ∈ c.support) (huv : u ≠ v) :
      CleanCycleChain G u v [c.toSubgraph]
  | extend {u v w : V} {L : List G.Subgraph}
      (hL : CleanCycleChain G u v L) (c : G.Walk v v) (hc : c.IsCycle)
      (hw : w ∈ c.support) (hvw : v ≠ w)
      (hinter : ∀ H ∈ L, ∀ x, x ∈ H.verts → x ∈ c.support → x = v)
      (hdis : ∀ H ∈ L, Disjoint H.edgeSet c.toSubgraph.edgeSet) :
      CleanCycleChain G u w (L ++ [c.toSubgraph])

lemma CleanCycleChain.nonempty {u v : V} {L : List G.Subgraph}
    (hL : CleanCycleChain G u v L) : L ≠ [] := by
  cases hL <;> simp

lemma CleanCycleChain.mem_cycle {u v : V} {L : List G.Subgraph}
    (hL : CleanCycleChain G u v L) {H : G.Subgraph} (hH : H ∈ L) :
    ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧ c.toSubgraph = H := by
  induction hL with
  | single c hc hv huv =>
    have he : c.toSubgraph = H := (List.mem_singleton.mp hH).symm
    exact ⟨_, c, hc, he⟩
  | extend hL c hc hw hvw hi hd ih =>
    rcases List.mem_append.mp hH with hH | hH
    · exact ih hH
    · exact ⟨_, c, hc, (List.mem_singleton.mp hH).symm⟩

lemma CleanCycleChain.nodup {u v : V} {L : List G.Subgraph}
    (hL : CleanCycleChain G u v L) : L.Nodup := by
  induction hL with
  | single => exact List.nodup_singleton _
  | extend hL c hc hw hvw hi hd ih =>
    rw [List.nodup_append]
    refine ⟨ih, List.nodup_singleton _, ?_⟩
    intro H hH K hK
    have heK : K = c.toSubgraph := List.mem_singleton.mp hK
    subst K
    intro he
    have hec : s(_, c.snd) ∈ c.toSubgraph.edgeSet := c.toSubgraph_adj_snd hc.not_nil
    exact Set.disjoint_left.mp (hd H hH) (he ▸ hec) hec

lemma CleanCycleChain.end_mem {u v : V} {L : List G.Subgraph}
    (hL : CleanCycleChain G u v L) : ∃ H ∈ L, v ∈ H.verts := by
  cases hL with
  | single c hc hv huv => exact ⟨_, List.mem_singleton_self _, c.mem_verts_toSubgraph.mpr hv⟩
  | extend hL c hc hw hvw hi hd =>
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), c.mem_verts_toSubgraph.mpr hw⟩

lemma CleanCycleChain.start_mem {u v : V} {L : List G.Subgraph}
    (hL : CleanCycleChain G u v L) : ∃ H ∈ L, u ∈ H.verts := by
  induction hL with
  | single c hc hv huv =>
    exact ⟨_, List.mem_singleton_self _, c.mem_verts_toSubgraph.mpr c.start_mem_support⟩
  | extend hL c hc hw hvw hi hd ih =>
    obtain ⟨H, hH, hu⟩ := ih
    exact ⟨H, List.mem_append_left _ hH, hu⟩

lemma CleanCycleChain.end_unique {u v : V} {L : List G.Subgraph}
    (hL : CleanCycleChain G u v L) :
    ∃ H ∈ L, v ∈ H.verts ∧ ∀ K ∈ L, v ∈ K.verts → K = H := by
  cases hL with
  | single c hc hv huv =>
    refine ⟨_, List.mem_singleton_self _, c.mem_verts_toSubgraph.mpr hv, ?_⟩
    intro K hK _
    exact List.mem_singleton.mp hK
  | extend hL c hc hw hvw hi hd =>
    refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
      c.mem_verts_toSubgraph.mpr hw, ?_⟩
    intro K hK hvK
    rcases List.mem_append.mp hK with hK | hK
    · exact (hvw (hi K hK _ hvK hw).symm).elim
    · exact List.mem_singleton.mp hK

/-- Trim a clean chain after its last contact with a set which meets each
constituent cycle in at most one vertex. -/
lemma CleanCycleChain.trim_to_set {u v : V} {L : List G.Subgraph}
    (hL : CleanCycleChain G u v L) (X : Set V) (hv : v ∉ X)
    (hcontact : ∃ H ∈ L, ∃ x ∈ H.verts, x ∈ X)
    (hlinear : ∀ H ∈ L, ∀ x ∈ H.verts, ∀ y ∈ H.verts, x ∈ X → y ∈ X → x = y) :
    ∃ w L', CleanCycleChain G w v L' ∧ (∀ H ∈ L', H ∈ L) ∧ w ∈ X ∧
      ∀ H ∈ L', ∀ x ∈ H.verts, x ∈ X → x = w := by
  classical
  induction hL with
  | @single v c hc hvc huv =>
    obtain ⟨H, hH, w, hwH, hwX⟩ := hcontact
    have heH : H = c.toSubgraph := List.mem_singleton.mp hH
    subst H
    let d := c.rotate (c.mem_verts_toSubgraph.mp hwH)
    have hsub : d.toSubgraph = c.toSubgraph := c.toSubgraph_rotate (c.mem_verts_toSubgraph.mp hwH)
    have hdv : v ∈ d.support := (c.mem_support_rotate_iff (c.mem_verts_toSubgraph.mp hwH)).mpr hvc
    have hd : CleanCycleChain G w v [c.toSubgraph] := by
      rw [← hsub]
      exact .single d (hc.rotate _) hdv (ne_of_mem_of_not_mem hwX hv)
    refine ⟨w, [c.toSubgraph], hd, fun _ h => h, hwX, ?_⟩
    intro H hH x hx hxX
    have heH : H = c.toSubgraph := List.mem_singleton.mp hH
    subst H
    exact hlinear _ (List.mem_singleton_self _) x hx w hwH hxX hwX
  | @extend t v L hL c hc hvc htv hinter hdis ih =>
    by_cases hcx : ∃ w ∈ c.support, w ∈ X
    · obtain ⟨w, hwc, hwX⟩ := hcx
      let d := c.rotate hwc
      have hsub : d.toSubgraph = c.toSubgraph := c.toSubgraph_rotate hwc
      have hdv : v ∈ d.support := (c.mem_support_rotate_iff hwc).mpr hvc
      have hd : CleanCycleChain G w v [c.toSubgraph] := by
        rw [← hsub]
        exact .single d (hc.rotate _) hdv (ne_of_mem_of_not_mem hwX hv)
      refine ⟨w, [c.toSubgraph], hd, fun H h => List.mem_append_right _ h, hwX, ?_⟩
      intro H hH x hx hxX
      have heH : H = c.toSubgraph := List.mem_singleton.mp hH
      subst H
      exact hlinear _ (List.mem_append_right _ (List.mem_singleton_self _))
        x hx w (c.mem_verts_toSubgraph.mpr hwc) hxX hwX
    · have hcn : ∀ x ∈ c.support, x ∉ X := by
        intro x hx hxX
        exact hcx ⟨x, hx, hxX⟩
      have ht : t ∉ X := hcn t c.start_mem_support
      have hpcontact : ∃ H ∈ L, ∃ x ∈ H.verts, x ∈ X := by
        obtain ⟨H, hH, x, hx, hxX⟩ := hcontact
        rcases List.mem_append.mp hH with hH | hH
        · exact ⟨H, hH, x, hx, hxX⟩
        · have heH : H = c.toSubgraph := List.mem_singleton.mp hH
          subst H
          exact (hcn x (c.mem_verts_toSubgraph.mp hx) hxX).elim
      obtain ⟨w, L', hwL, hsub, hwX, hmeet⟩ := ih ht hpcontact
        (fun H hH => hlinear H (List.mem_append_left _ hH))
      refine ⟨w, L' ++ [c.toSubgraph],
        hwL.extend c hc hvc htv (fun H hH => hinter H (hsub H hH))
          (fun H hH => hdis H (hsub H hH)), ?_, hwX, ?_⟩
      · intro H hH
        rcases List.mem_append.mp hH with hH | hH
        · exact List.mem_append_left _ (hsub H hH)
        · exact List.mem_append_right _ hH
      · intro H hH x hx hxX
        rcases List.mem_append.mp hH with hH | hH
        · exact hmeet H hH x hx hxX
        · have heH : H = c.toSubgraph := List.mem_singleton.mp hH
          subst H
          exact (hcn x (c.mem_verts_toSubgraph.mp hx) hxX).elim

set_option maxHeartbeats 1000000 in
lemma CleanCycleChain.two_paths {u v : V} {L : List G.Subgraph}
    (hL : CleanCycleChain G u v L) :
    ∃ p q : G.Walk u v,
      p.IsPath ∧ q.IsPath ∧ p.edges.Disjoint q.edges ∧
      (∀ e, (e ∈ p.edges ∨ e ∈ q.edges) ↔ ∃ H ∈ L, e ∈ H.edgeSet) ∧
      (∀ x, (x ∈ p.support ∨ x ∈ q.support) ↔ ∃ H ∈ L, x ∈ H.verts) := by
  induction hL with
  | single c hc hv huv =>
    obtain ⟨p, q, hp, hq, hpq, he, hs⟩ := split_cycle_paths c hc hv huv
    refine ⟨p, q, hp, hq, hpq, ?_, ?_⟩
    · intro e
      simpa only [List.mem_singleton, exists_eq_left, Walk.mem_edges_toSubgraph] using he e
    · intro x
      simpa only [List.mem_singleton, exists_eq_left, Walk.mem_verts_toSubgraph] using hs x
  | @extend v w L hL c hc hw hvw hinter hdis ih =>
    obtain ⟨p, q, hp, hq, hpq, he, hs⟩ := ih
    obtain ⟨r, s, hr, ht, hrs, hce, hcs⟩ := split_cycle_paths c hc hw hvw
    have hpr : ∀ x, x ∈ p.support → x ∈ r.support → x = v := by
      intro x hxp hxr
      obtain ⟨H, hH, hxH⟩ := (hs x).mp (Or.inl hxp)
      exact hinter H hH x hxH ((hcs x).mp (Or.inl hxr))
    have hqs : ∀ x, x ∈ q.support → x ∈ s.support → x = v := by
      intro x hxq hxs
      obtain ⟨H, hH, hxH⟩ := (hs x).mp (Or.inr hxq)
      exact hinter H hH x hxH ((hcs x).mp (Or.inr hxs))
    have hcross : ∀ e, (e ∈ p.edges ∨ e ∈ q.edges) →
        (e ∈ r.edges ∨ e ∈ s.edges) → False := by
      intro e hep her
      obtain ⟨H, hH, heH⟩ := (he e).mp hep
      exact Set.disjoint_left.mp (hdis H hH) heH
        (c.mem_edges_toSubgraph.mpr ((hce e).mp her))
    refine ⟨p.append r, q.append s,
      append_isPath_of_support_inter hp hr hpr,
      append_isPath_of_support_inter hq ht hqs, ?_, ?_, ?_⟩
    · simp only [Walk.edges_append]
      refine List.disjoint_append_left.mpr ⟨List.disjoint_append_right.mpr ⟨hpq, ?_⟩,
        List.disjoint_append_right.mpr ⟨?_, hrs⟩⟩
      · intro e hep hes
        exact hcross e (Or.inl hep) (Or.inr hes)
      · intro e her heq
        exact hcross e (Or.inr heq) (Or.inl her)
    · intro e
      have hec := hce e
      have heL := he e
      simp only [Walk.edges_append, List.mem_append, List.mem_singleton,
        or_and_right, exists_or, exists_eq_left, Walk.mem_edges_toSubgraph]
      rw [← heL, ← hec]
      exact or_or_or_comm
    · intro x
      have hsc := hcs x
      have hsL := hs x
      simp only [Walk.mem_support_append_iff, List.mem_append, List.mem_singleton,
        or_and_right, exists_or, exists_eq_left, Walk.mem_verts_toSubgraph]
      rw [← hsL, ← hsc]
      exact or_or_or_comm

/-- Closing an arbitrarily long clean cycle chain produces two simple cycles,
not merely two closed trails. -/
lemma CleanCycleChain.close {u v : V} {L : List G.Subgraph}
    (hL : CleanCycleChain G u v L) (huv : u ≠ v)
    (c : G.Walk v v) (hc : c.IsCycle) (hu : u ∈ c.support)
    (hinter : ∀ H ∈ L, ∀ x, x ∈ H.verts → x ∈ c.support → x = u ∨ x = v)
    (hdis : ∀ H ∈ L, Disjoint H.edgeSet c.toSubgraph.edgeSet) :
    ∃ a b : G.Walk u u,
      a.IsCycle ∧ b.IsCycle ∧ a.edges.Disjoint b.edges ∧
      ∀ e, (e ∈ a.edges ∨ e ∈ b.edges) ↔
        ∃ H ∈ L ++ [c.toSubgraph], e ∈ H.edgeSet := by
  obtain ⟨p, q, hp, hq, hpq, he, hs⟩ := hL.two_paths
  obtain ⟨r, s, hr, ht, hrs, hce, hcs⟩ := split_cycle_paths c hc hu huv.symm
  have hcross : ∀ e, (e ∈ p.edges ∨ e ∈ q.edges) →
      (e ∈ r.edges ∨ e ∈ s.edges) → False := by
    intro e hep her
    obtain ⟨H, hH, heH⟩ := (he e).mp hep
    exact Set.disjoint_left.mp (hdis H hH) heH
      (c.mem_edges_toSubgraph.mpr ((hce e).mp her))
  have hpr : ∀ x, x ∈ p.support → x ∈ r.support → x = u ∨ x = v := by
    intro x hxp hxr
    obtain ⟨H, hH, hxH⟩ := (hs x).mp (Or.inl hxp)
    exact hinter H hH x hxH ((hcs x).mp (Or.inl hxr))
  have hqs : ∀ x, x ∈ q.support → x ∈ s.support → x = u ∨ x = v := by
    intro x hxq hxs
    obtain ⟨H, hH, hxH⟩ := (hs x).mp (Or.inr hxq)
    exact hinter H hH x hxH ((hcs x).mp (Or.inr hxs))
  refine ⟨p.append r, q.append s,
    append_isCycle_of_support_inter hp hr huv (fun e hep her => hcross e (.inl hep) (.inl her)) hpr,
    append_isCycle_of_support_inter hq ht huv (fun e heq hes => hcross e (.inr heq) (.inr hes)) hqs,
    ?_, ?_⟩
  · simp only [Walk.edges_append]
    refine List.disjoint_append_left.mpr ⟨List.disjoint_append_right.mpr ⟨hpq, ?_⟩,
      List.disjoint_append_right.mpr ⟨?_, hrs⟩⟩
    · intro e hep hes
      exact hcross e (Or.inl hep) (Or.inr hes)
    · intro e her heq
      exact hcross e (Or.inr heq) (Or.inl her)
  · intro e
    have hec := hce e
    have heL := he e
    simp only [Walk.edges_append, List.mem_append, List.mem_singleton,
      or_and_right, exists_or, exists_eq_left, Walk.mem_edges_toSubgraph]
    rw [← heL, ← hec]
    exact or_or_or_comm

open scoped Classical in
lemma CleanCycleChain.improve [Fintype V] (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D)
    {u v : V} {L : List G.Subgraph}
    (hL : CleanCycleChain G u v L) (huv : u ≠ v)
    (c : G.Walk v v) (hc : c.IsCycle) (hu : u ∈ c.support)
    (hinter : ∀ H ∈ L, ∀ x, x ∈ H.verts → x ∈ c.support → x = u ∨ x = v)
    (hdis : ∀ H ∈ L, Disjoint H.edgeSet c.toSubgraph.edgeSet)
    (hmem : ∀ H ∈ L ++ [c.toSubgraph], H ∈ D)
    (hcard : 2 < (L ++ [c.toSubgraph]).toFinset.card) :
    ∃ D' : Finset G.Subgraph,
      (∀ H ∈ D', IsCycleOrEdge H.coe) ∧ IsDecomposition G D' ∧ D'.card < D.card := by
  classical
  obtain ⟨a, b, ha, hb, heab, hcover⟩ := hL.close huv c hc hu hinter hdis
  let A : Finset G.Subgraph := (L ++ [c.toSubgraph]).toFinset
  let B : Finset G.Subgraph := {a.toSubgraph, b.toSubgraph}
  have hAD : A ⊆ D := by
    intro H hH
    exact hmem H (List.mem_toFinset.mp hH)
  have hB : ∀ H ∈ B, IsCycleOrEdge H.coe := by
    intro H hH
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact Or.inl (by
        simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using cycle_coe_regular G ha)
    · exact Or.inl (by
        simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using cycle_coe_regular G hb)
  have hpairB : Set.PairwiseDisjoint (B : Set G.Subgraph) (fun H => H.edgeSet) := by
    have hset : Disjoint a.toSubgraph.edgeSet b.toSubgraph.edgeSet := by
      apply Set.disjoint_left.mpr
      intro e heA heB
      exact heab (a.mem_edges_toSubgraph.mp heA) (b.mem_edges_toSubgraph.mp heB)
    simp only [B, Finset.coe_insert, Finset.coe_singleton]
    apply (Set.pairwiseDisjoint_singleton _ _).insert
    intro H hH _
    have hH' : H = b.toSubgraph := Set.mem_singleton_iff.mp hH
    subst H
    exact hset
  have hcoverAB : (⋃ H ∈ A, H.edgeSet) = ⋃ H ∈ B, H.edgeSet := by
    ext e
    simpa [A, B, Walk.mem_edges_toSubgraph, or_and_right, exists_or, or_comm] using (hcover e).symm
  have hBcard : B.card ≤ 2 := by
    have h := Finset.card_insert_le a.toSubgraph {b.toSubgraph}
    simpa only [Finset.card_singleton] using h
  exact replace_decomposition_subfamily D A B hD hdec hAD hB hpairB hcoverAB
    (lt_of_le_of_lt hBcard hcard)

/-- Every pair of distinct constituent cycles meets in at most one vertex. -/
def LinearIntersections (D : Finset G.Subgraph) : Prop :=
  ∀ H ∈ D, ∀ K ∈ D, H ≠ K →
    ∀ x ∈ H.verts, ∀ y ∈ H.verts, x ∈ K.verts → y ∈ K.verts → x = y

open scoped Classical in
lemma CleanCycleChain.improve_of_contact [Fintype V] (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D)
    (hlinear : LinearIntersections D)
    {u t v : V} {L : List G.Subgraph} (hL : CleanCycleChain G u t L)
    (c : G.Walk t t) (hc : c.IsCycle) (hv : v ∈ c.support) (htv : t ≠ v)
    (hinter : ∀ H ∈ L, ∀ x, x ∈ H.verts → x ∈ c.support → x = t)
    (hdis : ∀ H ∈ L, Disjoint H.edgeSet c.toSubgraph.edgeSet)
    (k : G.Walk v v) (hk : k.IsCycle)
    (hmem : ∀ H ∈ L ++ [c.toSubgraph], H ∈ D)
    (hkD : k.toSubgraph ∈ D) (hknot : k.toSubgraph ∉ L ++ [c.toSubgraph])
    (hcontact : ∃ H ∈ L, ∃ x ∈ H.verts, x ∈ k.support) :
    ∃ D' : Finset G.Subgraph,
      (∀ H ∈ D', IsCycleOrEdge H.coe) ∧ IsDecomposition G D' ∧ D'.card < D.card := by
  classical
  have hneq : ∀ H ∈ L ++ [c.toSubgraph], H ≠ k.toSubgraph := by
    intro H hH he
    exact hknot (he ▸ hH)
  have hlin := fun H hH => hlinear H (hmem H hH) k.toSubgraph hkD (hneq H hH)
  have hc_mem : c.toSubgraph ∈ L ++ [c.toSubgraph] :=
    List.mem_append_right _ (List.mem_singleton_self _)
  have hck : ∀ x ∈ c.support, x ∈ k.support → x = v := by
    intro x hx hxk
    exact hlin _ hc_mem x (c.mem_verts_toSubgraph.mpr hx)
      v (c.mem_verts_toSubgraph.mpr hv) (k.mem_verts_toSubgraph.mpr hxk)
      (k.mem_verts_toSubgraph.mpr k.start_mem_support)
  have ht : t ∉ k.toSubgraph.verts := by
    intro htk
    exact htv (hck t c.start_mem_support (k.mem_verts_toSubgraph.mp htk))
  obtain ⟨w, L', hwL, hsub, hwk, hmeet⟩ := hL.trim_to_set k.toSubgraph.verts ht
    (by simpa only [Walk.mem_verts_toSubgraph] using hcontact)
    (fun H hH => hlin H (List.mem_append_left _ hH))
  have hwv : w ≠ v := by
    intro he
    obtain ⟨H, hH, hwH⟩ := hwL.start_mem
    have hwt := hinter H (hsub H hH) w hwH (he.symm ▸ hv)
    exact htv (hwt.symm.trans he)
  have hchain := hwL.extend c hc hv htv
    (fun H hH => hinter H (hsub H hH)) (fun H hH => hdis H (hsub H hH))
  apply hchain.improve D hD hdec hwv k hk (k.mem_verts_toSubgraph.mp hwk)
  · intro H hH x hx hxk
    rcases List.mem_append.mp hH with hH | hH
    · exact Or.inl (hmeet H hH x hx (k.mem_verts_toSubgraph.mpr hxk))
    · have heH := List.mem_singleton.mp hH
      subst H
      exact Or.inr (hck x (c.mem_verts_toSubgraph.mp hx) hxk)
  · intro H hH
    have hHL : H ∈ L ++ [c.toSubgraph] := by
      rcases List.mem_append.mp hH with hH | hH
      · exact List.mem_append_left _ (hsub H hH)
      · exact List.mem_append_right _ hH
    exact hdec.1 (hmem H hHL) hkD (hneq H hHL)
  · intro H hH
    rcases List.mem_append.mp hH with hH | hH
    · rcases List.mem_append.mp hH with hH | hH
      · exact hmem H (List.mem_append_left _ (hsub H hH))
      · exact hmem H (List.mem_append_right _ hH)
    · exact (List.mem_singleton.mp hH) ▸ hkD
  · have hn : (L' ++ [c.toSubgraph] ++ [k.toSubgraph]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hchain.nodup, List.nodup_singleton _, ?_⟩
      intro H hH K hK he
      have hK : K = k.toSubgraph := List.mem_singleton.mp hK
      subst K
      subst H
      rcases List.mem_append.mp hH with hH | hH
      · exact hknot (List.mem_append_left _ (hsub _ hH))
      · exact hknot (List.mem_append_right _ hH)
    rw [List.toFinset_card_of_nodup hn]
    have hpos := List.length_pos_iff.mpr hwL.nonempty
    simp only [List.length_append, List.length_singleton]
    omega

open scoped Classical in
lemma CleanCycleChain.extend_or_improve [Fintype V] (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D)
    (hlinear : LinearIntersections D)
    {u v w : V} {L : List G.Subgraph} (hL : CleanCycleChain G u v L)
    (k : G.Walk v v) (hk : k.IsCycle) (hw : w ∈ k.support) (hvw : v ≠ w)
    (hmem : ∀ H ∈ L, H ∈ D) (hkD : k.toSubgraph ∈ D) (hknot : k.toSubgraph ∉ L) :
    CleanCycleChain G u w (L ++ [k.toSubgraph]) ∨
    ∃ D' : Finset G.Subgraph,
      (∀ H ∈ D', IsCycleOrEdge H.coe) ∧ IsDecomposition G D' ∧ D'.card < D.card := by
  classical
  have hneq : ∀ H ∈ L, H ≠ k.toSubgraph := by
    intro H hH he
    exact hknot (he ▸ hH)
  have hd : ∀ H ∈ L, Disjoint H.edgeSet k.toSubgraph.edgeSet := by
    intro H hH
    exact hdec.1 (hmem H hH) hkD (hneq H hH)
  have hlin := fun H hH => hlinear H (hmem H hH) k.toSubgraph hkD (hneq H hH)
  have hmeet : (∀ H ∈ L, ∀ x ∈ H.verts, x ∈ k.support → x = v) ∨
      ∃ D' : Finset G.Subgraph,
        (∀ H ∈ D', IsCycleOrEdge H.coe) ∧ IsDecomposition G D' ∧ D'.card < D.card := by
    cases hL with
    | single c hc hv huv =>
      left
      intro H hH x hx hxk
      have heH := List.mem_singleton.mp hH
      subst H
      exact hlin _ (List.mem_singleton_self _) x hx v (c.mem_verts_toSubgraph.mpr hv)
        (k.mem_verts_toSubgraph.mpr hxk) (k.mem_verts_toSubgraph.mpr k.start_mem_support)
    | @extend t v L₀ hL c hc hv htv hinter hdis =>
      by_cases hcontact : ∃ H ∈ L₀, ∃ x ∈ H.verts, x ∈ k.support
      · exact Or.inr (hL.improve_of_contact D hD hdec hlinear c hc hv htv
          hinter hdis k hk hmem hkD hknot hcontact)
      · left
        intro H hH x hx hxk
        rcases List.mem_append.mp hH with hH | hH
        · exact (hcontact ⟨H, hH, x, hx, hxk⟩).elim
        · have heH := List.mem_singleton.mp hH
          subst H
          exact hlin _ (List.mem_append_right _ (List.mem_singleton_self _))
            x hx v (c.mem_verts_toSubgraph.mpr hv)
            (k.mem_verts_toSubgraph.mpr hxk) (k.mem_verts_toSubgraph.mpr k.start_mem_support)
  rcases hmeet with hmeet | himprove
  · exact Or.inl (hL.extend k hk hw hvw hmeet hd)
  · exact Or.inr himprove

open scoped Classical in
/-- A cycle family with singleton pairwise intersections, minimal among all
cycle-and-edge decompositions, cannot contain a nonempty incidence 2-core. -/
lemma minimal_linear_no_core [Fintype V] (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D)
    (hlinear : LinearIntersections D)
    (hwalk : ∀ H ∈ D, ∀ v ∈ H.verts,
      ∃ c : G.Walk v v, c.IsCycle ∧ c.toSubgraph = H)
    (hmin : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, IsCycleOrEdge H.coe) → IsDecomposition G E → D.card ≤ E.card)
    (A : Finset G.Subgraph) (S : Set V) (hAD : A ⊆ D) (hA : A.Nonempty)
    (hcycle : ∀ H ∈ A, ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ u ∈ H.verts ∧ v ∈ H.verts)
    (hvertex : ∀ v ∈ S, ∃ H ∈ A, ∃ K ∈ A, H ≠ K ∧ v ∈ H.verts ∧ v ∈ K.verts) :
    False := by
  classical
  have hstep : ∀ {u v L}, CleanCycleChain G u v L →
      (∀ H ∈ L, H ∈ A) → v ∈ S →
      ∃ w L', CleanCycleChain G u w L' ∧ (∀ H ∈ L', H ∈ A) ∧
        w ∈ S ∧ L.length < L'.length := by
    intro u v L hL hmem hvS
    obtain ⟨H, hHL, hvH, hunique⟩ := hL.end_unique
    obtain ⟨H₁, h₁, H₂, h₂, h₁₂, hv₁, hv₂⟩ := hvertex v hvS
    have hother : ∃ K ∈ A, K ≠ H ∧ v ∈ K.verts := by
      by_cases he : H₁ = H
      · exact ⟨H₂, h₂, fun he₂ => h₁₂ (he.trans he₂.symm), hv₂⟩
      · exact ⟨H₁, h₁, he, hv₁⟩
    obtain ⟨K, hKA, hKH, hvK⟩ := hother
    have hKnot : K ∉ L := fun hKL => hKH (hunique K hKL hvK)
    obtain ⟨u', huS, v', hvS', huv', huK, hvK'⟩ := hcycle K hKA
    have hw : ∃ w ∈ S, w ∈ K.verts ∧ v ≠ w := by
      by_cases he : v = u'
      · exact ⟨v', hvS', hvK', he ▸ huv'⟩
      · exact ⟨u', huS, huK, he⟩
    obtain ⟨w, hwS, hwK, hvw⟩ := hw
    obtain ⟨k, hk, heK⟩ := hwalk K (hAD hKA) v hvK
    have hkw : w ∈ k.support := k.mem_verts_toSubgraph.mp (heK.symm ▸ hwK)
    rcases hL.extend_or_improve D hD hdec hlinear k hk hkw hvw
        (fun H hH => hAD (hmem H hH)) (heK.symm ▸ hAD hKA) (heK.symm ▸ hKnot) with
      hnew | ⟨E, hE, hEdec, hlt⟩
    · refine ⟨w, L ++ [k.toSubgraph], hnew, ?_, hwS, ?_⟩
      · intro J hJ
        rcases List.mem_append.mp hJ with hJ | hJ
        · exact hmem J hJ
        · have hJK : J = K := (List.mem_singleton.mp hJ).trans heK
          exact hJK.symm ▸ hKA
      · simp only [List.length_append, List.length_singleton]
        omega
    · exact (not_lt_of_ge (hmin E hE hEdec) hlt).elim
  have hgrow : ∀ n : ℕ, ∃ u v L, CleanCycleChain G u v L ∧
      (∀ H ∈ L, H ∈ A) ∧ v ∈ S ∧ n ≤ L.length := by
    intro n
    induction n with
    | zero =>
      obtain ⟨H, hH⟩ := hA
      obtain ⟨u, huS, v, hvS, huv, huH, hvH⟩ := hcycle H hH
      obtain ⟨c, hc, heH⟩ := hwalk H (hAD hH) u huH
      refine ⟨u, v, [c.toSubgraph], .single c hc
        (c.mem_verts_toSubgraph.mp (heH.symm ▸ hvH)) huv, ?_, hvS, Nat.zero_le _⟩
      intro K hK
      have hKH : K = H := (List.mem_singleton.mp hK).trans heH
      exact hKH.symm ▸ hH
    | succ n ih =>
      obtain ⟨u, v, L, hL, hmem, hvS, hn⟩ := ih
      obtain ⟨w, L', hL', hmem', hwS, hlen⟩ := hstep hL hmem hvS
      exact ⟨u, w, L', hL', hmem', hwS, by omega⟩
  obtain ⟨u, v, L, hL, hmem, hS, hlen⟩ := hgrow (A.card + 1)
  have hbound : L.length ≤ A.card := by
    rw [← List.toFinset_card_of_nodup hL.nodup]
    exact Finset.card_le_card (fun H hH => hmem H (List.mem_toFinset.mp hH))
  omega

open scoped Classical in
lemma regular_cycle_walk_at [Fintype V] (H : G.Subgraph)
    (hconn : H.coe.Connected) (hreg : H.coe.IsRegularOfDegree 2)
    (v : V) (hv : v ∈ H.verts) :
    ∃ c : G.Walk v v, c.IsCycle ∧ c.toSubgraph = H := by
  classical
  have hcyc : H.coe.IsCycles := by
    intro w _
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hreg w
  let v' : H.verts := ⟨v, hv⟩
  have hn : (H.coe.neighborSet v').Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    have h := hreg v'
    simp only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at h
    change (H.coe.neighborSet v').ncard = 2 at h
    exact h.trans_ne (by decide)
  obtain ⟨p, hp, hverts⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := H.coe.connectedComponentMk v') (by simp) hn
  have hall : ∀ w : H.verts, w ∈ p.toSubgraph.verts := by
    intro w
    rw [hverts, SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq]
    exact hconn.preconnected w v'
  have hpTop : p.toSubgraph = ⊤ := by
    apply SimpleGraph.Subgraph.ext
    · exact Set.eq_univ_of_forall hall
    · funext w z
      exact propext (hp.adj_toSubgraph_iff_of_isCycles hcyc (hall w) z)
  refine ⟨p.map H.hom, hp.map Subtype.val_injective, ?_⟩
  rw [Walk.toSubgraph_map, hpTop, SimpleGraph.Subgraph.map_hom_top]

/-- Bipartite incidence graph of the vertices and pieces of a decomposition. -/
def incidenceGraph (D : Finset G.Subgraph) : SimpleGraph (V ⊕ D) where
  Adj
    | .inl v, .inr H => v ∈ H.val.verts
    | .inr H, .inl v => v ∈ H.val.verts
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> exact id
  loopless := by intro x; cases x <;> exact id

lemma cycle_two_neighbors {X : Type*} {I : SimpleGraph X} {a x : X}
    {p : I.Walk a a} (hp : p.IsCycle) (hx : x ∈ p.support) :
    ∃ y z, y ≠ z ∧ I.Adj x y ∧ I.Adj x z ∧ y ∈ p.support ∧ z ∈ p.support := by
  classical
  obtain ⟨y, hy, z, hz, hyz⟩ := (Set.one_lt_ncard (Walk.finite_neighborSet_toSubgraph p)).mp
    (show 1 < (p.toSubgraph.neighborSet x).ncard by
      rw [hp.ncard_neighborSet_toSubgraph_eq_two hx]; omega)
  exact ⟨y, z, hyz, p.toSubgraph.adj_sub hy, p.toSubgraph.adj_sub hz,
    p.mem_verts_toSubgraph.mp (p.toSubgraph.neighborSet_subset_verts x hy),
    p.mem_verts_toSubgraph.mp (p.toSubgraph.neighborSet_subset_verts x hz)⟩

open scoped Classical in
lemma minimal_linear_incidence_acyclic [Fintype V] (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) (hlinear : LinearIntersections D)
    (hmin : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, IsCycleOrEdge H.coe) → IsDecomposition G E → D.card ≤ E.card) :
    (incidenceGraph D).IsAcyclic := by
  classical
  intro a p hp
  let S : Set V := {v | Sum.inl v ∈ p.support}
  let A : Finset G.Subgraph := D.filter (fun H => ∃ hH : H ∈ D,
    Sum.inr (⟨H, hH⟩ : D) ∈ p.support)
  have hAD : A ⊆ D := Finset.filter_subset _ _
  have hmemA : ∀ H : D, H.val ∈ A ↔ Sum.inr H ∈ p.support := by
    intro H
    constructor
    · intro h
      obtain ⟨_, _, h⟩ := Finset.mem_filter.mp h
      exact h
    · intro h
      exact Finset.mem_filter.mpr ⟨H.property, H.property, h⟩
  have hcycle : ∀ H ∈ A, ∃ u ∈ S, ∃ v ∈ S,
      u ≠ v ∧ u ∈ H.verts ∧ v ∈ H.verts := by
    intro H hH
    have hx := (hmemA ⟨H, hAD hH⟩).mp hH
    obtain ⟨y, z, hyz, hxy, hxz, hy, hz⟩ := cycle_two_neighbors hp hx
    cases y with
    | inr K => exact hxy.elim
    | inl u =>
      cases z with
      | inr K => exact hxz.elim
      | inl v => exact ⟨u, hy, v, hz, fun he => hyz (congrArg Sum.inl he), hxy, hxz⟩
  have hvertex : ∀ v ∈ S, ∃ H ∈ A, ∃ K ∈ A,
      H ≠ K ∧ v ∈ H.verts ∧ v ∈ K.verts := by
    intro v hv
    obtain ⟨y, z, hyz, hxy, hxz, hy, hz⟩ := cycle_two_neighbors hp hv
    cases y with
    | inl w => exact hxy.elim
    | inr H =>
      cases z with
      | inl w => exact hxz.elim
      | inr K =>
        exact ⟨H.val, (hmemA H).mpr hy, K.val, (hmemA K).mpr hz,
          fun he => hyz (congrArg Sum.inr (Subtype.ext he)), hxy, hxz⟩
  have hA : A.Nonempty := by
    cases a with
    | inr H => exact ⟨H.val, (hmemA H).mpr p.start_mem_support⟩
    | inl v =>
      obtain ⟨H, hH, _⟩ := hvertex v p.start_mem_support
      exact ⟨H, hH⟩
  have hvalid : ∀ H ∈ D, IsCycleOrEdge H.coe := by
    intro H hH
    exact Or.inl (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hD H hH)
  exact minimal_linear_no_core D hvalid hdec hlinear
    (fun H hH => regular_cycle_walk_at H (hD H hH).1 (hD H hH).2)
    hmin A S hAD hA hcycle hvertex

open scoped Classical in
lemma incidence_degree [Fintype V] (D : Finset G.Subgraph) (H : D) :
    (incidenceGraph D).degree (Sum.inr H) = Nat.card H.val.verts := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  change ((incidenceGraph D).neighborSet (Sum.inr H)).ncard = H.val.verts.ncard
  have he : (incidenceGraph D).neighborSet (Sum.inr H) = Sum.inl '' H.val.verts := by
    ext x
    cases x <;> simp [SimpleGraph.mem_neighborSet, incidenceGraph]
  rw [he, Set.ncard_image_of_injective _ Sum.inl_injective]

open scoped Classical in
lemma incidence_card_edges [Fintype V] (D : Finset G.Subgraph) :
    (incidenceGraph D).edgeFinset.card = ∑ H : D, Nat.card H.val.verts := by
  classical
  let s : Finset (V ⊕ D) := Finset.univ.map Function.Embedding.inl
  let t : Finset (V ⊕ D) := Finset.univ.map Function.Embedding.inr
  have hb : (incidenceGraph D).IsBipartiteWith (s : Set (V ⊕ D)) (t : Set (V ⊕ D)) := by
    constructor
    · apply Set.disjoint_left.mpr
      intro x hxS hxT
      cases x <;> simp [s, t] at *
    · intro x y hxy
      cases x <;> cases y <;> simp_all [s, t, incidenceGraph]
  have hc := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hb
  rw [← hc]
  simp only [t, Finset.sum_map, Function.Embedding.inr_apply, incidence_degree]

open scoped Classical in
lemma cycle_incidence_lower_bound [Fintype V] (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    3 * D.card ≤ (incidenceGraph D).edgeFinset.card := by
  classical
  have hverts : ∀ H : D, 3 ≤ Nat.card H.val.verts := by
    intro H
    obtain ⟨v⟩ := (hD H.val H.property).1.nonempty
    have hdeg := H.val.coe.degree_lt_card_verts v
    have hreg := (hD H.val H.property).2 v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hdeg hreg
    omega
  rw [incidence_card_edges]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun H _ => hverts H)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    smul_eq_mul, mul_comm] using hsum

open scoped Classical in
/-- The conjectured sharp bound holds for a minimum cycle decomposition if
its constituent cycles have singleton pairwise intersections. -/
lemma minimal_linear_decomposition_bound [Fintype V] (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) (hlinear : LinearIntersections D)
    (hmin : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, IsCycleOrEdge H.coe) → IsDecomposition G E → D.card ≤ E.card) :
    2 * D.card ≤ Fintype.card V := by
  classical
  have hacyc := minimal_linear_incidence_acyclic D hD hdec hlinear hmin
  have hupper := acyclic_card_edges_le (incidenceGraph D) hacyc
  have hlower := cycle_incidence_lower_bound D hD
  simp only [Fintype.card_sum, Fintype.card_coe] at hupper
  omega

open scoped Classical in
lemma minimal_linear_decomposition_strict_bound [Fintype V] [Nonempty V]
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) (hlinear : LinearIntersections D)
    (hmin : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, IsCycleOrEdge H.coe) → IsDecomposition G E → D.card ≤ E.card) :
    2 * D.card < Fintype.card V := by
  classical
  have hacyc := minimal_linear_incidence_acyclic D hD hdec hlinear hmin
  have hupper := acyclic_card_edges_lt (incidenceGraph D) hacyc
  have hlower := cycle_incidence_lower_bound D hD
  simp only [Fintype.card_sum, Fintype.card_coe] at hupper
  omega

#print axioms CleanCycleChain.close
#print axioms CleanCycleChain.improve
#print axioms CleanCycleChain.extend_or_improve
#print axioms minimal_linear_no_core
#print axioms minimal_linear_incidence_acyclic
#print axioms minimal_linear_decomposition_strict_bound
end LongRing
end Erdos184Work



/- Sparse-cut reduction. These are partial results, not a uniform cycle bound. -/
open Filter SimpleGraph
namespace Erdos184Work
namespace SparseCuts
universe u

open scoped Classical in
lemma piece_property_map_injective {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H) (hf : Function.Injective f)
    (K : G.Subgraph) (hK : IsCycleOrEdge K.coe) : IsCycleOrEdge (K.map f).coe := by
  classical
  rcases hK with hK | hK
  · exact Or.inl (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using cycle_property_map_injective f hf K (by
          simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
            ← Nat.card_eq_fintype_card] using hK))
  · right
    have he := (subgraphMapInjective f hf K).card_edgeFinset_eq
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at he hK ⊢
    exact he.symm.trans hK

open scoped Classical in
lemma map_decomposition_injective {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H) (hf : Function.Injective f)
    (D : Finset G.Subgraph) (hD : ∀ K ∈ D, IsCycleOrEdge K.coe)
    (hdec : IsDecomposition G D) :
    ∃ E : Finset H.Subgraph,
      (∀ K ∈ E, IsCycleOrEdge K.coe) ∧
      Set.PairwiseDisjoint (E : Set H.Subgraph) (fun K => K.edgeSet) ∧
      (⋃ K ∈ E, K.edgeSet) = Sym2.map f '' G.edgeSet ∧ E.card ≤ D.card := by
  classical
  let E := D.image (SimpleGraph.Subgraph.map f)
  refine ⟨E, ?_, ?_, ?_, Finset.card_image_le⟩
  · intro K hK
    obtain ⟨K', hK', rfl⟩ := Finset.mem_image.mp hK
    exact piece_property_map_injective f hf K' (hD K' hK')
  · intro K hK L hL hne
    obtain ⟨K', hK', rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨L', hL', rfl⟩ := Finset.mem_image.mp hL
    change Disjoint (K'.map f).edgeSet (L'.map f).edgeSet
    rw [SimpleGraph.Subgraph.edgeSet_map, SimpleGraph.Subgraph.edgeSet_map]
    apply Set.disjoint_left.mpr
    rintro e ⟨a, ha, rfl⟩ ⟨b, hb, heq⟩
    have hba : b = a := Sym2.map.injective hf heq
    subst b
    exact Set.disjoint_left.mp (hdec.1 hK' hL' (by
      intro h
      exact hne (congrArg (SimpleGraph.Subgraph.map f) h))) ha hb
  · ext e
    constructor
    · intro he
      obtain ⟨K, he⟩ := Set.mem_iUnion.mp he
      obtain ⟨hK, heK⟩ := Set.mem_iUnion.mp he
      obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
      rw [SimpleGraph.Subgraph.edgeSet_map] at heK
      obtain ⟨a, ha, rfl⟩ := heK
      exact ⟨a, L.edgeSet_subset ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      rw [← hdec.2] at ha
      obtain ⟨K, ha⟩ := Set.mem_iUnion.mp ha
      obtain ⟨hK, ha⟩ := Set.mem_iUnion.mp ha
      refine Set.mem_iUnion.mpr ⟨K.map f, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_image.mpr ⟨K, hK, rfl⟩
      · rw [SimpleGraph.Subgraph.edgeSet_map]
        exact ⟨a, ha, rfl⟩

open scoped Classical in
lemma lift_decomposition_spanningCoe {V : Type*} [Fintype V] {s : Set V}
    (G : SimpleGraph s) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D) :
    ∃ E : Finset G.spanningCoe.Subgraph,
      (∀ H ∈ E, IsCycleOrEdge H.coe) ∧ IsDecomposition G.spanningCoe E ∧
      E.card ≤ D.card := by
  classical
  obtain ⟨E, hE, hpE, heE, hcard⟩ := map_decomposition_injective
    (SimpleGraph.Embedding.spanningCoe G).toHom Subtype.val_injective D hD hdec
  refine ⟨E, hE, ⟨hpE, heE.trans ?_⟩, hcard⟩
  exact (SimpleGraph.edgeSet_map _ G).symm

lemma spanningCoe_induce_adj {V : Type*} (G : SimpleGraph V) (s : Set V) (v w : V) :
    (G.induce s).spanningCoe.Adj v w ↔ G.Adj v w ∧ v ∈ s ∧ w ∈ s := by
  simp only [SimpleGraph.map_adj, SimpleGraph.induce_adj]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact ⟨hab, a.property, b.property⟩
  · rintro ⟨h, hv, hw⟩
    exact ⟨⟨v, hv⟩, ⟨w, hw⟩, h, rfl, rfl⟩

open scoped Classical in
set_option maxHeartbeats 1000000 in
lemma decompose_across_cut {V : Type*} [Fintype V] (G : SimpleGraph V) (s : Set V)
    (D₁ : Finset (G.induce s).Subgraph) (D₂ : Finset (G.induce sᶜ).Subgraph)
    (h₁ : ∀ H ∈ D₁, IsCycleOrEdge H.coe) (hdec₁ : IsDecomposition (G.induce s) D₁)
    (h₂ : ∀ H ∈ D₂, IsCycleOrEdge H.coe) (hdec₂ : IsDecomposition (G.induce sᶜ) D₂) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card ≤ D₁.card + D₂.card + (G.between s sᶜ).edgeFinset.card := by
  classical
  let H := (G.induce s).spanningCoe
  let K := (G.induce sᶜ).spanningCoe
  have hH : H ≤ G := G.spanningCoe_induce_le s
  have hK : K ≤ G := G.spanningCoe_induce_le sᶜ
  have hHK : Disjoint H.edgeSet K.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heH heK
    induction e using Sym2.ind with | h v w =>
    have hv := ((spanningCoe_induce_adj G s v w).mp heH).2.1
    have hnv := ((spanningCoe_induce_adj G sᶜ v w).mp heK).2.1
    exact hnv hv
  obtain ⟨A, hA, hdecA, hcA⟩ := lift_decomposition_spanningCoe (G.induce s) D₁ (by
    simpa only [IsCycleOrEdge, SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.edgeFinset_card,
      ← Nat.card_eq_fintype_card] using h₁) hdec₁
  obtain ⟨B, hB, hdecB, hcB⟩ := lift_decomposition_spanningCoe (G.induce sᶜ) D₂ (by
    simpa only [IsCycleOrEdge, SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.edgeFinset_card,
      ← Nat.card_eq_fintype_card] using h₂) hdec₂
  obtain ⟨I, hI, hdecI, hcI⟩ := combine_decompositions (G := H ⊔ K)
    le_sup_left le_sup_right hHK (SimpleGraph.edgeSet_sup H K).symm A B hA hdecA hB hdecB
  let R := G.between s sᶜ
  have hIR : Disjoint (H ⊔ K).edgeSet R.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heI heR
    induction e using Sym2.ind with | h v w =>
    change H.Adj v w ∨ K.Adj v w at heI
    change G.Adj v w ∧ (v ∈ s ∧ w ∈ sᶜ ∨ v ∈ sᶜ ∧ w ∈ s) at heR
    simp only [H, K, spanningCoe_induce_adj, Set.mem_compl_iff] at heI heR
    tauto
  have hcover : (H ⊔ K).edgeSet ∪ R.edgeSet = G.edgeSet := by
    ext e
    induction e using Sym2.ind with | h v w =>
    change (H.Adj v w ∨ K.Adj v w) ∨ R.Adj v w ↔ G.Adj v w
    simp only [H, K, R, spanningCoe_induce_adj, SimpleGraph.between_adj, Set.mem_compl_iff]
    tauto
  obtain ⟨E, hE, hdecE, hcE⟩ := exists_edge_decomposition R
  obtain ⟨D, hD, hdecD, hcD⟩ := combine_decompositions (sup_le hH hK)
    SimpleGraph.between_le hIR hcover I E hI hdecI hE hdecE
  refine ⟨D, hD, hdecD, ?_⟩
  dsimp only [R] at hcE
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcE ⊢
  omega

open scoped Classical in
lemma edge_connected_of_cut_bound {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hcut : ∀ s : Set V, s.Nonempty → sᶜ.Nonempty → k ≤ (G.between s sᶜ).edgeFinset.card) :
    G.IsEdgeConnected k := by
  classical
  intro u v t ht
  by_contra huv
  let R := G.deleteEdges t
  let s : Set V := {w | R.Reachable u w}
  have hu : u ∈ s := SimpleGraph.Reachable.rfl
  have hv : v ∈ sᶜ := huv
  have hsub : (G.between s sᶜ).edgeSet ⊆ t := by
    intro e he
    induction e using Sym2.ind with | h a b =>
    change G.Adj a b ∧ (a ∈ s ∧ b ∈ sᶜ ∨ a ∈ sᶜ ∧ b ∈ s) at he
    by_contra hnot
    have hab : R.Adj a b := SimpleGraph.deleteEdges_adj.mpr ⟨he.1, hnot⟩
    rcases he.2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hb (ha.trans hab.reachable)
    · exact ha (hb.trans hab.symm.reachable)
  have hupper : (G.between s sᶜ).edgeFinset.card ≤ t.toFinset.card := by
    apply Finset.card_le_card
    intro e he
    exact Set.mem_toFinset.mpr (hsub (SimpleGraph.mem_edgeFinset.mp he))
  have ht' : t.toFinset.card < k := by
    have he := Set.encard_eq_coe_toFinset_card t
    rw [he] at ht
    exact_mod_cast ht
  have hlower := hcut s ⟨u, hu⟩ ⟨v, hv⟩
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hupper hlower
  omega

open scoped Classical in
lemma smallest_counterexample_cuts {V : Type u} [Fintype V] (G : SimpleGraph V) (C : ℕ)
    (hbad : ∀ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) →
      IsDecomposition G D → C * (Fintype.card V - 1) < D.card)
    (hsmall : ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      Fintype.card W < Fintype.card V →
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition R D ∧
        D.card ≤ C * (Fintype.card W - 1)) :
    ∀ s : Set V, s.Nonempty → sᶜ.Nonempty → C < (G.between s sᶜ).edgeFinset.card := by
  classical
  intro s hs hsc
  by_contra hcut
  have hcut' : (G.between s sᶜ).edgeFinset.card ≤ C := Nat.le_of_not_gt hcut
  obtain ⟨x, hx⟩ := hs
  obtain ⟨y, hy⟩ := hsc
  have hslt : Fintype.card s < Fintype.card V := Fintype.card_subtype_lt (x := y) hy
  have hsclt : Fintype.card (sᶜ : Set V) < Fintype.card V :=
    Fintype.card_subtype_lt (x := x) (by simpa using hx)
  obtain ⟨A, hA, hdecA, hcA⟩ := hsmall (G.induce s) hslt
  obtain ⟨B, hB, hdecB, hcB⟩ := hsmall (G.induce sᶜ) hsclt
  obtain ⟨D, hD, hdecD, hcD⟩ := decompose_across_cut G s A B (by
    simpa only [IsCycleOrEdge, SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.edgeFinset_card,
      ← Nat.card_eq_fintype_card] using hA) hdecA (by
    simpa only [IsCycleOrEdge, SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.edgeFinset_card,
      ← Nat.card_eq_fintype_card] using hB) hdecB
  have hbadD := hbad D hD hdecD
  have hspos : 0 < Fintype.card s := Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
  have hscpos : 0 < Fintype.card (sᶜ : Set V) := Fintype.card_pos_iff.mpr ⟨⟨y, hy⟩⟩
  have hsum : Fintype.card s + Fintype.card (sᶜ : Set V) = Fintype.card V := by
    simpa only [← Nat.card_eq_fintype_card] using Set.ncard_add_ncard_compl s
  have hbudget : C * (Fintype.card s - 1) + C * (Fintype.card (sᶜ : Set V) - 1) + C =
      C * (Fintype.card V - 1) := by
    have he : (Fintype.card s - 1) + (Fintype.card (sᶜ : Set V) - 1) + 1 =
        Fintype.card V - 1 := by omega
    calc
      _ = C * ((Fintype.card s - 1) + (Fintype.card (sᶜ : Set V) - 1) + 1) := by ring
      _ = _ := congrArg (C * ·) he
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
    at hcA hcB hcD hbadD hbudget hcut'
  omega

open scoped Classical in
lemma smallest_counterexample_edge_connected {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : ℕ)
    (hbad : ∀ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) →
      IsDecomposition G D → C * (Fintype.card V - 1) < D.card)
    (hsmall : ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      Fintype.card W < Fintype.card V →
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition R D ∧
        D.card ≤ C * (Fintype.card W - 1)) :
    G.IsEdgeConnected (C + 1) := by
  classical
  exact edge_connected_of_cut_bound G (C + 1)
    (fun s hs hsc => smallest_counterexample_cuts G C hbad hsmall s hs hsc)

open scoped Classical in
/-- A fixed bound of `C(n-1)` need only be proved for `(C+1)`-edge-connected graphs.
The missing high-connectivity theorem is still substantive. -/
lemma uniform_bound_of_edge_connected (C : ℕ)
    (hhigh : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.IsEdgeConnected (C + 1) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        D.card ≤ C * (Fintype.card V - 1)) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        D.card ≤ C * (Fintype.card V - 1) := by
  classical
  have main : ∀ n : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      Fintype.card V = n →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        D.card ≤ C * (Fintype.card V - 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ _ G hn
      by_contra hbad
      have hconn : G.IsEdgeConnected (C + 1) := by
        apply smallest_counterexample_edge_connected G C
        · intro D hD hdec
          by_contra hc
          exact hbad ⟨D, hD, hdec, Nat.le_of_not_gt hc⟩
        · intro W _ _ R hcard
          exact ih (Fintype.card W) (hcard.trans_eq hn) R rfl
      exact hbad (hhigh G hconn)
  intro V _ _ G
  exact main (Fintype.card V) G rfl

open scoped Classical in
lemma decomposition_of_card_le_one {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hn : Fintype.card V ≤ 1) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ D.card = 0 := by
  classical
  obtain ⟨D, hD, hdec, hc⟩ := exists_edge_decomposition G
  have he : G.edgeFinset.card = 0 := by
    have h := G.card_edgeFinset_le_card_choose_two
    rw [Nat.choose_eq_zero_of_lt (show Fintype.card V < 2 by omega)] at h
    omega
  exact ⟨D, hD, hdec, by omega⟩

open scoped Classical in
lemma uniform_bound_iff_shifted_bound :
    (∃ C : ℝ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ C * Fintype.card V) ↔
    (∃ C : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        D.card ≤ C * (Fintype.card V - 1)) := by
  classical
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨2 * ⌈C⌉₊, ?_⟩
    intro V _ _ G
    by_cases hn : Fintype.card V ≤ 1
    · obtain ⟨D, hD, hdec, hc⟩ := decomposition_of_card_le_one G hn
      exact ⟨D, hD, hdec, by rw [hc]; exact Nat.zero_le _⟩
    obtain ⟨D, hD, hdec, hc⟩ := hC G
    have hnat : D.card ≤ ⌈C⌉₊ * Fintype.card V := by
      have hle : (D.card : ℝ) ≤ (⌈C⌉₊ : ℝ) * Fintype.card V :=
        hc.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (Nat.cast_nonneg _))
      exact_mod_cast hle
    refine ⟨D, hD, hdec, hnat.trans ?_⟩
    calc
      ⌈C⌉₊ * Fintype.card V ≤ ⌈C⌉₊ * (2 * (Fintype.card V - 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = (2 * ⌈C⌉₊) * (Fintype.card V - 1) := by ring
  · rintro ⟨C, hC⟩
    refine ⟨(C : ℝ), ?_⟩
    intro V _ _ G
    obtain ⟨D, hD, hdec, hc⟩ := hC G
    refine ⟨D, hD, hdec, ?_⟩
    have hle : D.card ≤ C * Fintype.card V :=
      hc.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    exact_mod_cast hle

open scoped Classical in
/-- An exact reformulation of the original asymptotic conjecture on highly
edge-connected graphs. No uniform high-connectivity bound is asserted here. -/
lemma asymptotic_iff_edge_connected_uniform :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.IsEdgeConnected (C + 1) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        D.card ≤ C * (Fintype.card V - 1)) := by
  rw [asymptotic_iff_uniform, uniform_bound_iff_shifted_bound]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun G _ => hC G⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, uniform_bound_of_edge_connected C hC⟩

open scoped Classical in
/-- Sparse cuts incur at most `k(n-1)` additional pieces. Thus a bound on
`(k+1)`-edge-connected graphs extends to all graphs, with no dependence of
`k` on the hypothesized coefficient `B`. -/
lemma uniform_bound_from_fixed_edge_connectivity (k B : ℕ)
    (hhigh : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.IsEdgeConnected (k + 1) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        D.card ≤ B * Fintype.card V) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        D.card ≤ B * Fintype.card V + k * (Fintype.card V - 1) := by
  classical
  have main : ∀ n : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      Fintype.card V = n →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        D.card ≤ B * Fintype.card V + k * (Fintype.card V - 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ _ G hn
      by_cases hconn : G.IsEdgeConnected (k + 1)
      · obtain ⟨D, hD, hdec, hc⟩ := hhigh G hconn
        exact ⟨D, hD, hdec, hc.trans (Nat.le_add_right _ _)⟩
      have hcut : ∃ s : Set V, s.Nonempty ∧ sᶜ.Nonempty ∧
          (G.between s sᶜ).edgeFinset.card ≤ k := by
        by_contra! hc
        exact hconn (edge_connected_of_cut_bound G (k + 1) (fun s hs hsc => hc s hs hsc))
      obtain ⟨s, ⟨x, hx⟩, ⟨y, hy⟩, hcut⟩ := hcut
      have hslt : Fintype.card s < n := (Fintype.card_subtype_lt (x := y) hy).trans_eq hn
      have hsclt : Fintype.card (sᶜ : Set V) < n :=
        (Fintype.card_subtype_lt (x := x) (by simpa using hx)).trans_eq hn
      obtain ⟨A, hA, hdecA, hcA⟩ := ih _ hslt (G.induce s) rfl
      obtain ⟨E, hE, hdecE, hcE⟩ := ih _ hsclt (G.induce sᶜ) rfl
      obtain ⟨D, hD, hdecD, hcD⟩ := decompose_across_cut G s A E (by
        simpa only [IsCycleOrEdge, SimpleGraph.IsRegularOfDegree,
          ← SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.edgeFinset_card,
          ← Nat.card_eq_fintype_card] using hA) hdecA (by
        simpa only [IsCycleOrEdge, SimpleGraph.IsRegularOfDegree,
          ← SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.edgeFinset_card,
          ← Nat.card_eq_fintype_card] using hE) hdecE
      refine ⟨D, hD, hdecD, ?_⟩
      have hspos : 0 < Fintype.card s := Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
      have hscpos : 0 < Fintype.card (sᶜ : Set V) := Fintype.card_pos_iff.mpr ⟨⟨y, hy⟩⟩
      have hsum : Fintype.card s + Fintype.card (sᶜ : Set V) = Fintype.card V := by
        simpa only [← Nat.card_eq_fintype_card] using Set.ncard_add_ncard_compl s
      have hsub : (Fintype.card s - 1) + (Fintype.card (sᶜ : Set V) - 1) + 1 =
          Fintype.card V - 1 := by omega
      have hbudget : (B * Fintype.card s + k * (Fintype.card s - 1)) +
          (B * Fintype.card (sᶜ : Set V) + k * (Fintype.card (sᶜ : Set V) - 1)) + k =
          B * Fintype.card V + k * (Fintype.card V - 1) := by
        calc
          _ = B * (Fintype.card s + Fintype.card (sᶜ : Set V)) +
            k * ((Fintype.card s - 1) + (Fintype.card (sᶜ : Set V) - 1) + 1) := by ring
          _ = _ := by rw [hsum, hsub]
      simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
        at hcA hcE hcD hbudget hcut ⊢
      omega
  intro V _ _ G
  exact main (Fintype.card V) G rfl

open scoped Classical in
/-- For any fixed positive edge-connectivity threshold, a uniform linear bound
on that class is equivalent to the original conjecture. -/
lemma asymptotic_iff_fixed_edge_connectivity (k : ℕ) :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C : ℝ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.IsEdgeConnected (k + 1) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ C * Fintype.card V) := by
  rw [asymptotic_iff_uniform]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun G _ => hC G⟩
  · rintro ⟨C, hC⟩
    have hnat : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        G.IsEdgeConnected (k + 1) →
        ∃ D : Finset G.Subgraph,
          (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
          D.card ≤ ⌈C⌉₊ * Fintype.card V := by
      intro V _ _ G hG
      obtain ⟨D, hD, hdec, hc⟩ := hC G hG
      refine ⟨D, hD, hdec, ?_⟩
      have hle : (D.card : ℝ) ≤ (⌈C⌉₊ : ℝ) * Fintype.card V :=
        hc.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (Nat.cast_nonneg _))
      exact_mod_cast hle
    refine ⟨(⌈C⌉₊ + k : ℕ), ?_⟩
    intro V _ _ G
    obtain ⟨D, hD, hdec, hc⟩ := uniform_bound_from_fixed_edge_connectivity k ⌈C⌉₊ hnat G
    refine ⟨D, hD, hdec, ?_⟩
    have hle : D.card ≤ (⌈C⌉₊ + k) * Fintype.card V := by
      calc
        _ ≤ ⌈C⌉₊ * Fintype.card V + k * (Fintype.card V - 1) := hc
        _ ≤ ⌈C⌉₊ * Fintype.card V + k * Fintype.card V :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _
        _ = _ := by ring
    exact_mod_cast hle

#print axioms decompose_across_cut
#print axioms smallest_counterexample_edge_connected
#print axioms uniform_bound_of_edge_connected
#print axioms asymptotic_iff_edge_connected_uniform
#print axioms uniform_bound_from_fixed_edge_connectivity
#print axioms asymptotic_iff_fixed_edge_connectivity
end SparseCuts
end Erdos184Work



/- Edge-critical reductions for cycle-and-edge decompositions. No linear
bound for the critical class is assumed or proved here. -/
open SimpleGraph
namespace Erdos184Work
namespace Critical
open scoped Classical

private lemma size_exists {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ n : ℕ, ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ D.card = n := by
  obtain ⟨D, hD, hdec, _⟩ := exists_edge_decomposition G
  exact ⟨D.card, D, hD, hdec, rfl⟩

noncomputable def number {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.find (size_exists G)

lemma exists_minimum {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ D.card = number G :=
  Nat.find_spec (size_exists G)

lemma number_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D) : number G ≤ D.card :=
  Nat.find_min' (size_exists G) ⟨D, hD, hdec, rfl⟩

lemma number_le_iff {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ) :
    number G ≤ n ↔ ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ D.card ≤ n := by
  constructor
  · intro hn
    obtain ⟨D, hD, hdec, hc⟩ := exists_minimum G
    exact ⟨D, hD, hdec, hc.trans_le hn⟩
  · rintro ⟨D, hD, hdec, hc⟩
    exact (number_le D hD hdec).trans hc

open scoped Classical in
lemma restore_single_edge {V : Type*} [Fintype V] (G : SimpleGraph V) (e : G.edgeSet)
    (D : Finset (G.deleteEdges {e.val}).Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition (G.deleteEdges {e.val}) D) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, IsCycleOrEdge H.coe) ∧ IsDecomposition G E ∧ E.card ≤ D.card + 1 ∧
      ∃ H ∈ E, H.edgeSet = {e.val} ∧ H.coe.edgeFinset.card = 1 := by
  classical
  obtain ⟨A, hA, hpA, heA, hcA⟩ := lift_decomposition (G.deleteEdges_le {e.val}) D hD hdec
  obtain ⟨H, heH, hcH⟩ := exists_single_edge_subgraph G e
  have hnot : e.val ∉ (G.deleteEdges {e.val}).edgeSet := by
    simp [SimpleGraph.edgeSet_deleteEdges]
  refine ⟨insert H A, ?_, ⟨?_, ?_⟩, ?_, H, Finset.mem_insert_self _ _, heH, hcH⟩
  · intro K hK
    rcases Finset.mem_insert.mp hK with rfl | hK
    · exact Or.inr hcH
    · exact hA K hK
  · rw [Finset.coe_insert]
    apply hpA.insert
    intro K hK _
    apply Set.disjoint_left.mpr
    intro f hfH hfK
    have hfe : f = e.val := Set.mem_singleton_iff.mp (heH ▸ hfH)
    subst f
    apply hnot
    rw [← heA]
    exact Set.mem_iUnion.mpr ⟨K, Set.mem_iUnion.mpr ⟨hK, hfK⟩⟩
  · rw [Finset.set_biUnion_insert, heH, heA, SimpleGraph.edgeSet_deleteEdges]
    exact Set.union_diff_cancel (Set.singleton_subset_iff.mpr e.property)
  · exact (Finset.card_insert_le H A).trans (Nat.add_le_add_right hcA 1)

lemma number_restore_edge {V : Type*} [Fintype V] (G : SimpleGraph V) (e : G.edgeSet) :
    number G ≤ number (G.deleteEdges {e.val}) + 1 := by
  obtain ⟨D, hD, hdec, hc⟩ := exists_minimum (G.deleteEdges {e.val})
  obtain ⟨E, hE, hdecE, hEcard, _⟩ := restore_single_edge G e D hD hdec
  exact (number_le E hE hdecE).trans (hEcard.trans_eq (congrArg (· + 1) hc))

open scoped Classical in
lemma delete_edge_card_lt {V : Type*} [Fintype V] (G : SimpleGraph V) (e : G.edgeSet) :
    (G.deleteEdges {e.val}).edgeFinset.card < G.edgeFinset.card := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨SimpleGraph.edgeFinset_mono (G.deleteEdges_le _), ?_⟩
  intro heq
  have he : e.val ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr e.property
  rw [← heq] at he
  simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges, Set.mem_diff,
    Set.mem_singleton_iff, not_true_eq_false, and_false] using he

open scoped Classical in
lemma exists_edge_minimal_above {V : Type*} [Fintype V] (G : SimpleGraph V) (K : ℕ)
    (hbad : K < number G) :
    ∃ R : SimpleGraph V, R ≤ G ∧ K < number R ∧
      ∀ S ≤ R, S.edgeFinset.card < R.edgeFinset.card → number S ≤ K := by
  classical
  let P : ℕ → Prop := fun m => ∃ R : SimpleGraph V,
    R ≤ G ∧ K < number R ∧ R.edgeFinset.card = m
  have hex : ∃ m, P m := ⟨G.edgeFinset.card, G, le_rfl, hbad, rfl⟩
  obtain ⟨R, hRG, hRbad, hcR⟩ := Nat.find_spec hex
  refine ⟨R, hRG, hRbad, ?_⟩
  intro S hSR hcard
  by_contra! hS
  have hmin := Nat.find_min' hex ⟨S, hSR.trans hRG, hS, rfl⟩
  rw [← hcR] at hmin
  omega

open scoped Classical in
lemma edge_minimal_exposes_every_edge {V : Type*} [Fintype V] (G : SimpleGraph V) (K : ℕ)
    (hbad : K < number G)
    (hmin : ∀ R ≤ G, R.edgeFinset.card < G.edgeFinset.card → number R ≤ K)
    (e : G.edgeSet) :
    number G = K + 1 ∧ number (G.deleteEdges {e.val}) = K ∧
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ D.card = number G ∧
        ∃ H ∈ D, H.edgeSet = {e.val} ∧ H.coe.edgeFinset.card = 1 := by
  classical
  have hsmall := hmin (G.deleteEdges {e.val}) (G.deleteEdges_le _) (by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
      using delete_edge_card_lt G e)
  have hrestore := number_restore_edge G e
  have hG : number G = K + 1 := by omega
  have hR : number (G.deleteEdges {e.val}) = K := by omega
  obtain ⟨D, hD, hdec, hc⟩ := exists_minimum (G.deleteEdges {e.val})
  obtain ⟨E, hE, hdecE, hcE, hsingle⟩ := restore_single_edge G e D hD hdec
  have hlower := number_le E hE hdecE
  exact ⟨hG, hR, E, hE, hdecE, by omega, hsingle⟩

lemma number_le_edges {V : Type*} [Fintype V] (G : SimpleGraph V) :
    number G ≤ G.edgeFinset.card := by
  obtain ⟨D, hD, hdec, hc⟩ := exists_edge_decomposition G
  exact (number_le D hD hdec).trans hc

lemma regular_two_not_single_edge {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected) (hr : G.IsRegularOfDegree 2) : G.edgeFinset.card ≠ 1 := by
  classical
  obtain ⟨v⟩ := hc.nonempty
  have hd := G.degree_le_card_edgeFinset v
  have hreg := hr v
  simp only [← SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] at hd hreg ⊢
  omega

lemma edge_minimal_not_even {V : Type*} [Fintype V] (G : SimpleGraph V) (K : ℕ)
    (hbad : K < number G)
    (hmin : ∀ R ≤ G, R.edgeFinset.card < G.edgeFinset.card → number R ≤ K) :
    ¬ ∀ v, Even (G.degree v) := by
  classical
  intro heven
  have hpos : 0 < G.edgeFinset.card := lt_of_le_of_lt (Nat.zero_le K)
    (hbad.trans_le (number_le_edges G))
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  obtain ⟨_, _, D, hD, hdec, hcD, H, hHD, _, hcH⟩ :=
    edge_minimal_exposes_every_edge G K hbad hmin ⟨e, SimpleGraph.mem_edgeFinset.mp he⟩
  have hcycles := minimal_even_decomposition_cycles heven D hD hdec (by
    intro E hE hdecE
    rw [hcD]
    exact number_le E hE hdecE)
  exact regular_two_not_single_edge H.coe (hcycles H hHD).1 (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using (hcycles H hHD).2) hcH

lemma number_lt_edges_of_cycle {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : ¬ G.IsAcyclic) : number G < G.edgeFinset.card := by
  classical
  obtain ⟨u, p, hp⟩ := by
    simpa only [SimpleGraph.IsAcyclic, not_forall, not_not] using hG
  let C := p.toSubgraph.spanningCoe
  have hCG : C ≤ G := p.toSubgraph.spanningCoe_le
  obtain ⟨D, hD, hdec, hc⟩ := exists_edge_decomposition (G \ C)
  obtain ⟨E, hE, hdecE, hcE⟩ := add_cycle_to_decomposition G hp D hD hdec
  have hlen : 3 ≤ C.edgeFinset.card := by
    rw [cycle_edge_count G hp]
    exact hp.three_le_length
  have hsum : (G \ C).edgeFinset.card + C.edgeFinset.card = G.edgeFinset.card := by
    rw [SimpleGraph.edgeFinset_sdiff]
    exact Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hCG)
  have hn := number_le E hE hdecE
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc hlen hsum ⊢
  omega

noncomputable def edgePieces {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph) : Finset G.Subgraph :=
  D.filter (fun H => H.coe.edgeFinset.card = 1)

lemma edgePieces_graph_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph) (hdec : IsDecomposition G D) :
    (subfamilyGraph (edgePieces D)).edgeFinset.card = (edgePieces D).card := by
  classical
  have hsub : edgePieces D ⊆ D := Finset.filter_subset _ _
  rw [subfamilyGraph_card_edges _ (fun _ hH _ hK hne => hdec.1 (hsub hH) (hsub hK) hne)]
  calc
    _ = ∑ _H ∈ edgePieces D, (1 : ℕ) := Finset.sum_congr rfl (fun H hH => (Finset.mem_filter.mp hH).2)
    _ = _ := by simp

lemma minimal_edge_pieces_acyclic {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D) (hcD : D.card = number G) :
    (subfamilyGraph (edgePieces D)).IsAcyclic := by
  classical
  by_contra hcycle
  let A := edgePieces D
  have hAD : A ⊆ D := Finset.filter_subset _ _
  have hlt := number_lt_edges_of_cycle (subfamilyGraph A) hcycle
  obtain ⟨E, hE, hdecE, hcE⟩ := exists_minimum (subfamilyGraph A)
  obtain ⟨B, hB, hpB, heB, hcB⟩ := lift_decomposition (subfamilyGraph_le A) E hE hdecE
  have hcover : (⋃ H ∈ A, H.edgeSet) = ⋃ H ∈ B, H.edgeSet :=
    (subfamilyGraph_edges A).symm.trans heB.symm
  have hcardA : (subfamilyGraph A).edgeFinset.card = A.card := edgePieces_graph_card D hdec
  have hcard : B.card < A.card := by
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hlt hcardA
    omega
  obtain ⟨D', hD', hdecD', hcD'⟩ := replace_decomposition_subfamily
    D A B hD hdec hAD hB hpB hcover hcard
  have hn := number_le D' hD' hdecD'
  omega

lemma minimal_edge_piece_count {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D) (hcD : D.card = number G) :
    (edgePieces D).card ≤ Fintype.card V := by
  have hacyc := minimal_edge_pieces_acyclic D hD hdec hcD
  have hc := acyclic_card_edges_le _ hacyc
  rwa [edgePieces_graph_card D hdec] at hc

lemma edgePieces_degree_parity {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D) (v : V) :
    Even ((subfamilyGraph (edgePieces D)).degree v) ↔ Even (G.degree v) := by
  classical
  let A := edgePieces D
  let C := D \ A
  have hAD : A ⊆ D := Finset.filter_subset _ _
  have hC : ∀ H ∈ C, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    rcases hD H (Finset.mem_sdiff.mp hH).1 with hcyc | he
    · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hcyc
    · exact ((Finset.mem_sdiff.mp hH).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hH).1, he⟩)).elim
  have hce : Even (∑ H ∈ C, H.spanningCoe.degree v) :=
    Finset.even_sum _ (fun H hH => regular_two_spanning_even H (hC H hH).2 v)
  have heq : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  have hsum := Finset.sum_sdiff (f := fun H : G.Subgraph => H.spanningCoe.degree v) hAD
  change (∑ H ∈ C, H.spanningCoe.degree v) +
    (∑ H ∈ A, H.spanningCoe.degree v) = ∑ H ∈ D, H.spanningCoe.degree v at hsum
  rw [← subfamilyGraph_degree D hdec.1 v, heq] at hsum
  rw [← subfamilyGraph_degree A (fun _ hH _ hK hne => hdec.1 (hAD hH) (hAD hK) hne) v] at hsum
  rw [Nat.even_iff] at hce ⊢
  rw [Nat.even_iff]
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    at hsum hce ⊢
  dsimp only [A] at hsum
  omega

/-- Deleting any edge lowers the minimum piece count by exactly one. -/
def EdgeCritical {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ e : G.edgeSet, number G = number (G.deleteEdges {e.val}) + 1

lemma number_bot {V : Type*} [Fintype V] : number (⊥ : SimpleGraph V) = 0 := by
  apply Nat.eq_zero_of_le_zero
  have h := number_le (G := (⊥ : SimpleGraph V)) ∅ (by simp)
    (by simp [IsDecomposition])
  simpa using h

lemma edgeCritical_bot {V : Type*} [Fintype V] : EdgeCritical (⊥ : SimpleGraph V) := by
  intro e
  exact (show False by simpa using e.property).elim

lemma edge_minimal_is_critical {V : Type*} [Fintype V] (G : SimpleGraph V) (K : ℕ)
    (hbad : K < number G)
    (hmin : ∀ R ≤ G, R.edgeFinset.card < G.edgeFinset.card → number R ≤ K) :
    EdgeCritical G := by
  intro e
  obtain ⟨hG, hR, _⟩ := edge_minimal_exposes_every_edge G K hbad hmin e
  omega

lemma exists_critical_subgraph {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ R : SimpleGraph V, R ≤ G ∧ EdgeCritical R ∧ number R = number G := by
  classical
  by_cases hzero : number G = 0
  · exact ⟨⊥, bot_le, edgeCritical_bot, number_bot.trans hzero.symm⟩
  obtain ⟨R, hRG, hbad, hmin⟩ := exists_edge_minimal_above G (number G - 1) (by omega)
  have hc : EdgeCritical R := edge_minimal_is_critical R _ hbad hmin
  have hpos : 0 < R.edgeFinset.card := lt_of_le_of_lt (Nat.zero_le (number G - 1))
    (hbad.trans_le (number_le_edges R))
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  have hnum := (edge_minimal_exposes_every_edge R _ hbad hmin
    ⟨e, SimpleGraph.mem_edgeFinset.mp he⟩).1
  exact ⟨R, hRG, hc, by omega⟩

lemma EdgeCritical.exposes_every_edge {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : EdgeCritical G) (e : G.edgeSet) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ D.card = number G ∧
      ∃ H ∈ D, H.edgeSet = {e.val} ∧ H.coe.edgeFinset.card = 1 := by
  obtain ⟨D, hD, hdec, hcard⟩ := exists_minimum (G.deleteEdges {e.val})
  obtain ⟨E, hE, hdecE, hcE, hsingle⟩ := restore_single_edge G e D hD hdec
  have hlo := number_le E hE hdecE
  have heq := hc e
  exact ⟨E, hE, hdecE, by omega, hsingle⟩

lemma EdgeCritical.eq_bot_of_even {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : EdgeCritical G) (heven : ∀ v, Even (G.degree v)) : G = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro u v huv
  obtain ⟨D, hD, hdec, hcard, H, hHD, _, hcH⟩ :=
    hc.exposes_every_edge ⟨s(u,v), huv⟩
  have hcycles := minimal_even_decomposition_cycles heven D hD hdec (by
    intro E hE hdecE
    rw [hcard]
    exact number_le E hE hdecE)
  exact (regular_two_not_single_edge H.coe (hcycles H hHD).1 (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using (hcycles H hHD).2) hcH).elim

universe u

/-- Edge-criticality and high edge-connectivity may be imposed simultaneously
in the remaining uniform-bound problem. -/
lemma uniform_bound_of_critical_edge_connected (C : ℕ)
    (hhigh : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      EdgeCritical G → G.IsEdgeConnected (C + 1) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        D.card ≤ C * (Fintype.card V - 1)) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        D.card ≤ C * (Fintype.card V - 1) := by
  classical
  have main : ∀ n : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      Fintype.card V = n → number G ≤ C * (Fintype.card V - 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ _ G hn
      by_contra! hbad
      obtain ⟨R, hRG, hcrit, hnumber⟩ := exists_critical_subgraph G
      have hRbad : C * (Fintype.card V - 1) < number R := hnumber.symm ▸ hbad
      have hconn : R.IsEdgeConnected (C + 1) := by
        apply SparseCuts.smallest_counterexample_edge_connected R C
        · intro D hD hdec
          exact hRbad.trans_le (number_le D hD hdec)
        · intro W _ _ H hcard
          apply (number_le_iff H _).mp
          exact ih (Fintype.card W) (hcard.trans_eq hn) H rfl
      obtain ⟨D, hD, hdec, hc⟩ := hhigh R hcrit hconn
      exact (not_lt_of_ge ((number_le D hD hdec).trans hc) hRbad)
  intro V _ _ G
  exact (number_le_iff G _).mp (main (Fintype.card V) G rfl)

open Filter in
/-- Exact reduction to graphs satisfying both global criticality and high
edge-connectivity. This theorem does not assert a bound on that class. -/
lemma asymptotic_iff_critical_edge_connected_uniform :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      EdgeCritical G → G.IsEdgeConnected (C + 1) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        D.card ≤ C * (Fintype.card V - 1)) := by
  rw [asymptotic_iff_uniform, SparseCuts.uniform_bound_iff_shifted_bound]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun G _ _ => hC G⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, uniform_bound_of_critical_edge_connected C hC⟩

#print axioms edge_minimal_exposes_every_edge
#print axioms edge_minimal_not_even
#print axioms minimal_edge_pieces_acyclic
#print axioms edgePieces_degree_parity
#print axioms exists_critical_subgraph
#print axioms EdgeCritical.eq_bot_of_even
#print axioms uniform_bound_of_critical_edge_connected
#print axioms asymptotic_iff_critical_edge_connected_uniform
end Critical
end Erdos184Work



/- Lower bounds from unbalanced complete bipartite graphs. These do not
contradict the existence of some uniform linear bound. -/
open SimpleGraph
namespace Erdos184Work
namespace BipartiteLower
open scoped Classical

lemma bipartite_edge_sums {A B : Type*} [Fintype A] [Fintype B]
    (H : SimpleGraph (A ⊕ B)) (hH : H ≤ completeBipartiteGraph A B) :
    H.edgeFinset.card = ∑ a : A, H.degree (Sum.inl a) ∧
    H.edgeFinset.card = ∑ b : B, H.degree (Sum.inr b) := by
  classical
  let s : Finset (A ⊕ B) := Finset.univ.map Function.Embedding.inl
  let t : Finset (A ⊕ B) := Finset.univ.map Function.Embedding.inr
  have hb : H.IsBipartiteWith (s : Set (A ⊕ B)) (t : Set (A ⊕ B)) := by
    constructor
    · apply Set.disjoint_left.mpr
      intro x hxS hxT
      cases x <;> simp [s, t] at *
    · intro x y hxy
      have h := hH hxy
      cases x <;> cases y <;> simp_all [s, t, completeBipartiteGraph]
  have hl := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hb
  have hr := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hb
  constructor
  · simpa only [s, Finset.sum_map, Function.Embedding.inl_apply] using hl.symm
  · simpa only [t, Finset.sum_map, Function.Embedding.inr_apply] using hr.symm

lemma complete_degree_left {A B : Type*} [Fintype A] [Fintype B] (a : A) :
    (completeBipartiteGraph A B).degree (Sum.inl a) = Fintype.card B := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card]
  have he : (completeBipartiteGraph A B).neighborSet (Sum.inl a) =
      Set.range (Sum.inr : B → A ⊕ B) := by
    ext x
    cases x <;> simp [SimpleGraph.mem_neighborSet, completeBipartiteGraph]
  change ((completeBipartiteGraph A B).neighborSet (Sum.inl a)).ncard = Nat.card B
  rw [he, Set.ncard_range_of_injective Sum.inr_injective]

lemma complete_degree_right {A B : Type*} [Fintype A] [Fintype B] (b : B) :
    (completeBipartiteGraph A B).degree (Sum.inr b) = Fintype.card A := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card]
  have he : (completeBipartiteGraph A B).neighborSet (Sum.inr b) =
      Set.range (Sum.inl : A → A ⊕ B) := by
    ext x
    cases x <;> simp [SimpleGraph.mem_neighborSet, completeBipartiteGraph]
  change ((completeBipartiteGraph A B).neighborSet (Sum.inr b)).ncard = Nat.card A
  rw [he, Set.ncard_range_of_injective Sum.inl_injective]

lemma complete_edge_card {A B : Type*} [Fintype A] [Fintype B] :
    (completeBipartiteGraph A B).edgeFinset.card = Fintype.card A * Fintype.card B := by
  rw [(bipartite_edge_sums (completeBipartiteGraph A B) le_rfl).1]
  simp only [complete_degree_left, Finset.sum_const, Finset.card_univ, smul_eq_mul]

lemma cycle_edge_bound {A B : Type*} [Fintype A] [Fintype B]
    (H : (completeBipartiteGraph A B).Subgraph) (hH : H.coe.IsRegularOfDegree 2) :
    H.coe.edgeFinset.card ≤ 2 * Fintype.card A := by
  classical
  rw [← subgraph_edge_card H, (bipartite_edge_sums H.spanningCoe H.spanningCoe_le).1]
  have hd : ∀ a : A, H.spanningCoe.degree (Sum.inl a) ≤ 2 := by
    intro a
    rw [regular_two_spanning_degree H hH]
    split_ifs <;> omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hd a)
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] using hs

lemma single_piece_lower_bound {A B : Type*} [Fintype A] [Fintype B]
    (ha : Odd (Fintype.card A)) (D : Finset (completeBipartiteGraph A B).Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition (completeBipartiteGraph A B) D) :
    Fintype.card B ≤ (Critical.edgePieces D).card := by
  classical
  let F := subfamilyGraph (Critical.edgePieces D)
  have hF : F ≤ completeBipartiteGraph A B := subfamilyGraph_le _
  have hpos : ∀ b : B, 1 ≤ F.degree (Sum.inr b) := by
    intro b
    have hpar := Critical.edgePieces_degree_parity D hD hdec (Sum.inr b)
    have hd := complete_degree_right (A := A) b
    have hodd : ¬ Even ((completeBipartiteGraph A B).degree (Sum.inr b)) := by
      rw [hd]
      exact Nat.not_even_iff_odd.mpr ha
    have hnot := mt hpar.mp hodd
    change ¬ Even (F.degree (Sum.inr b)) at hnot
    rw [Nat.even_iff] at hnot
    omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hpos b)
  have hcard := (bipartite_edge_sums F hF).2
  have heF := Critical.edgePieces_graph_card D hdec
  change F.edgeFinset.card = _ at heF
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hs
  omega

lemma decomposition_lower_bound {A B : Type*} [Fintype A] [Fintype B]
    (m : ℕ) (ha : Fintype.card A = 2 * m + 1)
    (D : Finset (completeBipartiteGraph A B).Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition (completeBipartiteGraph A B) D) :
    (6 * m + 2) * Fintype.card B ≤ (4 * m + 2) * D.card := by
  classical
  let E := Critical.edgePieces D
  let C := D \ E
  have hED : E ⊆ D := Finset.filter_subset _ _
  have hC : ∀ H ∈ C, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    rcases hD H (Finset.mem_sdiff.mp hH).1 with hc | he
    · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hc
    · exact ((Finset.mem_sdiff.mp hH).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hH).1, he⟩)).elim
  have hcyclecard : ∑ H ∈ C, H.coe.edgeFinset.card ≤ (2 * Fintype.card A) * C.card := by
    have h := Finset.sum_le_sum (s := C) (fun H hH => cycle_edge_bound H (hC H hH).2)
    simpa only [Finset.sum_const, smul_eq_mul, mul_comm] using h
  have hEcard : ∑ H ∈ E, H.coe.edgeFinset.card = E.card := by
    calc
      _ = ∑ _H ∈ E, (1 : ℕ) := Finset.sum_congr rfl (fun H hH => (Finset.mem_filter.mp hH).2)
      _ = _ := by simp
  have hDG : subfamilyGraph D = completeBipartiteGraph A B :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  have htotal := subfamilyGraph_card_edges D hdec.1
  rw [hDG, complete_edge_card] at htotal
  have hsum := Finset.sum_sdiff (f := fun H : (completeBipartiteGraph A B).Subgraph =>
    H.coe.edgeFinset.card) hED
  change (∑ H ∈ C, H.coe.edgeFinset.card) + (∑ H ∈ E, H.coe.edgeFinset.card) = _ at hsum
  rw [hEcard, ← htotal] at hsum
  have hcount : C.card + E.card = D.card := Finset.card_sdiff_add_card_eq_card hED
  have hEmin : Fintype.card B ≤ E.card := single_piece_lower_bound (by
    rw [ha]; exact ⟨m, by omega⟩) D hD hdec
  have hmul := Nat.mul_le_mul_left (4 * m + 1) hEmin
  rw [ha] at hcyclecard hsum
  nlinarith

universe u

lemma universal_bound_ge_bipartite (f : ℕ → ℝ)
    (hf : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V)) (m : ℕ) :
    ((3 * m ^ 2 + m : ℕ) : ℝ) ≤ f ((2 * m + 1) * (m + 1)) := by
  classical
  let A := ULift.{u} (Fin (2 * m + 1))
  let B := ULift.{u} (Fin ((2 * m + 1) * m))
  obtain ⟨D, hD, hdec, hc⟩ := hf (completeBipartiteGraph A B)
  have hlow := decomposition_lower_bound (A := A) (B := B) m (by simp [A]) D hD hdec
  have hscaled : (4 * m + 2) * (3 * m ^ 2 + m) ≤ (4 * m + 2) * D.card := by
    calc
      _ = (6 * m + 2) * Fintype.card B := by simp only [B, Fintype.card_ulift, Fintype.card_fin]; ring
      _ ≤ _ := hlow
  have hDcard : 3 * m ^ 2 + m ≤ D.card := Nat.le_of_mul_le_mul_left hscaled (by omega)
  have hn : Fintype.card (A ⊕ B) = (2 * m + 1) * (m + 1) := by
    simp only [Fintype.card_sum, A, B, Fintype.card_ulift, Fintype.card_fin]
    ring
  rw [hn] at hc
  exact (Nat.cast_le.mpr hDcard).trans hc

/-- Any universal linear coefficient must be at least `3/2`. The unbalanced
bipartite examples are stronger than the lower bound supplied by trees. -/
lemma universal_linear_constant_ge_three_halves (C : ℝ)
    (hC : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ C * Fintype.card V) : 3 / 2 ≤ C := by
  have hC1 := universal_linear_constant_ge_one C hC
  by_contra! hlt
  have hpos : 0 < 3 - 2 * C := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (4 * C / (3 - 2 * C)))
  have hm1 : 1 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hmpos : 0 < (m : ℝ) := lt_trans zero_lt_one hm1
  have hmdiv : 4 * C / (3 - 2 * C) < (m : ℝ) := (le_max_right _ _).trans_lt hm
  have hmC : 4 * C < (m : ℝ) * (3 - 2 * C) := (div_lt_iff₀ hpos).mp hmdiv
  have hmul := mul_lt_mul_of_pos_right hmC hmpos
  have hCm : C ≤ C * (m : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ C by linarith) (show 0 ≤ (m : ℝ) - 1 by linarith)]
  have hb := universal_bound_ge_bipartite (fun n => C * (n : ℝ)) hC m
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hb
  nlinarith

/-- This rules out the stronger `n-1` proposal, not the original `O(n)` conjecture. -/
lemma three_seven_at_least_ten
    (D : Finset (completeBipartiteGraph (Fin 3) (Fin 7)).Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition (completeBipartiteGraph (Fin 3) (Fin 7)) D) : 10 ≤ D.card := by
  have h := decomposition_lower_bound (A := Fin 3) (B := Fin 7) 1 (by decide) D hD hdec
  norm_num only [Fintype.card_fin] at h
  omega

#print axioms decomposition_lower_bound
#print axioms universal_linear_constant_ge_three_halves
end BipartiteLower
end Erdos184Work



/- Restricting pieces to their edge union and transporting minimality. -/
open SimpleGraph
namespace Erdos184Work
namespace Subfamilies
open scoped Classical
universe u

/-- The same piece, viewed in the graph which is the union of the family. -/
def lowerPiece {V : Type*} {G R : SimpleGraph V} (D : Finset G.Subgraph)
    (hcover : (⋃ H ∈ D, H.edgeSet) = R.edgeSet) (H : D) : R.Subgraph where
  verts := H.val.verts
  Adj := H.val.Adj
  adj_sub {v w} h := by
    have he : s(v,w) ∈ ⋃ K ∈ D, K.edgeSet :=
      Set.mem_iUnion.mpr ⟨H.val, Set.mem_iUnion.mpr ⟨H.property, h⟩⟩
    rw [hcover] at he
    exact he
  edge_vert := H.val.edge_vert
  symm := H.val.symm

lemma lowerPiece_verts {V : Type*} {G R : SimpleGraph V} (D : Finset G.Subgraph)
    (hcover : (⋃ H ∈ D, H.edgeSet) = R.edgeSet) (H : D) :
    (lowerPiece D hcover H).verts = H.val.verts := rfl

lemma lowerPiece_edges {V : Type*} {G R : SimpleGraph V} (D : Finset G.Subgraph)
    (hcover : (⋃ H ∈ D, H.edgeSet) = R.edgeSet) (H : D) :
    (lowerPiece D hcover H).edgeSet = H.val.edgeSet := rfl

lemma lowerPiece_injective {V : Type*} {G R : SimpleGraph V} (D : Finset G.Subgraph)
    (hcover : (⋃ H ∈ D, H.edgeSet) = R.edgeSet) :
    Function.Injective (lowerPiece D hcover) := by
  intro H K he
  apply Subtype.ext
  apply SimpleGraph.Subgraph.ext
  · exact congrArg (fun J : R.Subgraph => J.verts) he
  · exact congrArg (fun J : R.Subgraph => J.Adj) he

noncomputable def lowerFamily {V : Type*} {G R : SimpleGraph V} (D : Finset G.Subgraph)
    (hcover : (⋃ H ∈ D, H.edgeSet) = R.edgeSet) : Finset R.Subgraph :=
  Finset.univ.image (lowerPiece D hcover)

lemma lowerFamily_card {V : Type*} {G R : SimpleGraph V} (D : Finset G.Subgraph)
    (hcover : (⋃ H ∈ D, H.edgeSet) = R.edgeSet) : (lowerFamily D hcover).card = D.card := by
  rw [lowerFamily, Finset.card_image_of_injective _ (lowerPiece_injective D hcover)]
  simp

lemma lowerFamily_property (P : ∀ {W : Type u} [Fintype W], SimpleGraph W → Prop)
    {V : Type u} [Fintype V] {G R : SimpleGraph V} (D : Finset G.Subgraph)
    (hcover : (⋃ H ∈ D, H.edgeSet) = R.edgeSet) (hD : ∀ H ∈ D, P H.coe) :
    ∀ H ∈ lowerFamily D hcover, P H.coe := by
  intro H hH
  obtain ⟨K, _, rfl⟩ := Finset.mem_image.mp hH
  exact hD K.val K.property

lemma lowerFamily_decomposition {V : Type*} {G R : SimpleGraph V} (D : Finset G.Subgraph)
    (hcover : (⋃ H ∈ D, H.edgeSet) = R.edgeSet)
    (hp : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    IsDecomposition R (lowerFamily D hcover) := by
  constructor
  · intro H hH K hK hne
    obtain ⟨H', _, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨K', _, rfl⟩ := Finset.mem_image.mp hK
    exact hp H'.property K'.property (fun he => hne
      (congrArg (lowerPiece D hcover) (Subtype.ext he)))
  · rw [← hcover]
    ext e
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨H, hH, heH⟩
      obtain ⟨K, _, rfl⟩ := Finset.mem_image.mp hH
      exact ⟨K.val, K.property, heH⟩
    · rintro ⟨H, hH, heH⟩
      exact ⟨lowerPiece D hcover ⟨H, hH⟩,
        Finset.mem_image.mpr ⟨⟨H, hH⟩, Finset.mem_univ _, rfl⟩, heH⟩

lemma lowerFamily_linear {V : Type*} {G R : SimpleGraph V} (D : Finset G.Subgraph)
    (hcover : (⋃ H ∈ D, H.edgeSet) = R.edgeSet) (hlin : LongRing.LinearIntersections D) :
    LongRing.LinearIntersections (lowerFamily D hcover) := by
  intro H hH K hK hne
  obtain ⟨H', _, rfl⟩ := Finset.mem_image.mp hH
  obtain ⟨K', _, rfl⟩ := Finset.mem_image.mp hK
  exact hlin H'.val H'.property K'.val K'.property (fun he => hne
    (congrArg (lowerPiece D hcover) (Subtype.ext he)))

/-- A subfamily of a minimum decomposition is minimum for its own edge union. -/
lemma minimal_subfamily_number {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D) (hcD : D.card = Critical.number G)
    (A : Finset G.Subgraph) (hAD : A ⊆ D) :
    Critical.number (subfamilyGraph A) = A.card := by
  have hcover := (subfamilyGraph_edges A).symm
  have hpA : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hdec.1 (hAD hH) (hAD hK) hne
  apply le_antisymm
  · have hn := Critical.number_le (lowerFamily A hcover)
      (lowerFamily_property IsCycleOrEdge A hcover (fun H hH => hD H (hAD hH)))
      (lowerFamily_decomposition A hcover hpA)
    rwa [lowerFamily_card] at hn
  · by_contra! hlt
    obtain ⟨E, hE, hdecE, hcE⟩ := Critical.exists_minimum (subfamilyGraph A)
    obtain ⟨B, hB, hpB, heB, hcB⟩ := lift_decomposition (subfamilyGraph_le A) E hE hdecE
    have hAB : (⋃ H ∈ A, H.edgeSet) = ⋃ H ∈ B, H.edgeSet := hcover.trans heB.symm
    obtain ⟨D', hD', hdecD', hcD'⟩ := replace_decomposition_subfamily D A B
      hD hdec hAD hB hpB hAB (by omega)
    have hn := Critical.number_le D' hD' hdecD'
    omega

/-- The linear-intersection counting theorem applies to any such subfamily
of a global minimum, not just to the entire decomposition. -/
lemma minimal_linear_subfamily_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D) (hcD : D.card = Critical.number G)
    (A : Finset G.Subgraph) (hAD : A ⊆ D)
    (hA : ∀ H ∈ A, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hlin : LongRing.LinearIntersections A) : 2 * A.card ≤ Fintype.card V := by
  let hcover := (subfamilyGraph_edges A).symm
  have hpA : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hdec.1 (hAD hH) (hAD hK) hne
  have hnum := minimal_subfamily_number D hD hdec hcD A hAD
  have hbound := LongRing.minimal_linear_decomposition_bound (lowerFamily A hcover)
    (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using lowerFamily_property
        (fun H => H.Connected ∧ H.IsRegularOfDegree 2) A hcover (by
          simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
            ← Nat.card_eq_fintype_card] using hA))
    (lowerFamily_decomposition A hcover hpA) (lowerFamily_linear A hcover hlin)
    (by
      intro E hE hdecE
      rw [lowerFamily_card, ← hnum]
      exact Critical.number_le E hE hdecE)
  simpa only [lowerFamily_card] using hbound

lemma remove_single_piece_number {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D) (hcD : D.card = Critical.number G)
    (e : G.edgeSet) (H : G.Subgraph) (hHD : H ∈ D) (heH : H.edgeSet = {e.val}) :
    Critical.number G = Critical.number (G.deleteEdges {e.val}) + 1 := by
  let A := D.erase H
  have hAD : A ⊆ D := Finset.erase_subset _ _
  have hcover : (⋃ K ∈ A, K.edgeSet) = (G.deleteEdges {e.val}).edgeSet := by
    rw [SimpleGraph.edgeSet_deleteEdges]
    ext f
    constructor
    · intro hf
      obtain ⟨K, hf⟩ := Set.mem_iUnion.mp hf
      obtain ⟨hK, hfK⟩ := Set.mem_iUnion.mp hf
      refine ⟨K.edgeSet_subset hfK, ?_⟩
      intro hfe
      have hfe' : f = e.val := Set.mem_singleton_iff.mp hfe
      subst f
      exact Set.disjoint_left.mp (hdec.1 (hAD hK) hHD (Finset.mem_erase.mp hK).1)
        hfK (by change e.val ∈ H.edgeSet; rw [heH]; exact Set.mem_singleton _)
    · rintro ⟨hfG, hfe⟩
      rw [← hdec.2] at hfG
      obtain ⟨K, hfG⟩ := Set.mem_iUnion.mp hfG
      obtain ⟨hK, hfK⟩ := Set.mem_iUnion.mp hfG
      have hne : K ≠ H := by
        intro heq
        subst K
        exact hfe (heH ▸ hfK)
      exact Set.mem_iUnion.mpr ⟨K, Set.mem_iUnion.mpr
        ⟨Finset.mem_erase.mpr ⟨hne, hK⟩, hfK⟩⟩
  have hnum := Critical.number_le (lowerFamily A hcover)
    (lowerFamily_property IsCycleOrEdge A hcover (fun K hK => hD K (hAD hK)))
    (lowerFamily_decomposition A hcover (fun _ hK _ hL hne => hdec.1 (hAD hK) (hAD hL) hne))
  rw [lowerFamily_card] at hnum
  have hcard : A.card + 1 = D.card := Finset.card_erase_add_one hHD
  have hlo := Critical.number_restore_edge G e
  omega

/-- Edge transitivity is stated explicitly to avoid imposing a chosen action. -/
def IsEdgeTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ e f : G.edgeSet, ∃ φ : G ≃g G, Sym2.map φ.toHom e.val = f.val

/-- Non-even edge-transitive graphs are edge-critical. Thus edge-criticality
alone does not restrict the problem to graphs with low degrees or sparse cuts. -/
lemma edge_transitive_non_even_critical {V : Type*} [Fintype V] (G : SimpleGraph V)
    (htrans : IsEdgeTransitive G) (hodd : ¬ ∀ v, Even (G.degree v)) :
    Critical.EdgeCritical G := by
  obtain ⟨D, hD, hdec, hcD⟩ := Critical.exists_minimum G
  have hsingle : ∃ H ∈ D, H.coe.edgeFinset.card = 1 := by
    by_contra! hnone
    have hcyc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
      intro H hH
      rcases hD H hH with hh | he
      · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hh
      · exact (hnone H hH he).elim
    have hg : subfamilyGraph D = G :=
      SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
    apply hodd
    have he := cycle_subfamily_even D hcyc hdec.1
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at he ⊢
    rwa [hg] at he
  obtain ⟨H, hHD, hcH⟩ := hsingle
  have hs : H.edgeSet.ncard = 1 := by
    have h := (subgraph_edge_card H).trans hcH
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using h
  obtain ⟨e, heH⟩ := Set.ncard_eq_one.mp hs
  have heG : e ∈ G.edgeSet := H.edgeSet_subset (heH.symm ▸ Set.mem_singleton e)
  intro f
  obtain ⟨φ, hφ⟩ := htrans ⟨e, heG⟩ f
  let E := D.image (SimpleGraph.Subgraph.map φ.toHom)
  have hE : ∀ K ∈ E, IsCycleOrEdge K.coe := by
    intro K hK
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
    exact SparseCuts.piece_property_map_injective φ.toHom φ.injective L (hD L hL)
  have hdecE : IsDecomposition G E := map_isDecomposition_iso φ D hdec
  have hcE : E.card = Critical.number G := by
    have hlo := Critical.number_le E hE hdecE
    have hhi : E.card ≤ D.card := Finset.card_image_le
    omega
  apply remove_single_piece_number E hE hdecE hcE f (H.map φ.toHom)
    (Finset.mem_image.mpr ⟨H, hHD, rfl⟩)
  rw [SimpleGraph.Subgraph.edgeSet_map, heH, Set.image_singleton, hφ]

lemma edge_transitive_critical_iff {V : Type*} [Fintype V] (G : SimpleGraph V)
    (htrans : IsEdgeTransitive G) :
    Critical.EdgeCritical G ↔ G = ⊥ ∨ ¬ ∀ v, Even (G.degree v) := by
  constructor
  · intro hc
    by_cases heven : ∀ v, Even (G.degree v)
    · exact Or.inl (hc.eq_bot_of_even heven)
    · exact Or.inr heven
  · rintro (rfl | hodd)
    · exact Critical.edgeCritical_bot
    · exact edge_transitive_non_even_critical G htrans hodd

def bipartiteIso {A B A' B' : Type*} (eA : A ≃ A') (eB : B ≃ B') :
    completeBipartiteGraph A B ≃g completeBipartiteGraph A' B' where
  toEquiv := eA.sumCongr eB
  map_rel_iff' := by
    intro x y
    cases x <;> cases y <;> simp [completeBipartiteGraph]

lemma bipartite_edge_representation {A B : Type*} (e : (completeBipartiteGraph A B).edgeSet) :
    ∃ a : A, ∃ b : B, e.val = s(Sum.inl a, Sum.inr b) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with | h x y =>
  cases x with
  | inl a =>
    cases y with
    | inl a' => simp [completeBipartiteGraph] at he
    | inr b => exact ⟨a, b, rfl⟩
  | inr b =>
    cases y with
    | inl a => exact ⟨a, b, Sym2.eq_swap⟩
    | inr b' => simp [completeBipartiteGraph] at he

lemma complete_bipartite_edge_transitive (A B : Type*) :
    IsEdgeTransitive (completeBipartiteGraph A B) := by
  classical
  intro e f
  obtain ⟨a, b, he⟩ := bipartite_edge_representation e
  obtain ⟨a', b', hf⟩ := bipartite_edge_representation f
  refine ⟨bipartiteIso (Equiv.swap a a') (Equiv.swap b b'), ?_⟩
  rw [he, hf, Sym2.map_pair_eq]
  simp [bipartiteIso]

lemma complete_bipartite_odd_critical {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (ha : Odd (Fintype.card A)) : Critical.EdgeCritical (completeBipartiteGraph A B) := by
  apply edge_transitive_non_even_critical _ (complete_bipartite_edge_transitive A B)
  intro heven
  obtain ⟨b⟩ := ‹Nonempty B›
  have h := heven (Sum.inr b)
  have hd := BipartiteLower.complete_degree_right (A := A) b
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h hd
  rw [hd] at h
  exact Nat.not_even_iff_odd.mpr ha (by simpa only [Nat.card_eq_fintype_card] using h)

#print axioms minimal_subfamily_number
#print axioms minimal_linear_subfamily_bound
#print axioms edge_transitive_critical_iff
#print axioms complete_bipartite_odd_critical
end Subfamilies
end Erdos184Work



/- Parity correction and vertex elimination for cycle/edge decompositions. -/
namespace Erdos184Work.Vertex
open SimpleGraph
open scoped Classical symmDiff

lemma degree_sup_inf {V : Type*} [Fintype V] (G H : SimpleGraph V) (v : V) :
    (G ⊔ H).degree v + (G ⊓ H).degree v = G.degree v + H.degree v := by
  classical
  have hu : (G ⊔ H).neighborFinset v = G.neighborFinset v ∪ H.neighborFinset v := by
    ext w
    simp
  have hi : (G ⊓ H).neighborFinset v = G.neighborFinset v ∩ H.neighborFinset v := by
    ext w
    simp
  simp only [SimpleGraph.degree, hu, hi]
  exact Finset.card_union_add_card_inter _ _

lemma degree_symmDiff {V : Type*} [Fintype V] (G H : SimpleGraph V) (v : V) :
    (G ∆ H).degree v + 2 * (G ⊓ H).degree v = G.degree v + H.degree v := by
  classical
  have h := degree_sdiff_add (G ⊔ H) (G ⊓ H) inf_le_sup v
  have hi := degree_sup_inf G H v
  rw [symmDiff_eq_sup_sdiff_inf]
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h hi ⊢
  omega

lemma degree_symmDiff_mod_two {V : Type*} [Fintype V] (G H : SimpleGraph V) (v : V) :
    (G ∆ H).degree v % 2 = (G.degree v + H.degree v) % 2 := by
  have h := degree_symmDiff G H v
  omega

lemma degree_edge {V : Type*} [Fintype V] {u v : V} (huv : u ≠ v) (w : V) :
    (SimpleGraph.edge u v).degree w = if w = u ∨ w = v then 1 else 0 := by
  classical
  have hn : (SimpleGraph.edge u v).neighborFinset w =
      if w = u then {v} else if w = v then {u} else ∅ := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.edge_adj]
    split_ifs <;> simp_all
  rw [SimpleGraph.degree, hn]
  split_ifs <;> simp_all

lemma walk_boundary {V : Type*} [Fintype V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) :
    ∃ R : SimpleGraph V, R ≤ G ∧ ∀ w,
      R.degree w % 2 = ((if w = u then 1 else 0) + (if w = v then 1 else 0)) % 2 := by
  classical
  induction p with
  | nil =>
    refine ⟨⊥, bot_le, ?_⟩
    intro w
    split_ifs <;> simp [SimpleGraph.degree, SimpleGraph.neighborFinset]
  | @cons u x v h p ih =>
    obtain ⟨R, hRG, hR⟩ := ih
    refine ⟨SimpleGraph.edge u x ∆ R,
      le_trans symmDiff_le_sup (sup_le ((SimpleGraph.edge_le_iff G).mpr (Or.inr h)) hRG), ?_⟩
    intro w
    have hs := degree_symmDiff_mod_two (SimpleGraph.edge u x) R w
    have he := degree_edge h.ne w
    have hr := hR w
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hs he hr ⊢
    rw [Nat.add_mod, he, hr] at hs
    have hux := h.ne
    by_cases hwU : w = u <;> by_cases hwX : w = x <;> by_cases hwV : w = v
    all_goals simp_all

lemma parity_subgraph_with_root {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.Preconnected) (r : V) (S : Finset V) :
    ∃ R : SimpleGraph V, R ≤ G ∧ ∀ w,
      R.degree w % 2 = ((if w ∈ S then 1 else 0) + (if w = r then S.card else 0)) % 2 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨⊥, bot_le, ?_⟩
    simp [SimpleGraph.degree, SimpleGraph.neighborFinset]
  | @insert a S ha ih =>
    obtain ⟨R, hRG, hR⟩ := ih
    obtain ⟨p⟩ := hG a r
    obtain ⟨P, hPG, hP⟩ := walk_boundary p
    refine ⟨R ∆ P, le_trans symmDiff_le_sup (sup_le hRG hPG), ?_⟩
    intro w
    have hs := degree_symmDiff_mod_two R P w
    have hr := hR w
    have hp := hP w
    simp only [Finset.mem_insert, Finset.card_insert_of_notMem ha]
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hs hr hp ⊢
    rw [Nat.add_mod, hr, hp] at hs
    clear hR hP hr hp
    by_cases hwa : w = a <;> by_cases hwS : w ∈ S <;> by_cases hwr : w = r
    all_goals simp_all only [true_or, false_or, ite_true, ite_false]
    all_goals omega

/-- Every even set of terminals in a connected graph is the odd-degree set of a subgraph. -/
lemma exists_parity_subgraph {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.Preconnected) (S : Finset V) (hS : Even S.card) :
    ∃ R : SimpleGraph V, R ≤ G ∧ ∀ w,
      R.degree w % 2 = if w ∈ S then 1 else 0 := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h => exact ⟨⊥, bot_le, fun w => isEmptyElim w⟩
  | inr h =>
    obtain ⟨r⟩ := h
    obtain ⟨R, hRG, hR⟩ := parity_subgraph_with_root hG r S
    refine ⟨R, hRG, ?_⟩
    intro w
    have hr := hR w
    have hs : S.card % 2 = 0 := Nat.even_iff.mp hS
    by_cases hwS : w ∈ S <;> by_cases hwr : w = r <;> simp_all [Nat.add_mod]

lemma spanningCoe_support_subset {V : Type*} {s : Set V} (R : SimpleGraph s) :
    R.spanningCoe.support ⊆ s := by
  rintro w ⟨x, h⟩
  obtain ⟨a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp h
  exact a.property

lemma spanningCoe_degree {V : Type*} [Fintype V] {s : Set V}
    (R : SimpleGraph s) (w : s) : R.spanningCoe.degree w = R.degree w := by
  classical
  have h := SimpleGraph.degree_induce_of_support_subset (spanningCoe_support_subset R) w
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
  simpa only [SimpleGraph.induce_spanningCoe] using h.symm

/-- If deleting `v` leaves a preconnected graph and its degree is even, a parity
correction away from `v` gives an even subgraph containing all edges at `v`. -/
lemma even_subgraph_preserving_vertex {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v : V) (hG : (G.induce {w : V | w ≠ v}).Preconnected) (hv : Even (G.degree v)) :
    ∃ H : SimpleGraph V, H ≤ G ∧ (∀ w, Even (H.degree w)) ∧
      ∀ w, H.Adj v w ↔ G.Adj v w := by
  classical
  let s : Set V := {w | w ≠ v}
  let T : Finset s := Finset.univ.filter (fun w => Odd (G.degree w.val))
  have hTimage : T.image Subtype.val = Finset.univ.filter (fun w => Odd (G.degree w)) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Finset.mem_filter.mp hx).2
    · intro hw
      have hwv : w ≠ v := by
        rintro rfl
        exact Nat.not_odd_iff_even.mpr hv hw
      exact ⟨⟨w, hwv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩, rfl⟩
  have hT : Even T.card := by
    have h := G.even_card_odd_degree_vertices
    rw [← hTimage, Finset.card_image_of_injective T Subtype.val_injective] at h
    exact h
  obtain ⟨R, hRG, hpar⟩ := exists_parity_subgraph hG T hT
  have hRG' : R.spanningCoe ≤ G := by
    intro w x h
    obtain ⟨a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp h
    exact hRG hab
  have hvR : v ∉ R.spanningCoe.support := by
    intro h
    exact spanningCoe_support_subset R h rfl
  have hdv : R.spanningCoe.degree v = 0 :=
    (SimpleGraph.degree_eq_zero_iff_notMem_support _ _).mpr hvR
  refine ⟨G ∆ R.spanningCoe, le_trans symmDiff_le_sup (sup_le le_rfl hRG'), ?_, ?_⟩
  · intro w
    apply Nat.even_iff.mpr
    have hd := degree_symmDiff_mod_two G R.spanningCoe w
    by_cases hw : w = v
    · subst w
      have hv' := Nat.even_iff.mp hv
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        at hdv hd hv' ⊢
      omega
    · have hp := hpar ⟨w, hw⟩
      have hr := spanningCoe_degree R ⟨w, hw⟩
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        at hd hr hp ⊢
      by_cases hodd : Odd (G.degree w)
      · have ho := Nat.odd_iff.mp hodd
        simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hodd ho
        rw [if_pos hodd] at hp
        omega
      · have he := Nat.even_iff.mp (Nat.not_odd_iff_even.mp hodd)
        simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hodd he
        rw [if_neg hodd] at hp
        omega
  · intro w
    have hn : ¬ R.spanningCoe.Adj v w := fun h => hvR ⟨w, h⟩
    simp only [symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj, hn, not_false_eq_true,
      and_true, false_and, or_false]

/-- A preconnected vertex complement lets us cover every incident edge of an
even-degree vertex using exactly half its degree many edge-disjoint cycles. -/
lemma exists_vertex_cycle_cover {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v : V) (hG : (G.induce {w : V | w ≠ v}).Preconnected) (hv : Even (G.degree v)) :
    ∃ (L : SimpleGraph V) (D : Finset L.Subgraph), L ≤ G ∧
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition L D ∧ (∀ w, L.Adj v w ↔ G.Adj v w) ∧
      2 * D.card = G.degree v := by
  classical
  obtain ⟨H, hHG, heven, hstar⟩ := even_subgraph_preserving_vertex G v hG hv
  obtain ⟨D, hD, hdec, _⟩ := exists_cycle_decomposition H heven
  obtain ⟨R, A, hRH, hReven, hvR, hA, hpA, hdis, hcover, hcardA⟩ :=
    prune_cycles_at_vertex D hD hdec v
  let L := subfamilyGraph A
  have hLA : (⋃ K ∈ A, K.edgeSet) = L.edgeSet := (subfamilyGraph_edges A).symm
  let B := Subfamilies.lowerFamily A hLA
  have hdeg : H.degree v = G.degree v := by
    have hn : H.neighborFinset v = G.neighborFinset v := by
      ext w
      simpa using hstar w
    exact congrArg Finset.card hn
  refine ⟨L, B, le_trans (subfamilyGraph_le A) hHG, ?_,
    Subfamilies.lowerFamily_decomposition A hLA hpA, ?_, ?_⟩
  · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using
      Subfamilies.lowerFamily_property (fun J => J.Connected ∧ J.IsRegularOfDegree 2) A hLA
        (by simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hA)
  · intro w
    constructor
    · intro h
      exact hHG (subfamilyGraph_le A h)
    · intro h
      have he : s(v,w) ∈ H.edgeSet := (hstar w).mpr h
      rw [← hcover] at he
      rcases he with he | he
      · show s(v,w) ∈ L.edgeSet
        rw [← hLA]
        exact he
      · exact (hvR ⟨w, he⟩).elim
  · have hc : B.card = A.card := Subfamilies.lowerFamily_card A hLA
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hcardA hdeg ⊢
    omega

lemma lift_decomposition_induce_support {V : Type*} [Fintype V]
    (G : SimpleGraph V) (s : Set V) (hs : G.support ⊆ s)
    (D : Finset (G.induce s).Subgraph)
    (hD : ∀ K ∈ D, IsCycleOrEdge K.coe) (hdec : IsDecomposition (G.induce s) D) :
    ∃ E : Finset G.Subgraph,
      (∀ K ∈ E, IsCycleOrEdge K.coe) ∧ IsDecomposition G E ∧ E.card ≤ D.card := by
  classical
  let f := (SimpleGraph.Embedding.induce (G := G) s).toHom
  obtain ⟨E, hE, hpE, heE, hcE⟩ :=
    SparseCuts.map_decomposition_injective f Subtype.val_injective D hD hdec
  refine ⟨E, hE, ⟨hpE, heE.trans ?_⟩, hcE⟩
  ext e
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact f.map_mem_edgeSet ha
  · intro he
    induction e using Sym2.ind with | h u v =>
    have hu : u ∈ s := hs ⟨v, he⟩
    have hv : v ∈ s := hs ⟨u, he.symm⟩
    exact ⟨s(⟨u, hu⟩, ⟨v, hv⟩), he, rfl⟩

lemma eliminate_even_degree_vertex {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v : V) (hG : (G.induce {w : V | w ≠ v}).Preconnected) (hv : Even (G.degree v))
    (k : ℕ) (hsmall : ∀ R : SimpleGraph {w : V // w ≠ v},
      ∃ D : Finset R.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition R D ∧ D.card ≤ k) :
    ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition G D ∧ 2 * D.card ≤ G.degree v + 2 * k := by
  classical
  obtain ⟨L, A, hLG, hA, hdecA, hstar, hcardA⟩ := exists_vertex_cycle_cover G v hG hv
  let R := G \ L
  let s : Set V := {w | w ≠ v}
  have hs : R.support ⊆ s := by
    rintro w ⟨x, h⟩ rfl
    exact h.2 ((hstar x).mpr h.1)
  obtain ⟨B, hB, hdecB, hcB⟩ := hsmall (R.induce s)
  obtain ⟨B', hB', hdecB', hcB'⟩ := lift_decomposition_induce_support R s hs B (by
    simpa only [IsCycleOrEdge, SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.edgeFinset_card,
      ← Nat.card_eq_fintype_card] using hB) hdecB
  obtain ⟨D, hD, hdecD, hcD⟩ := combine_decompositions hLG (show R ≤ G from sdiff_le)
    (by rw [show R = G \ L from rfl, SimpleGraph.edgeSet_sdiff]; exact Set.disjoint_sdiff_right)
    (by rw [show R = G \ L from rfl, SimpleGraph.edgeSet_sdiff];
        exact Set.union_diff_cancel (SimpleGraph.edgeSet_mono hLG))
    A B' (by
      intro H hH
      left
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hA H hH) hdecA hB' hdecB' 
  refine ⟨D, hD, hdecD, ?_⟩
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hcardA ⊢
  omega

set_option maxHeartbeats 600000 in
/-- Elimination for a vertex of arbitrary degree, paying at most half its degree
rounded up. The assumption concerns all possible residual graphs after deletion,
not just the original induced graph. -/
lemma eliminate_vertex {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v : V) (hG : (G.induce {w : V | w ≠ v}).Preconnected)
    (k : ℕ) (hsmall : ∀ R : SimpleGraph {w : V // w ≠ v},
      ∃ D : Finset R.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition R D ∧ D.card ≤ k) :
    ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition G D ∧ 2 * D.card ≤ G.degree v + G.degree v % 2 + 2 * k := by
  classical
  by_cases he : Even (G.degree v)
  · obtain ⟨D, hD, hdec, hc⟩ := eliminate_even_degree_vertex G v hG he k hsmall
    exact ⟨D, hD, hdec, by omega⟩
  · have ho := Nat.not_even_iff_odd.mp he
    obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp ho.pos
    let G' := G.deleteEdges {s(v,w)}
    have hconn : (G'.induce {x : V | x ≠ v}).Preconnected := by
      apply SimpleGraph.Preconnected.mono (G := G.induce {x : V | x ≠ v}) ?_ hG
      intro a b hab
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hab, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨ha, _⟩ | ⟨_, hb⟩)
      · exact a.property ha
      · exact b.property hb
    have hd : G'.degree v + 1 = G.degree v := by
      have h := degree_sdiff_add G (SimpleGraph.edge v w)
        ((SimpleGraph.edge_le_iff G).mpr (Or.inr hvw)) v
      have hd := degree_edge hvw.ne v
      simp only [true_or, ite_true] at hd
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h hd ⊢
      change Nat.card ((G \ SimpleGraph.edge v w).neighborSet v) + 1 = _
      omega
    have he' : Even (G'.degree v) := by
      have ho' := Nat.odd_iff.mp ho
      apply Nat.even_iff.mpr
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd ho' ⊢
      omega
    obtain ⟨D, hD, hdec, hc⟩ := eliminate_even_degree_vertex G' v hconn (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using he') k (by
      simpa only [IsCycleOrEdge, SimpleGraph.IsRegularOfDegree,
        ← SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.edgeFinset_card,
        ← Nat.card_eq_fintype_card] using hsmall)
    obtain ⟨E, hE, hdecE, hcE, _⟩ := Critical.restore_single_edge G ⟨s(v,w), hvw⟩ D (by
      simpa only [IsCycleOrEdge, SimpleGraph.IsRegularOfDegree,
        ← SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.edgeFinset_card,
        ← Nat.card_eq_fintype_card] using hD) hdec
    refine ⟨E, hE, hdecE, ?_⟩
    have ho' := Nat.odd_iff.mp ho
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd ho' hc ⊢
    omega

lemma separating_cut_adj {V : Type*} (G : SimpleGraph V) (v : V) (s : Set V)
    (hv : v ∉ s) (hsep : ∀ a ∈ s, ∀ b, b ∉ s → b ≠ v → ¬ G.Adj a b)
    (a b : V) : (G.between s sᶜ).Adj a b ↔
      G.Adj a b ∧ (a = v ∧ b ∈ s ∨ b = v ∧ a ∈ s) := by
  classical
  rw [SimpleGraph.between_adj]
  constructor
  · rintro ⟨hab, (⟨has, hbs⟩ | ⟨has, hbs⟩)⟩
    · exact ⟨hab, Or.inr ⟨by by_contra hb; exact hsep a has b hbs hb hab, has⟩⟩
    · exact ⟨hab, Or.inl ⟨by by_contra ha; exact hsep b hbs a has ha hab.symm, hbs⟩⟩
  · rintro ⟨hab, (⟨rfl, hbs⟩ | ⟨rfl, has⟩)⟩
    · exact ⟨hab, Or.inr ⟨hv, hbs⟩⟩
    · exact ⟨hab, Or.inl ⟨has, hv⟩⟩

lemma separating_cuts_degree_bound {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)
    (s t : Set V) (hdis : Disjoint s t) (hvs : v ∉ s) (hvt : v ∉ t)
    (hs : ∀ a ∈ s, ∀ b, b ∉ s → b ≠ v → ¬ G.Adj a b)
    (ht : ∀ a ∈ t, ∀ b, b ∉ t → b ≠ v → ¬ G.Adj a b) :
    (G.between s sᶜ).edgeFinset.card + (G.between t tᶜ).edgeFinset.card ≤ G.degree v := by
  classical
  have hcut (r : Set V) (hvr : v ∉ r)
      (hr : ∀ a ∈ r, ∀ b, b ∉ r → b ≠ v → ¬ G.Adj a b) :
      (G.between r rᶜ).edgeFinset ⊆ G.incidenceFinset v := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    rw [SimpleGraph.mem_incidenceFinset]
    induction e using Sym2.ind with | h a b =>
    rcases (separating_cut_adj G v r hvr hr a b).mp he with ⟨hab, (⟨rfl, _⟩ | ⟨rfl, _⟩)⟩
    · exact (G.mem_incidenceSet _ _).mpr hab
    · rw [Sym2.eq_swap]
      exact (G.mem_incidenceSet _ _).mpr hab.symm
  have hds : Disjoint (G.between s sᶜ).edgeFinset (G.between t tᶜ).edgeFinset := by
    apply Finset.disjoint_left.mpr
    intro e hes het
    rw [SimpleGraph.mem_edgeFinset] at hes het
    induction e using Sym2.ind with | h a b =>
    have hsa := (separating_cut_adj G v s hvs hs a b).mp hes
    have hta := (separating_cut_adj G v t hvt ht a b).mp het
    have hd := Set.disjoint_left.mp hdis
    rcases hsa.2 with ⟨rfl, hbs⟩ | ⟨rfl, has⟩
    · rcases hta.2 with ⟨_, hbt⟩ | ⟨hb, _⟩
      · exact hd hbs hbt
      · exact hvs (hb ▸ hbs)
    · rcases hta.2 with ⟨ha, _⟩ | ⟨_, hat⟩
      · exact hvs (ha ▸ has)
      · exact hd has hat
  calc
    _ = ((G.between s sᶜ).edgeFinset ∪ (G.between t tᶜ).edgeFinset).card :=
      (Finset.card_union_of_disjoint hds).symm
    _ ≤ (G.incidenceFinset v).card := Finset.card_le_card
      (Finset.union_subset (hcut s hvs hs) (hcut t hvt ht))
    _ = _ := G.card_incidenceFinset_eq_degree v

/-- Large edge cuts force the complement of a low-degree vertex to be preconnected. -/
lemma preconnected_vertex_complement_of_cuts {V : Type*} [Fintype V]
    (G : SimpleGraph V) (C : ℕ)
    (hcut : ∀ s : Set V, s.Nonempty → sᶜ.Nonempty → C < (G.between s sᶜ).edgeFinset.card)
    (v : V) (hv : G.degree v ≤ 2 * C) :
    (G.induce {w : V | w ≠ v}).Preconnected := by
  classical
  let I := G.induce {w : V | w ≠ v}
  intro a b
  by_contra hab
  let s : Set V := {w | ∃ hw : w ≠ v, I.Reachable a ⟨w, hw⟩}
  let t : Set V := {w | w ≠ v ∧ w ∉ s}
  have hvs : v ∉ s := by rintro ⟨h, _⟩; exact h rfl
  have hvt : v ∉ t := fun h => h.1 rfl
  have has : a.val ∈ s := ⟨a.property, .rfl⟩
  have hbt : b.val ∈ t := ⟨b.property, by rintro ⟨h, hr⟩; exact hab hr⟩
  have hs : ∀ x ∈ s, ∀ y, y ∉ s → y ≠ v → ¬ G.Adj x y := by
    rintro x ⟨hx, hr⟩ y hys hyv hxy
    exact hys ⟨hyv, hr.trans (show I.Adj ⟨x,hx⟩ ⟨y,hyv⟩ from hxy).reachable⟩
  have ht : ∀ x ∈ t, ∀ y, y ∉ t → y ≠ v → ¬ G.Adj x y := by
    rintro x ⟨hx, hxs⟩ y hyt hyv hxy
    have hys : y ∈ s := by by_contra h; exact hyt ⟨hyv, h⟩
    exact hs y hys x hxs hx hxy.symm
  have hd := separating_cuts_degree_bound G v s t
    (Set.disjoint_left.mpr (fun x hxs hxt => hxt.2 hxs)) hvs hvt hs ht
  have hcs := hcut s ⟨a.val, has⟩ ⟨v, hvs⟩
  have hct := hcut t ⟨b.val, hbt⟩ ⟨v, hvt⟩
  simp only [← SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] at hd hcs hct hv
  omega

universe u

/-- The general cycle-and-edge problem, not just its even-graph restriction, has
no smallest counterexample with degree at most `2C`. -/
lemma smallest_counterexample_min_degree {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : ℕ)
    (hbad : ∀ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) →
      IsDecomposition G D → C * (Fintype.card V - 1) < D.card)
    (hsmall : ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      Fintype.card W < Fintype.card V →
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition R D ∧
        D.card ≤ C * (Fintype.card W - 1)) :
    ∀ v, 2 * C < G.degree v := by
  classical
  have hn : 2 ≤ Fintype.card V := by
    by_contra h
    obtain ⟨D, hD, hdec, hc⟩ := SparseCuts.decomposition_of_card_le_one G (by omega)
    have hb := hbad D hD hdec
    omega
  intro v
  by_contra hv
  have hd : G.degree v ≤ 2 * C := Nat.le_of_not_gt hv
  have hc := preconnected_vertex_complement_of_cuts G C
    (SparseCuts.smallest_counterexample_cuts G C hbad hsmall) v hd
  obtain ⟨D, hD, hdec, hcD⟩ := eliminate_vertex G v hc
    (C * (Fintype.card {w : V // w ≠ v} - 1)) (by
      intro R
      apply hsmall R
      exact Fintype.card_subtype_lt (x := v) (by simp))
  have hb := hbad D hD hdec
  have hcard : Fintype.card {w : V // w ≠ v} = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl (fun w : V => w = v)]
    simp
  have hbudget : C * (Fintype.card {w : V // w ≠ v} - 1) + C =
      C * (Fintype.card V - 1) := by
    rw [hcard, ← Nat.mul_succ]
    congr 1
    omega
  have hround : G.degree v + G.degree v % 2 ≤ 2 * C := by omega
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    at hcD hb hbudget hround
  omega

/-- The missing uniform bound can be restricted simultaneously to edge-critical,
highly edge-connected graphs of minimum degree greater than `2C`. -/
lemma uniform_bound_of_critical_high_min_degree (C : ℕ)
    (hhigh : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      Critical.EdgeCritical G → G.IsEdgeConnected (C + 1) → (∀ v, 2 * C < G.degree v) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        D.card ≤ C * (Fintype.card V - 1)) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        D.card ≤ C * (Fintype.card V - 1) := by
  classical
  have main : ∀ n : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      Fintype.card V = n → Critical.number G ≤ C * (Fintype.card V - 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ _ G hn
      by_contra! hbad
      obtain ⟨R, hRG, hcrit, hnumber⟩ := Critical.exists_critical_subgraph G
      have hRbad : C * (Fintype.card V - 1) < Critical.number R := hnumber.symm ▸ hbad
      have hsmall : ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W),
          Fintype.card W < Fintype.card V →
          ∃ D : Finset H.Subgraph, (∀ K ∈ D, IsCycleOrEdge K.coe) ∧
            IsDecomposition H D ∧ D.card ≤ C * (Fintype.card W - 1) := by
        intro W _ _ H hcard
        apply (Critical.number_le_iff H _).mp
        exact ih (Fintype.card W) (hcard.trans_eq hn) H rfl
      have hRbad' : ∀ D : Finset R.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) →
          IsDecomposition R D → C * (Fintype.card V - 1) < D.card := by
        intro D hD hdec
        exact hRbad.trans_le (Critical.number_le D hD hdec)
      have hconn := SparseCuts.smallest_counterexample_edge_connected R C hRbad' hsmall
      have hmin := smallest_counterexample_min_degree R C hRbad' hsmall
      obtain ⟨D, hD, hdec, hc⟩ := hhigh R hcrit hconn (by
        simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hmin)
      exact (not_lt_of_ge ((Critical.number_le D hD hdec).trans hc) hRbad)
  intro V _ _ G
  exact (Critical.number_le_iff G _).mp (main (Fintype.card V) G rfl)

open Filter in
lemma asymptotic_iff_critical_high_min_degree_uniform :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      Critical.EdgeCritical G → G.IsEdgeConnected (C + 1) → (∀ v, 2 * C < G.degree v) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        D.card ≤ C * (Fintype.card V - 1)) := by
  rw [asymptotic_iff_uniform, SparseCuts.uniform_bound_iff_shifted_bound]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun G _ _ _ => hC G⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, uniform_bound_of_critical_high_min_degree C hC⟩

#print axioms exists_parity_subgraph
#print axioms even_subgraph_preserving_vertex
#print axioms exists_vertex_cycle_cover
#print axioms eliminate_even_degree_vertex
#print axioms eliminate_vertex
#print axioms preconnected_vertex_complement_of_cuts
#print axioms smallest_counterexample_min_degree
#print axioms asymptotic_iff_critical_high_min_degree_uniform
end Erdos184Work.Vertex



/- Minimum decomposition size after adding one edge to an even graph. -/
namespace Erdos184Work.SingleAddition
open SimpleGraph
open scoped Classical

lemma regular_two_not_acyclic {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected) (hreg : G.IsRegularOfDegree 2) : ¬ G.IsAcyclic := by
  classical
  intro ha
  have hb := acyclic_even_eq_bot G ha (fun v => by rw [hreg v]; decide)
  obtain ⟨v⟩ := hconn.nonempty
  have h := hreg v
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h
  rw [hb] at h
  simp [SimpleGraph.neighborSet] at h

lemma cycle_family_le_feedback_edges {V : Type*} [Fintype V] (G F : SimpleGraph V)
    (hF : F.IsAcyclic) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hp : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    D.card ≤ (G \ F).edgeFinset.card := by
  classical
  have hex : ∀ H : D, ∃ e : (G \ F).edgeSet, e.val ∈ H.val.edgeSet := by
    intro H
    by_contra! h
    have hHF : H.val.spanningCoe ≤ F := by
      intro u v huv
      by_contra hFuv
      exact h ⟨s(u,v), H.val.adj_sub huv, hFuv⟩ huv
    have hacyc : H.val.coe.IsAcyclic := hF.comap
      (⟨Subtype.val, fun h => hHF h⟩ : H.val.coe →g F) Subtype.val_injective
    exact regular_two_not_acyclic H.val.coe (hD H.val H.property).1
      (by simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using (hD H.val H.property).2) hacyc
  choose f hf using hex
  have hi : Function.Injective f := by
    intro H K he
    apply Subtype.ext
    by_contra hne
    exact Set.disjoint_left.mp (hp H.property K.property hne) (hf H) (he ▸ hf K)
  have hcard := Fintype.card_le_of_injective f hi
  simpa only [Fintype.card_coe, SimpleGraph.card_edgeSet] using hcard

lemma even_feedback_decomposition {V : Type*} [Fintype V] (G F : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) (hF : F.IsAcyclic) :
    ∃ D : Finset G.Subgraph, (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ (G \ F).edgeFinset.card := by
  obtain ⟨D, hD, hdec, _⟩ := exists_cycle_decomposition G heven
  exact ⟨D, hD, hdec, cycle_family_le_feedback_edges G F hF D hD hdec.1⟩

lemma cycle_closed_under_walk {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsCycles) {u : V} (p : G.Walk u u) (hp : p.IsCycle)
    {x y : V} (q : G.Walk x y) (hy : y ∈ p.toSubgraph.verts) : x ∈ p.toSubgraph.verts := by
  classical
  induction q with
  | nil => exact hy
  | @cons x z y hx q ih =>
    have hz := ih hy
    have hzx := (hp.adj_toSubgraph_iff_of_isCycles hG hz x).mpr hx.symm
    exact p.toSubgraph.edge_vert hzx.symm

lemma delete_cycle_edge_acyclic {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H : G.Subgraph) (hconn : H.coe.Connected) (hreg : H.coe.IsRegularOfDegree 2)
    (e : H.edgeSet) : (H.spanningCoe.deleteEdges {e.val}).IsAcyclic := by
  classical
  have hcyc : H.spanningCoe.IsCycles := by
    intro v hv
    have hverts : v ∈ H.verts := by
      obtain ⟨w, hw⟩ := hv
      exact H.edge_vert hw
    have h := regular_two_spanning_degree H hreg v
    rw [if_pos hverts] at h
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using h
  intro u c hc
  let p := c.mapLe (H.spanningCoe.deleteEdges_le {e.val})
  have hp : p.IsCycle := hc.mapLe _
  have huH : u ∈ H.verts :=
    H.edge_vert ((SimpleGraph.deleteEdges_adj.mp (c.toSubgraph.adj_sub
      (c.toSubgraph_adj_snd hc.not_nil))).1)
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with | h a b =>
  have ha : a ∈ H.verts := H.edge_vert he
  obtain ⟨q⟩ := hconn.preconnected ⟨a,ha⟩ ⟨u,huH⟩
  let f : H.coe →g H.spanningCoe := ⟨Subtype.val, fun h => h⟩
  have hpa : a ∈ p.toSubgraph.verts := cycle_closed_under_walk hcyc p hp (q.map f) (by change u ∈ p.toSubgraph.verts; simp)
  have hpab : p.toSubgraph.Adj a b := (hp.adj_toSubgraph_iff_of_isCycles hcyc hpa b).mpr he
  have hcab : c.toSubgraph.Adj a b := by simpa only [p, Walk.adj_toSubgraph_mapLe] using hpab
  exact (SimpleGraph.deleteEdges_adj.mp (c.toSubgraph.adj_sub hcab)).2 (Set.mem_singleton _)

set_option maxHeartbeats 700000 in
lemma remove_edge_in_cycle_to_even {V : Type*} [Fintype V] (G : SimpleGraph V)
    (e : G.edgeSet) (heven : ∀ v, Even ((G.deleteEdges {e.val}).degree v))
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D) (H : G.Subgraph) (hHD : H ∈ D)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) (heH : e.val ∈ H.edgeSet) :
    ∃ E : Finset (G.deleteEdges {e.val}).Subgraph,
      (∀ K ∈ E, IsCycleOrEdge K.coe) ∧ IsDecomposition (G.deleteEdges {e.val}) E ∧
      E.card + 1 ≤ D.card := by
  classical
  let A := Critical.edgePieces D
  let B := D \ insert H A
  let M := subfamilyGraph B
  let G' := G.deleteEdges {e.val}
  let R := G' \ M
  let F := H.spanningCoe.deleteEdges {e.val}
  have hAD : A ⊆ D := Finset.filter_subset _ _
  have hBD : B ⊆ D := Finset.sdiff_subset
  have hHA : H ∉ A := by
    intro h
    exact Critical.regular_two_not_single_edge H.coe hH.1 (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hH.2) (Finset.mem_filter.mp h).2
  have hpB : Set.PairwiseDisjoint (B : Set G.Subgraph) (fun K => K.edgeSet) :=
    fun _ hK _ hL hne => hdec.1 (hBD hK) (hBD hL) hne
  have hB : ∀ K ∈ B, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2 := by
    intro K hK
    have hn : K ∉ A := fun h => (Finset.mem_sdiff.mp hK).2 (Finset.mem_insert_of_mem h)
    rcases hD K (hBD hK) with hc | he
    · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hc
    · exact (hn (Finset.mem_filter.mpr ⟨hBD hK, he⟩)).elim
  have hMe : e.val ∉ M.edgeSet := by
    rw [subfamilyGraph_edges]
    intro he
    obtain ⟨K, hK⟩ := Set.mem_iUnion.mp he
    obtain ⟨hKB, heK⟩ := Set.mem_iUnion.mp hK
    exact Set.disjoint_left.mp (hdec.1 (hBD hKB) hHD (by
      intro h
      exact (Finset.mem_sdiff.mp hKB).2 (Finset.mem_insert.mpr (Or.inl h)))) heK heH
  have hMG' : M ≤ G' := by
    intro x y hxy
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨subfamilyGraph_le B hxy, ?_⟩
    intro he
    exact hMe (Set.mem_singleton_iff.mp he ▸ hxy)
  have hMeven := cycle_subfamily_even B hB hpB
  have hReven : ∀ v, Even (R.degree v) := by
    intro v
    have hd := degree_sdiff_add G' M hMG' v
    have hg := Nat.even_iff.mp (heven v)
    have hm := Nat.even_iff.mp (hMeven v)
    apply Nat.even_iff.mpr
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd hg hm ⊢
    dsimp only [M, G', R] at hd hg hm ⊢
    omega
  have hF : F.IsAcyclic := delete_cycle_edge_acyclic H hH.1 hH.2 ⟨e.val, heH⟩
  have hRF : R \ F ≤ subfamilyGraph A := by
    intro x y hxy
    have hGxy : G.Adj x y := (SimpleGraph.deleteEdges_adj.mp hxy.1.1).1
    have hxye : s(x,y) ≠ e.val := by
      simpa only [Set.mem_singleton_iff] using (SimpleGraph.deleteEdges_adj.mp hxy.1.1).2
    have hnotH : ¬ H.Adj x y := by
      intro h
      exact hxy.2 (SimpleGraph.deleteEdges_adj.mpr ⟨h, by simpa using hxye⟩)
    have heD : s(x,y) ∈ ⋃ K ∈ D, K.edgeSet := hdec.2.symm ▸ hGxy
    obtain ⟨K, heK⟩ := Set.mem_iUnion.mp heD
    obtain ⟨hKD, heK⟩ := Set.mem_iUnion.mp heK
    by_cases hKA : K ∈ A
    · show s(x,y) ∈ (subfamilyGraph A).edgeSet
      rw [subfamilyGraph_edges]
      exact Set.mem_iUnion.mpr ⟨K, Set.mem_iUnion.mpr ⟨hKA, heK⟩⟩
    · have hKH : K ≠ H := by rintro rfl; exact hnotH heK
      have hKB : K ∈ B := Finset.mem_sdiff.mpr ⟨hKD, by simpa using And.intro hKH hKA⟩
      apply (hxy.1.2 ?_).elim
      show s(x,y) ∈ M.edgeSet
      rw [subfamilyGraph_edges]
      exact Set.mem_iUnion.mpr ⟨K, Set.mem_iUnion.mpr ⟨hKB, heK⟩⟩
  obtain ⟨E, hE, hdecE, hcE⟩ := even_feedback_decomposition R F (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hReven) hF
  have hcardA : (subfamilyGraph A).edgeFinset.card = A.card := by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
      Critical.edgePieces_graph_card D hdec
  have hcEF : (R \ F).edgeFinset.card ≤ (subfamilyGraph A).edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hRF)
  let hcover := (subfamilyGraph_edges B).symm
  let B' := Subfamilies.lowerFamily B hcover
  have hB' : ∀ K ∈ B', IsCycleOrEdge K.coe := by
    apply Subfamilies.lowerFamily_property IsCycleOrEdge B hcover
    intro K hK
    left
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hB K hK
  have hdecB' := Subfamilies.lowerFamily_decomposition B hcover hpB
  obtain ⟨J, hJ, hdecJ, hcJ⟩ := combine_decompositions hMG' (show R ≤ G' from sdiff_le)
    (by rw [show R = G' \ M from rfl, SimpleGraph.edgeSet_sdiff]; exact Set.disjoint_sdiff_right)
    (by rw [show R = G' \ M from rfl, SimpleGraph.edgeSet_sdiff];
        exact Set.union_diff_cancel (SimpleGraph.edgeSet_mono hMG'))
    B' E hB' hdecB' (by
      intro K hK
      left
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hE K hK) hdecE
  refine ⟨J, hJ, hdecJ, ?_⟩
  have hcB' : B'.card = B.card := Subfamilies.lowerFamily_card B hcover
  have hcardD : B.card + (insert H A).card = D.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hHD hAD)
  rw [Finset.card_insert_of_notMem hHA] at hcardD
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcE hcardA hcEF
  omega

lemma remove_edge_to_even_number {V : Type*} [Fintype V] (G : SimpleGraph V)
    (e : G.edgeSet) (heven : ∀ v, Even ((G.deleteEdges {e.val}).degree v)) :
    Critical.number G = Critical.number (G.deleteEdges {e.val}) + 1 := by
  classical
  obtain ⟨D, hD, hdec, hcD⟩ := Critical.exists_minimum G
  have heD : e.val ∈ ⋃ H ∈ D, H.edgeSet := hdec.2.symm ▸ e.property
  obtain ⟨H, heH⟩ := Set.mem_iUnion.mp heD
  obtain ⟨hHD, heH⟩ := Set.mem_iUnion.mp heH
  rcases hD H hHD with hcyc | hedge
  · obtain ⟨E, hE, hdecE, hcE⟩ := remove_edge_in_cycle_to_even G e heven D hD hdec H hHD (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hcyc) heH
    have hlo := Critical.number_le E hE hdecE
    have hhi := Critical.number_restore_edge G e
    omega
  · have hcard : H.spanningCoe.edgeFinset.card = 1 := (subgraph_edge_card H).trans hedge
    obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard
    have he : e.val = f := by
      have h : e.val ∈ H.spanningCoe.edgeFinset := SimpleGraph.mem_edgeFinset.mpr heH
      change e.val ∈ H.spanningCoe.edgeFinset at h
      simpa only [hf, Finset.mem_singleton] using h
    have hedgeSet : H.edgeSet = {e.val} := by
      ext g
      change g ∈ H.spanningCoe.edgeSet ↔ _
      rw [← SimpleGraph.mem_edgeFinset, hf]
      simp [he]
    exact Subfamilies.remove_single_piece_number D hD hdec hcD e H hHD hedgeSet

/-- Adding a genuinely new edge to an even graph increases the optimum by
exactly one. This is a local exact formula, not a uniform bound. -/
lemma add_edge_to_even_number {V : Type*} [Fintype V] (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) {u v : V} (hne : u ≠ v) (hn : ¬ G.Adj u v) :
    Critical.number (G ⊔ SimpleGraph.edge u v) = Critical.number G + 1 := by
  classical
  have heq : (G ⊔ SimpleGraph.edge u v).deleteEdges {s(u,v)} = G := by
    change (G ⊔ SimpleGraph.edge u v) \ SimpleGraph.edge u v = G
    rw [sup_sdiff, sdiff_self, sup_bot_eq, SimpleGraph.sdiff_edge G hn]
  have he : s(u,v) ∈ (G ⊔ SimpleGraph.edge u v).edgeSet :=
    Or.inr ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)
  have h := remove_edge_to_even_number (G ⊔ SimpleGraph.edge u v) ⟨s(u,v), he⟩ (by
    intro w
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    rw [heq]
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heven w)
  simpa only [heq] using h

#print axioms cycle_family_le_feedback_edges
#print axioms delete_cycle_edge_acyclic
#print axioms remove_edge_in_cycle_to_even
#print axioms remove_edge_to_even_number
#print axioms add_edge_to_even_number
end Erdos184Work.SingleAddition



/- A checked obstruction to an additional structural restriction on critical graphs. -/
namespace Erdos184Work.CriticalExample
open SimpleGraph
open scoped Classical

lemma independent_right_degree_sum_le {A B : Type*} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B)) (hno : ∀ b c : B, ¬ G.Adj (.inr b) (.inr c)) :
    (∑ b : B, G.degree (.inr b)) ≤ G.edgeFinset.card := by
  classical
  let K := G ⊓ completeBipartiteGraph A B
  have hd : ∀ b : B, K.degree (.inr b) = G.degree (.inr b) := by
    intro b
    have hn : K.neighborFinset (.inr b) = G.neighborFinset (.inr b) := by
      ext x
      cases x <;> simp [K, completeBipartiteGraph, hno]
    exact congrArg Finset.card hn
  have hc := (BipartiteLower.bipartite_edge_sums K inf_le_right).2
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hc hd ⊢
  rw [Finset.sum_congr (s₁ := Finset.univ) rfl (fun b _ => hd b)] at hc
  have hu := Finset.card_le_card (SimpleGraph.edgeFinset_mono (show K ≤ G from inf_le_left))
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc hu ⊢
  omega

/-- A parity lower bound using an independent side of a vertex partition. -/
lemma independent_side_lower_bound {A B : Type*} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B)) (ha : 1 ≤ Fintype.card A)
    (hno : ∀ b c : B, ¬ G.Adj (.inr b) (.inr c))
    (hodd : ∀ b : B, Odd (G.degree (.inr b)))
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D) :
    (∑ a : A, G.degree (.inl a)) + 2 * Fintype.card A * Fintype.card B ≤
      2 * Fintype.card A * D.card + Fintype.card B := by
  classical
  let E := Critical.edgePieces D
  let C := D \ E
  let F := subfamilyGraph E
  let M := subfamilyGraph C
  have hED : E ⊆ D := Finset.filter_subset _ _
  have hCD : C ⊆ D := Finset.sdiff_subset
  have hpE : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hdec.1 (hED hH) (hED hK) hne
  have hpC : Set.PairwiseDisjoint (C : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hdec.1 (hCD hH) (hCD hK) hne
  have hC : ∀ H ∈ C, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    rcases hD H (hCD hH) with hc | he
    · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hc
    · exact ((Finset.mem_sdiff.mp hH).2 (Finset.mem_filter.mpr ⟨hCD hH, he⟩)).elim
  have hFcard : F.edgeFinset.card = E.card := Critical.edgePieces_graph_card D hdec
  have hFright : Fintype.card B ≤ ∑ b : B, F.degree (.inr b) := by
    have hpos : ∀ b : B, 1 ≤ F.degree (.inr b) := by
      intro b
      have hpar := Critical.edgePieces_degree_parity D hD hdec (.inr b)
      have hn : ¬ Even (G.degree (.inr b)) := Nat.not_even_iff_odd.mpr (hodd b)
      have hnot := mt hpar.mp hn
      change ¬ Even (F.degree (.inr b)) at hnot
      rw [Nat.even_iff] at hnot
      omega
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hpos b)
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using hs
  have hFright' : (∑ b : B, F.degree (.inr b)) ≤ E.card := by
    have h := independent_right_degree_sum_le F (fun b c hbc => hno b c (subfamilyGraph_le E hbc))
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at h hFcard
    exact h.trans_eq hFcard
  have hMleft : (∑ a : A, M.degree (.inl a)) ≤ 2 * Fintype.card A * C.card := by
    have hd : ∀ a : A, M.degree (.inl a) ≤ 2 * C.card := by
      intro a
      rw [subfamilyGraph_degree C hpC]
      have h := Finset.sum_le_sum (s := C) (fun H hH => show H.spanningCoe.degree (.inl a) ≤ 2 by
        rw [regular_two_spanning_degree H (hC H hH).2]
        split_ifs <;> omega)
      simpa only [Finset.sum_const, smul_eq_mul, mul_comm] using h
    have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hd a)
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← mul_assoc, mul_comm] using h
  have htotalF : (∑ a : A, F.degree (.inl a)) + (∑ b : B, F.degree (.inr b)) = 2 * E.card := by
    have h := F.sum_degrees_eq_twice_card_edges
    rw [Fintype.sum_sum_type] at h
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at h hFcard
    omega
  have hDG : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  have hdegs : ∀ v, M.degree v + F.degree v = G.degree v := by
    intro v
    have h := Finset.sum_sdiff (f := fun H : G.Subgraph => H.spanningCoe.degree v) hED
    change (∑ H ∈ C, H.spanningCoe.degree v) + (∑ H ∈ E, H.spanningCoe.degree v) = _ at h
    rw [← subfamilyGraph_degree C hpC, ← subfamilyGraph_degree E hpE,
      ← subfamilyGraph_degree D hdec.1, hDG] at h
    exact h
  have hleft : (∑ a : A, M.degree (.inl a)) + (∑ a : A, F.degree (.inl a)) =
      ∑ a : A, G.degree (.inl a) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => hdegs _)
  have hcount : C.card + E.card = D.card := Finset.card_sdiff_add_card_eq_card hED
  have hmul := Nat.mul_le_mul_left (2 * Fintype.card A - 2) (hFright.trans hFright')
  have ha' : 2 * Fintype.card A - 2 + 2 = 2 * Fintype.card A := by omega
  nlinarith

/-- Complete graph on the left part, independent set on the right, all crossing edges. -/
def splitGraph (A B : Type*) : SimpleGraph (A ⊕ B) where
  Adj
    | .inl a, .inl b => a ≠ b
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr _, .inr _ => False
  symm := by intro x y h; cases x <;> cases y <;> simp_all [ne_comm]
  loopless := by intro x; cases x <;> simp

instance {A B : Type*} [DecidableEq A] : DecidableRel (splitGraph A B).Adj := fun x y => by
  cases x <;> cases y <;> dsimp [splitGraph] <;> infer_instance

abbrev V := Fin 3 ⊕ Fin 4
abbrev exampleGraph := splitGraph (Fin 3) (Fin 4)

lemma example_degrees :
    (∀ a : Fin 3, exampleGraph.degree (.inl a) = 6) ∧
    (∀ b : Fin 4, exampleGraph.degree (.inr b) = 3) := by decide

lemma example_lower_bound (D : Finset exampleGraph.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition exampleGraph D) :
    7 ≤ D.card := by
  have hd := example_degrees
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd
  have h := independent_side_lower_bound exampleGraph (by decide)
    (by intro b c; exact id) (by
      intro b
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      rw [hd.2 b]
      decide) D hD hdec
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h
  simp only [hd.1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.card_fin,
    smul_eq_mul] at h
  omega

def c0 : exampleGraph.Walk (.inl 0) (.inl 0) :=
  .cons (show exampleGraph.Adj (.inl 0) (.inl 2) by decide) (.cons (show exampleGraph.Adj (.inl 2) (.inr 0) by decide) (.cons (show exampleGraph.Adj (.inr 0) (.inl 1) by decide) (.cons (show exampleGraph.Adj (.inl 1) (.inr 2) by decide) (.cons (show exampleGraph.Adj (.inr 2) (.inl 0) by decide) (.nil)))))

lemma c0_cycle : c0.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def c1 : exampleGraph.Walk (.inl 0) (.inl 0) :=
  .cons (show exampleGraph.Adj (.inl 0) (.inr 1) by decide) (.cons (show exampleGraph.Adj (.inr 1) (.inl 2) by decide) (.cons (show exampleGraph.Adj (.inl 2) (.inl 1) by decide) (.cons (show exampleGraph.Adj (.inl 1) (.inr 3) by decide) (.cons (show exampleGraph.Adj (.inr 3) (.inl 0) by decide) (.nil)))))

lemma c1_cycle : c1.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

lemma single_piece_property {W : Type*} [Fintype W] {G : SimpleGraph W}
    {a b : W} (h : G.Adj a b) : IsCycleOrEdge (G.subgraphOfAdj h).coe := by
  right
  rw [← subgraph_edge_card]
  have he : (G.subgraphOfAdj h).spanningCoe.edgeSet = {s(a,b)} := SimpleGraph.edgeSet_subgraphOfAdj h
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  change ((G.subgraphOfAdj h).spanningCoe.edgeSet).ncard = 1
  rw [he]
  simp

def piece : Fin 7 → exampleGraph.Subgraph
  | 0 => c0.toSubgraph
  | 1 => c1.toSubgraph
  | 2 => exampleGraph.subgraphOfAdj (show exampleGraph.Adj (.inl 0) (.inl 1) by decide)
  | 3 => exampleGraph.subgraphOfAdj (show exampleGraph.Adj (.inl 0) (.inr 0) by decide)
  | 4 => exampleGraph.subgraphOfAdj (show exampleGraph.Adj (.inl 1) (.inr 1) by decide)
  | 5 => exampleGraph.subgraphOfAdj (show exampleGraph.Adj (.inl 2) (.inr 2) by decide)
  | 6 => exampleGraph.subgraphOfAdj (show exampleGraph.Adj (.inl 2) (.inr 3) by decide)

def pieceEdges : Fin 7 → Finset (Sym2 V)
  | 0 => c0.edges.toFinset
  | 1 => c1.edges.toFinset
  | 2 => {s(.inl 0, .inl 1)}
  | 3 => {s(.inl 0, .inr 0)}
  | 4 => {s(.inl 1, .inr 1)}
  | 5 => {s(.inl 2, .inr 2)}
  | 6 => {s(.inl 2, .inr 3)}

lemma piece_edges (i : Fin 7) : (piece i).edgeSet = (pieceEdges i : Set (Sym2 V)) := by
  fin_cases i
  · ext e
    simp only [piece, pieceEdges, Finset.mem_coe, List.mem_toFinset]
    exact c0.mem_edges_toSubgraph
  · ext e
    simp only [piece, pieceEdges, Finset.mem_coe, List.mem_toFinset]
    exact c1.mem_edges_toSubgraph
  all_goals simp [piece, pieceEdges, SimpleGraph.edgeSet_subgraphOfAdj]

lemma piece_property (i : Fin 7) : IsCycleOrEdge (piece i).coe := by
  fin_cases i
  · left
    simpa only [piece, SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular exampleGraph c0_cycle
  · left
    simpa only [piece, SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular exampleGraph c1_cycle
  all_goals exact single_piece_property (by decide)

lemma pieceEdges_disjoint : ∀ i j : Fin 7, i ≠ j → Disjoint (pieceEdges i) (pieceEdges j) := by
  decide

lemma pieceEdges_cover : ∀ a b : V, exampleGraph.Adj a b ↔ ∃ i : Fin 7, s(a,b) ∈ pieceEdges i := by
  decide

noncomputable def exampleDecomposition : Finset exampleGraph.Subgraph := Finset.univ.image piece

lemma exampleDecomposition_property : ∀ H ∈ exampleDecomposition, IsCycleOrEdge H.coe := by
  intro H hH
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
  exact piece_property i

lemma exampleDecomposition_isDecomposition : IsDecomposition exampleGraph exampleDecomposition := by
  constructor
  · intro H hH K hK hne
    change H ∈ exampleDecomposition at hH
    change K ∈ exampleDecomposition at hK
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hK
    change Disjoint (piece i).edgeSet (piece j).edgeSet
    rw [piece_edges, piece_edges, Finset.disjoint_coe]
    exact pieceEdges_disjoint i j (fun h => hne (congrArg piece h))
  · ext e
    induction e using Sym2.ind with | h a b =>
    simp only [Set.mem_iUnion, exists_prop, exampleDecomposition, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨H, ⟨i, rfl⟩, he⟩
      exact (piece i).edgeSet_subset he
    · intro he
      obtain ⟨i, hi⟩ := (pieceEdges_cover a b).mp he
      exact ⟨piece i, ⟨i, rfl⟩, (piece_edges i).symm ▸ hi⟩

lemma example_number : Critical.number exampleGraph = 7 := by
  have hlo : 7 ≤ Critical.number exampleGraph := by
    obtain ⟨D, hD, hdec, hc⟩ := Critical.exists_minimum exampleGraph
    rw [← hc]
    exact example_lower_bound D hD hdec
  have hhi := Critical.number_le exampleDecomposition exampleDecomposition_property
    exampleDecomposition_isDecomposition
  have hc : exampleDecomposition.card ≤ 7 := by
    have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin 7))) (f := piece)
    simpa [exampleDecomposition] using h
  omega

lemma critical_of_exposure_orbits {W : Type*} [Fintype W] (G : SimpleGraph W)
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D) (hcD : D.card = Critical.number G)
    (horbit : ∀ e : G.edgeSet, ∃ H ∈ D, ∃ φ : G ≃g G,
      Sym2.map φ.toHom '' H.edgeSet = {e.val}) : Critical.EdgeCritical G := by
  classical
  intro e
  obtain ⟨H, hHD, φ, hφ⟩ := horbit e
  let E := D.image (SimpleGraph.Subgraph.map φ.toHom)
  have hE : ∀ K ∈ E, IsCycleOrEdge K.coe := by
    intro K hK
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
    exact SparseCuts.piece_property_map_injective φ.toHom φ.injective L (hD L hL)
  have hdecE : IsDecomposition G E := map_isDecomposition_iso φ D hdec
  have hcE : E.card = Critical.number G := by
    have hlo := Critical.number_le E hE hdecE
    have hhi : E.card ≤ D.card := Finset.card_image_le
    omega
  apply Subfamilies.remove_single_piece_number E hE hdecE hcE e (H.map φ.toHom)
    (Finset.mem_image.mpr ⟨H, hHD, rfl⟩)
  rw [SimpleGraph.Subgraph.edgeSet_map]
  exact hφ

def splitIso {A B A' B' : Type*} (eA : A ≃ A') (eB : B ≃ B') :
    splitGraph A B ≃g splitGraph A' B' where
  toEquiv := eA.sumCongr eB
  map_rel_iff' := by
    intro x y
    cases x <;> cases y <;> simp [splitGraph]

lemma pair_perm (a b : Fin 3) (hne : a ≠ b) :
    ∃ e : Equiv.Perm (Fin 3), e 0 = a ∧ e 1 = b := by
  let f := Equiv.swap (0 : Fin 3) a
  refine ⟨f.trans (Equiv.swap (f 1) b), ?_, ?_⟩
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (by
      have h := f.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
      simpa only [f, Equiv.swap_apply_left] using h) hne
  · exact Equiv.swap_apply_left _ _

lemma example_exposure_orbits : ∀ e : exampleGraph.edgeSet,
    ∃ H ∈ exampleDecomposition, ∃ φ : exampleGraph ≃g exampleGraph,
      Sym2.map φ.toHom '' H.edgeSet = {e.val} := by
  have h2 : (piece 2).edgeSet = {s((.inl 0 : V), .inl 1)} := by rw [piece_edges]; simp [pieceEdges]
  have h3 : (piece 3).edgeSet = {s((.inl 0 : V), .inr 0)} := by rw [piece_edges]; simp [pieceEdges]
  have hmem : ∀ i, piece i ∈ exampleDecomposition := fun i =>
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rintro ⟨e, he⟩
  induction e using Sym2.ind with | h x y =>
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      obtain ⟨p, hp0, hp1⟩ := pair_perm a b he
      refine ⟨piece 2, hmem 2, splitIso p (Equiv.refl _), ?_⟩
      rw [h2, Set.image_singleton, Sym2.map_pair_eq]
      simp [splitIso, hp0, hp1]
    | inr b =>
      refine ⟨piece 3, hmem 3, splitIso (Equiv.swap 0 a) (Equiv.swap 0 b), ?_⟩
      rw [h3, Set.image_singleton, Sym2.map_pair_eq]
      simp [splitIso]
  | inr b =>
    cases y with
    | inl a =>
      refine ⟨piece 3, hmem 3, splitIso (Equiv.swap 0 a) (Equiv.swap 0 b), ?_⟩
      rw [h3, Set.image_singleton, Sym2.map_pair_eq]
      simp [splitIso, Sym2.eq_swap]
    | inr c => exact he.elim

lemma example_critical : Critical.EdgeCritical exampleGraph := by
  apply critical_of_exposure_orbits exampleGraph exampleDecomposition exampleDecomposition_property
    exampleDecomposition_isDecomposition ?_ example_exposure_orbits
  have hl := Critical.number_le exampleDecomposition exampleDecomposition_property
    exampleDecomposition_isDecomposition
  have hh : exampleDecomposition.card ≤ 7 := by
    have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin 7))) (f := piece)
    simpa [exampleDecomposition] using h
  rw [example_number] at hl ⊢
  omega

lemma example_delete_vertex_connected (v : V) :
    (exampleGraph.induce {w : V | w ≠ v}).Connected := by
  have hex : ∀ v : V, ∃ a : Fin 3, (.inl a : V) ≠ v := by decide
  obtain ⟨a, ha⟩ := hex v
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨.inl a, ha⟩, ?_⟩
  intro w
  by_cases hw : w.val = .inl a
  · have heq : w = ⟨.inl a,ha⟩ := Subtype.ext hw
    rw [heq]
  · apply SimpleGraph.Adj.reachable
    change exampleGraph.Adj (.inl a) w.val
    cases hwv : w.val with
    | inl b => exact fun h => hw (by simp [hwv, h])
    | inr b => trivial

noncomputable def evenVertex (a : Fin 3) : {v : V // Even (exampleGraph.degree v)} :=
  ⟨.inl a, by
    have h := example_degrees.1 a
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
    rw [h]
    decide⟩

noncomputable def evenTriangle :
    (exampleGraph.induce {v : V | Even (exampleGraph.degree v)}).Walk (evenVertex 0) (evenVertex 0) :=
  .cons (show (exampleGraph.induce {v : V | Even (exampleGraph.degree v)}).Adj
    (evenVertex 0) (evenVertex 1) by change (0 : Fin 3) ≠ 1; decide)
    (.cons (show (exampleGraph.induce {v : V | Even (exampleGraph.degree v)}).Adj
      (evenVertex 1) (evenVertex 2) by change (1 : Fin 3) ≠ 2; decide)
      (.cons (show (exampleGraph.induce {v : V | Even (exampleGraph.degree v)}).Adj
        (evenVertex 2) (evenVertex 0) by change (2 : Fin 3) ≠ 0; decide) .nil))

lemma evenTriangle_cycle : evenTriangle.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

lemma even_vertices_not_acyclic :
    ¬ (exampleGraph.induce {v : V | Even (exampleGraph.degree v)}).IsAcyclic := by
  intro h
  exact h evenTriangle evenTriangle_cycle

/-- A seven-vertex edge-critical graph, connected after any vertex deletion,
whose even-degree vertices contain a triangle. This refutes only the proposed
additional structural restriction, not the cycle decomposition conjecture. -/
theorem even_induced_forest_rule_obstruction :
    Critical.EdgeCritical exampleGraph ∧
    (∀ v : V, (exampleGraph.induce {w : V | w ≠ v}).Connected) ∧
    ¬ (exampleGraph.induce {v : V | Even (exampleGraph.degree v)}).IsAcyclic :=
  ⟨example_critical, example_delete_vertex_connected, even_vertices_not_acyclic⟩

#print axioms independent_side_lower_bound
#print axioms example_lower_bound
#print axioms example_number
#print axioms example_critical
#print axioms even_induced_forest_rule_obstruction
end Erdos184Work.CriticalExample



/- Cycle decompositions for a fixed common-neighbor bound. This is not the unrestricted bound. -/
namespace Erdos184Work.Codegree
open SimpleGraph
open scoped Classical

lemma bounded_inter_union {α β : Type*} (S : Finset α) (A : α → Finset β) (r : ℕ)
    (hinter : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (A a ∩ A b).card ≤ r) :
    2 * (∑ a ∈ S, (A a).card) + r * S.card ≤
      2 * (S.biUnion A).card + r * S.card * S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hS : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (A a ∩ A b).card ≤ r := by
      intro b hb c hc hbc
      exact hinter b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc) hbc
    have hi := ih hS
    have hinter' : (A a ∩ S.biUnion A).card ≤ S.card * r := by
      rw [Finset.inter_biUnion]
      exact Finset.card_biUnion_le_card_mul S (fun b => A a ∩ A b) r (by
        intro b hb
        exact hinter a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb)
          (by intro hab; subst b; exact ha hb))
    have hu := Finset.card_union_add_card_inter (A a) (S.biUnion A)
    simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Finset.biUnion_insert]
    nlinarith

/-- Every two distinct vertices have at most `r` common neighbors. -/
def BoundedCommonNeighbors {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ x y, x ≠ y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ r

lemma BoundedCommonNeighbors.mono {V : Type*} [Finite V] {G H : SimpleGraph V} {r : ℕ}
    (h : BoundedCommonNeighbors G r) (hHG : H ≤ G) : BoundedCommonNeighbors H r := by
  intro x y hxy
  have hs : H.neighborSet x ∩ H.neighborSet y ⊆ G.neighborSet x ∩ G.neighborSet y :=
    fun _ hz => ⟨hHG hz.1, hHG hz.2⟩
  exact (Set.ncard_le_ncard hs).trans (h x y hxy)

lemma BoundedCommonNeighbors.induce {V : Type*} [Finite V] {G : SimpleGraph V} {r : ℕ}
    (h : BoundedCommonNeighbors G r) (s : Set V) : BoundedCommonNeighbors (G.induce s) r := by
  intro x y hxy
  have hi : Subtype.val '' ((G.induce s).neighborSet x ∩ (G.induce s).neighborSet y) ⊆
      G.neighborSet x.val ∩ G.neighborSet y.val := by
    rintro z ⟨z', hz, rfl⟩
    exact hz
  calc
    _ = (Subtype.val '' ((G.induce s).neighborSet x ∩ (G.induce s).neighborSet y)).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (G.neighborSet x.val ∩ G.neighborSet y.val).ncard := Set.ncard_le_ncard hi
    _ ≤ r := h x.val y.val (fun he => hxy (Subtype.ext he))

lemma BoundedCommonNeighbors.card_inter_le {V : Type*} [Fintype V] {G : SimpleGraph V} {r : ℕ}
    (h : BoundedCommonNeighbors G r) (x y : V) (hxy : x ≠ y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card ≤ r := by
  simpa only [← Set.ncard_coe_finset, Finset.coe_inter, SimpleGraph.coe_neighborFinset] using h x y hxy

lemma min_degree_overlap_bound {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V}
    (d q k r : ℕ) (hk : 2 ≤ k) (hq : q ≤ d) (hdeg : ∀ x, d ≤ G.degree x)
    (hinter : ∀ x y, x ≠ y → (G.neighborFinset x ∩ G.neighborFinset y).card ≤ r)
    (hno : ∀ a (c : G.Walk a a), c.IsCycle → c.length ≤ k) :
    2 * q * d + r * q ≤ 2 * k + r * q * q := by  classical
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  let I := (Finset.Icc 1 p.length).filter (fun i => G.Adj u (p.getVert i))
  have hImem : ∀ i, i ∈ I ↔ 1 ≤ i ∧ i ≤ p.length ∧ G.Adj u (p.getVert i) := by
    intro i
    simp only [I, Finset.mem_filter, Finset.mem_Icc, and_assoc]
  have hIcard : I.card = G.degree u := by
    rw [← G.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun i _ => p.getVert i)
    · intro i hi
      exact (G.mem_neighborFinset _ _).mpr ((hImem i).mp hi).2.2
    · intro i hi j hj heq
      exact hp.getVert_injOn ((hImem i).mp hi).2.1 ((hImem j).mp hj).2.1 heq
    · intro w hw
      have hwa : G.Adj u w := (G.mem_neighborFinset _ _).mp hw
      obtain ⟨i, hiw, hil⟩ := Walk.mem_support_iff_exists_getVert.mp
        (longest_path_neighbors_mem hp hmax w hwa)
      have hi0 : 1 ≤ i := by
        by_contra! hi0
        have hi : i = 0 := by omega
        have huw : u = w := by simpa [hi] using hiw
        exact hwa.ne huw
      exact ⟨i, (hImem i).mpr ⟨hi0, hil, hiw.symm ▸ hwa⟩, hiw⟩
  let R := I.image (fun i => p.getVert (i - 1))
  have hRcard : R.card = G.degree u := by
    rw [← hIcard]
    apply Finset.card_image_iff.mpr
    intro i hi j hj heq
    have hi' := (hImem i).mp hi
    have hj' := (hImem j).mp hj
    have he := hp.getVert_injOn (show i - 1 ≤ p.length by omega)
      (show j - 1 ≤ p.length by omega) heq
    omega
  obtain ⟨S, hSR, hScard⟩ := Finset.exists_subset_card_eq
    (show q ≤ R.card by rw [hRcard]; exact hq.trans (hdeg u))
  have hSprefix : S.biUnion (fun x => G.neighborFinset x) ⊆ (Finset.range k).image p.getVert := by
    intro w hw
    obtain ⟨x, hx, hwx⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp (hSR hx)
    have hi' := (hImem i).mp hi
    subst x
    exact rotation_neighbors_prefix hp hmax k hk hno i hi'.1 hi'.2.1 hi'.2.2 hwx
  have hScount : (S.biUnion (fun x => G.neighborFinset x)).card ≤ k := by
    exact (Finset.card_le_card hSprefix).trans (Finset.card_image_le.trans (by simp))
  have hsum : q * d ≤ ∑ x ∈ S, (G.neighborFinset x).card := by
    calc
      q * d = ∑ _x ∈ S, d := by simp [hScard]
      _ ≤ _ := Finset.sum_le_sum (fun x _ => by simpa using hdeg x)
  have hbound := bounded_inter_union S (fun x => G.neighborFinset x) r
    (fun x _ y _ hxy => hinter x y hxy)
  rw [hScard] at hbound
  nlinarith



universe u

lemma codegree_edges_le_of_no_long_cycle {V : Type u} [Fintype V]
    (G : SimpleGraph V) (d q k r : ℕ) (hd : 0 < d) (hq : q ≤ d) (hk : 2 ≤ k)
    (hdk : 2 * k + r * q * q < 2 * q * d + r * q) (huni : BoundedCommonNeighbors G r)
    (hno : ∀ u (p : G.Walk u u), p.IsCycle → p.length ≤ k) :
    G.edgeFinset.card ≤ (d - 1) * Fintype.card V := by
  classical
  have main : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
      Fintype.card W = n → BoundedCommonNeighbors H r →
      (∀ u (p : H.Walk u u), p.IsCycle → p.length ≤ k) →
      H.edgeFinset.card ≤ (d - 1) * n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ H hcard huniH hnoH
      cases isEmpty_or_nonempty W with
      | inl he =>
        have hbot : H = ⊥ := by ext a; exact isEmptyElim a
        subst H
        simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
          SimpleGraph.edgeSet_bot]
        simp
      | inr he =>
        obtain ⟨v, hv⟩ : ∃ v, H.degree v < d := by
          by_contra! hn
          have hb := min_degree_overlap_bound d q k r hk hq hn
            huniH.card_inter_le hnoH
          omega
        let S : Set W := {v}ᶜ
        let K := H.induce S
        have hc : Fintype.card S = Fintype.card W - 1 := by
          change Fintype.card ↑({v}ᶜ : Set W) = _
          rw [Fintype.card_compl_set]
          simp only [Fintype.card_unique]
        have hpos : 0 < n := hcard ▸ Fintype.card_pos
        have hsmall : Fintype.card S < n := by omega
        have hnoK : ∀ u (p : K.Walk u u), p.IsCycle → p.length ≤ k := by
          intro u p hp
          let e : K ↪g H := SimpleGraph.Embedding.induce S
          have hp' := SimpleGraph.Walk.IsCycle.map (f := e.toHom) e.injective hp
          have hlen := hnoH (e u) (p.map e.toHom) hp'
          simpa using hlen
        have hb := ih (Fintype.card S) hsmall K rfl (huniH.induce S) hnoK
        have hem : K.edgeFinset.card + H.degree v = H.edgeFinset.card := by
          change (H.induce {v}ᶜ).edgeFinset.card + H.degree v = H.edgeFinset.card
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
            SimpleGraph.card_edgeFinset_deleteIncidenceSet,
            Nat.sub_add_cancel (H.degree_le_card_edgeFinset v)]
        rw [hc, hcard] at hb
        have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hb hem ⊢
        simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hv hem
        have hksub : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
        nlinarith
  exact main _ G rfl huni hno

lemma common_neighbors_decomposition_scaled {V : Type*} [Fintype V]
    (r B s : ℕ) (hr : 0 < r)
    (hbase : ∀ H : SimpleGraph V, H.edgeFinset.card ≤ 2 * r * Fintype.card V →
      ∃ D : Finset H.Subgraph, (∀ K ∈ D, IsCycleOrEdge K.coe) ∧
        IsDecomposition H D ∧ D.card ≤ B * Fintype.card V)
    (G : SimpleGraph V) (huni : BoundedCommonNeighbors G r)
    (hm : G.edgeFinset.card ≤ 2 ^ (s + 1) * r * Fintype.card V) :
    ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      2 ^ s * D.card + 4 * Fintype.card V ≤ (B + 4) * 2 ^ s * Fintype.card V := by
  classical
  induction s generalizing G with
  | zero =>
    obtain ⟨D, hD, hdec, hc⟩ := hbase G (by
      simpa only [Nat.zero_add, pow_one, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hm)
    refine ⟨D, hD, hdec, ?_⟩
    simp only [pow_zero, one_mul, mul_one]
    nlinarith
  | succ s ih =>
    let t := 2 ^ s
    have ht : 0 < t := by positivity
    have hcycles : ∀ H : SimpleGraph V, BoundedCommonNeighbors H r →
        (2 * r * t) * Fintype.card V < H.edgeFinset.card →
        ∃ (u : V) (p : H.Walk u u), p.IsCycle ∧ 2 * r * t * t ≤ p.length := by
      intro H hH hmH
      by_contra! hn
      have hno : ∀ u (p : H.Walk u u), p.IsCycle → p.length ≤ 2 * r * t * t := by
        intro u p hp
        exact (hn u p hp).le
      have hb := codegree_edges_le_of_no_long_cycle H (2 * r * t) (2 * t) (2 * r * t * t) r
        (by positivity) (by nlinarith) (by nlinarith [Nat.mul_pos (Nat.mul_pos hr ht) ht])
        (by nlinarith [Nat.mul_pos hr ht]) hH hno
      have hle : (2 * r * t - 1) * Fintype.card V ≤ (2 * r * t) * Fintype.card V :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hb hmH hle
      omega
    obtain ⟨D, hD, hdec, hc⟩ := scaled_decomposition_above_threshold
      (fun H => BoundedCommonNeighbors H r) (fun _ _ h hle => h.mono hle)
      (2 * r * t) (2 * r * t * t) t ((B + 4) * t * Fintype.card V) (4 * Fintype.card V)
      (by positivity)
      (fun H hH hmH => ih H hH (by
        simpa only [pow_succ, t, mul_assoc, mul_left_comm, mul_comm,
          SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hmH)) hcycles G huni
    refine ⟨D, hD, hdec, ?_⟩
    have hm' : G.edgeFinset.card ≤ 4 * r * t * Fintype.card V := by
      simp only [pow_succ] at hm
      change G.edgeFinset.card ≤ 4 * r * 2 ^ s * Fintype.card V
      nlinarith
    have hd := Nat.div_mul_le_self G.edgeFinset.card (2 * r * t * t)
    have hdiv : t * (G.edgeFinset.card / (2 * r * t * t)) ≤ 2 * Fintype.card V := by
      have hmul : (r * t) * (t * (G.edgeFinset.card / (2 * r * t * t))) ≤
          (r * t) * (2 * Fintype.card V) := by nlinarith
      exact Nat.le_of_mul_le_mul_left hmul (Nat.mul_pos hr ht)
    change 2 ^ (s + 1) * D.card + 4 * Fintype.card V ≤
      (B + 4) * 2 ^ (s + 1) * Fintype.card V
    rw [pow_succ]
    change (t * 2) * D.card + 4 * Fintype.card V ≤ (B + 4) * (t * 2) * Fintype.card V
    nlinarith

/-- A fixed common-neighbor bound gives a uniform linear decomposition bound.
The coefficient depends logarithmically on that bound, not on the vertex count. -/
lemma bounded_common_neighbors_decomposition_linear {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (hr : 0 < r) (huni : BoundedCommonNeighbors G r) :
    ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card ≤ (2 * Nat.clog 2 (2 * r) + 5) * Fintype.card V := by
  classical
  let B := 2 * Nat.clog 2 (2 * r) + 1
  have hbase : ∀ H : SimpleGraph V, H.edgeFinset.card ≤ 2 * r * Fintype.card V →
      ∃ D : Finset H.Subgraph, (∀ K ∈ D, IsCycleOrEdge K.coe) ∧
        IsDecomposition H D ∧ D.card ≤ B * Fintype.card V := by
    intro H hH
    apply decomposition_dyadic_bound (Nat.clog 2 (2 * r)) H
    exact hH.trans (Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _))
  let s := Fintype.card V
  have hs : Fintype.card V ≤ 2 ^ (s + 1) :=
    Nat.le_trans (Nat.le_of_lt Nat.lt_two_pow_self)
      (Nat.pow_le_pow_right (by decide) (Nat.le_succ s))
  have hm : G.edgeFinset.card ≤ 2 ^ (s + 1) * r * Fintype.card V := by
    calc
      _ ≤ (Fintype.card V).choose 2 := G.card_edgeFinset_le_card_choose_two
      _ ≤ Fintype.card V ^ 2 := Nat.choose_le_pow _ _
      _ ≤ 2 ^ (s + 1) * Fintype.card V := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ (by
        have h := Nat.mul_le_mul_left (2 ^ (s + 1)) (show 1 ≤ r from hr)
        simpa only [mul_one] using h)
  obtain ⟨D, hD, hdec, hc⟩ := common_neighbors_decomposition_scaled r B s hr hbase G huni hm
  refine ⟨D, hD, hdec, ?_⟩
  have hpos : 0 < 2 ^ s := by positivity
  have hmul : 2 ^ s * D.card ≤ 2 ^ s * ((B + 4) * Fintype.card V) := by nlinarith
  have hb := Nat.le_of_mul_le_mul_left hmul hpos
  simpa only [B, Nat.add_assoc] using hb

lemma BoundedCommonNeighbors.increase {V : Type*} {G : SimpleGraph V} {r t : ℕ}
    (h : BoundedCommonNeighbors G r) (hrt : r ≤ t) : BoundedCommonNeighbors G t :=
  fun x y hxy => (h x y hxy).trans hrt

lemma bounded_common_neighbors_decomposition {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (huni : BoundedCommonNeighbors G r) :
    ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card ≤ (2 * Nat.clog 2 (2 * max 1 r) + 5) * Fintype.card V :=
  bounded_common_neighbors_decomposition_linear G (max 1 r) (by omega)
    (huni.increase (Nat.le_max_right _ _))

/-- Containment is by an injective homomorphism, not necessarily an induced embedding. -/
def ContainsKTwo {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ f : completeBipartiteGraph (Fin 2) (Fin t) →g G, Function.Injective f

lemma containsKTwo_of_common_neighbors {V : Type*} {G : SimpleGraph V} {x y : V}
    (hxy : x ≠ y) (t : ℕ) (g : Fin t ↪ ↥(G.neighborSet x ∩ G.neighborSet y)) :
    ContainsKTwo G t := by
  classical
  let f : completeBipartiteGraph (Fin 2) (Fin t) →g G := {
    toFun := Sum.elim (fun i => if i = 0 then x else y) (fun j => (g j).val)
    map_rel' := by
      intro a b hab
      cases a with
      | inl a =>
        cases b with
        | inl b => simp [completeBipartiteGraph] at hab
        | inr b =>
          fin_cases a
          · exact (g b).property.1
          · exact (g b).property.2
      | inr a =>
        cases b with
        | inl b =>
          fin_cases b
          · exact ((g a).property.1 : G.Adj x (g a)).symm
          · exact ((g a).property.2 : G.Adj y (g a)).symm
        | inr b => simp [completeBipartiteGraph] at hab }
  refine ⟨f, ?_⟩
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      fin_cases a <;> fin_cases b <;> simp_all [f]
    | inr b =>
      fin_cases a
      · exact (((g b).property.1 : G.Adj x (g b)).ne he).elim
      · exact (((g b).property.2 : G.Adj y (g b)).ne he).elim
  | inr a =>
    cases b with
    | inl b =>
      fin_cases b
      · exact (((g a).property.1 : G.Adj x (g a)).ne he.symm).elim
      · exact (((g a).property.2 : G.Adj y (g a)).ne he.symm).elim
    | inr b => exact congrArg Sum.inr (g.injective (Subtype.ext he))

lemma boundedCommonNeighbors_iff_no_biclique_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) :
    BoundedCommonNeighbors G r ↔ ¬ ContainsKTwo G (r + 1) := by
  classical
  constructor
  · rintro h ⟨f, hf⟩
    let x := f (.inl 0)
    let y := f (.inl 1)
    have hxy : x ≠ y := by
      intro he
      have hij : (0 : Fin 2) = 1 := Sum.inl_injective (hf he)
      exact (show (0 : Fin 2) ≠ 1 by decide) hij
    let g : Fin (r + 1) ↪ ↥(G.neighborSet x ∩ G.neighborSet y) := {
      toFun := fun i => ⟨f (.inr i), f.map_adj (by simp [completeBipartiteGraph]), f.map_adj (by simp [completeBipartiteGraph])⟩
      inj' := fun i j he => Sum.inr_injective (hf (congrArg Subtype.val he)) }
    have hc := Fintype.card_le_of_embedding g
    have hb := h x y hxy
    simp only [← Nat.card_eq_fintype_card, Nat.card_fin] at hc
    change r + 1 ≤ (G.neighborSet x ∩ G.neighborSet y).ncard at hc
    omega
  · intro h x y hxy
    by_contra! hc
    have he : Nonempty (Fin (r + 1) ↪ ↥(G.neighborSet x ∩ G.neighborSet y)) := by
      apply Function.Embedding.nonempty_iff_card_le.mpr
      simp only [← Nat.card_eq_fintype_card, Nat.card_fin]
      change r + 1 ≤ (G.neighborSet x ∩ G.neighborSet y).ncard
      omega
    obtain ⟨g⟩ := he
    exact h (containsKTwo_of_common_neighbors hxy (r + 1) g)

/-- Every graph excluding a fixed `K_(2,r+1)` has a linear cycle-and-edge decomposition. -/
lemma no_biclique_two_decomposition_linear {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (hno : ¬ ContainsKTwo G (r + 1)) :
    ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card ≤ (2 * Nat.clog 2 (2 * max 1 r) + 5) * Fintype.card V :=
  bounded_common_neighbors_decomposition G r ((boundedCommonNeighbors_iff_no_biclique_two G r).mpr hno)

#print axioms common_neighbors_decomposition_scaled
#print axioms bounded_common_neighbors_decomposition_linear
#print axioms bounded_common_neighbors_decomposition
#print axioms boundedCommonNeighbors_iff_no_biclique_two
#print axioms no_biclique_two_decomposition_linear
end Erdos184Work.Codegree


/- Complete bipartite graphs: a sharp uniform coefficient and optimal even decompositions. -/
open Filter SimpleGraph
open scoped Classical Fin.NatCast
namespace Erdos184Work.Rectangles

variable {a b : ℕ} [NeZero a] [NeZero b]

def nextIndex (j : Fin a) (x y : Bool) : Fin a :=
  if x = false ∧ y = true then j - 1 else j

def baseCycle (a : ℕ) [NeZero a] : SimpleGraph ((Fin a × Bool) ⊕ (Fin a × Bool)) where
  Adj
    | .inl (j,x), .inr (k,y) => k = nextIndex j x y
    | .inr (k,y), .inl (j,x) => k = nextIndex j x y
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp
  loopless := by intro x; cases x <;> simp

lemma baseCycle_le : baseCycle a ≤ gridGraph (Fin a) (Fin a) := by
  intro x y h
  cases x <;> cases y <;> simp_all [baseCycle, gridGraph]

lemma baseCycle_step (j : Fin a) :
    (baseCycle a).Reachable (.inl (j,false)) (.inl (j+1,false)) := by
  have h₁ : (baseCycle a).Adj (.inl (j,false)) (.inr (j,false)) := by
    simp [baseCycle, nextIndex]
  have h₂ : (baseCycle a).Adj (.inr (j,false)) (.inl (j,true)) := by
    simp [baseCycle, nextIndex]
  have h₃ : (baseCycle a).Adj (.inl (j,true)) (.inr (j,true)) := by
    simp [baseCycle, nextIndex]
  have h₄ : (baseCycle a).Adj (.inr (j,true)) (.inl (j+1,false)) := by
    simp [baseCycle, nextIndex]
  exact h₁.reachable.trans (h₂.reachable.trans (h₃.reachable.trans h₄.reachable))

lemma baseCycle_connected : (baseCycle a).Connected := by
  have hNat : ∀ k : ℕ, (baseCycle a).Reachable (.inl (0,false)) (.inl ((k : Fin a),false)) := by
    intro k
    induction k with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ k ih =>
      simpa only [Nat.cast_add, Nat.cast_one] using ih.trans (baseCycle_step (k : Fin a))
  have hleft : ∀ j : Fin a, (baseCycle a).Reachable (.inl (0,false)) (.inl (j,false)) := by
    intro j
    simpa only [Fin.cast_val_eq_self] using hNat j.val
  have hroot : ∀ v, (baseCycle a).Reachable (.inl (0,false)) v := by
    intro v
    cases v with
    | inl v =>
      rcases v with ⟨j,x⟩
      cases x
      · exact hleft j
      · have h₁ : (baseCycle a).Adj (.inl (j,false)) (.inr (j,false)) := by
          simp [baseCycle, nextIndex]
        have h₂ : (baseCycle a).Adj (.inr (j,false)) (.inl (j,true)) := by
          simp [baseCycle, nextIndex]
        exact (hleft j).trans (h₁.reachable.trans h₂.reachable)
    | inr v =>
      rcases v with ⟨j,x⟩
      cases x
      · exact (hleft j).trans (show (baseCycle a).Adj (.inl (j,false)) (.inr (j,false)) by
          simp [baseCycle, nextIndex]).reachable
      · exact (hleft (j+1)).trans (show (baseCycle a).Adj (.inl (j+1,false)) (.inr (j,true)) by
          simp [baseCycle, nextIndex]).reachable
  exact ⟨fun x y => (hroot x).symm.trans (hroot y)⟩

lemma baseCycle_regular : (baseCycle a).IsRegularOfDegree 2 := by
  classical
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  cases v with
  | inl v =>
    rcases v with ⟨j,x⟩
    have hn : (baseCycle a).neighborFinset (.inl (j,x)) =
        {Sum.inr (nextIndex j x false, false), Sum.inr (nextIndex j x true, true)} := by
      ext v
      cases v with
      | inl v => simp [SimpleGraph.mem_neighborFinset, baseCycle]
      | inr v =>
        rcases v with ⟨k,y⟩
        cases y <;> simp [SimpleGraph.mem_neighborFinset, baseCycle]
    rw [hn, Finset.card_pair (by simp)]
  | inr v =>
    rcases v with ⟨k,y⟩
    have hn : (baseCycle a).neighborFinset (.inr (k,y)) =
        {Sum.inl ((if y then k+1 else k), false), Sum.inl (k,true)} := by
      ext v
      cases v with
      | inr v => simp [SimpleGraph.mem_neighborFinset, baseCycle]
      | inl v =>
        rcases v with ⟨j,x⟩
        cases x <;> cases y <;> simp [SimpleGraph.mem_neighborFinset, baseCycle, nextIndex, eq_comm]
        constructor <;> intro h <;> rw [h] <;> abel
    rw [hn, Finset.card_pair (by simp)]

noncomputable def basePiece (a : ℕ) [NeZero a] : (gridGraph (Fin a) (Fin a)).Subgraph :=
  SimpleGraph.toSubgraph (baseCycle a) baseCycle_le

lemma basePiece_cycle : (basePiece a).coe.Connected ∧ (basePiece a).coe.IsRegularOfDegree 2 := by
  apply coe_toSubgraph_cycle
  · exact baseCycle_connected
  · exact baseCycle_regular

def shiftHom (hab : a ≤ b) (i : Fin b) : gridGraph (Fin a) (Fin a) →g gridGraph (Fin a) (Fin b) where
  toFun := Sum.map id (fun p => (Fin.castLE hab p.1 + i, p.2))
  map_rel' := by
    intro u v h
    cases u <;> cases v <;> simp_all [gridGraph]

lemma shiftHom_injective (hab : a ≤ b) (i : Fin b) : Function.Injective (shiftHom hab i) := by
  intro u v h
  cases u <;> cases v <;> simp_all [shiftHom, Prod.mk.injEq]
  exact Prod.ext h.1 h.2

noncomputable def rectangularPiece (hab : a ≤ b) (i : Fin b) : (gridGraph (Fin a) (Fin b)).Subgraph :=
  (basePiece a).map (shiftHom hab i)

lemma rectangularPiece_cycle (hab : a ≤ b) (i : Fin b) :
    (rectangularPiece hab i).coe.Connected ∧ (rectangularPiece hab i).coe.IsRegularOfDegree 2 := by
  simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using
    cycle_property_map_injective (shiftHom hab i) (shiftHom_injective hab i) (basePiece a) (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using basePiece_cycle (a := a))

lemma rectangularPiece_adj (hab : a ≤ b) (i : Fin b) (j : Fin a) (k : Fin b) (x y : Bool) :
    (rectangularPiece hab i).Adj (.inl (j,x)) (.inr (k,y)) ↔
      k = Fin.castLE hab (nextIndex j x y) + i := by
  change (∃ u v, (baseCycle a).Adj u v ∧ shiftHom hab i u = .inl (j,x) ∧
    shiftHom hab i v = .inr (k,y)) ↔ _
  simp only [Sum.exists, Prod.exists, shiftHom]
  cases x <;> cases y <;> simp [baseCycle, eq_comm]

lemma rectangularPiece_unique (hab : a ≤ b) {i i' : Fin b}
    {u v : (Fin a × Bool) ⊕ (Fin b × Bool)}
    (hi : (rectangularPiece hab i).Adj u v)
    (hi' : (rectangularPiece hab i').Adj u v) : i = i' := by
  have huv := (rectangularPiece hab i).adj_sub hi
  cases u with
  | inl u =>
    cases v with
    | inl v => simp [gridGraph] at huv
    | inr v =>
      have h := (rectangularPiece_adj hab i u.1 v.1 u.2 v.2).mp hi
      have h' := (rectangularPiece_adj hab i' u.1 v.1 u.2 v.2).mp hi'
      exact add_left_cancel (h.symm.trans h')
  | inr u =>
    cases v with
    | inr v => simp [gridGraph] at huv
    | inl v =>
      have h := (rectangularPiece_adj hab i v.1 u.1 v.2 u.2).mp hi.symm
      have h' := (rectangularPiece_adj hab i' v.1 u.1 v.2 u.2).mp hi'.symm
      exact add_left_cancel (h.symm.trans h')

lemma rectangular_decomposition (hab : a ≤ b) :
    ∃ D : Finset (gridGraph (Fin a) (Fin b)).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (gridGraph (Fin a) (Fin b)) D ∧ D.card ≤ b := by
  classical
  let D := Finset.univ.image (rectangularPiece hab)
  refine ⟨D, ?_, ⟨?_, ?_⟩, Finset.card_image_le.trans (by simp)⟩
  · intro H hH
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using rectangularPiece_cycle hab i
  · intro H hH K hK hne
    change H ∈ Finset.univ.image (rectangularPiece hab) at hH
    change K ∈ Finset.univ.image (rectangularPiece hab) at hK
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨i', _, rfl⟩ := Finset.mem_image.mp hK
    apply Set.disjoint_left.mpr
    intro e hi hi'
    induction e using Sym2.ind with | h u v =>
    exact hne (congrArg (rectangularPiece hab) (rectangularPiece_unique hab hi hi'))
  · ext e
    constructor
    · intro he
      obtain ⟨H, he⟩ := Set.mem_iUnion.mp he
      obtain ⟨_, he⟩ := Set.mem_iUnion.mp he
      exact H.edgeSet_subset he
    · intro he
      obtain ⟨⟨j,x⟩, ⟨k,y⟩, heq⟩ := Subfamilies.bipartite_edge_representation
        (⟨e,he⟩ : (gridGraph (Fin a) (Fin b)).edgeSet)
      change e = _ at heq
      subst e
      let i := k - Fin.castLE hab (nextIndex j x y)
      refine Set.mem_iUnion.mpr ⟨rectangularPiece hab i, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      · apply (rectangularPiece_adj hab i j k x y).mpr
        dsimp only [i]
        abel

end Erdos184Work.Rectangles

namespace Erdos184Work.Rectangles

lemma cycle_bound_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) {k : ℕ}
    (h : ∃ D : Finset G.Subgraph, (∀ K ∈ D, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ k) :
    ∃ D : Finset H.Subgraph, (∀ K ∈ D, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      IsDecomposition H D ∧ D.card ≤ k := by
  classical
  obtain ⟨D, hD, hdec, hc⟩ := h
  refine ⟨D.image (SimpleGraph.Subgraph.map e.toHom), ?_, map_isDecomposition_iso e D hdec,
    Finset.card_image_le.trans hc⟩
  intro K hK
  obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
  simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using cycle_property_map_iso (subgraphMapIso e L) (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hD L hL)

def swapIso (A B : Type*) : completeBipartiteGraph A B ≃g completeBipartiteGraph B A where
  toEquiv := Equiv.sumComm A B
  map_rel_iff' := by intro x y; cases x <;> cases y <;> simp [completeBipartiteGraph]

lemma even_bipartite_decomposition_ordered (a b : ℕ) (hab : a ≤ b) :
    ∃ D : Finset (completeBipartiteGraph (Fin (2*a)) (Fin (2*b))).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (completeBipartiteGraph (Fin (2*a)) (Fin (2*b))) D ∧ D.card ≤ b := by
  classical
  by_cases ha : a = 0
  · subst a
    obtain ⟨D, _, hdec, hc⟩ := exists_edge_decomposition
      (completeBipartiteGraph (Fin (2*0)) (Fin (2*b)))
    rw [BipartiteLower.complete_edge_card] at hc
    simp only [Fintype.card_fin, mul_zero, zero_mul] at hc
    have hD : D = ∅ := Finset.card_eq_zero.mp (by omega)
    refine ⟨D, ?_, hdec, by omega⟩
    simp [hD]
  · haveI : NeZero a := ⟨ha⟩
    haveI : NeZero b := ⟨by omega⟩
    let eA : Fin a × Bool ≃ Fin (2*a) := Fintype.equivOfCardEq (by simp [mul_comm])
    let eB : Fin b × Bool ≃ Fin (2*b) := Fintype.equivOfCardEq (by simp [mul_comm])
    exact cycle_bound_iso (Subfamilies.bipartiteIso eA eB) (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using rectangular_decomposition hab)

lemma even_bipartite_decomposition (a b : ℕ) :
    ∃ D : Finset (completeBipartiteGraph (Fin (2*a)) (Fin (2*b))).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (completeBipartiteGraph (Fin (2*a)) (Fin (2*b))) D ∧ D.card ≤ max a b := by
  rcases le_total a b with hab | hba
  · simpa only [max_eq_right hab] using even_bipartite_decomposition_ordered a b hab
  · rw [max_eq_left hba]
    exact cycle_bound_iso (swapIso (Fin (2*b)) (Fin (2*a)))
      (even_bipartite_decomposition_ordered b a hba)

lemma extend_injective_decomposition {V W : Type*} [Fintype V] [Fintype W]
    {H : SimpleGraph V} {G : SimpleGraph W} (f : H →g G) (hf : Function.Injective f)
    (D : Finset H.Subgraph) (hD : ∀ K ∈ D, IsCycleOrEdge K.coe) (hdec : IsDecomposition H D) :
    ∃ E : Finset G.Subgraph, (∀ K ∈ E, IsCycleOrEdge K.coe) ∧ IsDecomposition G E ∧
      E.card + H.edgeFinset.card ≤ D.card + G.edgeFinset.card := by
  classical
  let e : V ↪ W := ⟨f,hf⟩
  let R := H.map e
  have hRG : R ≤ G := by
    rintro u v ⟨x,y,hxy,rfl,rfl⟩
    exact f.map_adj hxy
  obtain ⟨A, hA, hpA, heA, hcA⟩ := SparseCuts.map_decomposition_injective
    (SimpleGraph.Embedding.map e H).toHom (SimpleGraph.Embedding.map e H).injective D hD hdec
  have hdecA : IsDecomposition R A := ⟨hpA, heA.trans (SimpleGraph.edgeSet_map e H).symm⟩
  obtain ⟨B, hB, hdecB, hcB⟩ := exists_edge_decomposition (G \ R)
  obtain ⟨E, hE, hdecE, hcE⟩ := combine_decompositions hRG sdiff_le
    (by rw [SimpleGraph.edgeSet_sdiff]; exact Set.disjoint_sdiff_right)
    (by rw [SimpleGraph.edgeSet_sdiff]; exact Set.union_diff_cancel (SimpleGraph.edgeSet_mono hRG))
    A B hA hdecA hB hdecB
  have hcount : (G \ R).edgeFinset.card + R.edgeFinset.card = G.edgeFinset.card := by
    rw [SimpleGraph.edgeFinset_sdiff]
    exact Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hRG)
  have hmap : R.edgeFinset.card = H.edgeFinset.card := SimpleGraph.card_edgeFinset_map e H
  refine ⟨E, hE, hdecE, ?_⟩
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcB hcount hmap ⊢
  omega

lemma complete_bipartite_decomposition_parity (m n : ℕ) :
    ∃ D : Finset (completeBipartiteGraph (Fin m) (Fin n)).Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition (completeBipartiteGraph (Fin m) (Fin n)) D ∧
      D.card + 4 * (m / 2) * (n / 2) ≤ max (m / 2) (n / 2) + m * n := by
  classical
  obtain ⟨D, hD, hdec, hc⟩ := even_bipartite_decomposition (m/2) (n/2)
  let f : completeBipartiteGraph (Fin (2*(m/2))) (Fin (2*(n/2))) →g
      completeBipartiteGraph (Fin m) (Fin n) := {
    toFun := Sum.map (Fin.castLE (by omega)) (Fin.castLE (by omega))
    map_rel' := by intro x y h; cases x <;> cases y <;> simp_all [completeBipartiteGraph] }
  have hf : Function.Injective f := by
    intro x y h
    cases x <;> cases y <;> simp_all [f]
  obtain ⟨E, hE, hdecE, hcE⟩ := extend_injective_decomposition f hf D (fun H hH => Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD H hH)) hdec
  simp only [BipartiteLower.complete_edge_card, Fintype.card_fin] at hcE
  exact ⟨E, hE, hdecE, by nlinarith⟩

lemma complete_bipartite_decomposition_linear_fin (m n : ℕ) :
    ∃ D : Finset (completeBipartiteGraph (Fin m) (Fin n)).Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition (completeBipartiteGraph (Fin m) (Fin n)) D ∧
      2 * D.card ≤ 3 * (m + n) := by
  obtain ⟨D, hD, hdec, hc⟩ := complete_bipartite_decomposition_parity m n
  have hprod : m*n ≤ 4*(m/2)*(n/2) + m + n := by
    have hm : m = 2*(m/2) ∨ m = 2*(m/2)+1 := by omega
    have hn : n = 2*(n/2) ∨ n = 2*(n/2)+1 := by omega
    rcases hm with hm | hm <;> rcases hn with hn | hn <;> nlinarith
  have hmax : 2 * max (m/2) (n/2) ≤ m+n := by
    rcases le_total (m/2) (n/2) with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  exact ⟨D, hD, hdec, by omega⟩

lemma complete_bipartite_decomposition_linear (A B : Type*) [Fintype A] [Fintype B] :
    ∃ D : Finset (completeBipartiteGraph A B).Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition (completeBipartiteGraph A B) D ∧
      2 * D.card ≤ 3 * (Fintype.card A + Fintype.card B) := by
  classical
  obtain ⟨D, hD, hdec, hc⟩ := complete_bipartite_decomposition_linear_fin (Fintype.card A) (Fintype.card B)
  let e := Subfamilies.bipartiteIso (Fintype.equivFin A).symm (Fintype.equivFin B).symm
  refine ⟨D.image (SimpleGraph.Subgraph.map e.toHom), ?_, map_isDecomposition_iso e D hdec, ?_⟩
  · intro K hK
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
    exact SparseCuts.piece_property_map_injective e.toHom e.injective L (hD L hL)
  · exact (Nat.mul_le_mul_left 2 Finset.card_image_le).trans hc

lemma decomposition_degree_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D) (v : V) : G.degree v ≤ 2 * D.card := by
  classical
  have hgraph : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  have hsum := subfamilyGraph_degree D hdec.1 v
  rw [hgraph] at hsum
  have hp : ∀ H ∈ D, H.spanningCoe.degree v ≤ 2 := by
    intro H hH
    rcases hD H hH with hcycle | hedge
    · rw [regular_two_spanning_degree H (by
        simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hcycle.2)]
      split_ifs <;> omega
    · have hd := H.spanningCoe.degree_le_card_edgeFinset v
      have hc := subgraph_edge_card H
      simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hd hc hedge
      omega
  rw [hsum]
  calc
    _ ≤ ∑ _H ∈ D, (2 : ℕ) := Finset.sum_le_sum hp
    _ = _ := by simp [mul_comm]

lemma even_bipartite_number (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Critical.number (completeBipartiteGraph (Fin (2*a)) (Fin (2*b))) = max a b := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨D,hD,hdec,hc⟩ := even_bipartite_decomposition a b
    exact (Critical.number_le D (fun H hH => Or.inl (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hD H hH)) hdec).trans hc
  · obtain ⟨D,hD,hdec,hc⟩ := Critical.exists_minimum
      (completeBipartiteGraph (Fin (2*a)) (Fin (2*b)))
    have hl := decomposition_degree_bound D hD hdec (Sum.inl ⟨0, by omega⟩)
    have hr := decomposition_degree_bound D hD hdec (Sum.inr ⟨0, by omega⟩)
    rw [BipartiteLower.complete_degree_left, Fintype.card_fin] at hl
    rw [BipartiteLower.complete_degree_right, Fintype.card_fin] at hr
    omega

lemma bipartite_coefficient_lower (C : ℝ)
    (hC : ∀ m n : ℕ, ∃ D : Finset (completeBipartiteGraph (Fin m) (Fin n)).Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition (completeBipartiteGraph (Fin m) (Fin n)) D ∧
      (D.card : ℝ) ≤ C * (m+n)) : 3/2 ≤ C := by
  have hC0 : 0 ≤ C := by
    obtain ⟨D, _, _, hc⟩ := hC 1 0
    simpa using (show (0 : ℝ) ≤ D.card from Nat.cast_nonneg _).trans hc
  by_contra! hlt
  have hpos : 0 < 3 - 2*C := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (4*C/(3-2*C)))
  have hm1 : 1 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hmpos : 0 < (m : ℝ) := lt_trans zero_lt_one hm1
  have hmdiv : 4*C/(3-2*C) < (m : ℝ) := (le_max_right _ _).trans_lt hm
  have hmC : 4*C < (m : ℝ)*(3-2*C) := (div_lt_iff₀ hpos).mp hmdiv
  have hmul := mul_lt_mul_of_pos_right hmC hmpos
  have hCm : C ≤ C*(m : ℝ) := by nlinarith [mul_nonneg hC0 (show 0 ≤ (m : ℝ)-1 by linarith)]
  obtain ⟨D,hD,hdec,hc⟩ := hC (2*m+1) ((2*m+1)*m)
  have hlow := BipartiteLower.decomposition_lower_bound m (by simp) D hD hdec
  simp only [Fintype.card_fin] at hlow
  have hscaled : (4*m+2)*(3*m^2+m) ≤ (4*m+2)*D.card := by nlinarith [hlow]
  have hDcard : 3*m^2+m ≤ D.card := Nat.le_of_mul_le_mul_left hscaled (by omega)
  have hreal := (Nat.cast_le (α := ℝ)).mpr hDcard
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hc hreal
  nlinarith

lemma bipartite_coefficient_optimal :
    (∀ m n : ℕ, ∃ D : Finset (completeBipartiteGraph (Fin m) (Fin n)).Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition (completeBipartiteGraph (Fin m) (Fin n)) D ∧
      (D.card : ℝ) ≤ (3/2) * (m+n)) ∧
    ∀ C : ℝ, (∀ m n : ℕ, ∃ D : Finset (completeBipartiteGraph (Fin m) (Fin n)).Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition (completeBipartiteGraph (Fin m) (Fin n)) D ∧
      (D.card : ℝ) ≤ C * (m+n)) → 3/2 ≤ C := by
  refine ⟨?_, bipartite_coefficient_lower⟩
  intro m n
  obtain ⟨D,hD,hdec,hc⟩ := complete_bipartite_decomposition_linear_fin m n
  refine ⟨D,hD,hdec,?_⟩
  have hr : (2 : ℝ)*D.card ≤ 3*((m : ℝ)+n) := by exact_mod_cast hc
  linarith

#print axioms even_bipartite_number
#print axioms bipartite_coefficient_optimal
#print axioms even_bipartite_decomposition
#print axioms complete_bipartite_decomposition_linear

end Erdos184Work.Rectangles


/- Opposite-pair overlaps: two cycles replace an arbitrarily long doubled path. -/
open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.DoublePath

variable {V : Type*} {G : SimpleGraph V}

def doubleGraph (G : SimpleGraph V) : SimpleGraph (V × Bool) where
  Adj x y := G.Adj x.1 y.1
  symm := by intro x y h; exact h.symm
  loopless := by intro x h; exact G.loopless x.1 h

def liftHom (G : SimpleGraph V) (f : V → Bool) : G →g doubleGraph G where
  toFun := fun x => (x,f x)
  map_rel' := fun h => h

lemma liftHom_injective (f : V → Bool) : Function.Injective (liftHom G f) := by
  intro x y h
  exact congrArg Prod.fst h

lemma lift_subgraph_adj (H : G.Subgraph) (f : V → Bool) (x y : V) (b c : Bool) :
    (H.map (liftHom G f)).Adj (x,b) (y,c) ↔ H.Adj x y ∧ b = f x ∧ c = f y := by
  change (∃ u v, H.Adj u v ∧ (u,f u) = (x,b) ∧ (v,f v) = (y,c)) ↔ _
  simp only [Prod.mk.injEq]
  aesop

lemma path_coloring {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    ∃ f : V → Bool, ∀ x y, s(x,y) ∈ p.edges → f x ≠ f y := by
  classical
  induction p with
  | nil => exact ⟨fun _ => false, by simp⟩
  | @cons u v w huv p ih =>
    obtain ⟨hp', hu⟩ := (Walk.cons_isPath_iff _ _).mp hp
    obtain ⟨f,hf⟩ := ih hp'
    refine ⟨Function.update f u (!f v), ?_⟩
    intro x y hxy
    rcases List.mem_cons.mp hxy with he | he
    · have heq := Sym2.eq_iff.mp he
      rcases heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · simp [Function.update, huv.ne.symm]
      · simp [Function.update, huv.ne.symm]
    · have hxu : x ≠ u := by
        intro h; subst x
        exact hu (p.fst_mem_support_of_mem_edges he)
      have hyu : y ≠ u := by
        intro h; subst y
        exact hu (p.snd_mem_support_of_mem_edges he)
      simpa only [Function.update_of_ne hxu, Function.update_of_ne hyu] using hf x y he

lemma path_end_edge_absent {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hl : 2 ≤ p.length) :
    ¬ p.toSubgraph.Adj u v := by
  intro h
  have hs := hp.snd_of_toSubgraph_adj h
  have hi : (1 : ℕ) = p.length := hp.getVert_injOn (by simpa using (show 1 ≤ p.length by omega))
    (by simp) (hs.trans p.getVert_length.symm)
  omega

noncomputable def endColor (u v : V) (b : Bool) (f : V → Bool) (x : V) : Bool :=
  if x = u ∨ x = v then b else f x

@[simp] lemma endColor_left (u v : V) (b : Bool) (f : V → Bool) : endColor u v b f u = b := by
  simp [endColor]

@[simp] lemma endColor_right (u v : V) (b : Bool) (f : V → Bool) : endColor u v b f v = b := by
  simp [endColor]

noncomputable def liftedPath {u v : V} (p : G.Walk u v) (b : Bool) (f : V → Bool) :
    (doubleGraph G).Walk (u,b) (v,b) :=
  (p.map (liftHom G (endColor u v b f))).copy
    (by simp [liftHom]) (by simp [liftHom])

lemma liftedPath_isPath {u v : V} (p : G.Walk u v) (hp : p.IsPath) (b : Bool) (f : V → Bool) :
    (liftedPath p b f).IsPath := by
  simpa only [liftedPath, Walk.isPath_def, Walk.support_copy] using
    (Walk.map_isPath_of_injective (liftHom_injective (G := G) (endColor u v b f))) hp

lemma liftedPath_adj {u v : V} (p : G.Walk u v) (b : Bool) (f : V → Bool)
    (x y : V) (c d : Bool) :
    (liftedPath p b f).toSubgraph.Adj (x,c) (y,d) ↔
      p.toSubgraph.Adj x y ∧ c = endColor u v b f x ∧ d = endColor u v b f y := by
  change (s((x,c),(y,d)) ∈ (liftedPath p b f).toSubgraph.edgeSet) ↔ _
  rw [Walk.mem_edges_toSubgraph]
  simp only [liftedPath, Walk.edges_copy]
  rw [← Walk.mem_edges_toSubgraph, Walk.toSubgraph_map]
  exact lift_subgraph_adj _ _ _ _ _ _

lemma liftedPath_support {u v : V} (p : G.Walk u v) (b : Bool) (f : V → Bool) (x : V) (c : Bool) :
    (x,c) ∈ (liftedPath p b f).support ↔ x ∈ p.support ∧ c = endColor u v b f x := by
  simp only [liftedPath, Walk.support_copy, Walk.support_map, List.mem_map]
  simp [liftHom, eq_comm]

noncomputable def doublePathCycle {u v : V} (p : G.Walk u v) (b : Bool) (f : V → Bool) :
    (doubleGraph G).Walk (u,b) (u,b) :=
  (liftedPath p b f).append (liftedPath p b (fun x => !f x)).reverse

lemma doublePathCycle_adj {u v : V} (p : G.Walk u v) (b : Bool) (f : V → Bool)
    (x y : V) (c d : Bool) :
    (doublePathCycle p b f).toSubgraph.Adj (x,c) (y,d) ↔
      p.toSubgraph.Adj x y ∧
      ((c = endColor u v b f x ∧ d = endColor u v b f y) ∨
        (c = endColor u v b (fun x => !f x) x ∧ d = endColor u v b (fun x => !f x) y)) := by
  simp only [doublePathCycle, Walk.toSubgraph_append, Walk.toSubgraph_reverse,
    SimpleGraph.Subgraph.sup_adj, liftedPath_adj]
  tauto

lemma endColor_eq_complement_iff (u v : V) (b : Bool) (f : V → Bool) (x : V) :
    endColor u v b f x = endColor u v b (fun x => !f x) x ↔ x = u ∨ x = v := by
  classical
  by_cases hx : x = u ∨ x = v
  · simp [endColor, hx]
  · cases h : f x <;> simp [endColor, hx, h]

lemma path_edge_not_both_ends {u v x y : V} (p : G.Walk u v) (hp : p.IsPath)
    (hl : 2 ≤ p.length) (hxy : p.toSubgraph.Adj x y) :
    ¬ ((x = u ∨ x = v) ∧ (y = u ∨ y = v)) := by
  rintro ⟨hx,hy⟩
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact hxy.ne rfl
  · exact path_end_edge_absent p hp hl hxy
  · exact path_end_edge_absent p hp hl hxy.symm
  · exact hxy.ne rfl

lemma doublePathCycle_isCycle {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hl : 2 ≤ p.length) (b : Bool) (f : V → Bool) : (doublePathCycle p b f).IsCycle := by
  have huv : u ≠ v := by
    intro h; subst v
    have hnil := (Walk.isPath_iff_eq_nil p).mp hp
    simp [hnil] at hl
  apply append_isCycle_of_support_inter (liftedPath_isPath p hp b f)
    (liftedPath_isPath p hp b (fun x => !f x)).reverse
    (fun h => huv (congrArg Prod.fst h))
  · intro e he he'
    simp only [Walk.edges_reverse, List.mem_reverse] at he'
    induction e using Sym2.ind with | h x y =>
    rcases x with ⟨x,c⟩
    rcases y with ⟨y,d⟩
    have h₁ := (liftedPath_adj p b f x y c d).mp
      ((liftedPath p b f).mem_edges_toSubgraph.mpr he)
    have h₂ := (liftedPath_adj p b (fun x => !f x) x y c d).mp
      ((liftedPath p b (fun x => !f x)).mem_edges_toSubgraph.mpr he')
    exact path_edge_not_both_ends p hp hl h₁.1 ⟨
      (endColor_eq_complement_iff u v b f x).mp (h₁.2.1.symm.trans h₂.2.1),
      (endColor_eq_complement_iff u v b f y).mp (h₁.2.2.symm.trans h₂.2.2)⟩
  · rintro ⟨x,c⟩ hx hx'
    simp only [Walk.support_reverse, List.mem_reverse] at hx'
    have h₁ := (liftedPath_support p b f x c).mp hx
    have h₂ := (liftedPath_support p b (fun x => !f x) x c).mp hx'
    have hends := (endColor_eq_complement_iff u v b f x).mp (h₁.2.symm.trans h₂.2)
    rcases hends with rfl | rfl
    · left
      simpa using h₁.2
    · right
      simpa using h₁.2

lemma doublePath_edges_split {u v x y : V} (p : G.Walk u v) (hp : p.IsPath)
    (hl : 2 ≤ p.length) (f : V → Bool)
    (hf : ∀ x y, s(x,y) ∈ p.edges → f x ≠ f y)
    (hxy : p.toSubgraph.Adj x y) (c d : Bool) :
    ((doublePathCycle p false (fun _ => false)).toSubgraph.Adj (x,c) (y,d) ∨
      (doublePathCycle p true f).toSubgraph.Adj (x,c) (y,d)) ∧
    ¬ ((doublePathCycle p false (fun _ => false)).toSubgraph.Adj (x,c) (y,d) ∧
      (doublePathCycle p true f).toSubgraph.Adj (x,c) (y,d)) := by
  classical
  have hends := path_edge_not_both_ends p hp hl hxy
  have hcol := hf x y (p.mem_edges_toSubgraph.mp hxy)
  simp only [doublePathCycle_adj, hxy, true_and]
  by_cases hx : x = u ∨ x = v <;> by_cases hy : y = u ∨ y = v
  · exact (hends ⟨hx,hy⟩).elim
  all_goals cases hc : f x <;> cases hd : f y <;> cases c <;> cases d <;>
    simp_all [endColor]

lemma doublePathCycle_projection {u v : V} (p : G.Walk u v) (b : Bool) (f : V → Bool)
    {x y : V × Bool} (h : (doublePathCycle p b f).toSubgraph.Adj x y) :
    p.toSubgraph.Adj x.1 y.1 := (doublePathCycle_adj p b f x.1 y.1 x.2 y.2).mp h |>.1

lemma doublePath_two_cycles {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hl : 2 ≤ p.length) :
    ∃ c₀ : (doubleGraph G).Walk (u,false) (u,false),
    ∃ c₁ : (doubleGraph G).Walk (u,true) (u,true),
      c₀.IsCycle ∧ c₁.IsCycle ∧ c₀.edges.Disjoint c₁.edges ∧
      ∀ x y : V × Bool,
        (c₀.toSubgraph.Adj x y ∨ c₁.toSubgraph.Adj x y) ↔ p.toSubgraph.Adj x.1 y.1 := by
  obtain ⟨f,hf⟩ := path_coloring p hp
  refine ⟨doublePathCycle p false (fun _ => false), doublePathCycle p true f,
    doublePathCycle_isCycle p hp hl false _, doublePathCycle_isCycle p hp hl true _, ?_, ?_⟩
  · intro e he he'
    induction e using Sym2.ind with | h x y =>
    have h₀ := (doublePathCycle p false (fun _ => false)).mem_edges_toSubgraph.mpr he
    have h₁ := (doublePathCycle p true f).mem_edges_toSubgraph.mpr he'
    exact (doublePath_edges_split p hp hl f hf (doublePathCycle_projection p false _ h₀)
      x.2 y.2).2 ⟨h₀,h₁⟩
  · intro x y
    constructor
    · rintro (h | h)
      · exact doublePathCycle_projection p false _ h
      · exact doublePathCycle_projection p true _ h
    · intro h
      exact (doublePath_edges_split p hp hl f hf h x.2 y.2).1

def edgeSquare {u v : V} (h : G.Adj u v) : (doubleGraph G).Walk (u,false) (u,false) :=
  .cons (v := (v,false)) h (.cons (v := (u,true)) h.symm
    (.cons (v := (v,true)) h (.cons (v := (u,false)) h.symm .nil)))

lemma edgeSquare_isCycle {u v : V} (h : G.Adj u v) : (edgeSquare h).IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  simp [edgeSquare, h.ne, h.ne.symm]

lemma edgeSquare_adj {u v : V} (h : G.Adj u v) (x y : V × Bool) :
    (edgeSquare h).toSubgraph.Adj x y ↔ s(x.1,y.1) = s(u,v) := by
  rcases x with ⟨x,c⟩
  rcases y with ⟨y,d⟩
  change (s((x,c),(y,d)) ∈ (edgeSquare h).toSubgraph.edgeSet) ↔ _
  rw [Walk.mem_edges_toSubgraph]
  cases c <;> cases d <;> simp [edgeSquare, Prod.mk.injEq, and_comm, or_comm]

def doubleEdges (s : Set (Sym2 V)) : Set (Sym2 (V × Bool)) := (Sym2.map Prod.fst) ⁻¹' s

@[simp] lemma mem_doubleEdges (s : Set (Sym2 V)) (x y : V × Bool) :
    s(x,y) ∈ doubleEdges s ↔ s(x.1,y.1) ∈ s := Iff.rfl

lemma doublePath_family [Fintype V] {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    ∃ D : Finset (doubleGraph G).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (D : Set (doubleGraph G).Subgraph) (fun H => H.edgeSet) ∧
      (⋃ H ∈ D, H.edgeSet) = doubleEdges p.toSubgraph.edgeSet ∧ D.card ≤ 2 := by
  classical
  by_cases hl : 2 ≤ p.length
  · obtain ⟨c₀,c₁,hc₀,hc₁,hdis,hcover⟩ := doublePath_two_cycles p hp hl
    let D : Finset (doubleGraph G).Subgraph := {c₀.toSubgraph,c₁.toSubgraph}
    refine ⟨D, ?_, ?_, ?_, by simpa only [Finset.card_singleton] using Finset.card_insert_le c₀.toSubgraph {c₁.toSubgraph}⟩
    · intro H hH
      simp only [D, Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl
      · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using cycle_coe_regular (doubleGraph G) hc₀
      · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using cycle_coe_regular (doubleGraph G) hc₁
    · simp only [D, Finset.coe_insert, Finset.coe_singleton]
      apply (Set.pairwiseDisjoint_singleton _ _).insert
      intro H hH _
      have hH' : H = c₁.toSubgraph := Set.mem_singleton_iff.mp hH
      subst H
      apply Set.disjoint_left.mpr
      intro e he he'
      exact hdis (c₀.mem_edges_toSubgraph.mp he) (c₁.mem_edges_toSubgraph.mp he')
    · ext e
      induction e using Sym2.ind with | h x y =>
      simpa only [D, Finset.set_biUnion_insert, Finset.set_biUnion_singleton,
        Set.mem_union, mem_doubleEdges, SimpleGraph.Subgraph.mem_edgeSet] using hcover x y
  · cases p with
    | nil =>
      refine ⟨∅, by simp, by simp, ?_, by simp⟩
      ext e
      simp [doubleEdges]
    | cons h q =>
      cases q with
      | nil =>
        refine ⟨{(edgeSquare h).toSubgraph}, ?_, by simp, ?_, by simp⟩
        · intro H hH
          have hH' : H = (edgeSquare h).toSubgraph := Finset.mem_singleton.mp hH
          subst H
          simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
            ← Nat.card_eq_fintype_card] using cycle_coe_regular (doubleGraph G) (edgeSquare_isCycle h)
        · ext e
          induction e using Sym2.ind with | h x y =>
          simp only [Finset.set_biUnion_singleton, mem_doubleEdges, SimpleGraph.Subgraph.mem_edgeSet,
            edgeSquare_adj]
          change _ ↔ s(x.1,y.1) ∈ (Walk.cons h Walk.nil).toSubgraph.edgeSet
          rw [Walk.mem_edges_toSubgraph]
          simp
      | cons _ q => simp only [Walk.length_cons] at hl; omega

lemma combine_finite_cycle_families {I W : Type*} [Fintype I] [Fintype W]
    {H : SimpleGraph W} (D : I → Finset H.Subgraph) (E : I → Set (Sym2 W))
    (hD : ∀ i K, K ∈ D i → K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hp : ∀ i, Set.PairwiseDisjoint (D i : Set H.Subgraph) (fun K => K.edgeSet))
    (he : ∀ i, (⋃ K ∈ D i, K.edgeSet) = E i)
    (hE : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hcover : (⋃ i, E i) = H.edgeSet) :
    ∃ F : Finset H.Subgraph,
      (∀ K ∈ F, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧ IsDecomposition H F ∧
      F.card ≤ ∑ i, (D i).card := by
  classical
  let F := Finset.univ.biUnion D
  have hsub : ∀ i K, K ∈ D i → K.edgeSet ⊆ E i := by
    intro i K hK e heK
    rw [← he i]
    exact Set.mem_iUnion.mpr ⟨K, Set.mem_iUnion.mpr ⟨hK,heK⟩⟩
  refine ⟨F, ?_, ⟨?_, ?_⟩, Finset.card_biUnion_le⟩
  · intro K hK
    obtain ⟨i,_,hK⟩ := Finset.mem_biUnion.mp hK
    exact hD i K hK
  · intro K hK L hL hne
    change K ∈ F at hK
    change L ∈ F at hL
    obtain ⟨i,_,hK⟩ := Finset.mem_biUnion.mp hK
    obtain ⟨j,_,hL⟩ := Finset.mem_biUnion.mp hL
    by_cases hij : i = j
    · subst j
      exact hp i hK hL hne
    · exact (hE hij).mono (hsub i K hK) (hsub j L hL)
  · rw [← hcover]
    ext e
    simp only [F, Finset.mem_biUnion, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨K,⟨i,hK⟩,heK⟩
      exact ⟨i,hsub i K hK heK⟩
    · rintro ⟨i,hi⟩
      rw [← he i] at hi
      obtain ⟨K,hi⟩ := Set.mem_iUnion.mp hi
      obtain ⟨hK,heK⟩ := Set.mem_iUnion.mp hi
      exact ⟨K,⟨i,hK⟩,heK⟩

def IsPathPiece (H : G.Subgraph) : Prop :=
  ∃ u v : V, ∃ p : G.Walk u v, p.IsPath ∧ H.edgeSet = p.toSubgraph.edgeSet

lemma path_decomposition_double_cycles [Fintype V]
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsPathPiece H) (hdec : IsDecomposition G D) :
    ∃ F : Finset (doubleGraph G).Subgraph,
      (∀ K ∈ F, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (doubleGraph G) F ∧ F.card ≤ 2 * D.card := by
  classical
  have hpaths : ∀ H : D, ∃ u v : V, ∃ p : G.Walk u v,
      p.IsPath ∧ H.val.edgeSet = p.toSubgraph.edgeSet := fun H => hD H.val H.property
  choose u v p hp he using hpaths
  have hfamilies : ∀ H : D, ∃ F : Finset (doubleGraph G).Subgraph,
      (∀ K ∈ F, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (F : Set (doubleGraph G).Subgraph) (fun K => K.edgeSet) ∧
      (⋃ K ∈ F, K.edgeSet) = doubleEdges H.val.edgeSet ∧ F.card ≤ 2 := by
    intro H
    rw [he H]
    exact doublePath_family (p H) (hp H)
  choose F hF hpF heF hcF using hfamilies
  have hE : Pairwise (fun H K : D => Disjoint (doubleEdges H.val.edgeSet) (doubleEdges K.val.edgeSet)) := by
    intro H K hne
    apply Set.disjoint_left.mpr
    intro e heH heK
    exact Set.disjoint_left.mp (hdec.1 H.property K.property (fun h => hne (Subtype.ext h))) heH heK
  have hcover : (⋃ H : D, doubleEdges H.val.edgeSet) = (doubleGraph G).edgeSet := by
    ext e
    induction e using Sym2.ind with | h x y =>
    simp only [Set.mem_iUnion, mem_doubleEdges]
    change (∃ H : D, s(x.1,y.1) ∈ H.val.edgeSet) ↔ G.Adj x.1 y.1
    have he : (∃ H : G.Subgraph, H ∈ D ∧ s(x.1,y.1) ∈ H.edgeSet) ↔ G.Adj x.1 y.1 := by
      simpa only [Set.mem_iUnion, exists_prop, SimpleGraph.mem_edgeSet] using
        Set.ext_iff.mp hdec.2 s(x.1,y.1)
    simpa only [Subtype.exists, exists_prop] using he
  obtain ⟨E,hE',hdecE,hcE⟩ := combine_finite_cycle_families F
    (fun H : D => doubleEdges H.val.edgeSet) hF hpF heF hE hcover
  refine ⟨E,hE',hdecE,hcE.trans ?_⟩
  calc
    _ ≤ ∑ _H : D, (2 : ℕ) := Finset.sum_le_sum (fun H _ => hcF H)
    _ = _ := by simp [mul_comm]

lemma doubled_path_graph_bound [Fintype V] {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hcover : p.toSubgraph.edgeSet = G.edgeSet) :
    ∃ D : Finset (doubleGraph G).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (doubleGraph G) D ∧ D.card ≤ 2 := by
  obtain ⟨D,hD,hpD,heD,hcD⟩ := doublePath_family p hp
  refine ⟨D,hD,⟨hpD,heD.trans ?_⟩,hcD⟩
  rw [hcover]
  ext e
  induction e using Sym2.ind with | h x y => rfl

lemma improve_of_doubled_path [Fintype V] {W : Type*} [Fintype W] {H : SimpleGraph W}
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hcover : p.toSubgraph.edgeSet = G.edgeSet)
    (f : doubleGraph G →g H) (hf : Function.Injective f)
    (D A : Finset H.Subgraph) (hD : ∀ K ∈ D, IsCycleOrEdge K.coe)
    (hdec : IsDecomposition H D) (hAD : A ⊆ D) (hcard : 2 < A.card)
    (hA : (⋃ K ∈ A, K.edgeSet) = Sym2.map f '' (doubleGraph G).edgeSet) :
    ∃ E : Finset H.Subgraph,
      (∀ K ∈ E, IsCycleOrEdge K.coe) ∧ IsDecomposition H E ∧ E.card < D.card := by
  classical
  obtain ⟨B,hB,hdecB,hcB⟩ := doubled_path_graph_bound p hp hcover
  obtain ⟨C,hC,hpC,heC,hcC⟩ := map_cycle_decomposition_injective f hf B hB hdecB
  apply replace_decomposition_subfamily D A C hD hdec hAD
    (fun K hK => Or.inl (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hC K hK)) hpC (hA.trans heC.symm)
  omega

#print axioms doublePath_two_cycles
#print axioms doublePath_family
#print axioms path_decomposition_double_cycles
#print axioms doubled_path_graph_bound
#print axioms improve_of_doubled_path
end Erdos184Work.DoublePath


/-! Nonseparating cycle exchanges. These partial results do not establish a uniform linear bound. -/

open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.Transversal

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def CycleTransversal (D : Finset G.Subgraph) (s : Set (Sym2 V)) : Prop :=
  ∀ H ∈ D, (H.edgeSet ∩ s).Subsingleton

lemma cycle_piece_not_bridge (H : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) (e : Sym2 V) (he : e ∈ H.edgeSet) :
    ¬ H.spanningCoe.IsBridge e := by
  classical
  induction e using Sym2.ind with | h u v =>
  obtain ⟨c,hc,hcH⟩ := LongRing.regular_cycle_walk_at H hH.1 (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hH.2) u (H.edge_vert he)
  have hce : ∀ e ∈ c.edges, e ∈ H.spanningCoe.edgeSet := by
    intro e hec
    have hec' := c.mem_edges_toSubgraph.mpr hec
    rwa [hcH] at hec'
  let q := c.transfer H.spanningCoe hce
  have hq : q.IsCycle := hc.transfer hce
  have heq : s(u,v) ∈ q.edges := by
    simp only [q, Walk.edges_transfer]
    exact c.mem_edges_toSubgraph.mp (hcH.symm ▸ he)
  intro hb
  exact (SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem.mp hb).2 q hq heq

lemma delete_transversal_reachable (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) (s : Set (Sym2 V)) (hs : CycleTransversal D s) (u v : V) :
    (G.deleteEdges s).Reachable u v ↔ G.Reachable u v := by
  classical
  have hstep : ∀ x y, G.Adj x y → (G.deleteEdges s).Reachable x y := by
    intro x y hxy
    by_cases he : s(x,y) ∈ s
    · have heD : s(x,y) ∈ ⋃ H ∈ D, H.edgeSet := hdec.2.symm ▸ hxy
      obtain ⟨H,heD⟩ := Set.mem_iUnion.mp heD
      obtain ⟨hHD,heH⟩ := Set.mem_iUnion.mp heD
      have hb := cycle_piece_not_bridge H (hD H hHD) s(x,y) heH
      have hr : (H.spanningCoe \ SimpleGraph.fromEdgeSet {s(x,y)}).Reachable x y := by
        simpa only [SimpleGraph.isBridge_iff, show H.spanningCoe.Adj x y from heH,
          true_and, not_not] using hb
      obtain ⟨p,hp⟩ := SimpleGraph.reachable_delete_edges_iff_exists_walk.mp hr
      refine ⟨p.transfer (G.deleteEdges s) ?_⟩
      intro e hep
      have heH' : e ∈ H.edgeSet := p.edges_subset_edgeSet hep
      have heG : e ∈ G.edgeSet := H.edgeSet_subset heH'
      have hens : e ∉ s := by
        intro hes
        have heq := hs H hHD ⟨heH',hes⟩ ⟨heH,he⟩
        exact hp (heq ▸ hep)
      simpa only [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff] using And.intro heG hens
    · exact (SimpleGraph.deleteEdges_adj.mpr ⟨hxy,he⟩).reachable
  constructor
  · exact SimpleGraph.Reachable.mono (G.deleteEdges_le s)
  · rintro ⟨p⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons h p ih => exact (hstep _ _ h).trans ih

lemma delete_transversal_connected (hG : G.Connected) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) (s : Set (Sym2 V)) (hs : CycleTransversal D s) :
    (G.deleteEdges s).Connected := by
  letI := hG.nonempty
  exact ⟨fun u v => (delete_transversal_reachable D hD hdec s hs u v).mpr (hG.preconnected u v)⟩

lemma even_connected_rank_bound (hG : G.Connected) (heven : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧ IsDecomposition G D ∧
      D.card + Fintype.card V ≤ G.edgeFinset.card + 1 := by
  classical
  obtain ⟨T,hTG,hT⟩ := hG.exists_isTree_le
  obtain ⟨D,hD,hdec,hc⟩ := SingleAddition.even_feedback_decomposition G T heven hT.IsAcyclic
  have htree := hT.card_edgeFinset
  have hcount : (G \ T).edgeFinset.card + T.edgeFinset.card = G.edgeFinset.card := by
    rw [SimpleGraph.edgeFinset_sdiff]
    exact Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hTG)
  refine ⟨D,hD,hdec,?_⟩
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc htree hcount ⊢
  omega

set_option maxHeartbeats 2000000 in
lemma nonseparating_cycle_decomposition (heven : ∀ v, Even (G.degree v))
    {u : V} (p : G.Walk u u) (hp : p.IsCycle)
    (hconn : (G \ p.toSubgraph.spanningCoe).Connected) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card + Fintype.card V + p.length ≤ G.edgeFinset.card + 2 := by
  classical
  let R := G \ p.toSubgraph.spanningCoe
  have hReven : ∀ v, Even (R.degree v) := by
    intro v
    have hd := degree_sdiff_add G p.toSubgraph.spanningCoe p.toSubgraph.spanningCoe_le v
    have he := cycle_spanning_even G hp v
    have hG := heven v
    rw [Nat.even_iff] at he hG ⊢
    change R.degree v + p.toSubgraph.spanningCoe.degree v = G.degree v at hd
    omega
  obtain ⟨A,hA,hdecA,hcA⟩ := even_connected_rank_bound (G := R) hconn (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hReven v)
  obtain ⟨D,hD,hdecD,hcD⟩ := add_cycle_to_decomposition G hp A
    (fun H hH => Or.inl (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hA H hH)) hdecA
  have hcount : R.edgeFinset.card + p.toSubgraph.spanningCoe.edgeFinset.card = G.edgeFinset.card := by
    dsimp only [R]
    rw [SimpleGraph.edgeFinset_sdiff]
    exact Finset.card_sdiff_add_card_eq_card
      (SimpleGraph.edgeFinset_mono p.toSubgraph.spanningCoe_le)
  have hlength := cycle_edge_count G hp
  refine ⟨D,hD,hdecD,?_⟩
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcA hcount hlength ⊢
  omega

lemma CycleTransversal.card_eq_of_hits {D : Finset G.Subgraph} {s : Set (Sym2 V)}
    (hs : CycleTransversal D s) (hdec : IsDecomposition G D) (hsub : s ⊆ G.edgeSet)
    (hhit : ∀ H ∈ D, (H.edgeSet ∩ s).Nonempty) : s.ncard = D.card := by
  classical
  have hex : ∀ H : D, ∃ e : s, e.val ∈ H.val.edgeSet := by
    intro H
    obtain ⟨e,heH,hes⟩ := hhit H.val H.property
    exact ⟨⟨e,hes⟩,heH⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro H K he
    apply Subtype.ext
    by_contra hne
    exact Set.disjoint_left.mp (hdec.1 H.property K.property hne) (hf H) (he ▸ hf K)
  have hsurj : Function.Surjective f := by
    intro e
    have heD : e.val ∈ ⋃ H ∈ D, H.edgeSet := hdec.2.symm ▸ hsub e.property
    obtain ⟨H,heD⟩ := Set.mem_iUnion.mp heD
    obtain ⟨hHD,heH⟩ := Set.mem_iUnion.mp heD
    refine ⟨⟨H,hHD⟩,Subtype.ext ?_⟩
    exact hs H hHD ⟨hf ⟨H,hHD⟩,(f ⟨H,hHD⟩).property⟩ ⟨heH,e.property⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)
  rw [Fintype.card_coe] at hc
  simpa only [← Nat.card_eq_fintype_card] using hc.symm

lemma rainbow_cycle_decomposition (hG : G.Connected)
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) {u : V} (p : G.Walk u u) (hp : p.IsCycle)
    (hrainbow : CycleTransversal D p.toSubgraph.edgeSet) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, IsCycleOrEdge H.coe) ∧ IsDecomposition G E ∧
      E.card + Fintype.card V + p.length ≤ G.edgeFinset.card + 2 := by
  classical
  have hgraph : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  have heven : ∀ v, Even (G.degree v) := by
    have h := cycle_subfamily_even D hD hdec.1
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
    rwa [hgraph] at h
  have hconn := delete_transversal_connected hG D hD hdec _ hrainbow
  change (G.deleteEdges p.toSubgraph.spanningCoe.edgeSet).Connected at hconn
  rw [SimpleGraph.deleteEdges_edgeSet] at hconn
  exact nonseparating_cycle_decomposition (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heven v) p hp hconn

lemma rainbow_cycle_improves_of_sparse_union (hG : G.Connected)
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) {u : V} (p : G.Walk u u) (hp : p.IsCycle)
    (hrainbow : CycleTransversal D p.toSubgraph.edgeSet)
    (hsparse : G.edgeFinset.card + 2 < D.card + Fintype.card V + p.length) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, IsCycleOrEdge H.coe) ∧ IsDecomposition G E ∧ E.card < D.card := by
  obtain ⟨E,hE,hdecE,hcE⟩ := rainbow_cycle_decomposition hG D hD hdec p hp hrainbow
  exact ⟨E,hE,hdecE,by omega⟩

lemma minimum_rainbow_cycle_overlap_bound (hG : G.Connected)
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D)
    (hmin : ∀ E : Finset G.Subgraph, (∀ H ∈ E, IsCycleOrEdge H.coe) →
      IsDecomposition G E → D.card ≤ E.card)
    {u : V} (p : G.Walk u u) (hp : p.IsCycle)
    (hrainbow : CycleTransversal D p.toSubgraph.edgeSet)
    (hhit : ∀ H ∈ D, (H.edgeSet ∩ p.toSubgraph.edgeSet).Nonempty) :
    2 * D.card + Fintype.card V ≤ G.edgeFinset.card + 2 := by
  obtain ⟨E,hE,hdecE,hcE⟩ := rainbow_cycle_decomposition hG D hD hdec p hp hrainbow
  have hc := hmin E hE hdecE
  have hcount := hrainbow.card_eq_of_hits hdec p.toSubgraph.edgeSet_subset hhit
  have hlength := cycle_edge_count G hp
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hlength hcE ⊢
  change p.toSubgraph.edgeSet.ncard = p.length at hlength
  omega

lemma CycleTransversal.mono {D : Finset G.Subgraph} {s t : Set (Sym2 V)}
    (ht : CycleTransversal D t) (hst : s ⊆ t) : CycleTransversal D s := by
  intro H hH x hx y hy
  exact ht H hH ⟨hx.1,hst hx.2⟩ ⟨hy.1,hst hy.2⟩

lemma exists_transversal_graph (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) :
    ∃ R : SimpleGraph V, R ≤ G ∧ CycleTransversal D R.edgeSet ∧
      (∀ H ∈ D, (H.edgeSet ∩ R.edgeSet).Nonempty) ∧ R.edgeFinset.card = D.card := by
  classical
  have hex : ∀ H : D, ∃ e : Sym2 V, e ∈ H.val.edgeSet := by
    intro H
    obtain ⟨v⟩ := (hD H.val H.property).1.nonempty
    have hreg := (hD H.val H.property).2 v
    obtain ⟨w,hw⟩ := (H.val.coe.degree_pos_iff_exists_adj v).mp (by omega)
    exact ⟨s(v.val,w.val),hw⟩
  choose f hf using hex
  let s := Set.range f
  have hsub : s ⊆ G.edgeSet := by
    rintro e ⟨H,rfl⟩
    exact H.val.edgeSet_subset (hf H)
  have hs : CycleTransversal D s := by
    intro H hH e he e' he'
    obtain ⟨K,rfl⟩ := he.2
    obtain ⟨L,rfl⟩ := he'.2
    have hKH : K.val = H := by
      by_contra hne
      exact Set.disjoint_left.mp (hdec.1 K.property hH hne) (hf K) he.1
    have hLH : L.val = H := by
      by_contra hne
      exact Set.disjoint_left.mp (hdec.1 L.property hH hne) (hf L) he'.1
    exact congrArg f (Subtype.ext (hKH.trans hLH.symm))
  have hhit : ∀ H ∈ D, (H.edgeSet ∩ s).Nonempty := by
    intro H hH
    exact ⟨f ⟨H,hH⟩,hf ⟨H,hH⟩,⟨⟨H,hH⟩,rfl⟩⟩
  let R := SimpleGraph.fromEdgeSet s
  have hRE : R.edgeSet = s := by
    ext e
    induction e using Sym2.ind with | h x y =>
    change (s(x,y) ∈ s ∧ x ≠ y) ↔ s(x,y) ∈ s
    exact ⟨And.left, fun h => ⟨h,(show G.Adj x y from hsub h).ne⟩⟩
  have hRG : R ≤ G := by
    intro x y hxy
    exact hsub hxy.1
  refine ⟨R,hRG,?_,?_,?_⟩
  · rwa [hRE]
  · rwa [hRE]
  · simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
    change R.edgeSet.ncard = D.card
    rw [hRE]
    exact hs.card_eq_of_hits hdec hsub hhit

lemma exists_long_nonseparating_rainbow_cycle (hG : G.Connected)
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) (k : ℕ) (hk : 2 ≤ k)
    (hlarge : (k-1) * Fintype.card V < D.card) :
    ∃ u : V, ∃ p : G.Walk u u, p.IsCycle ∧ k < p.length ∧
      CycleTransversal D p.toSubgraph.edgeSet ∧ (G \ p.toSubgraph.spanningCoe).Connected := by
  classical
  obtain ⟨R,hRG,hrainbow,_,hcard⟩ := exists_transversal_graph D hD hdec
  have hex : ∃ u : V, ∃ p : R.Walk u u, p.IsCycle ∧ k < p.length := by
    by_contra! hno
    have hc := edges_le_of_no_long_cycle R k hk hno
    omega
  obtain ⟨u,p,hp,hlen⟩ := hex
  have hsub : (p.mapLe hRG).toSubgraph.edgeSet ⊆ R.edgeSet := by
    intro e he
    induction e using Sym2.ind with | h x y =>
    exact p.toSubgraph.adj_sub ((Walk.adj_toSubgraph_mapLe hRG).mp he)
  have ht := hrainbow.mono hsub
  have hconn := delete_transversal_connected hG D hD hdec _ ht
  change (G.deleteEdges (p.mapLe hRG).toSubgraph.spanningCoe.edgeSet).Connected at hconn
  rw [SimpleGraph.deleteEdges_edgeSet] at hconn
  exact ⟨u,p.mapLe hRG,hp.mapLe hRG,by simpa using hlen,ht,hconn⟩

#print axioms exists_long_nonseparating_rainbow_cycle
#print axioms delete_transversal_reachable
#print axioms nonseparating_cycle_decomposition
#print axioms rainbow_cycle_decomposition
#print axioms rainbow_cycle_improves_of_sparse_union
#print axioms minimum_rainbow_cycle_overlap_bound
end Erdos184Work.Transversal


/-! Minimal even cores. These results do not prove a bound on their minimum degree. -/

open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.EvenCore
open Critical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Minimality only among even subgraphs, not among all subgraphs. -/
def EvenMinimal (G : SimpleGraph V) : Prop :=
  ∀ R ≤ G, (∀ v, Even (R.degree v)) →
    R.edgeFinset.card < G.edgeFinset.card → number R < number G

/-- Deleting any simple cycle decreases the optimum by exactly one. -/
def CycleCritical (G : SimpleGraph V) : Prop :=
  ∀ u (p : G.Walk u u), p.IsCycle →
    number G = number (G \ p.toSubgraph.spanningCoe) + 1

lemma delete_cycle_even (heven : ∀ v, Even (G.degree v))
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    ∀ v, Even ((G \ p.toSubgraph.spanningCoe).degree v) := by
  classical
  intro v
  have hd := degree_sdiff_add G p.toSubgraph.spanningCoe p.toSubgraph.spanningCoe_le v
  have hC := cycle_spanning_even G hp v
  have hG := heven v
  rw [Nat.even_iff] at hC hG ⊢
  omega

lemma delete_cycle_card_lt {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    (G \ p.toSubgraph.spanningCoe).edgeFinset.card < G.edgeFinset.card := by
  classical
  have hc : (G \ p.toSubgraph.spanningCoe).edgeFinset.card +
      p.toSubgraph.spanningCoe.edgeFinset.card = G.edgeFinset.card := by
    rw [SimpleGraph.edgeFinset_sdiff]
    exact Finset.card_sdiff_add_card_eq_card
      (SimpleGraph.edgeFinset_mono p.toSubgraph.spanningCoe_le)
  have hl := cycle_edge_count G hp
  have hp3 := hp.three_le_length
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc hl ⊢
  omega

lemma number_restore_cycle {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    number G ≤ number (G \ p.toSubgraph.spanningCoe) + 1 := by
  obtain ⟨D,hD,hdec,hc⟩ := exists_minimum (G \ p.toSubgraph.spanningCoe)
  obtain ⟨E,hE,hdecE,hcE⟩ := add_cycle_to_decomposition G hp D hD hdec
  exact (number_le E hE hdecE).trans (hcE.trans_eq (congrArg (· + 1) hc))

lemma EvenMinimal.cycleCritical (hmin : EvenMinimal G)
    (heven : ∀ v, Even (G.degree v)) : CycleCritical G := by
  intro u p hp
  have he := delete_cycle_even heven hp
  have hlt := hmin (G \ p.toSubgraph.spanningCoe) sdiff_le (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using he v) (by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
      using delete_cycle_card_lt hp)
  have hle := number_restore_cycle hp
  omega

lemma exists_minimal_even_above (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) (K : ℕ) (hbad : K < number G) :
    ∃ R : SimpleGraph V, R ≤ G ∧ (∀ v, Even (R.degree v)) ∧ K < number R ∧
      ∀ S ≤ R, (∀ v, Even (S.degree v)) →
        S.edgeFinset.card < R.edgeFinset.card → number S ≤ K := by
  classical
  let P : ℕ → Prop := fun m => ∃ R : SimpleGraph V,
    R ≤ G ∧ (∀ v, Even (R.degree v)) ∧ K < number R ∧ R.edgeFinset.card = m
  have hex : ∃ m, P m := ⟨G.edgeFinset.card,G,le_rfl,heven,hbad,rfl⟩
  obtain ⟨R,hRG,hReven,hRbad,hcR⟩ := Nat.find_spec hex
  refine ⟨R,hRG,hReven,hRbad,?_⟩
  intro S hSR hSeven hcard
  by_contra! hS
  have hmin := Nat.find_min' hex ⟨S,hSR.trans hRG,hSeven,hS,rfl⟩
  rw [← hcR] at hmin
  omega

lemma exists_even_minimal_core (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) :
    ∃ R : SimpleGraph V, R ≤ G ∧ (∀ v, Even (R.degree v)) ∧
      number R = number G ∧ EvenMinimal R ∧ CycleCritical R := by
  classical
  by_cases hzero : number G = 0
  · refine ⟨⊥,bot_le,?_,hzero ▸ number_bot,?_,?_⟩
    · intro v
      simp [← SimpleGraph.card_neighborSet_eq_degree]
    · intro S hS _ hlt
      have h : S = ⊥ := le_bot_iff.mp hS
      simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hlt
      rw [h] at hlt
      exact (lt_irrefl _ hlt).elim
    · intro u p hp
      exact (SimpleGraph.isAcyclic_bot p hp).elim
  obtain ⟨R,hRG,hReven,hbad,hmin⟩ :=
    exists_minimal_even_above G heven (number G - 1) (by omega)
  have hminimal : EvenMinimal R := by
    intro S hSR hSeven hcard
    have h := hmin S hSR hSeven hcard
    omega
  have hcritical := hminimal.cycleCritical (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hReven v)
  have hRbot : R ≠ ⊥ := by
    intro h
    have hzeroR : number R = 0 := by rw [h,number_bot]
    omega
  obtain ⟨u,p,hp⟩ := exists_cycle_of_even_ne_bot R (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hReven v) hRbot
  have hlt := delete_cycle_card_lt hp
  have he := delete_cycle_even (G := R) (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hReven v) hp
  have hsmall := hmin (R \ p.toSubgraph.spanningCoe) sdiff_le (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using he v) (by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hlt)
  have hrestore := hcritical u p hp
  exact ⟨R,hRG,hReven,by omega,hminimal,hcritical⟩

/-- Every cycle of a cycle-critical graph can be a piece of a minimum decomposition. -/
lemma CycleCritical.exposes_every_cycle (hcrit : CycleCritical G)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card = number G ∧ p.toSubgraph ∈ D := by
  classical
  obtain ⟨D,hD,hdecD,hcD⟩ := exists_minimum (G \ p.toSubgraph.spanningCoe)
  obtain ⟨A,hA,hpA,heA,hcA⟩ := lift_decomposition (G := G) sdiff_le D hD hdecD
  have hC : IsCycleOrEdge p.toSubgraph.coe := Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular G hp)
  have hdis : ∀ H ∈ A, Disjoint p.toSubgraph.edgeSet H.edgeSet := by
    intro H hH
    apply Set.disjoint_left.mpr
    intro e heC heH
    have heR : e ∈ (G \ p.toSubgraph.spanningCoe).edgeSet := by
      rw [← heA]
      exact Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hH,heH⟩⟩
    rw [SimpleGraph.edgeSet_sdiff] at heR
    exact heR.2 heC
  let E := insert p.toSubgraph A
  have hE : ∀ H ∈ E, IsCycleOrEdge H.coe := by
    intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH
    · exact hC
    · exact hA H hH
  have hdecE : IsDecomposition G E := by
    constructor
    · intro H hH K hK hne
      rcases Finset.mem_insert.mp hH with rfl | hH
      · rcases Finset.mem_insert.mp hK with rfl | hK
        · exact (hne rfl).elim
        · exact hdis K hK
      · rcases Finset.mem_insert.mp hK with rfl | hK
        · exact (hdis H hH).symm
        · exact hpA hH hK hne
    · change (⋃ H ∈ insert p.toSubgraph A, H.edgeSet) = G.edgeSet
      rw [Finset.set_biUnion_insert,heA,SimpleGraph.edgeSet_sdiff]
      exact Set.union_diff_cancel (SimpleGraph.edgeSet_mono p.toSubgraph.spanningCoe_le)
  have hcE : E.card ≤ D.card + 1 := (Finset.card_insert_le _ _).trans (by omega)
  have hlo := number_le E hE hdecE
  have hcrit' := hcrit u p hp
  exact ⟨E,hE,hdecE,by omega,Finset.mem_insert_self _ _⟩

universe u

set_option maxHeartbeats 1000000 in
/-- A uniform low-degree theorem for minimal even cores would suffice.
The hypothesis is not proved here. -/
lemma uniform_even_number_bound_of_low_degree_cores (C : ℕ)
    (hlow : ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) → EvenMinimal R → R ≠ ⊥ →
      ∃ v, R.degree v ≤ 2 * C) :
    ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      (∀ v, Even (G.degree v)) → number G ≤ C * Fintype.card W := by
  classical
  have main : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W), Fintype.card W = n →
      (∀ v, Even (G.degree v)) → number G ≤ C * Fintype.card W := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ G hn heven
      obtain ⟨R,hRG,hReven,hnum,hmin,_⟩ := exists_even_minimal_core G heven
      by_cases hRbot : R = ⊥
      · have hz : number G = 0 := by rw [← hnum,hRbot,number_bot]
        rw [hz]
        exact Nat.zero_le _
      obtain ⟨v,hv⟩ := hlow R (by
        intro v
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hReven v) hmin hRbot
      obtain ⟨E,hE,hdecE,hcE⟩ := even_vertex_elimination R (by
        intro v
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hReven v) v C (by
        intro S hSeven
        have hcard : Fintype.card {w : W // w ≠ v} < Fintype.card W :=
          Fintype.card_subtype_lt (x := v) (by simp)
        have hbound := ih _ (hcard.trans_eq hn) S rfl (by
          intro v
          simpa only [← SimpleGraph.card_neighborSet_eq_degree,
            ← Nat.card_eq_fintype_card] using hSeven v)
        obtain ⟨D,hD,hdec,hcD⟩ := exists_minimum S
        have hcycles := minimal_even_decomposition_cycles (by
          intro v
          simpa only [← SimpleGraph.card_neighborSet_eq_degree,
            ← Nat.card_eq_fintype_card] using hSeven v) D hD hdec (by
          intro A hA hdecA
          rw [hcD]
          exact number_le A hA hdecA)
        exact ⟨D,(by
          intro H hH
          simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
            ← Nat.card_eq_fintype_card] using hcycles H hH),hdec,(by
          simp only [← Nat.card_eq_fintype_card] at hbound ⊢
          omega)⟩)
      have hnumE := number_le E (fun H hH => Or.inl (by
        simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hE H hH)) hdecE
      have hnpos : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨v⟩
      have hnsub : Fintype.card W - 1 + 1 = Fintype.card W :=
        Nat.sub_add_cancel (by omega)
      simp only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] at hv hcE
      simp only [← Nat.card_eq_fintype_card] at hnpos hnsub ⊢
      nlinarith
  intro W _ _ G heven
  exact main (Fintype.card W) G rfl heven

#print axioms uniform_even_number_bound_of_low_degree_cores
#print axioms exists_even_minimal_core
#print axioms CycleCritical.exposes_every_cycle
end Erdos184Work.EvenCore


/-! A counterexample to monotonicity under cycle deletion, not to Erdős 184. -/

open SimpleGraph
namespace Erdos184Work.CycleDeletion
open scoped Fin.NatCast

def baseGraph : SimpleGraph (Fin 9) where
  Adj x y := x.val / 3 = y.val / 3 ∧ x ≠ y
  symm := by intro x y h; exact ⟨h.1.symm,h.2.symm⟩
  loopless := by intro x h; exact h.2 rfl

instance : DecidableRel baseGraph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

def fullEdges : Finset (Sym2 (Fin 9)) :=
  {s(0,1),s(0,2),s(1,2),s(3,4),s(3,5),s(4,5),s(6,7),s(6,8),s(7,8),
   s(0,4),s(3,7),s(6,1),s(0,7),s(3,1),s(6,4)}

def fullGraph : SimpleGraph (Fin 9) := SimpleGraph.fromEdgeSet fullEdges

instance : DecidableRel fullGraph.Adj := by unfold fullGraph; infer_instance

def removedCycle : fullGraph.Walk 0 0 :=
  .cons (by decide) (.cons (show fullGraph.Adj 4 6 by decide)
  (.cons (show fullGraph.Adj 6 1 by decide) (.cons (show fullGraph.Adj 1 3 by decide)
  (.cons (show fullGraph.Adj 3 7 by decide) (.cons (show fullGraph.Adj 7 0 by decide) .nil)))))

def firstCycle : fullGraph.Walk 0 0 :=
  .cons (by decide) (.cons (show fullGraph.Adj 1 6 by decide)
  (.cons (show fullGraph.Adj 6 7 by decide) (.cons (show fullGraph.Adj 7 3 by decide)
  (.cons (show fullGraph.Adj 3 4 by decide) (.cons (show fullGraph.Adj 4 0 by decide) .nil)))))

def secondCycle : fullGraph.Walk 0 0 :=
  .cons (by decide) (.cons (show fullGraph.Adj 2 1 by decide)
  (.cons (show fullGraph.Adj 1 3 by decide) (.cons (show fullGraph.Adj 3 5 by decide)
  (.cons (show fullGraph.Adj 5 4 by decide) (.cons (show fullGraph.Adj 4 6 by decide)
  (.cons (show fullGraph.Adj 6 8 by decide) (.cons (show fullGraph.Adj 8 7 by decide)
  (.cons (show fullGraph.Adj 7 0 by decide) .nil))))))))

lemma removedCycle_isCycle : removedCycle.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma firstCycle_isCycle : firstCycle.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma secondCycle_isCycle : secondCycle.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma remaining_graph : fullGraph \ removedCycle.toSubgraph.spanningCoe = baseGraph := by
  ext x y
  change (fullGraph.Adj x y ∧ ¬ s(x,y) ∈ removedCycle.toSubgraph.edgeSet) ↔ baseGraph.Adj x y
  rw [removedCycle.mem_edges_toSubgraph]
  revert x y
  decide

lemma cycle_edges_disjoint : firstCycle.edges.Disjoint secondCycle.edges := by
  simp only [List.disjoint_iff_ne,firstCycle,secondCycle,Walk.edges_cons,Walk.edges_nil,
    List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  repeat' apply And.intro
  all_goals decide

lemma cycles_cover : ∀ x y : Fin 9, fullGraph.Adj x y ↔
    s(x,y) ∈ firstCycle.edges ∨ s(x,y) ∈ secondCycle.edges := by decide

open scoped Classical in
lemma full_number_le_two : Critical.number fullGraph ≤ 2 := by
  classical
  let D : Finset fullGraph.Subgraph := {firstCycle.toSubgraph,secondCycle.toSubgraph}
  have hD : ∀ H ∈ D, IsCycleOrEdge H.coe := by
    intro H hH
    simp only [D,Finset.mem_insert,Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact Or.inl (by simpa only [SimpleGraph.IsRegularOfDegree,
        ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using cycle_coe_regular fullGraph firstCycle_isCycle)
    · exact Or.inl (by simpa only [SimpleGraph.IsRegularOfDegree,
        ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using cycle_coe_regular fullGraph secondCycle_isCycle)
  have hdec : IsDecomposition fullGraph D := by
    have hdis : Disjoint firstCycle.toSubgraph.edgeSet secondCycle.toSubgraph.edgeSet := by
      apply Set.disjoint_left.mpr
      intro e he hf
      exact cycle_edges_disjoint (firstCycle.mem_edges_toSubgraph.mp he)
        (secondCycle.mem_edges_toSubgraph.mp hf)
    constructor
    · intro H hH K hK hne
      change H ∈ D at hH
      change K ∈ D at hK
      simp only [D,Finset.mem_insert,Finset.mem_singleton] at hH hK
      rcases hH with rfl | rfl <;> rcases hK with rfl | rfl
      · exact (hne rfl).elim
      · exact hdis
      · exact hdis.symm
      · exact (hne rfl).elim
    · ext e
      simp only [D,Set.mem_iUnion,Finset.mem_insert,Finset.mem_singleton,exists_prop]
      induction e using Sym2.ind with | h x y =>
      have h := cycles_cover x y
      simp only [← firstCycle.mem_edges_toSubgraph, ← secondCycle.mem_edges_toSubgraph] at h
      change (∃ H, (H = firstCycle.toSubgraph ∨ H = secondCycle.toSubgraph) ∧ s(x,y) ∈ H.edgeSet) ↔ _
      simpa only [exists_or,or_and_right,exists_eq_left] using h.symm
  exact (Critical.number_le D hD hdec).trans (by
    simpa only [D,Finset.card_singleton] using
      Finset.card_insert_le firstCycle.toSubgraph {secondCycle.toSubgraph})

open scoped Classical in
lemma base_piece_edge_bound (H : baseGraph.Subgraph) (hH : IsCycleOrEdge H.coe) :
    H.coe.edgeFinset.card ≤ 3 := by
  classical
  rcases hH with ⟨hconn,hreg⟩ | hsingle
  · have hwalk : ∀ {a b : H.verts} (p : H.coe.Walk a b), a.val.val / 3 = b.val.val / 3 := by
      intro a b p
      induction p with
      | nil => rfl
      | cons h p ih => exact (H.adj_sub h).1.trans ih
    obtain ⟨v⟩ := hconn.nonempty
    have hindex : ∀ w : H.verts, w.val.val / 3 = v.val.val / 3 := by
      intro w
      obtain ⟨p⟩ := hconn.preconnected w v
      exact hwalk p
    let f : H.verts → Fin 3 := fun w => ⟨w.val.val % 3, Nat.mod_lt _ (by omega)⟩
    have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      apply Fin.ext
      have he := congrArg Fin.val h
      have ha := hindex a
      have hb := hindex b
      dsimp only [f] at he
      omega
    have hc : Fintype.card H.verts ≤ 3 := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
    have hs := H.coe.sum_degrees_eq_twice_card_edges
    simp only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hreg hc hs ⊢
    simp only [hreg,Finset.sum_const,Finset.card_univ,smul_eq_mul,
      ← Nat.card_eq_fintype_card] at hs
    omega
  · omega

open scoped Classical in
lemma base_number_ge_three : 3 ≤ Critical.number baseGraph := by
  classical
  obtain ⟨D,hD,hdec,hcard⟩ := Critical.exists_minimum baseGraph
  have hg : subfamilyGraph D = baseGraph :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  have hc := subfamilyGraph_card_edges D hdec.1
  have hle : (∑ H ∈ D, H.coe.edgeFinset.card) ≤ D.card * 3 := by
    calc
      _ ≤ ∑ H ∈ D, 3 := Finset.sum_le_sum (fun H hH => base_piece_edge_bound H (hD H hH))
      _ = _ := by simp
  have hbase : baseGraph.edgeFinset.card = 9 := by decide
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc hbase hle
  rw [hg] at hc
  omega

lemma cycle_deletion_increases_number :
    Critical.number fullGraph < Critical.number (fullGraph \ removedCycle.toSubgraph.spanningCoe) := by
  rw [remaining_graph]
  exact lt_of_le_of_lt full_number_le_two base_number_ge_three

lemma base_even : ∀ v, Even (baseGraph.degree v) := by decide

lemma full_even : ∀ v, Even (fullGraph.degree v) := by decide

lemma full_degree_zero : fullGraph.degree 0 = 4 := by decide

open scoped Classical in
lemma full_number : Critical.number fullGraph = 2 := by
  classical
  obtain ⟨D,hD,hdec,hc⟩ := Critical.exists_minimum fullGraph
  have hd := Rectangles.decomposition_degree_bound D hD hdec (0 : Fin 9)
  have hzero := full_degree_zero
  have hu := full_number_le_two
  simp only [← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hd hzero
  omega

open scoped Classical in
lemma base_number : Critical.number baseGraph = 3 := by
  classical
  obtain ⟨D,hD,hdec,hc⟩ := exists_cycle_decomposition baseGraph (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using base_even v)
  have hle := Critical.number_le D (fun H hH => Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD H hH)) hdec
  have hbase : baseGraph.edgeFinset.card = 9 := by decide
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc hbase
  have hlo := base_number_ge_three
  omega

open scoped Classical in
/-- Deleting a simple cycle can strictly increase the optimum, even from an even graph. -/
lemma even_cycle_deletion_not_monotone :
    ¬ (∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) → ∀ u (p : G.Walk u u), p.IsCycle →
      Critical.number (G \ p.toSubgraph.spanningCoe) ≤ Critical.number G) := by
  intro h
  have hle := h fullGraph (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using full_even v) 0 removedCycle removedCycle_isCycle
  exact Nat.not_le_of_lt cycle_deletion_increases_number hle

#print axioms base_number
#print axioms full_number
#print axioms even_cycle_deletion_not_monotone
#print axioms cycle_deletion_increases_number
end Erdos184Work.CycleDeletion


/-! Even subgraphs with one feedback vertex, and saturated minimal even cores.
No uniform low-degree bound for arbitrary minimal even cores is proved here. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.StarCore
open Critical EvenCore

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Every even graph has a smaller even graph retaining all edges at `v`, in which
all cycles pass through `v`. This construction does not preserve the optimum in general. -/
lemma exists_even_star_core (G : SimpleGraph V) (heven : ∀ w, Even (G.degree w)) (v : V) :
    ∃ R : SimpleGraph V, R ≤ G ∧ (∀ w, Even (R.degree w)) ∧
      (∀ w, R.Adj v w ↔ G.Adj v w) ∧
      ∀ u (p : R.Walk u u), p.IsCycle → v ∈ p.support := by
  classical
  let P : ℕ → Prop := fun m => ∃ R : SimpleGraph V,
    R ≤ G ∧ (∀ w, Even (R.degree w)) ∧
      (∀ w, R.Adj v w ↔ G.Adj v w) ∧ R.edgeFinset.card = m
  have hex : ∃ m, P m := ⟨G.edgeFinset.card,G,le_rfl,heven,fun _ => Iff.rfl,rfl⟩
  obtain ⟨R,hRG,hReven,hRv,hcard⟩ := Nat.find_spec hex
  refine ⟨R,hRG,hReven,hRv,?_⟩
  intro u p hp
  by_contra hv
  let S := R \ p.toSubgraph.spanningCoe
  have hSeven : ∀ w, Even (S.degree w) := by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using delete_cycle_even (G := R) (by
        intro w
        simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
          using hReven w) hp w
  have hSv : ∀ w, S.Adj v w ↔ G.Adj v w := by
    intro w
    have hnot : ¬ p.toSubgraph.spanningCoe.Adj v w := by
      intro h
      exact hv (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert h))
    simpa only [S,SimpleGraph.sdiff_adj,hnot,not_false_eq_true,and_true] using hRv w
  have hmin := Nat.find_min' hex ⟨S,(sdiff_le : S ≤ R).trans hRG,(by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hSeven w),hSv,rfl⟩
  have hlt := delete_cycle_card_lt hp
  change S.edgeFinset.card < R.edgeFinset.card at hlt
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hmin hlt hcard
  rw [← hcard] at hmin
  omega

lemma number_degree_bound (G : SimpleGraph V) (v : V) : G.degree v ≤ 2 * number G := by
  obtain ⟨D,hD,hdec,hc⟩ := exists_minimum G
  have h := Rectangles.decomposition_degree_bound D hD hdec v
  simpa only [hc] using h

/-- If every cycle goes through `v`, an even graph's optimum is exactly half its degree. -/
lemma twice_number_eq_degree_of_cycle_hits (heven : ∀ w, Even (G.degree w)) (v : V)
    (hhit : ∀ u (p : G.Walk u u), p.IsCycle → v ∈ p.support) :
    2 * number G = G.degree v := by
  classical
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum G
  have hcycles := minimal_even_decomposition_cycles heven D hD hdec (by
    intro E hE hdecE
    rw [hcard]
    exact number_le E hE hdecE)
  have hvH : ∀ H ∈ D, v ∈ H.verts := by
    intro H hH
    obtain ⟨w⟩ := (hcycles H hH).1.nonempty
    obtain ⟨p,hp,hpH⟩ := LongRing.regular_cycle_walk_at H (hcycles H hH).1 (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using (hcycles H hH).2) w.val w.property
    have hvp := p.mem_verts_toSubgraph.mpr (hhit w.val p hp)
    rwa [hpH] at hvp
  have hsum := subfamilyGraph_degree D hdec.1 v
  have hgraph : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  rw [hgraph] at hsum
  have hdeg : ∀ H ∈ D, H.spanningCoe.degree v = 2 := by
    intro H hH
    rw [regular_two_spanning_degree H (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using (hcycles H hH).2),if_pos (hvH H hH)]
  have heq : (∑ H ∈ D, H.spanningCoe.degree v) = D.card * 2 := by
    calc
      _ = ∑ H ∈ D, 2 := Finset.sum_congr rfl hdeg
      _ = _ := by simp
  omega

lemma cycle_hits_iff_induce_acyclic (v : V) :
    (∀ u (p : G.Walk u u), p.IsCycle → v ∈ p.support) ↔
      (G.induce {v}ᶜ).IsAcyclic := by
  constructor
  · intro hhit u p hp
    let f := (SimpleGraph.Embedding.induce ({v}ᶜ : Set V) (G := G)).toHom
    have hpm := hp.map (f := f) Subtype.val_injective
    have hv := hhit u.val (p.map f) hpm
    simp only [Walk.support_map,List.mem_map] at hv
    obtain ⟨w,_,hw⟩ := hv
    exact w.property (Set.mem_singleton_iff.mpr hw)
  · intro hacy u p hp
    by_contra hv
    have hu : u ∈ ({v}ᶜ : Set V) := by
      intro hu
      have huv : u = v := Set.mem_singleton_iff.mp hu
      exact hv (huv ▸ p.start_mem_support)
    let H := G.induce ({v}ᶜ : Set V)
    have hs : ∀ w ∈ p.support, w ∈ ({v}ᶜ : Set V) := by
      intro w hw hwv
      exact hv ((Set.mem_singleton_iff.mp hwv) ▸ hw)
    let q := p.induce ({v}ᶜ : Set V) hs
    apply hacy q
    apply (Walk.map_isCycle_iff_of_injective
      (f := (SimpleGraph.Embedding.induce ({v}ᶜ : Set V) (G := G)).toHom)
      Subtype.val_injective).mp
    simpa only [q,Walk.map_induce] using hp

/-- An even graph with a feedback vertex has a vertex of degree at most two. -/
lemma low_degree_of_feedback_vertex (heven : ∀ w, Even (G.degree w)) (v : V)
    (hacy : (G.induce {v}ᶜ).IsAcyclic) : ∃ w, G.degree w ≤ 2 := by
  classical
  by_contra! hmin
  have hfour : ∀ w, 4 ≤ G.degree w := by
    intro w
    have he := Nat.even_iff.mp (heven w)
    have hm := hmin w
    omega
  have hforest := acyclic_card_edges_le (G.induce {v}ᶜ) hacy
  have hcard : Fintype.card ({v}ᶜ : Set V) = Fintype.card V - 1 := by
    rw [Fintype.card_compl_set]
    simp only [Fintype.card_unique]
  have hedges : (G.induce {v}ᶜ).edgeFinset.card + G.degree v = G.edgeFinset.card := by
    rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
      SimpleGraph.card_edgeFinset_deleteIncidenceSet, Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)]
  have hdeg := G.degree_lt_card_verts v
  have hs := G.sum_degrees_eq_twice_card_edges
  have hsum : 4 * Fintype.card V ≤ ∑ w : V, G.degree w := by
    calc
      _ = ∑ w : V, 4 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun w _ => hfour w)
  simp only [← SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] at hforest hcard hedges hdeg hs hsum
  omega

/-- Saturation of the vertex-degree lower bound forces a minimal even graph to
have a feedback vertex, hence a low-degree vertex. This does not cover cores
whose optimum exceeds every vertex-degree lower bound. -/
lemma EvenMinimal.saturated_vertex (hmin : EvenMinimal G)
    (heven : ∀ w, Even (G.degree w)) (v : V) (hsat : G.degree v = 2 * number G) :
    (G.induce {v}ᶜ).IsAcyclic ∧ ∃ w, G.degree w ≤ 2 := by
  classical
  obtain ⟨R,hRG,hReven,hRv,hhit⟩ := exists_even_star_core G heven v
  have hdeg : R.degree v = G.degree v := by
    have hn : R.neighborSet v = G.neighborSet v := Set.ext hRv
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    rw [hn]
  have hRnum := number_degree_bound R v
  have heq : R = G := by
    by_contra hne
    have hcard : R.edgeFinset.card < G.edgeFinset.card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨SimpleGraph.edgeFinset_mono hRG,?_⟩
      intro he
      apply hne
      exact SimpleGraph.edgeFinset_inj.mp he
    have hlt := hmin R hRG (by
      intro w
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using hReven w) (by
      simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hcard)
    omega
  have hacy := (cycle_hits_iff_induce_acyclic (G := R) v).mp hhit
  subst R
  exact ⟨hacy,low_degree_of_feedback_vertex heven v hacy⟩

lemma exists_even_star_core_number (G : SimpleGraph V)
    (heven : ∀ w, Even (G.degree w)) (v : V) :
    ∃ R : SimpleGraph V, R ≤ G ∧ (∀ w, Even (R.degree w)) ∧
      (∀ w, R.Adj v w ↔ G.Adj v w) ∧ (R.induce {v}ᶜ).IsAcyclic ∧
      2 * number R = G.degree v := by
  classical
  obtain ⟨R,hRG,hReven,hRv,hhit⟩ := exists_even_star_core G heven v
  have hnum := twice_number_eq_degree_of_cycle_hits (G := R) (by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hReven w) v hhit
  have hdeg : R.degree v = G.degree v := by
    have hn : R.neighborSet v = G.neighborSet v := Set.ext hRv
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    rw [hn]
  exact ⟨R,hRG,hReven,hRv,(cycle_hits_iff_induce_acyclic v).mp hhit,by omega⟩

lemma EvenMinimal.degree_gap (hmin : EvenMinimal G)
    (heven : ∀ w, Even (G.degree w)) (hhigh : ∀ w, 2 < G.degree w) (v : V) :
    G.degree v + 2 ≤ 2 * number G := by
  have hle := number_degree_bound G v
  have hne : G.degree v ≠ 2 * number G := by
    intro heq
    obtain ⟨w,hw⟩ := (EvenMinimal.saturated_vertex hmin heven v heq).2
    exact Nat.not_le_of_lt (hhigh w) hw
  have he := Nat.even_iff.mp (heven v)
  omega

lemma EvenMinimal.regular_four_of_number_three (hmin : EvenMinimal G)
    (heven : ∀ w, Even (G.degree w)) (hhigh : ∀ w, 2 < G.degree w)
    (hnum : number G = 3) : G.IsRegularOfDegree 4 := by
  intro v
  have hg := EvenMinimal.degree_gap hmin heven hhigh v
  have he := Nat.even_iff.mp (heven v)
  have hh := hhigh v
  omega

#print axioms exists_even_star_core_number
#print axioms EvenMinimal.degree_gap
#print axioms EvenMinimal.regular_four_of_number_three
#print axioms exists_even_star_core
#print axioms twice_number_eq_degree_of_cycle_hits
#print axioms EvenMinimal.saturated_vertex
end Erdos184Work.StarCore


/-! Characterization of degree-certified minimal even cores. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.StarCharacterization
open Critical EvenCore StarCore

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma number_eq_zero_iff (G : SimpleGraph V) : number G = 0 ↔ G = ⊥ := by
  classical
  constructor
  · intro h
    obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum G
    have hD0 : D = ∅ := Finset.card_eq_zero.mp (hcard.trans h)
    have he : G.edgeSet = ∅ := by simpa only [hD0,Finset.notMem_empty,Set.iUnion_of_empty,
      Set.iUnion_empty] using hdec.2.symm
    exact SimpleGraph.edgeSet_injective (he.trans SimpleGraph.edgeSet_bot.symm)
  · rintro rfl
    exact number_bot

lemma cycle_hits_mono {R : SimpleGraph V} (hRG : R ≤ G) (v : V)
    (hhit : ∀ u (p : G.Walk u u), p.IsCycle → v ∈ p.support) :
    ∀ u (p : R.Walk u u), p.IsCycle → v ∈ p.support := by
  intro u p hp
  simpa using hhit u (p.mapLe hRG) (hp.mapLe hRG)

/-- In the feedback-vertex case, the optimum is additive across every even
edge partition. This additivity is not asserted for arbitrary even graphs. -/
lemma number_sdiff_add_of_cycle_hits (heven : ∀ w, Even (G.degree w)) (v : V)
    (hhit : ∀ u (p : G.Walk u u), p.IsCycle → v ∈ p.support)
    (R : SimpleGraph V) (hRG : R ≤ G) (hReven : ∀ w, Even (R.degree w)) :
    number (G \ R) + number R = number G := by
  classical
  have hSeven : ∀ w, Even ((G \ R).degree w) := by
    intro w
    have hd := degree_sdiff_add G R hRG w
    have hG := Nat.even_iff.mp (heven w)
    have hR := Nat.even_iff.mp (hReven w)
    apply Nat.even_iff.mpr
    omega
  have hnG := twice_number_eq_degree_of_cycle_hits heven v hhit
  have hnR := twice_number_eq_degree_of_cycle_hits hReven v (cycle_hits_mono hRG v hhit)
  have hnS := twice_number_eq_degree_of_cycle_hits (G := G \ R) (by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hSeven w) v (cycle_hits_mono sdiff_le v hhit)
  have hd := degree_sdiff_add G R hRG v
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    at hnG hnR hnS hd
  omega

lemma evenMinimal_of_cycle_hits (heven : ∀ w, Even (G.degree w)) (v : V)
    (hhit : ∀ u (p : G.Walk u u), p.IsCycle → v ∈ p.support) : EvenMinimal G := by
  classical
  intro R hRG hReven hcard
  have hn := number_sdiff_add_of_cycle_hits heven v hhit R hRG (by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hReven w)
  have hS : G \ R ≠ ⊥ := by
    intro h
    have hGR : G ≤ R := by
      intro x y hxy
      by_contra hn
      have hs : (G \ R).Adj x y := ⟨hxy,hn⟩
      simpa only [h,SimpleGraph.bot_adj] using hs
    have heq : R = G := le_antisymm hRG hGR
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcard
    rw [heq] at hcard
    exact (lt_irrefl _ hcard).elim
  have hpos : number (G \ R) ≠ 0 := fun h => hS ((number_eq_zero_iff _).mp h)
  omega

/-- Exactly the saturated minimal even cores are the even graphs with a specified
feedback vertex. The unsaturated cores remain outside this characterization. -/
lemma saturated_minimal_iff_feedback_vertex (heven : ∀ w, Even (G.degree w)) (v : V) :
    (EvenMinimal G ∧ G.degree v = 2 * number G) ↔ (G.induce {v}ᶜ).IsAcyclic := by
  constructor
  · rintro ⟨hmin,hsat⟩
    exact (StarCore.EvenMinimal.saturated_vertex hmin heven v hsat).1
  · intro hacy
    have hhit := (cycle_hits_iff_induce_acyclic v).mpr hacy
    exact ⟨evenMinimal_of_cycle_hits heven v hhit,
      (twice_number_eq_degree_of_cycle_hits heven v hhit).symm⟩

#print axioms number_sdiff_add_of_cycle_hits
#print axioms evenMinimal_of_cycle_hits
#print axioms saturated_minimal_iff_feedback_vertex
end Erdos184Work.StarCharacterization


/- Adjacent compression is not monotone, even on edge-critical graphs. -/

open SimpleGraph
namespace Erdos184Work.Compression
open Critical CriticalExample

/-- Transfer the private neighbors of `v` to `u`, keeping the edge `uv`. -/
def transfer {V : Type*} (G : SimpleGraph V) (u v : V) : SimpleGraph V :=
  let p := fun w => w ≠ u ∧ G.Adj v w ∧ ¬ G.Adj u w
  (G \ SimpleGraph.fromRel (fun x y => x = v ∧ p y)) ⊔
    SimpleGraph.fromRel (fun x y => x = u ∧ p y)

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : DecidableRel (transfer G u v).Adj := by
  intro x y
  change Decidable ((G.Adj x y ∧
    ¬ (x ≠ y ∧ ((x = v ∧ y ≠ u ∧ G.Adj v y ∧ ¬ G.Adj u y) ∨
      (y = v ∧ x ≠ u ∧ G.Adj v x ∧ ¬ G.Adj u x)))) ∨
    (x ≠ y ∧ ((x = u ∧ y ≠ u ∧ G.Adj v y ∧ ¬ G.Adj u y) ∨
      (y = u ∧ x ≠ u ∧ G.Adj v x ∧ ¬ G.Adj u x))))
  infer_instance

open scoped Classical

lemma finite_family_decomposition {V I : Type*} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (piece : I → G.Subgraph) (edges : I → Finset (Sym2 V))
    (he : ∀ i, (piece i).edgeSet = (edges i : Set (Sym2 V)))
    (hp : ∀ i j, i ≠ j → Disjoint (edges i) (edges j))
    (hc : ∀ a b, G.Adj a b ↔ ∃ i, s(a,b) ∈ edges i) :
    IsDecomposition G (Finset.univ.image piece) := by
  constructor
  · intro H hH K hK hne
    change H ∈ Finset.univ.image piece at hH
    change K ∈ Finset.univ.image piece at hK
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hK
    change Disjoint (piece i).edgeSet (piece j).edgeSet
    rw [he i, he j, Finset.disjoint_coe]
    exact hp i j (fun h => hne (congrArg piece h))
  · ext e
    induction e using Sym2.ind with | h a b =>
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨H, ⟨i, rfl⟩, h⟩
      exact (piece i).edgeSet_subset h
    · intro h
      obtain ⟨i, hi⟩ := (hc a b).mp h
      exact ⟨piece i, ⟨i, rfl⟩, (he i).symm ▸ hi⟩

abbrev V := Fin 3 ⊕ Fin 2
abbrev l (i : Fin 3) : V := .inl i
abbrev r (i : Fin 2) : V := .inr i

def wheelEdges : Finset (Sym2 V) :=
  {s(l 0,l 1), s(l 0,l 2), s(l 0,r 0), s(l 0,r 1),
   s(l 1,r 0), s(l 1,r 1), s(l 2,r 0), s(l 2,r 1)}
def wheel : SimpleGraph V := SimpleGraph.fromEdgeSet wheelEdges
instance : DecidableRel wheel.Adj := by unfold wheel; infer_instance

def compressedEdges : Finset (Sym2 V) :=
  {s(l 0,l 1), s(l 0,l 2), s(l 0,r 0), s(l 0,r 1),
   s(l 1,r 0), s(l 1,r 1), s(l 1,l 2), s(l 2,r 1)}
def compressed : SimpleGraph V := SimpleGraph.fromEdgeSet compressedEdges
instance : DecidableRel compressed.Adj := by unfold compressed; infer_instance

lemma transferred_graph : transfer wheel (l 1) (r 0) = compressed := by
  have h : ∀ x y, (transfer wheel (l 1) (r 0)).Adj x y ↔ compressed.Adj x y := by decide
  apply SimpleGraph.ext
  funext x y
  exact propext (h x y)

lemma wheel_lower_bound (D : Finset wheel.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition wheel D) :
    4 ≤ D.card := by
  have hodd : ∀ b : Fin 2, Odd (wheel.degree (.inr b)) := by decide
  have h := independent_side_lower_bound wheel (by decide)
    (by decide) (by
      intro b
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using hodd b) D hD hdec
  have hd : (∑ a : Fin 3, wheel.degree (.inl a)) = 10 := by decide
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h hd
  rw [hd] at h
  norm_num only [Fintype.card_fin, Nat.card_fin] at h
  omega

def wheelCycle : wheel.Walk (l 0) (l 0) :=
  .cons (show wheel.Adj (l 0) (l 1) by decide)
  (.cons (show wheel.Adj (l 1) (r 0) by decide)
  (.cons (show wheel.Adj (r 0) (l 2) by decide)
  (.cons (show wheel.Adj (l 2) (r 1) by decide)
  (.cons (show wheel.Adj (r 1) (l 0) by decide) .nil))))
lemma wheelCycle_isCycle : wheelCycle.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def wheelPiece : Fin 4 → wheel.Subgraph
  | 0 => wheelCycle.toSubgraph
  | 1 => wheel.subgraphOfAdj (show wheel.Adj (l 0) (l 2) by decide)
  | 2 => wheel.subgraphOfAdj (show wheel.Adj (l 0) (r 0) by decide)
  | 3 => wheel.subgraphOfAdj (show wheel.Adj (l 1) (r 1) by decide)
def wheelPieceEdges : Fin 4 → Finset (Sym2 V)
  | 0 => wheelCycle.edges.toFinset
  | 1 => {s(l 0,l 2)}
  | 2 => {s(l 0,r 0)}
  | 3 => {s(l 1,r 1)}
lemma wheelPiece_edges (i : Fin 4) :
    (wheelPiece i).edgeSet = (wheelPieceEdges i : Set (Sym2 V)) := by
  fin_cases i
  · ext e
    simp only [wheelPiece, wheelPieceEdges, Finset.mem_coe, List.mem_toFinset]
    exact wheelCycle.mem_edges_toSubgraph
  all_goals simp [wheelPiece, wheelPieceEdges, SimpleGraph.edgeSet_subgraphOfAdj]
lemma wheelPiece_property (i : Fin 4) : IsCycleOrEdge (wheelPiece i).coe := by
  fin_cases i
  · left
    simpa only [wheelPiece, SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using cycle_coe_regular wheel wheelCycle_isCycle
  all_goals exact single_piece_property (by decide)
noncomputable def wheelDecomposition : Finset wheel.Subgraph := Finset.univ.image wheelPiece
lemma wheelDecomposition_property :
    ∀ H ∈ wheelDecomposition, IsCycleOrEdge H.coe := by
  intro H hH
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
  exact wheelPiece_property i
lemma wheelDecomposition_isDecomposition : IsDecomposition wheel wheelDecomposition :=
  finite_family_decomposition wheelPiece wheelPieceEdges wheelPiece_edges (by decide) (by decide)
lemma wheelDecomposition_card_le : wheelDecomposition.card ≤ 4 := by
  have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin 4))) (f := wheelPiece)
  simpa [wheelDecomposition] using h
lemma wheel_number : number wheel = 4 := by
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum wheel
  have hlo := wheel_lower_bound D hD hdec
  have hhi := (number_le wheelDecomposition wheelDecomposition_property
    wheelDecomposition_isDecomposition).trans wheelDecomposition_card_le
  omega

def compressedCycle₀ : compressed.Walk (l 0) (l 0) :=
  .cons (show compressed.Adj (l 0) (l 1) by decide)
  (.cons (show compressed.Adj (l 1) (r 0) by decide)
  (.cons (show compressed.Adj (r 0) (l 0) by decide) .nil))
def compressedCycle₁ : compressed.Walk (l 0) (l 0) :=
  .cons (show compressed.Adj (l 0) (l 2) by decide)
  (.cons (show compressed.Adj (l 2) (l 1) by decide)
  (.cons (show compressed.Adj (l 1) (r 1) by decide)
  (.cons (show compressed.Adj (r 1) (l 0) by decide) .nil)))
lemma compressedCycle₀_isCycle : compressedCycle₀.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide
lemma compressedCycle₁_isCycle : compressedCycle₁.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def compressedPiece : Fin 3 → compressed.Subgraph
  | 0 => compressedCycle₀.toSubgraph
  | 1 => compressedCycle₁.toSubgraph
  | 2 => compressed.subgraphOfAdj (show compressed.Adj (l 2) (r 1) by decide)
def compressedPieceEdges : Fin 3 → Finset (Sym2 V)
  | 0 => compressedCycle₀.edges.toFinset
  | 1 => compressedCycle₁.edges.toFinset
  | 2 => {s(l 2,r 1)}
lemma compressedPiece_edges (i : Fin 3) :
    (compressedPiece i).edgeSet = (compressedPieceEdges i : Set (Sym2 V)) := by
  fin_cases i
  · ext e
    simp only [compressedPiece, compressedPieceEdges, Finset.mem_coe, List.mem_toFinset]
    exact compressedCycle₀.mem_edges_toSubgraph
  · ext e
    simp only [compressedPiece, compressedPieceEdges, Finset.mem_coe, List.mem_toFinset]
    exact compressedCycle₁.mem_edges_toSubgraph
  · simp [compressedPiece, compressedPieceEdges, SimpleGraph.edgeSet_subgraphOfAdj]
lemma compressedPiece_property (i : Fin 3) : IsCycleOrEdge (compressedPiece i).coe := by
  fin_cases i
  · left
    simpa only [compressedPiece, SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using cycle_coe_regular compressed compressedCycle₀_isCycle
  · left
    simpa only [compressedPiece, SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using cycle_coe_regular compressed compressedCycle₁_isCycle
  · exact single_piece_property (by decide)
lemma compressed_number_le : number compressed ≤ 3 := by
  let D := Finset.univ.image compressedPiece
  have hD : ∀ H ∈ D, IsCycleOrEdge H.coe := by
    intro H hH
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    exact compressedPiece_property i
  have hdec := finite_family_decomposition compressedPiece compressedPieceEdges
    compressedPiece_edges (by decide) (by decide)
  have hc : D.card ≤ 3 := by
    have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin 3))) (f := compressedPiece)
    simpa [D] using h
  exact (number_le D hD hdec).trans hc
lemma compressed_number : number compressed = 3 := by
  let R := compressed.deleteEdges {s(l 2,r 1)}
  have heven : ∀ v, Even (R.degree v) := by decide
  have hd : R.degree (l 0) = 4 := by decide
  have hlo := StarCore.number_degree_bound R (l 0)
  have hnum := SingleAddition.remove_edge_to_even_number compressed
    ⟨s(l 2,r 1), by decide⟩ (by
      intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using heven v)
  change number compressed = number R + 1 at hnum
  have hhi := compressed_number_le
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd hlo
  omega

def rotate : V → V
  | .inl 0 => .inl 0
  | .inl 1 => .inr 0
  | .inl 2 => .inr 1
  | .inr 0 => .inl 2
  | .inr 1 => .inl 1

def rotateEquiv : V ≃ V where
  toFun := rotate
  invFun := fun x => rotate (rotate (rotate x))
  left_inv := by decide
  right_inv := by decide

def rotateIso : wheel ≃g wheel where
  toEquiv := rotateEquiv
  map_rel_iff' := by decide

def rotation : Fin 4 → (wheel ≃g wheel)
  | 0 => SimpleGraph.Iso.refl
  | 1 => rotateIso
  | 2 => rotateIso.trans rotateIso
  | 3 => (rotateIso.trans rotateIso).trans rotateIso

def singleEdge : Fin 4 → Sym2 V
  | 0 => s(l 0,l 1)
  | 1 => s(l 0,l 2)
  | 2 => s(l 0,r 0)
  | 3 => s(l 1,r 1)

lemma wheel_single_edges (i : Fin 4) (hi : i ≠ 0) :
    (wheelPiece i).edgeSet = {singleEdge i} := by
  fin_cases i
  · exact (hi rfl).elim
  all_goals simp [wheelPiece, singleEdge, SimpleGraph.edgeSet_subgraphOfAdj]

lemma orbit_cover : ∀ a b : V, wheel.Adj a b →
    ∃ i : Fin 4, i ≠ 0 ∧ ∃ k : Fin 4,
      Sym2.map (rotation k).toHom (singleEdge i) = s(a,b) := by decide

lemma wheel_exposure_orbits : ∀ e : wheel.edgeSet,
    ∃ H ∈ wheelDecomposition, ∃ φ : wheel ≃g wheel,
      Sym2.map φ.toHom '' H.edgeSet = {e.val} := by
  rintro ⟨e,he⟩
  induction e using Sym2.ind with | h a b =>
  obtain ⟨i,hi,k,hk⟩ := orbit_cover a b he
  refine ⟨wheelPiece i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
    rotation k, ?_⟩
  rw [wheel_single_edges i hi, Set.image_singleton, hk]

lemma wheel_critical : EdgeCritical wheel := by
  apply critical_of_exposure_orbits wheel wheelDecomposition
    wheelDecomposition_property wheelDecomposition_isDecomposition
  · have hl := number_le wheelDecomposition wheelDecomposition_property
      wheelDecomposition_isDecomposition
    have hh := wheelDecomposition_card_le
    rw [wheel_number] at hl ⊢
    omega
  · exact wheel_exposure_orbits

/-- Adjacent neighborhood transfer can lower the optimum, even on an
edge-critical simple graph. This is not a counterexample to Erdős 184. -/
theorem adjacent_transfer_not_monotone :
    EdgeCritical wheel ∧ wheel.Adj (l 1) (r 0) ∧
      number (transfer wheel (l 1) (r 0)) < number wheel := by
  refine ⟨wheel_critical, by decide, ?_⟩
  rw [transferred_graph, compressed_number, wheel_number]
  omega

#print axioms wheel_number
#print axioms compressed_number
#print axioms wheel_critical
#print axioms adjacent_transfer_not_monotone
end Erdos184Work.Compression



/-!
Weighted path rotation. This file develops an auxiliary fractional bound, not
an integral cycle-and-edge decomposition bound.
-/

open SimpleGraph
open scoped BigOperators

namespace Erdos184Work.Weighted
open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {u v z : V}

def walkWeight (w : Sym2 V → ℝ) (p : G.Walk u v) : ℝ :=
  (p.edges.map w).sum

@[simp] lemma walkWeight_nil (w : Sym2 V → ℝ) (u : V) :
    walkWeight w (.nil : G.Walk u u) = 0 := by simp [walkWeight]

@[simp] lemma walkWeight_cons (w : Sym2 V → ℝ) (h : G.Adj u v) (p : G.Walk v z) :
    walkWeight w (.cons h p) = w s(u,v) + walkWeight w p := by
  simp [walkWeight]

@[simp] lemma walkWeight_append (w : Sym2 V → ℝ) (p : G.Walk u v) (q : G.Walk v z) :
    walkWeight w (p.append q) = walkWeight w p + walkWeight w q := by
  simp [walkWeight]

@[simp] lemma walkWeight_reverse (w : Sym2 V → ℝ) (p : G.Walk u v) :
    walkWeight w p.reverse = walkWeight w p := by simp [walkWeight]

@[simp] lemma walkWeight_copy (w : Sym2 V → ℝ) (p : G.Walk u v)
    {u' v' : V} (hu : u = u') (hv : v = v') :
    walkWeight w (p.copy hu hv) = walkWeight w p := by simp [walkWeight]

lemma walkWeight_nonneg (w : Sym2 V → ℝ)
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e) (p : G.Walk u v) : 0 ≤ walkWeight w p := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp ha
  exact hw e (p.edges_subset_edgeSet he)

@[simp] lemma walkWeight_take_zero (w : Sym2 V → ℝ) (p : G.Walk u v) :
    walkWeight w (p.take 0) = 0 := by cases p <;> simp [Walk.take]

lemma walkWeight_take_succ (w : Sym2 V → ℝ) (p : G.Walk u v)
    (i : ℕ) (hi : i < p.length) :
    walkWeight w (p.take (i+1)) = walkWeight w (p.take i) + w s(p.getVert i,p.getVert (i+1)) := by
  induction p generalizing i with
  | nil => simp at hi
  | @cons a b c hab p ih =>
    cases i with
    | zero => simp [Walk.take]
    | succ i =>
      have hi' : i < p.length := by simpa using hi
      simp [Walk.take, Walk.getVert, ih i hi', add_assoc]

lemma walkWeight_take_add_drop (w : Sym2 V → ℝ) (p : G.Walk u v) (i : ℕ) :
    walkWeight w (p.take i) + walkWeight w (p.drop i) = walkWeight w p := by
  rw [← walkWeight_append, Walk.append_take_drop_eq]

lemma walkWeight_rotate (w : Sym2 V → ℝ) (p : G.Walk u v)
    (i : ℕ) (hi : G.Adj u (p.getVert i)) (hi0 : 1 ≤ i) (hil : i ≤ p.length) :
    walkWeight w (rotatePath p i hi) + w s(p.getVert (i-1),p.getVert i) =
      walkWeight w p + w s(u,p.getVert i) := by
  have htake := walkWeight_take_succ w p (i-1) (by omega)
  have hsum := walkWeight_take_add_drop w p i
  rw [Nat.sub_add_cancel hi0] at htake
  simp only [rotatePath, walkWeight_append, walkWeight_reverse, walkWeight_cons]
  linarith

lemma walkWeight_take_eq_sum (w : Sym2 V → ℝ) (p : G.Walk u v)
    (j : ℕ) (hj : j ≤ p.length) :
    walkWeight w (p.take j) = ∑ i ∈ Finset.Icc 1 j, w s(p.getVert (i-1),p.getVert i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [walkWeight_take_succ w p j (by omega), ih (by omega)]
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp

open scoped Classical in
lemma exists_maximum_weight_path [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e) :
    ∃ u v, ∃ p : G.Walk u v, p.IsPath ∧
      (∀ a b (q : G.Walk a b), q.IsPath → walkWeight w q ≤ walkWeight w p) ∧
      ∀ x, G.Adj u x → x ∈ p.support := by
  classical
  let P := (a : V) × (b : V) × G.Path a b
  let f : P → ℝ ×ₗ ℕ := fun x => toLex (walkWeight w x.2.2.val, x.2.2.val.length)
  have hne : (Finset.univ : Finset P).Nonempty := by
    obtain ⟨a⟩ := ‹Nonempty V›
    exact ⟨⟨a,a,⟨.nil,by simp⟩⟩,Finset.mem_univ _⟩
  obtain ⟨⟨a,b,p⟩,_,hmax⟩ := Finset.exists_max_image Finset.univ f hne
  have hmax' : ∀ c d (q : G.Walk c d), q.IsPath →
      walkWeight w q < walkWeight w p.val ∨
      walkWeight w q = walkWeight w p.val ∧ q.length ≤ p.val.length := by
    intro c d q hq
    exact Prod.Lex.toLex_le_toLex.mp (hmax ⟨c,d,⟨q,hq⟩⟩ (Finset.mem_univ _))
  refine ⟨a,b,p.val,p.property,?_,?_⟩
  · intro c d q hq
    rcases hmax' c d q hq with h | ⟨h,_⟩
    · exact h.le
    · exact h.le
  · intro x hx
    by_contra hnot
    have hq : (Walk.cons hx.symm p.val).IsPath :=
      (Walk.cons_isPath_iff _ _).mpr ⟨p.property,hnot⟩
    have hn : 0 ≤ w s(x,a) := hw _ hx.symm
    rcases hmax' x b (.cons hx.symm p.val) hq with h | ⟨_,hlen⟩
    · simp only [walkWeight_cons] at h
      linarith
    · simp only [Walk.length_cons] at hlen
      omega

lemma neighbor_index {p : G.Walk u v} (hx : ∀ x, G.Adj u x → x ∈ p.support)
    {x : V} (hux : G.Adj u x) :
    ∃ i, 1 ≤ i ∧ i ≤ p.length ∧ p.getVert i = x := by
  obtain ⟨i,hi,hlen⟩ := Walk.mem_support_iff_exists_getVert.mp (hx x hux)
  refine ⟨i,?_,hlen,hi⟩
  by_contra! h
  have hi0 : i = 0 := by omega
  exact hux.ne (by simpa [hi0] using hi)

open scoped Classical in
lemma weighted_degree_le_prefix [Fintype V] (w : Sym2 V → ℝ)
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e) {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ a b (q : G.Walk a b), q.IsPath → walkWeight w q ≤ walkWeight w p)
    (j : ℕ) (hj : j ≤ p.length)
    (hneigh : ∀ x, G.Adj u x → ∃ i, 1 ≤ i ∧ i ≤ j ∧ p.getVert i = x) :
    (∑ x ∈ G.neighborFinset u, w s(u,x)) ≤ walkWeight w (p.take j) := by
  classical
  let I := (Finset.Icc 1 j).filter (fun i => G.Adj u (p.getVert i))
  have hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ j ∧ G.Adj u (p.getVert i) := by
    intro i hi
    simpa only [I, Finset.mem_filter, Finset.mem_Icc, and_assoc] using hi
  have hN : G.neighborFinset u = I.image p.getVert := by
    ext x
    constructor
    · intro hx
      have hx' := (G.mem_neighborFinset u x).mp hx
      obtain ⟨i,hi1,hij,hix⟩ := hneigh x hx'
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hi1,hij⟩,hix ▸ hx'⟩,hix⟩
    · intro hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact (G.mem_neighborFinset u _).mpr (hI i hi).2.2
  have hinj : Set.InjOn p.getVert (I : Set ℕ) := by
    intro i hi k hk heq
    exact hp.getVert_injOn ((hI i hi).2.1.trans hj) ((hI k hk).2.1.trans hj) heq
  rw [hN,Finset.sum_image hinj]
  calc
    _ ≤ ∑ i ∈ I, w s(p.getVert (i-1),p.getVert i) := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hi1,hij,hia⟩ := hI i hi
      have hr := hmax _ _ (rotatePath p i hia)
        (rotatePath_isPath hp i hia hi1 (hij.trans hj))
      have heq := walkWeight_rotate w p i hia hi1 (hij.trans hj)
      linarith
    _ ≤ ∑ i ∈ Finset.Icc 1 j, w s(p.getVert (i-1),p.getVert i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i hi _
      obtain ⟨hi1,hij⟩ := Finset.mem_Icc.mp hi
      have hadj := p.adj_getVert_succ (show i-1 < p.length by omega)
      rw [Nat.sub_add_cancel hi1] at hadj
      exact hw _ hadj
    _ = walkWeight w (p.take j) := (walkWeight_take_eq_sum w p j hj).symm

open scoped Classical in
/-- Edge and simple-cycle weight constraints force a vertex of small weighted degree. -/
lemma exists_weighted_degree_le [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (he : ∀ e ∈ G.edgeSet, w e ≤ t)
    (hc : ∀ a (p : G.Walk a a), p.IsCycle → walkWeight w p ≤ t) :
    ∃ a, (∑ x ∈ G.neighborFinset a, w s(a,x)) ≤ t := by
  classical
  obtain ⟨a,b,p,hp,hmax,hneigh⟩ := exists_maximum_weight_path G w hw
  let I := (Finset.Icc 1 p.length).filter (fun i => G.Adj a (p.getVert i))
  by_cases hI : I.Nonempty
  · let j := I.max' hI
    have hjmem : j ∈ I := Finset.max'_mem I hI
    obtain ⟨hj1,hja⟩ := Finset.mem_filter.mp hjmem
    have hj1' : 1 ≤ j := (Finset.mem_Icc.mp hj1).1
    have hjlen' : j ≤ p.length := (Finset.mem_Icc.mp hj1).2
    have hprefix := weighted_degree_le_prefix w hw hp hmax j hjlen' (by
      intro x hx
      obtain ⟨i,hi1,hilen,hix⟩ := neighbor_index hneigh hx
      have hiI : i ∈ I := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hi1,hilen⟩,hix ▸ hx⟩
      exact ⟨i,hi1,Finset.le_max' I i hiI,hix⟩)
    refine ⟨a,hprefix.trans ?_⟩
    by_cases hjtwo : 2 ≤ j
    · have hcycle := hc a (.cons hja (p.take j).reverse)
        (close_prefix_isCycle hp j hjlen' hjtwo hja)
      have hn := hw s(a,p.getVert j) hja
      simp only [walkWeight_cons,walkWeight_reverse] at hcycle
      linarith
    · have hjone : j = 1 := by omega
      have ht1 := walkWeight_take_succ w p 0 (by omega)
      rw [hjone]
      simp only [walkWeight_take_zero, Walk.getVert_zero, zero_add] at ht1
      rw [ht1]
      simpa only [hjone] using he s(a,p.getVert j) hja
  · have hn : G.neighborFinset a = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨i,hi1,hilen,hix⟩ := neighbor_index hneigh ((G.mem_neighborFinset a x).mp hx)
      apply hI
      refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi1,hilen⟩,?_⟩⟩
      simpa only [hix] using (G.mem_neighborFinset a x).mp hx
    exact ⟨a,by simpa [hn] using ht⟩

@[simp] lemma walkWeight_map {W : Type*} {H : SimpleGraph W}
    (f : G →g H) (w : Sym2 W → ℝ) (p : G.Walk u v) :
    walkWeight w (p.map f) = walkWeight (w ∘ Sym2.map f) p := by
  simp [walkWeight,List.map_map,Function.comp_def]

open scoped Classical in
lemma sum_incidence_eq_sum_neighbors [Fintype V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) (a : V) :
    (∑ e ∈ G.incidenceFinset a, w e) = ∑ x ∈ G.neighborFinset a, w s(a,x) := by
  classical
  have heq : G.incidenceFinset a = (G.neighborFinset a).image (fun x => s(a,x)) := by
    ext e
    induction e using Sym2.ind with | _ x y =>
      simp only [SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff,
        Finset.mem_image, SimpleGraph.mem_neighborFinset, Sym2.eq_iff]
      constructor
      · rintro ⟨h,hax | hay⟩
        · exact ⟨y,hax ▸ h,Or.inl ⟨hax,rfl⟩⟩
        · exact ⟨x,hay ▸ h.symm,Or.inr ⟨hay,rfl⟩⟩
      · rintro ⟨z,h,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
        · exact ⟨h,Or.inl rfl⟩
        · exact ⟨h.symm,Or.inr rfl⟩
  rw [heq,Finset.sum_image]
  intro x _ y _ he
  rcases Sym2.eq_iff.mp he with ⟨_,h⟩ | ⟨h1,h2⟩
  · exact h
  · exact h2.trans h1

open scoped Classical in
lemma sum_induce_compl_add_incidence [Fintype V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) (a : V) :
    (∑ e ∈ (G.induce ({a}ᶜ : Set V)).edgeFinset, w (Sym2.map Subtype.val e)) +
      (∑ x ∈ G.neighborFinset a, w s(a,x)) = ∑ e ∈ G.edgeFinset, w e := by
  classical
  have hmap : (G.induce ({a}ᶜ : Set V)).edgeFinset.map
      (Function.Embedding.subtype (· ∈ ({a}ᶜ : Set V))).sym2Map =
      G.edgeFinset \ G.incidenceFinset a := by
    rw [SimpleGraph.map_edgeFinset_induce]
    ext e
    induction e using Sym2.ind with | _ x y =>
      simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset, Finset.mk_mem_sym2_iff,
        Set.mem_toFinset, Set.mem_compl_iff, Set.mem_singleton_iff, Finset.mem_sdiff,
        SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff]
      tauto
  have hsum := congrArg (fun S : Finset (Sym2 V) => ∑ e ∈ S, w e) hmap
  dsimp only at hsum
  rw [Finset.sum_map] at hsum
  change (∑ e ∈ (G.induce ({a}ᶜ : Set V)).edgeFinset, w (Sym2.map Subtype.val e)) = _ at hsum
  rw [hsum,← sum_incidence_eq_sum_neighbors]
  exact Finset.sum_sdiff (G.incidenceFinset_subset a)

universe u

open scoped Classical in
/-- The nonnegative edge/cycle dual has total weight at most t(n-1). -/
lemma total_weight_le {V : Type u} [Fintype V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (he : ∀ e ∈ G.edgeSet, w e ≤ t)
    (hc : ∀ a (p : G.Walk a a), p.IsCycle → walkWeight w p ≤ t) :
    (∑ e ∈ G.edgeFinset, w e) ≤ t * (Fintype.card V - 1 : ℕ) := by
  classical
  have main : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] (H : SimpleGraph W)
      (w : Sym2 W → ℝ), Fintype.card W = n →
      (∀ e ∈ H.edgeSet, 0 ≤ w e) → (∀ e ∈ H.edgeSet, w e ≤ t) →
      (∀ a (p : H.Walk a a), p.IsCycle → walkWeight w p ≤ t) →
      (∑ e ∈ H.edgeFinset, w e) ≤ t * (n-1 : ℕ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ H w hn hw he hc
      by_cases hn2 : n ≤ 1
      · have hbot : H = ⊥ := by
          apply SimpleGraph.ext
          funext a b
          apply propext
          simp only [SimpleGraph.bot_adj, iff_false]
          intro hab
          have hcard : 2 ≤ Fintype.card W := Fintype.one_lt_card_iff.mpr ⟨a,b,hab.ne⟩
          omega
        have heq : H.edgeFinset = ∅ := by simp [hbot]
        rw [heq,Finset.sum_empty]
        positivity
      · haveI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
        obtain ⟨a,ha⟩ := exists_weighted_degree_le H w t ht hw he hc
        let S : Set W := {a}ᶜ
        let K := H.induce S
        let w' : Sym2 S → ℝ := w ∘ Sym2.map Subtype.val
        have hsub : ∀ e ∈ K.edgeSet, Sym2.map Subtype.val e ∈ H.edgeSet := by
          intro e he
          induction e using Sym2.ind with | _ x y => exact he
        have hcard : Fintype.card S = n-1 := by
          dsimp [S]
          rw [Fintype.card_compl_set,hn]
          simp only [Fintype.card_unique]
        have hsmall : Fintype.card S < n := by omega
        have hcK : ∀ x (p : K.Walk x x), p.IsCycle → walkWeight w' p ≤ t := by
          intro x p hp
          let f : K ↪g H := SimpleGraph.Embedding.induce S
          have h := hc (f x) (p.map f.toHom) (hp.map f.injective)
          simpa only [walkWeight_map] using h
        have hb := ih (Fintype.card S) hsmall K w' rfl
          (fun e he => hw _ (hsub e he)) (fun e heK => he _ (hsub e heK)) hcK
        have heq := sum_induce_compl_add_incidence H w a
        change (∑ e ∈ K.edgeFinset, w' e) + _ = _ at heq
        rw [hcard] at hb
        have hnat : (n-1-1 : ℕ)+1 = n-1 := by omega
        have hreal : ((n-1-1 : ℕ) : ℝ)+1 = ((n-1 : ℕ) : ℝ) := by exact_mod_cast hnat
        nlinarith
  exact main (Fintype.card V) G w rfl hw he hc

open scoped Classical in
/-- The same bound holds for signed weights, as needed for an exact-decomposition dual.
Negative edges are discarded before applying the nonnegative theorem. -/
lemma signed_total_weight_le {V : Type u} [Fintype V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (he : ∀ e ∈ G.edgeSet, w e ≤ t)
    (hc : ∀ a (p : G.Walk a a), p.IsCycle → walkWeight w p ≤ t) :
    (∑ e ∈ G.edgeFinset, w e) ≤ t * (Fintype.card V - 1 : ℕ) := by
  classical
  let K : SimpleGraph V := {
    Adj := fun a b => G.Adj a b ∧ 0 ≤ w s(a,b)
    symm := by intro a b h; simpa only [Sym2.eq_swap] using And.intro h.1.symm h.2
    loopless := by intro a h; exact G.loopless a h.1 }
  have hKG : K ≤ G := fun a b h => h.1
  have hwK : ∀ e ∈ K.edgeSet, 0 ≤ w e := by
    intro e he
    induction e using Sym2.ind with | _ a b => exact he.2
  have hcK : ∀ a (p : K.Walk a a), p.IsCycle → walkWeight w p ≤ t := by
    intro a p hp
    have h := hc a (p.mapLe hKG) (hp.mapLe hKG)
    simpa only [walkWeight,Walk.edges_mapLe_eq_edges] using h
  have hb := total_weight_le K w t ht hwK
    (fun e heK => he e (SimpleGraph.edgeSet_mono hKG heK)) hcK
  have hsubset := SimpleGraph.edgeFinset_mono hKG
  have hsum : (∑ e ∈ G.edgeFinset \ K.edgeFinset, w e) +
      (∑ e ∈ K.edgeFinset, w e) = ∑ e ∈ G.edgeFinset, w e := Finset.sum_sdiff hsubset
  have hnonpos : (∑ e ∈ G.edgeFinset \ K.edgeFinset, w e) ≤ 0 := by
    apply Finset.sum_nonpos
    intro e he
    obtain ⟨heG,heK⟩ := Finset.mem_sdiff.mp he
    induction e using Sym2.ind with | _ a b =>
      have hadj : G.Adj a b := (G.mem_edgeFinset).mp heG
      have hneg : ¬0 ≤ w s(a,b) := by
        intro h
        exact heK ((K.mem_edgeFinset).mpr ⟨hadj,h⟩)
      exact (lt_of_not_ge hneg).le
  have hb' : (∑ e ∈ K.edgeFinset, w e) ≤ t * (Fintype.card V - 1 : ℕ) := by
    convert hb using 1
    apply Finset.sum_congr
    · ext e; simp
    · intro e _; rfl
  rw [← hsum]
  exact (add_le_add hnonpos hb').trans_eq (zero_add _)

noncomputable def edgeVector {α : Type*} (S : Finset α) : α → ℝ :=
  fun e => if e ∈ S then 1 else 0

lemma edgeVector_eq_sum {α : Type*} [DecidableEq α] (S : Finset α) :
    edgeVector S = ∑ e ∈ S, Pi.single e (1 : ℝ) := by
  classical
  ext e
  simp [edgeVector,Finset.sum_apply,Pi.single_apply]

lemma functional_edgeVector {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (f : (α → ℝ) →L[ℝ] ℝ) :
    f (edgeVector S) = ∑ e ∈ S, f (Pi.single e 1) := by
  rw [edgeVector_eq_sum,map_sum]

open scoped Classical in
noncomputable def atoms [Fintype V] (G : SimpleGraph V) : Finset (Sym2 V → ℝ) :=
  insert 0 ((Finset.univ.filter fun H : G.Subgraph => IsCycleOrEdge H.coe).image
    fun H => edgeVector H.spanningCoe.edgeFinset)

open scoped Classical in
lemma zero_mem_atoms [Fintype V] (G : SimpleGraph V) : 0 ∈ atoms G :=
  Finset.mem_insert_self _ _

open scoped Classical in
lemma piece_mem_atoms [Fintype V] (H : G.Subgraph) (hH : IsCycleOrEdge H.coe) :
    edgeVector H.spanningCoe.edgeFinset ∈ atoms G := by
  classical
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨H,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hH⟩,rfl⟩

open scoped Classical in
lemma single_mem_atoms [Fintype V] (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    Pi.single e (1 : ℝ) ∈ atoms G := by
  classical
  obtain ⟨H,hH,hcH⟩ := exists_single_edge_subgraph G ⟨e,he⟩
  have heq : H.spanningCoe.edgeFinset = {e} := by
    ext x
    simpa only [SimpleGraph.mem_edgeFinset, Finset.mem_singleton] using Set.ext_iff.mp hH x
  have h := piece_mem_atoms H (Or.inr hcH)
  rw [heq,edgeVector_eq_sum,Finset.sum_singleton] at h
  exact h

open scoped Classical in
lemma cycle_mem_atoms [Fintype V] (G : SimpleGraph V)
    {a : V} {p : G.Walk a a} (hp : p.IsCycle) :
    edgeVector p.edges.toFinset ∈ atoms G := by
  classical
  have heq : p.toSubgraph.spanningCoe.edgeFinset = p.edges.toFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, List.mem_toFinset]
    exact p.mem_edges_toSubgraph
  rw [← heq]
  apply piece_mem_atoms
  exact Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular G hp)

open scoped Classical in
/-- A linear functional bounded on every cycle and edge atom is bounded on the full graph.
This is the exact fractional-decomposition dual inequality, without nonnegativity of the dual. -/
lemma functional_full_graph_le {V : Type u} [Fintype V] (G : SimpleGraph V)
    (f : (Sym2 V → ℝ) →L[ℝ] ℝ) (t : ℝ)
    (hf : ∀ x ∈ atoms G, f x ≤ t) :
    f (edgeVector G.edgeFinset) ≤ t * (Fintype.card V - 1 : ℕ) := by
  classical
  have ht : 0 ≤ t := by simpa using hf 0 (zero_mem_atoms G)
  let w : Sym2 V → ℝ := fun e => f (Pi.single e 1)
  have he : ∀ e ∈ G.edgeSet, w e ≤ t := fun e he => hf _ (single_mem_atoms G e he)
  have hc : ∀ a (p : G.Walk a a), p.IsCycle → walkWeight w p ≤ t := by
    intro a p hp
    have hb := hf _ (cycle_mem_atoms G hp)
    rw [functional_edgeVector,List.sum_toFinset _ hp.isTrail.edges_nodup] at hb
    exact hb
  rw [functional_edgeVector]
  exact signed_total_weight_le G w t ht he hc

open scoped Classical in
/-- Membership in the cycle-and-edge convex hull. This is fractional, not integral:
no pairwise edge-disjointness or integral rounding is asserted. -/
lemma normalized_graph_mem_convexHull {V : Type u} [Fintype V] (G : SimpleGraph V) :
    ((Fintype.card V - 1 : ℕ) : ℝ)⁻¹ • edgeVector G.edgeFinset ∈
      convexHull ℝ (atoms G : Set (Sym2 V → ℝ)) := by
  classical
  let C : ℝ := (Fintype.card V - 1 : ℕ)
  by_cases hC : C = 0
  · have hzero : ((Fintype.card V - 1 : ℕ) : ℝ)⁻¹ • edgeVector G.edgeFinset = 0 := by
      change C⁻¹ • _ = 0
      simp [hC]
    rw [hzero]
    exact subset_convexHull ℝ _ (zero_mem_atoms G)
  · have hCpos : 0 < C := lt_of_le_of_ne (by positivity) (Ne.symm hC)
    by_contra hnot
    obtain ⟨f,t,hft,hfx⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) (atoms G).finite_toSet.isClosed_convexHull hnot
    have hf : ∀ x ∈ atoms G, f x ≤ t := by
      intro x hx
      exact (hft x (subset_convexHull ℝ _ hx)).le
    have hb := functional_full_graph_le G f t hf
    change f (edgeVector G.edgeFinset) ≤ t * C at hb
    change t < f (C⁻¹ • edgeVector G.edgeFinset) at hfx
    rw [map_smul,smul_eq_mul] at hfx
    have hmul := (mul_lt_mul_of_pos_left hfx hCpos)
    rw [← mul_assoc,mul_inv_cancel₀ hC,one_mul] at hmul
    linarith

/-- A genuine fractional exact decomposition of every finite graph, of weight at most n-1.
The coefficients are real, not integers; this does not imply an edge-disjoint partition. -/
lemma exists_fractional_decomposition {V : Type u} [Fintype V] (G : SimpleGraph V) :
    ∃ (I : Type) (_ : Fintype I) (H : I → G.Subgraph) (c : I → ℝ),
      (∀ i, IsCycleOrEdge (H i).coe) ∧ (∀ i, 0 ≤ c i) ∧
      (∀ e, (∑ i, if e ∈ (H i).edgeSet then c i else 0) =
        if e ∈ G.edgeSet then 1 else 0) ∧
      (∑ i, c i) ≤ (Fintype.card V - 1 : ℕ) := by
  classical
  by_cases hG : G = ⊥
  · refine ⟨Fin 0,inferInstance,Fin.elim0,Fin.elim0,?_,?_,?_,?_⟩
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro e
      simp [hG]
    · simp
  · obtain ⟨e,he⟩ := SimpleGraph.edgeSet_nonempty.mpr hG
    obtain ⟨H₀,hH₀,hcH₀⟩ := exists_single_edge_subgraph G ⟨e,he⟩
    obtain ⟨a,b,hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hG
    have hn : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨a,b,hab.ne⟩
    let C : ℝ := (Fintype.card V - 1 : ℕ)
    have hCpos : 0 < C := by dsimp [C]; exact_mod_cast (show 0 < Fintype.card V - 1 by omega)
    have hC : C ≠ 0 := ne_of_gt hCpos
    obtain ⟨I,_,d,z,hd,hd1,hz,hcomb⟩ :=
      mem_convexHull_iff_exists_fintype.mp (normalized_graph_mem_convexHull G)
    have hchoose : ∀ i : I, ∃ H : G.Subgraph, IsCycleOrEdge H.coe ∧
        (z i ≠ 0 → edgeVector H.spanningCoe.edgeFinset = z i) := by
      intro i
      by_cases hi : z i = 0
      · exact ⟨H₀,Or.inr hcH₀,fun h => (h hi).elim⟩
      · have hzi : z i ∈ (Finset.univ.filter fun H : G.Subgraph => IsCycleOrEdge H.coe).image
            (fun H => edgeVector H.spanningCoe.edgeFinset) := by
          exact (Finset.mem_insert.mp (hz i)).resolve_left hi
        obtain ⟨H,hH,heq⟩ := Finset.mem_image.mp hzi
        exact ⟨H,(Finset.mem_filter.mp hH).2,fun _ => heq⟩
    choose H hH hHz using hchoose
    let c : I → ℝ := fun i => if z i = 0 then 0 else C * d i
    have hc : ∀ i, 0 ≤ c i := by
      intro i
      dsimp [c]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg hCpos.le (hd i)
    have hcle : ∀ i, c i ≤ C * d i := by
      intro i
      dsimp [c]
      split_ifs
      · exact mul_nonneg hCpos.le (hd i)
      · exact le_rfl
    have hterm : ∀ i, c i • edgeVector (H i).spanningCoe.edgeFinset =
        C • (d i • z i) := by
      intro i
      by_cases hi : z i = 0
      · simp [c,hi]
      · rw [hHz i hi]
        simp only [c,if_neg hi,mul_smul]
    have hvec : (∑ i, c i • edgeVector (H i).spanningCoe.edgeFinset) =
        edgeVector G.edgeFinset := by
      simp_rw [hterm]
      rw [← Finset.smul_sum,hcomb]
      change C • (C⁻¹ • edgeVector G.edgeFinset) = _
      rw [smul_smul,mul_inv_cancel₀ hC,one_smul]
    refine ⟨I,inferInstance,H,c,hH,hc,?_,?_⟩
    · intro e
      have h := congrFun hvec e
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,edgeVector,
        SimpleGraph.mem_edgeFinset, mul_ite, mul_one, mul_zero] at h
      convert h using 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
    · calc
        (∑ i, c i) ≤ ∑ i, C * d i := Finset.sum_le_sum (fun i _ => hcle i)
        _ = C := by rw [← Finset.mul_sum,hd1,mul_one]

#print axioms normalized_graph_mem_convexHull
#print axioms exists_fractional_decomposition
end Erdos184Work.Weighted



/-
An obstruction to pure multiplicative rounding, not to Erdős 184.
Three Hamilton cycles double-cover arbitrarily large cubic graphs, so their
fractional cost is at most 3/2, while parity forces linearly many single edges.
-/

open SimpleGraph
open scoped BigOperators Classical

namespace Erdos184Work.FractionalGap

variable {p : ℕ} [Fact p.Prime]

private lemma p_pos : 0 < p := (Fact.out : p.Prime).pos

local instance : NeZero p := ⟨(Nat.ne_of_gt p_pos)⟩

abbrev V (p : ℕ) := ZMod p ⊕ ZMod p

def pairGraph (a b : ZMod p) : SimpleGraph (V p) where
  Adj
    | .inl x, .inr y => y = x + a ∨ y = x + b
    | .inr y, .inl x => y = x + a ∨ y = x + b
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp
  loopless := by intro x; cases x <;> simp

lemma pairGraph_step (a b x : ZMod p) :
    (pairGraph a b).Reachable (.inl x) (.inl (x + (a-b))) := by
  have h₁ : (pairGraph a b).Adj (.inl x) (.inr (x+a)) := Or.inl rfl
  have h₂ : (pairGraph a b).Adj (.inr (x+a)) (.inl (x+(a-b))) := by
    apply Or.inr
    ring
  exact h₁.reachable.trans h₂.reachable

lemma pairGraph_connected (a b : ZMod p) (hab : a ≠ b) : (pairGraph a b).Connected := by
  have hd : a-b ≠ 0 := sub_ne_zero.mpr hab
  have hNat : ∀ k : ℕ, (pairGraph a b).Reachable (.inl 0) (.inl ((k : ZMod p) * (a-b))) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using
        ih.trans (pairGraph_step a b ((k : ZMod p) * (a-b)))
  have hleft : ∀ x : ZMod p, (pairGraph a b).Reachable (.inl 0) (.inl x) := by
    intro x
    have h := hNat (x / (a-b)).val
    simpa only [ZMod.natCast_zmod_val,div_mul_cancel₀ _ hd] using h
  have hroot : ∀ x : V p, (pairGraph a b).Reachable (.inl 0) x := by
    intro x
    cases x with
    | inl x => exact hleft x
    | inr y =>
      apply (hleft (y-a)).trans
      apply SimpleGraph.Adj.reachable
      exact Or.inl (by ring)
  exact ⟨fun x y => (hroot x).symm.trans (hroot y)⟩

lemma pairGraph_regular (a b : ZMod p) (hab : a ≠ b) :
    (pairGraph a b).IsRegularOfDegree 2 := by
  classical
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  cases v with
  | inl x =>
    have hn : (pairGraph a b).neighborFinset (.inl x) = {Sum.inr (x+a),Sum.inr (x+b)} := by
      ext v
      cases v <;> simp [SimpleGraph.mem_neighborFinset,pairGraph]
    rw [hn,Finset.card_pair]
    simpa using hab
  | inr y =>
    have hn : (pairGraph a b).neighborFinset (.inr y) = {Sum.inl (y-a),Sum.inl (y-b)} := by
      ext v
      cases v with
      | inr x => simp [SimpleGraph.mem_neighborFinset,pairGraph]
      | inl x =>
        simp only [SimpleGraph.mem_neighborFinset,pairGraph,Finset.mem_insert,
          Finset.mem_singleton,Sum.inl.injEq]
        constructor
        · rintro (h | h)
          · left; rw [h]; ring
          · right; rw [h]; ring
        · rintro (rfl | rfl)
          · left; ring
          · right; ring
    rw [hn,Finset.card_pair]
    simpa using hab

def shift (i : Fin 3) : ZMod p := i.val

lemma shift_injective (hp : 3 ≤ p) : Function.Injective (shift (p := p)) := by
  intro i j h
  apply Fin.ext
  have hval := congrArg ZMod.val h
  simpa only [shift,ZMod.val_natCast,Nat.mod_eq_of_lt (show i.val < p by omega),
    Nat.mod_eq_of_lt (show j.val < p by omega)] using hval

def graph (p : ℕ) [Fact p.Prime] : SimpleGraph (V p) where
  Adj
    | .inl x, .inr y => ∃ i : Fin 3, y = x + shift i
    | .inr y, .inl x => ∃ i : Fin 3, y = x + shift i
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp
  loopless := by intro x; cases x <;> simp

lemma graph_regular (hp : 3 ≤ p) : (graph p).IsRegularOfDegree 3 := by
  classical
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  cases v with
  | inl x =>
    have hn : (graph p).neighborFinset (.inl x) =
        Finset.univ.image (fun i : Fin 3 => Sum.inr (x + shift i)) := by
      ext v
      cases v <;> simp [SimpleGraph.mem_neighborFinset,graph,eq_comm]
    have hinj : Function.Injective (fun i : Fin 3 => (Sum.inr (x + shift i) : V p)) := by
      intro i j h
      exact shift_injective hp (add_left_cancel (Sum.inr.inj h))
    rw [hn,Finset.card_image_of_injective _ hinj]
    simp
  | inr y =>
    have hn : (graph p).neighborFinset (.inr y) =
        Finset.univ.image (fun i : Fin 3 => Sum.inl (y - shift i)) := by
      ext v
      cases v with
      | inr x => simp [SimpleGraph.mem_neighborFinset,graph]
      | inl x =>
        simp only [SimpleGraph.mem_neighborFinset,graph,Finset.mem_image,
          Finset.mem_univ,true_and,Sum.inl.injEq]
        constructor
        · rintro ⟨i,h⟩
          exact ⟨i,by rw [h]; ring⟩
        · rintro ⟨i,rfl⟩
          exact ⟨i,by ring⟩
    have hinj : Function.Injective (fun i : Fin 3 => (Sum.inl (y - shift i) : V p)) := by
      intro i j h
      exact shift_injective hp (sub_right_inj.mp (Sum.inl.inj h))
    rw [hn,Finset.card_image_of_injective _ hinj]
    simp

def pairs : Fin 3 → Fin 3 × Fin 3 := ![(0,1),(1,2),(0,2)]

lemma pairs_distinct (i : Fin 3) : (pairs i).1 ≠ (pairs i).2 := by
  fin_cases i <;> decide

lemma pairGraph_le (i : Fin 3) :
    pairGraph (shift (p := p) (pairs i).1) (shift (pairs i).2) ≤ graph p := by
  intro x y h
  cases x <;> cases y <;> simp only [pairGraph,graph] at h ⊢
  · rcases h with h | h
    · exact ⟨(pairs i).1,h⟩
    · exact ⟨(pairs i).2,h⟩
  · rcases h with h | h
    · exact ⟨(pairs i).1,h⟩
    · exact ⟨(pairs i).2,h⟩

noncomputable def piece (i : Fin 3) : (graph p).Subgraph :=
  SimpleGraph.toSubgraph
    (pairGraph (shift (p := p) (pairs i).1) (shift (pairs i).2)) (pairGraph_le i)

lemma piece_cycle (hp : 3 ≤ p) (i : Fin 3) :
    (piece (p := p) i).coe.Connected ∧ (piece (p := p) i).coe.IsRegularOfDegree 2 := by
  have hne : shift (p := p) (pairs i).1 ≠ shift (pairs i).2 :=
    (shift_injective hp).ne (pairs_distinct i)
  exact coe_toSubgraph_cycle _ (pairGraph_connected _ _ hne) (pairGraph_regular _ _ hne)

lemma fractional_cover_cross (hp : 3 ≤ p) (x y : ZMod p) :
    (∑ i : Fin 3, if s(Sum.inl x,Sum.inr y) ∈ (piece (p := p) i).edgeSet
      then (1/2 : ℝ) else 0) =
      if s(Sum.inl x,Sum.inr y) ∈ (graph p).edgeSet then 1 else 0 := by
  classical
  by_cases h0 : y = x + shift (p := p) 0
  · simp [(shift_injective hp).eq_iff,Fin.sum_univ_three,Fin.exists_fin_succ,piece,
      SimpleGraph.toSubgraph,SimpleGraph.Subgraph.mem_edgeSet,pairGraph,graph,pairs,h0]
    norm_num
  · by_cases h1 : y = x + shift (p := p) 1
    · simp [(shift_injective hp).eq_iff,Fin.sum_univ_three,Fin.exists_fin_succ,piece,
        SimpleGraph.toSubgraph,SimpleGraph.Subgraph.mem_edgeSet,pairGraph,graph,pairs,h1]
      norm_num
    · by_cases h2 : y = x + shift (p := p) 2
      · simp [(shift_injective hp).eq_iff,Fin.sum_univ_three,Fin.exists_fin_succ,piece,
          SimpleGraph.toSubgraph,SimpleGraph.Subgraph.mem_edgeSet,pairGraph,graph,pairs,h2]
        norm_num
      · simp [Fin.sum_univ_three,Fin.exists_fin_succ,piece,SimpleGraph.toSubgraph,
          SimpleGraph.Subgraph.mem_edgeSet,pairGraph,graph,pairs,h0,h1,h2]

lemma fractional_cover (hp : 3 ≤ p) (e : Sym2 (V p)) :
    (∑ i : Fin 3, if e ∈ (piece (p := p) i).edgeSet then (1/2 : ℝ) else 0) =
      if e ∈ (graph p).edgeSet then 1 else 0 := by
  classical
  induction e using Sym2.ind with | _ x y =>
    cases x with
    | inl x =>
      cases y with
      | inl y => simp [piece,SimpleGraph.toSubgraph,SimpleGraph.Subgraph.mem_edgeSet,pairGraph,graph]
      | inr y => exact fractional_cover_cross hp x y
    | inr x =>
      cases y with
      | inr y => simp [piece,SimpleGraph.toSubgraph,SimpleGraph.Subgraph.mem_edgeSet,pairGraph,graph]
      | inl y =>
        rw [show s(Sum.inr x,Sum.inl y) = s(Sum.inl y,Sum.inr x) from Sym2.eq_swap]
        exact fractional_cover_cross hp y x

/-- Every odd vertex must meet a single-edge piece. -/
lemma odd_vertex_lower_bound {W : Type*} [Fintype W] (G : SimpleGraph W)
    (hodd : ∀ v, Odd (G.degree v)) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D) :
    Fintype.card W ≤ 2 * D.card := by
  classical
  let E := Critical.edgePieces D
  let F := subfamilyGraph E
  have hpos : ∀ v, 1 ≤ F.degree v := by
    intro v
    have hpar := Critical.edgePieces_degree_parity D hD hdec v
    have hn : ¬Even (G.degree v) := Nat.not_even_iff_odd.mpr (hodd v)
    have hnF := mt hpar.mp hn
    change ¬Even (F.degree v) at hnF
    rw [Nat.even_iff] at hnF
    omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpos v)
  have hhand := F.sum_degrees_eq_twice_card_edges
  have hcard := Critical.edgePieces_graph_card D hdec
  have hsub : E.card ≤ D.card := Finset.card_le_card (Finset.filter_subset _ _)
  change F.edgeFinset.card = E.card at hcard
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at hsum
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
    SimpleGraph.edgeFinset_card] at hsum hhand hcard ⊢
  omega

lemma integral_lower_bound (hp : 3 ≤ p) (D : Finset (graph p).Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition (graph p) D) :
    p ≤ D.card := by
  have hb := odd_vertex_lower_bound (graph p) (by
    intro v
    rw [graph_regular hp v]
    decide) D hD hdec
  have hc : Fintype.card (V p) = 2*p := by simp [V,ZMod.card,two_mul]
  simp only [← Nat.card_eq_fintype_card] at hc hb
  omega

lemma number_lower_bound (hp : 3 ≤ p) : p ≤ Critical.number (graph p) := by
  obtain ⟨D,hD,hdec,hcD⟩ := Critical.exists_minimum (graph p)
  rw [← hcD]
  exact integral_lower_bound hp D hD hdec

/-- The obstruction family itself still has a linear integral bound. -/
lemma number_upper_bound (hp : 3 ≤ p) : Critical.number (graph p) ≤ 3*p := by
  have hs := (graph p).sum_degrees_eq_twice_card_edges
  have hsum : (∑ v : V p, (graph p).degree v) = 6*p := by
    calc
      _ = ∑ _v : V p, 3 := Finset.sum_congr rfl (fun v _ => graph_regular hp v)
      _ = 6*p := by simp [V,ZMod.card]; omega
  have hb := Critical.number_le_edges (graph p)
  rw [hsum] at hs
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hs hb
  omega

/-- Arbitrarily large integral costs occur even when three simple cycles of coefficient
one half cover every edge exactly once. This rules out any pure multiplicative rounding
bound for the unrestricted fractional problem, but not an additive O(n) bound. -/
lemma unbounded_integral_cost_at_fixed_fractional_cost (B : ℝ) :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W) (H : Fin 3 → G.Subgraph),
      (∀ i, (H i).coe.Connected ∧ (H i).coe.IsRegularOfDegree 2) ∧
      (∀ e, (∑ i : Fin 3, if e ∈ (H i).edgeSet then (1/2 : ℝ) else 0) =
        if e ∈ G.edgeSet then 1 else 0) ∧
      (∀ D : Finset G.Subgraph, (∀ K ∈ D, IsCycleOrEdge K.coe) → IsDecomposition G D →
        B * (∑ _i : Fin 3, (1/2 : ℝ)) < (D.card : ℝ)) := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_gt (B * (3/2 : ℝ))
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (max 3 N)
  letI : Fact q.Prime := ⟨hprime⟩
  have hq3 : 3 ≤ q := (Nat.le_max_left _ _).trans hq
  refine ⟨V q,inferInstance,graph q,piece,?_,fractional_cover hq3,?_⟩
  · intro i
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using piece_cycle hq3 i
  · intro D hD hdec
    have hDq := integral_lower_bound hq3 D hD hdec
    have hNq : N ≤ q := (Nat.le_max_right _ _).trans hq
    have hreal : (N : ℝ) ≤ D.card := by exact_mod_cast hNq.trans hDq
    have hsum : (∑ _i : Fin 3, (1/2 : ℝ)) = 3/2 := by norm_num
    rw [hsum]
    exact hN.trans_le hreal

#print axioms fractional_cover
#print axioms integral_lower_bound
#print axioms unbounded_integral_cost_at_fixed_fractional_cost
end Erdos184Work.FractionalGap



/- A finite even obstruction for the fractional rounding investigation. -/

open SimpleGraph
open scoped BigOperators

namespace Erdos184Work.EvenFractionalBase
open ThreeCycleObstruction

def h0 : exampleGraph.Walk 0 0 :=
  .cons (show exampleGraph.Adj 0 1 by decide) (.cons (show exampleGraph.Adj 1 5 by decide) (.cons (show exampleGraph.Adj 5 11 by decide) (.cons (show exampleGraph.Adj 11 9 by decide) (.cons (show exampleGraph.Adj 9 4 by decide) (.cons (show exampleGraph.Adj 4 2 by decide) (.cons (show exampleGraph.Adj 2 12 by decide) (.cons (show exampleGraph.Adj 12 3 by decide) (.cons (show exampleGraph.Adj 3 7 by decide) (.cons (show exampleGraph.Adj 7 13 by decide) (.cons (show exampleGraph.Adj 13 6 by decide) (.cons (show exampleGraph.Adj 6 10 by decide) (.cons (show exampleGraph.Adj 10 14 by decide) (.cons (show exampleGraph.Adj 14 8 by decide) (.cons (show exampleGraph.Adj 8 0 by decide) (.nil)))))))))))))))

lemma h0_isCycle : h0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def h1 : exampleGraph.Walk 0 0 :=
  .cons (show exampleGraph.Adj 0 7 by decide) (.cons (show exampleGraph.Adj 7 9 by decide) (.cons (show exampleGraph.Adj 9 11 by decide) (.cons (show exampleGraph.Adj 11 4 by decide) (.cons (show exampleGraph.Adj 4 14 by decide) (.cons (show exampleGraph.Adj 14 2 by decide) (.cons (show exampleGraph.Adj 2 3 by decide) (.cons (show exampleGraph.Adj 3 13 by decide) (.cons (show exampleGraph.Adj 13 10 by decide) (.cons (show exampleGraph.Adj 10 6 by decide) (.cons (show exampleGraph.Adj 6 5 by decide) (.cons (show exampleGraph.Adj 5 12 by decide) (.cons (show exampleGraph.Adj 12 1 by decide) (.cons (show exampleGraph.Adj 1 8 by decide) (.cons (show exampleGraph.Adj 8 0 by decide) (.nil)))))))))))))))

lemma h1_isCycle : h1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def h2 : exampleGraph.Walk 0 0 :=
  .cons (show exampleGraph.Adj 0 1 by decide) (.cons (show exampleGraph.Adj 1 5 by decide) (.cons (show exampleGraph.Adj 5 11 by decide) (.cons (show exampleGraph.Adj 11 6 by decide) (.cons (show exampleGraph.Adj 6 13 by decide) (.cons (show exampleGraph.Adj 13 10 by decide) (.cons (show exampleGraph.Adj 10 8 by decide) (.cons (show exampleGraph.Adj 8 14 by decide) (.cons (show exampleGraph.Adj 14 4 by decide) (.cons (show exampleGraph.Adj 4 2 by decide) (.cons (show exampleGraph.Adj 2 12 by decide) (.cons (show exampleGraph.Adj 12 3 by decide) (.cons (show exampleGraph.Adj 3 7 by decide) (.cons (show exampleGraph.Adj 7 9 by decide) (.cons (show exampleGraph.Adj 9 0 by decide) (.nil)))))))))))))))

lemma h2_isCycle : h2.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def h3 : exampleGraph.Walk 0 0 :=
  .cons (show exampleGraph.Adj 0 7 by decide) (.cons (show exampleGraph.Adj 7 13 by decide) (.cons (show exampleGraph.Adj 13 3 by decide) (.cons (show exampleGraph.Adj 3 2 by decide) (.cons (show exampleGraph.Adj 2 14 by decide) (.cons (show exampleGraph.Adj 14 10 by decide) (.cons (show exampleGraph.Adj 10 8 by decide) (.cons (show exampleGraph.Adj 8 1 by decide) (.cons (show exampleGraph.Adj 1 12 by decide) (.cons (show exampleGraph.Adj 12 5 by decide) (.cons (show exampleGraph.Adj 5 6 by decide) (.cons (show exampleGraph.Adj 6 11 by decide) (.cons (show exampleGraph.Adj 11 4 by decide) (.cons (show exampleGraph.Adj 4 9 by decide) (.cons (show exampleGraph.Adj 9 0 by decide) (.nil)))))))))))))))

lemma h3_isCycle : h3.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def hamilton : Fin 4 → exampleGraph.Walk 0 0 := ![h0,h1,h2,h3]

lemma hamilton_isCycle (i : Fin 4) : (hamilton i).IsCycle := by
  fin_cases i
  · exact h0_isCycle
  · exact h1_isCycle
  · exact h2_isCycle
  · exact h3_isCycle

lemma hamilton_spanning : ∀ (i : Fin 4) (v : Fin 15), v ∈ (hamilton i).support := by
  decide

lemma cover_twice : ∀ u v : Fin 15,
    (Finset.univ.filter fun i : Fin 4 => s(u,v) ∈ (hamilton i).edges).card =
      if exampleGraph.Adj u v then 2 else 0 := by
  decide

open scoped Classical in
lemma fractional_cover (e : Sym2 (Fin 15)) :
    (∑ i : Fin 4, if e ∈ (hamilton i).toSubgraph.edgeSet then (1/2 : ℝ) else 0) =
      if e ∈ exampleGraph.edgeSet then 1 else 0 := by
  classical
  simp only [Walk.mem_edges_toSubgraph,Finset.sum_ite,Finset.sum_const_zero,add_zero,
    Finset.sum_const]
  induction e using Sym2.ind with | _ u v =>
    rw [cover_twice]
    by_cases h : exampleGraph.Adj u v <;> simp [h]

open scoped Classical in
lemma four_hamilton_fractional_cover :
    (∀ v : Fin 15, Even (exampleGraph.degree v)) ∧
    (∀ i : Fin 4, ((hamilton i).toSubgraph.coe.Connected ∧
      (hamilton i).toSubgraph.coe.IsRegularOfDegree 2)) ∧
    (∀ i : Fin 4, (hamilton i).toSubgraph.IsSpanning) ∧
    (∀ e, (∑ i : Fin 4, if e ∈ (hamilton i).toSubgraph.edgeSet then (1/2 : ℝ) else 0) =
      if e ∈ exampleGraph.edgeSet then 1 else 0) ∧
    (∑ _i : Fin 4, (1/2 : ℝ)) = 2 := by
  classical
  refine ⟨?_,?_,?_,fractional_cover,?_⟩
  · intro v
    rw [exampleGraph_regular v]
    decide
  · intro i
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular exampleGraph (hamilton_isCycle i)
  · intro i v
    exact (hamilton i).mem_verts_toSubgraph.mpr (hamilton_spanning i v)
  · norm_num

open scoped Classical in
set_option maxHeartbeats 1000000 in
lemma number_lower_bound : 3 ≤ Critical.number exampleGraph := by
  classical
  have hd := StarCore.number_degree_bound exampleGraph (0 : Fin 15)
  have h4 := exampleGraph_regular (0 : Fin 15)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd h4
  by_contra! hn
  obtain ⟨D,hD,hdec,hcD⟩ := Critical.exists_minimum exampleGraph
  have hcycles := minimal_even_decomposition_cycles (G := exampleGraph) (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using four_hamilton_fractional_cover.1 v) D hD hdec (by
    intro A hA hdecA
    rw [hcD]
    exact Critical.number_le A hA hdecA)
  have hc2 : D.card = 2 := by omega
  obtain ⟨H,K,hne,rfl⟩ := Finset.card_eq_two.mp hc2
  apply no_two_cycle_subgraphs H K
    (by simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hcycles H (by simp))
    (by simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hcycles K (by simp))
  · exact hdec.1 (by simp) (by simp) hne
  · simpa only [Finset.set_biUnion_insert,Finset.set_biUnion_singleton] using hdec.2

open scoped Classical in
lemma number_upper_bound : Critical.number exampleGraph ≤ 3 := by
  classical
  let P : Fin 3 → exampleGraph.Subgraph := ![c0.toSubgraph,c1.toSubgraph,c2.toSubgraph]
  let E : Fin 3 → Finset (Sym2 (Fin 15)) := ![c0.edges.toFinset,c1.edges.toFinset,c2.edges.toFinset]
  have hP : ∀ i : Fin 3, IsCycleOrEdge (P i).coe := by
    intro i
    fin_cases i
    · exact Or.inl (by simpa only [SimpleGraph.IsRegularOfDegree,
        ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
        cycle_coe_regular exampleGraph c0_cycle)
    · exact Or.inl (by simpa only [SimpleGraph.IsRegularOfDegree,
        ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
        cycle_coe_regular exampleGraph c1_cycle)
    · exact Or.inl (by simpa only [SimpleGraph.IsRegularOfDegree,
        ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
        cycle_coe_regular exampleGraph c2_cycle)
  have hdec : IsDecomposition exampleGraph (Finset.univ.image P) := by
    apply Compression.finite_family_decomposition P E
    · intro i
      fin_cases i <;> ext e <;> simp [P,E]
    · intro i j hne
      fin_cases i <;> fin_cases j <;> first | exact (hne rfl).elim | decide
    · intro x y
      simpa [Fin.exists_fin_succ,E] using cycles_cover x y
  have hbound := Critical.number_le (Finset.univ.image P) (by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact hP i) hdec
  have hcard : (Finset.univ.image P).card ≤ 3 :=
    (Finset.card_image_le).trans (by simp)
  omega

lemma number_eq_three : Critical.number exampleGraph = 3 :=
  Nat.le_antisymm number_upper_bound number_lower_bound

lemma close_through_fresh_vertex_isCycle {W : Type*} {G : SimpleGraph W}
    {z a b : W} (p : G.Walk a b) (hp : p.IsPath) (hz : z ∉ p.support)
    (hab : a ≠ b) (hza : G.Adj z a) (hbz : G.Adj b z) :
    (Walk.cons hza (p.concat hbz)).IsCycle := by
  rw [Walk.cons_isCycle_iff]
  refine ⟨hp.concat hz hbz,?_⟩
  rw [Walk.edges_concat,List.concat_eq_append,List.mem_append,List.mem_singleton]
  rintro (he | he)
  · exact hz (p.fst_mem_support_of_mem_edges he)
  · rcases Sym2.eq_iff.mp he with ⟨hzb,haz⟩ | ⟨_,hab'⟩
    · exact hza.ne haz.symm
    · exact hab hab'

open scoped Classical in
/-- Two paths avoiding vertex zero cannot cover the remaining block while their
four disjoint endpoint spokes complete all edges of the base graph. Such paths
would close to the forbidden two-cycle decomposition. -/
lemma no_two_path_completion {a b c d : Fin 15}
    (p : exampleGraph.Walk a b) (q : exampleGraph.Walk c d)
    (hp : p.IsPath) (hq : q.IsPath) (hp0 : 0 ∉ p.support) (hq0 : 0 ∉ q.support)
    (hab : a ≠ b) (hcd : c ≠ d)
    (h0a : exampleGraph.Adj 0 a) (hb0 : exampleGraph.Adj b 0)
    (h0c : exampleGraph.Adj 0 c) (hd0 : exampleGraph.Adj d 0)
    (hdis : p.edges.Disjoint q.edges)
    (hspokes : Disjoint ({s(0,a),s(b,0)} : Set (Sym2 (Fin 15))) {s(0,c),s(d,0)})
    (hcover : ∀ e : Sym2 (Fin 15), e ∈ exampleGraph.edgeSet ↔
      e ∈ p.edges ∨ e ∈ q.edges ∨ e = s(0,a) ∨ e = s(b,0) ∨ e = s(0,c) ∨ e = s(d,0)) :
    False := by
  classical
  let P := Walk.cons h0a (p.concat hb0)
  let Q := Walk.cons h0c (q.concat hd0)
  have hP : P.IsCycle := close_through_fresh_vertex_isCycle p hp hp0 hab h0a hb0
  have hQ : Q.IsCycle := close_through_fresh_vertex_isCycle q hq hq0 hcd h0c hd0
  have hpe : ∀ e, e ∈ P.edges ↔ e ∈ p.edges ∨ e ∈ ({s(0,a),s(b,0)} : Set _) := by
    intro e
    simp only [P,Walk.edges_cons,Walk.edges_concat,List.mem_cons,List.concat_eq_append,List.mem_append,
      Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  have hqe : ∀ e, e ∈ Q.edges ↔ e ∈ q.edges ∨ e ∈ ({s(0,c),s(d,0)} : Set _) := by
    intro e
    simp only [Q,Walk.edges_cons,Walk.edges_concat,List.mem_cons,List.concat_eq_append,List.mem_append,
      Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  have hP0 : ∀ e ∈ ({s(0,a),s(b,0)} : Set (Sym2 (Fin 15))), (0 : Fin 15) ∈ e := by
    intro e he
    rcases he with rfl | rfl <;> simp
  have hQ0 : ∀ e ∈ ({s(0,c),s(d,0)} : Set (Sym2 (Fin 15))), (0 : Fin 15) ∈ e := by
    intro e he
    rcases he with rfl | rfl <;> simp
  have hdisPQ : Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heP heQ
    rcases (hpe e).mp (P.mem_edges_toSubgraph.mp heP) with heP | heP
    · rcases (hqe e).mp (Q.mem_edges_toSubgraph.mp heQ) with heQ | heQ
      · exact hdis heP heQ
      · exact hp0 (Walk.mem_support_of_mem_edges heP (hQ0 e heQ))
    · rcases (hqe e).mp (Q.mem_edges_toSubgraph.mp heQ) with heQ | heQ
      · exact hq0 (Walk.mem_support_of_mem_edges heQ (hP0 e heP))
      · exact Set.disjoint_left.mp hspokes heP heQ
  apply no_two_cycle_subgraphs P.toSubgraph Q.toSubgraph
    (by simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular exampleGraph hP)
    (by simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular exampleGraph hQ)
    hdisPQ
  ext e
  simp only [Set.mem_union,Walk.mem_edges_toSubgraph,hpe,hqe,Set.mem_insert_iff,
    Set.mem_singleton_iff]
  rw [hcover]
  tauto

#print axioms four_hamilton_fractional_cover
#print axioms number_eq_three
#print axioms no_two_path_completion
end Erdos184Work.EvenFractionalBase



/-! Local even partitions and a block restriction obstruction.
These auxiliary results do not settle the linear decomposition conjecture. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.BlockRestriction
open Critical StarCore

universe u v

/-- Subadditivity over a finite edge partition into even spanning graphs. -/
lemma number_le_sum_of_even_partition {I : Type*} {W : Type u}
    [Fintype I] [Fintype W] (B : SimpleGraph W) (R : I → SimpleGraph W)
    (hR : ∀ i, R i ≤ B) (heven : ∀ i w, Even ((R i).degree w))
    (hdis : Pairwise (fun i j => Disjoint (R i).edgeSet (R j).edgeSet))
    (hcover : (⋃ i, (R i).edgeSet) = B.edgeSet) :
    number B ≤ ∑ i, number (R i) := by
  classical
  have hex : ∀ i, ∃ D : Finset (R i).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (R i) D ∧ D.card = number (R i) := by
    intro i
    obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum (R i)
    refine ⟨D,?_,hdec,hcard⟩
    exact minimal_even_decomposition_cycles (heven i) D hD hdec (by
      intro E hE hdecE
      rw [hcard]
      exact number_le E hE hdecE)
  choose D hD hdec hc using hex
  have hlift : ∀ i, ∃ A : Finset B.Subgraph,
      (∀ H ∈ A, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (A : Set B.Subgraph) (fun H => H.edgeSet) ∧
      (⋃ H ∈ A, H.edgeSet) = (R i).edgeSet ∧ A.card ≤ number (R i) := by
    intro i
    obtain ⟨A,hA,hp,he,hcard⟩ := lift_decomposition_property
      (fun {_} [_] H => H.Connected ∧ H.IsRegularOfDegree 2)
      (hR i) (D i) (by
        intro H hH
        simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hD i H hH) (hdec i)
    refine ⟨A,?_,hp,he,hcard.trans_eq (hc i)⟩
    intro H hH
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hA H hH
  choose A hA hp he hcard using hlift
  obtain ⟨F,hF,hdecF,hcF⟩ := DoublePath.combine_finite_cycle_families
    A (fun i => (R i).edgeSet) hA hp he hdis hcover
  exact (number_le F (fun H hH => Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hF H hH)) hdecF).trans
    (hcF.trans (Finset.sum_le_sum (fun i _ => hcard i)))

lemma degree_eq_sum_of_partition {I W : Type*} [Fintype I] [Fintype W]
    (B : SimpleGraph W) (R : I → SimpleGraph W)
    (hdis : Pairwise (fun i j => Disjoint (R i).edgeSet (R j).edgeSet))
    (hcover : (⋃ i, (R i).edgeSet) = B.edgeSet) (w : W) :
    B.degree w = ∑ i, (R i).degree w := by
  classical
  have hn : B.neighborFinset w = Finset.univ.biUnion (fun i => (R i).neighborFinset w) := by
    ext x
    have hh := Set.ext_iff.mp hcover s(w,x)
    simpa only [SimpleGraph.mem_neighborFinset,Finset.mem_biUnion,Finset.mem_univ,
      true_and,Set.mem_iUnion,SimpleGraph.mem_edgeSet] using hh.symm
  have hd : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i => (R i).neighborFinset w) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    exact Set.disjoint_left.mp (hdis hij)
      (show s(w,x) ∈ (R i).edgeSet from ((R i).mem_neighborFinset w x).mp hi)
      (show s(w,x) ∈ (R j).edgeSet from ((R j).mem_neighborFinset w x).mp hj)
  rw [SimpleGraph.degree,hn,Finset.card_biUnion hd]
  rfl

/-- If every part has the same feedback vertex, the whole graph admits an
optimal decomposition in which every cycle passes through that vertex. -/
lemma number_eq_half_degree_of_feedback_partition {I : Type*} {W : Type u}
    [Fintype I] [Fintype W] (B : SimpleGraph W) (R : I → SimpleGraph W)
    (hR : ∀ i, R i ≤ B) (heven : ∀ i w, Even ((R i).degree w))
    (hdis : Pairwise (fun i j => Disjoint (R i).edgeSet (R j).edgeSet))
    (hcover : (⋃ i, (R i).edgeSet) = B.edgeSet) (z : W)
    (hforest : ∀ i, ((R i).induce {z}ᶜ).IsAcyclic) :
    2 * number B = B.degree z := by
  have hn := number_le_sum_of_even_partition B R hR heven hdis hcover
  have hdeg := degree_eq_sum_of_partition B R hdis hcover z
  have heq : ∀ i, 2 * number (R i) = (R i).degree z := by
    intro i
    exact twice_number_eq_degree_of_cycle_hits (heven i) z
      ((cycle_hits_iff_induce_acyclic z).mpr (hforest i))
  have hs : 2 * (∑ i, number (R i)) = B.degree z := by
    rw [Finset.mul_sum]
    simpa only [heq] using hdeg.symm
  have hlo := number_degree_bound B z
  omega

/-- The 15-vertex obstruction cannot be edge-partitioned into even graphs
whose only cycles go through vertex zero. -/
lemma base_partition_has_cycle_avoiding_zero {I : Type*} [Fintype I]
    (R : I → SimpleGraph (Fin 15))
    (hR : ∀ i, R i ≤ ThreeCycleObstruction.exampleGraph)
    (heven : ∀ i w, Even ((R i).degree w))
    (hdis : Pairwise (fun i j => Disjoint (R i).edgeSet (R j).edgeSet))
    (hcover : (⋃ i, (R i).edgeSet) = ThreeCycleObstruction.exampleGraph.edgeSet) :
    ∃ i u, ∃ p : (R i).Walk u u, p.IsCycle ∧ 0 ∉ p.support := by
  classical
  by_contra! h
  have hf : ∀ i, ((R i).induce {(0 : Fin 15)}ᶜ).IsAcyclic := by
    intro i
    exact (cycle_hits_iff_induce_acyclic 0).mp (h i)
  have hh := number_eq_half_degree_of_feedback_partition
    ThreeCycleObstruction.exampleGraph R hR heven hdis hcover 0 hf
  have hd : ThreeCycleObstruction.exampleGraph.degree 0 = 4 := by decide
  rw [EvenFractionalBase.number_eq_three] at hh
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh hd
  omega

/-- Restricting a cycle piece to a vertex set which omits one of its vertices
leaves a forest. This is stated via an injective map to ease block applications. -/
lemma cycle_comap_acyclic_of_missing_vertex {V W : Type*} [Fintype V]
    {G : SimpleGraph V} (H : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (f : W ↪ V) (hproper : ∃ v ∈ H.verts, v ∉ Set.range f) :
    (H.spanningCoe.comap f).IsAcyclic := by
  classical
  obtain ⟨v,hv,hout⟩ := hproper
  have hd : H.spanningCoe.degree v = 2 := by
    rw [regular_two_spanning_degree H hH.2,if_pos hv]
  obtain ⟨w,hw⟩ : ∃ w, H.Adj v w := by
    have hp : 0 < H.spanningCoe.degree v := by omega
    rw [SimpleGraph.degree_pos_iff_exists_adj] at hp
    exact hp
  have ha := SingleAddition.delete_cycle_edge_acyclic H hH.1 hH.2 ⟨s(v,w),hw⟩
  apply ha.comap (f := ⟨f,?_⟩) f.injective
  intro a b hab
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨hab,?_⟩
  intro he
  have heq : s(f a,f b) = s(v,w) := Set.mem_singleton_iff.mp he
  rcases Sym2.eq_iff.mp heq with ⟨ha,_⟩ | ⟨_,hb⟩
  · exact hout ⟨a,ha⟩
  · exact hout ⟨b,hb⟩

#print axioms base_partition_has_cycle_avoiding_zero
#print axioms cycle_comap_acyclic_of_missing_vertex

/-- A block is obtained by deleting `none` from `B` and attaching each of its
former neighbors to a single vertex outside the block. -/
structure BlockModel {V W : Type*} (G : SimpleGraph V) (B : SimpleGraph (Option W)) where
  emb : W ↪ V
  outer : W → V
  outside : ∀ w, outer w ∉ Set.range emb
  internal : ∀ u v, G.Adj (emb u) (emb v) ↔ B.Adj (some u) (some v)
  boundary : ∀ u x, x ∉ Set.range emb →
    (G.Adj (emb u) x ↔ x = outer u ∧ B.Adj (some u) none)

namespace BlockModel
variable {V W : Type*} {G : SimpleGraph V} {B : SimpleGraph (Option W)}
    (M : BlockModel G B)

def neighborMap (u : W) : Option W → V
  | none => M.outer u
  | some v => M.emb v

lemma neighborMap_injective (u : W) : Function.Injective (M.neighborMap u) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => exact (M.outside u ⟨b,hab.symm⟩).elim
  | some a =>
    cases b with
    | none => exact (M.outside u ⟨a,hab⟩).elim
    | some b => exact congrArg some (M.emb.injective hab)

def trace (H : G.Subgraph) : SimpleGraph (Option W) where
  Adj
    | none, none => False
    | some u, none => H.Adj (M.emb u) (M.outer u)
    | none, some u => H.Adj (M.emb u) (M.outer u)
    | some u, some v => H.Adj (M.emb u) (M.emb v)
  symm := by
    intro x y h
    cases x <;> cases y <;> first | exact h | exact H.symm h
  loopless := by
    intro x
    cases x
    · exact not_false
    · exact H.loopless _

lemma trace_le (H : G.Subgraph) : M.trace H ≤ B := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => exact h.elim
    | some y => exact ((M.boundary y _ (M.outside y)).mp (H.adj_sub h)).2.symm
  | some x =>
    cases y with
    | none => exact ((M.boundary x _ (M.outside x)).mp (H.adj_sub h)).2
    | some y => exact (M.internal x y).mp (H.adj_sub h)

lemma trace_adj_some (H : G.Subgraph) (u : W) (x : Option W) :
    (M.trace H).Adj (some u) x ↔ H.Adj (M.emb u) (M.neighborMap u x) := by
  cases x <;> rfl

lemma neighbor_lift (H : G.Subgraph) (u : W) {x : V} (hx : H.Adj (M.emb u) x) :
    ∃ t : Option W, M.neighborMap u t = x ∧ (M.trace H).Adj (some u) t := by
  by_cases hxin : x ∈ Set.range M.emb
  · obtain ⟨w,rfl⟩ := hxin
    exact ⟨some w,rfl,hx⟩
  · have h := ((M.boundary u x hxin).mp (H.adj_sub hx)).1
    exact ⟨none,h.symm,by simpa only [h] using hx⟩

lemma trace_degree_some [Fintype V] [Fintype W] (H : G.Subgraph) (u : W) :
    (M.trace H).degree (some u) = H.spanningCoe.degree (M.emb u) := by
  classical
  let f : (M.trace H).neighborSet (some u) → H.spanningCoe.neighborSet (M.emb u) :=
    fun x => ⟨M.neighborMap u x.val,(M.trace_adj_some H u x.val).mp x.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Subtype.ext (M.neighborMap_injective u (congrArg Subtype.val h))
    · intro x
      obtain ⟨t,ht,ha⟩ := M.neighbor_lift H u x.property
      exact ⟨⟨t,ha⟩,Subtype.ext ht⟩
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.ofBijective f hf)

lemma trace_even [Fintype V] [Fintype W] (H : G.Subgraph)
    (heven : ∀ v, Even (H.spanningCoe.degree v)) : ∀ w, Even ((M.trace H).degree w) := by
  classical
  have hs : ∀ w : W, Even ((M.trace H).degree (some w)) := by
    intro w
    rw [M.trace_degree_some]
    exact heven _
  intro w
  cases w with
  | some w => exact hs w
  | none =>
    have hsum := (M.trace H).sum_degrees_eq_twice_card_edges
    rw [Fintype.sum_option] at hsum
    have he : Even (∑ w : W, (M.trace H).degree (some w)) :=
      Finset.even_sum _ (fun w _ => hs w)
    rw [Nat.even_iff] at he ⊢
    omega

lemma trace_partition [Fintype V] (D : Finset G.Subgraph) (hdec : IsDecomposition G D) :
    Pairwise (fun H K : D => Disjoint (M.trace H.val).edgeSet (M.trace K.val).edgeSet) ∧
      (⋃ H : D, (M.trace H.val).edgeSet) = B.edgeSet := by
  constructor
  · intro H K hne
    apply Set.disjoint_left.mpr
    intro e heH heK
    have hdis := hdec.1 H.property K.property (fun h => hne (Subtype.ext h))
    induction e using Sym2.ind with | h x y =>
    cases x with
    | none =>
      cases y with
      | none => exact heH.elim
      | some y =>
        exact Set.disjoint_left.mp hdis
          (show s(M.emb y,M.outer y) ∈ H.val.edgeSet from heH) heK
    | some x =>
      cases y with
      | none =>
        exact Set.disjoint_left.mp hdis
          (show s(M.emb x,M.outer x) ∈ H.val.edgeSet from heH) heK
      | some y =>
        exact Set.disjoint_left.mp hdis
          (show s(M.emb x,M.emb y) ∈ H.val.edgeSet from heH) heK
  · ext e
    induction e using Sym2.ind with | h x y =>
    constructor
    · intro he
      obtain ⟨H,hH⟩ := Set.mem_iUnion.mp he
      exact M.trace_le H.val hH
    · intro hB
      have hfind : ∀ {a b : V}, G.Adj a b → ∃ H : D, H.val.Adj a b := by
        intro a b hab
        have hmem : s(a,b) ∈ ⋃ H ∈ D, H.edgeSet := by rw [hdec.2]; exact hab
        obtain ⟨H,hH⟩ := Set.mem_iUnion.mp hmem
        obtain ⟨hHD,heH⟩ := Set.mem_iUnion.mp hH
        exact ⟨⟨H,hHD⟩,heH⟩
      cases x with
      | none =>
        cases y with
        | none => exact (B.loopless _ hB).elim
        | some y =>
          have hG := (M.boundary y _ (M.outside y)).mpr ⟨rfl,hB.symm⟩
          obtain ⟨H,hH⟩ := hfind hG
          exact Set.mem_iUnion.mpr ⟨H,hH⟩
      | some x =>
        cases y with
        | none =>
          have hG := (M.boundary x _ (M.outside x)).mpr ⟨rfl,hB⟩
          obtain ⟨H,hH⟩ := hfind hG
          exact Set.mem_iUnion.mpr ⟨H,hH⟩
        | some y =>
          obtain ⟨H,hH⟩ := hfind ((M.internal x y).mpr hB)
          exact Set.mem_iUnion.mpr ⟨H,hH⟩

lemma trace_forest_of_not_internal [Fintype V] (H : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hproper : ∃ v ∈ H.verts, v ∉ Set.range M.emb) :
    ((M.trace H).induce {(none : Option W)}ᶜ).IsAcyclic := by
  have ha := cycle_comap_acyclic_of_missing_vertex H hH M.emb hproper
  have hex : ∀ x : ({(none : Option W)}ᶜ : Set (Option W)), ∃ w : W, x.val = some w := by
    rintro ⟨x,hx⟩
    cases x with
    | none => exact (hx (Set.mem_singleton _)).elim
    | some w => exact ⟨w,rfl⟩
  choose f hf using hex
  have hi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    rw [hf x,hf y,hxy]
  apply ha.comap (f := ⟨f,?_⟩) hi
  intro x y hxy
  change (M.trace H).Adj x.val y.val at hxy
  rw [hf x,hf y] at hxy
  exact hxy

/-- If the completed block needs more cycles than half the degree of its
completion vertex, every cycle partition of the ambient graph has a cycle
wholly inside the block. -/
lemma exists_internal_cycle [Fintype V] [Fintype W]
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D)
    (hgap : B.degree none < 2 * number B) :
    ∃ H ∈ D, H.verts ⊆ Set.range M.emb := by
  classical
  by_contra! hno
  have hproper : ∀ H : D, ∃ v ∈ H.val.verts, v ∉ Set.range M.emb := by
    intro H
    exact Set.not_subset.mp (hno H.val H.property)
  have hforest : ∀ H : D, ((M.trace H.val).induce {(none : Option W)}ᶜ).IsAcyclic := by
    intro H
    exact M.trace_forest_of_not_internal H.val (hD H.val H.property) (hproper H)
  have heven : ∀ H : D, ∀ w, Even ((M.trace H.val).degree w) := by
    intro H
    apply M.trace_even H.val
    exact regular_two_spanning_even H.val (hD H.val H.property).2
  obtain ⟨hdis,hcover⟩ := M.trace_partition D hdec
  have hh := number_eq_half_degree_of_feedback_partition B (fun H : D => M.trace H.val)
    (fun H => M.trace_le H.val) heven hdis hcover none hforest
  omega

end BlockModel

/-- Disjoint obstructing blocks force distinct wholly internal cycle pieces.
This is an integral lower bound, not a superlinear example: the blocks themselves
occupy disjoint vertex sets. -/
lemma card_blocks_le_number {I V W : Type*} [Fintype I] [Fintype V] [Fintype W]
    (G : SimpleGraph V) (B : I → SimpleGraph (Option W))
    (M : ∀ i, BlockModel G (B i))
    (heven : ∀ v, Even (G.degree v))
    (hgap : ∀ i, (B i).degree none < 2 * number (B i))
    (hdis : Pairwise (fun i j => Disjoint (Set.range (M i).emb) (Set.range (M j).emb))) :
    Fintype.card I ≤ number G := by
  classical
  obtain ⟨D,hD,hdec,hc⟩ := exists_minimum G
  have hcycles := minimal_even_decomposition_cycles heven D hD hdec (by
    intro E hE hdecE
    rw [hc]
    exact number_le E hE hdecE)
  have hex : ∀ i, ∃ H : D, H.val.verts ⊆ Set.range (M i).emb := by
    intro i
    obtain ⟨H,hHD,hH⟩ := (M i).exists_internal_cycle D hcycles hdec (hgap i)
    exact ⟨⟨H,hHD⟩,hH⟩
  choose H hH using hex
  have hi : Function.Injective H := by
    intro i j hij
    by_contra hne
    obtain ⟨v⟩ := (hcycles (H i).val (H i).property).1.nonempty
    have hv := hH i v.property
    have hw : v.val ∈ Set.range (M j).emb := by
      apply hH j
      rw [← hij]
      exact v.property
    exact Set.disjoint_left.mp (hdis hne) hv hw
  have hcard := Fintype.card_le_of_injective H hi
  simpa only [Fintype.card_coe,hc] using hcard

#print axioms BlockModel.exists_internal_cycle
#print axioms card_blocks_le_number

lemma number_le_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : number H ≤ number G := by
  classical
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum G
  have hp : ∀ K ∈ D.image (SimpleGraph.Subgraph.map e.toHom), IsCycleOrEdge K.coe := by
    intro K hK
    obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hK
    exact SparseCuts.piece_property_map_injective e.toHom e.injective L (hD L hL)
  exact (number_le _ hp (map_isDecomposition_iso e D hdec)).trans
    (Finset.card_image_le.trans_eq hcard)

lemma number_eq_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : number G = number H :=
  Nat.le_antisymm (number_le_of_iso e.symm) (number_le_of_iso e)

/-- The deleted-vertex block has fourteen vertices. -/
abbrev BaseVertex := {v : Fin 15 // v ≠ 0}

noncomputable def completedBase : SimpleGraph (Option BaseVertex) :=
  ThreeCycleObstruction.exampleGraph.comap (Equiv.optionSubtypeNe (0 : Fin 15))

noncomputable def completedBaseIso : completedBase ≃g ThreeCycleObstruction.exampleGraph :=
  SimpleGraph.Iso.comap (Equiv.optionSubtypeNe (0 : Fin 15)) _

lemma completedBase_number : number completedBase = 3 :=
  (number_eq_of_iso completedBaseIso).trans EvenFractionalBase.number_eq_three

lemma completedBase_degree_none : completedBase.degree none = 4 := by
  classical
  have h := completedBaseIso.degree_eq (none : Option BaseVertex)
  have h4 : ThreeCycleObstruction.exampleGraph.degree 0 = 4 := by decide
  simpa only [completedBaseIso,SimpleGraph.Iso.comap_apply,Equiv.optionSubtypeNe_none,
    ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h.symm.trans h4

lemma completedBase_gap : completedBase.degree none < 2 * number completedBase := by
  rw [completedBase_number,completedBase_degree_none]
  decide

lemma card_base_blocks_le_number {I V : Type*} [Fintype I] [Fintype V]
    (G : SimpleGraph V) (M : I → BlockModel G completedBase)
    (heven : ∀ v, Even (G.degree v))
    (hdis : Pairwise (fun i j => Disjoint (Set.range (M i).emb) (Set.range (M j).emb))) :
    Fintype.card I ≤ number G :=
  card_blocks_le_number G (fun _ => completedBase) M heven (fun _ => completedBase_gap) hdis

#print axioms completedBase_gap
#print axioms card_base_blocks_le_number
end Erdos184Work.BlockRestriction



/-! Cyclic concatenation of equal-length paths. Auxiliary development only. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CyclicPath

lemma cycleGraph_connected_of_pos {n : ℕ} (hn : 0 < n) : (cycleGraph n).Connected := by
  cases n with
  | zero => omega
  | succ n => exact cycleGraph_connected

lemma cycleGraph_regular_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    (cycleGraph n).IsRegularOfDegree 2 := by
  match n with
  | 0 | 1 | 2 => omega
  | n + 3 => exact fun _ => cycleGraph_degree_three_le

lemma cycleGraph_adj_succ {n : ℕ} [NeZero n] (hn : 2 ≤ n) (u v : Fin n) :
    (cycleGraph n).Adj u v ↔ u + 1 = v ∨ v + 1 = u := by
  rcases n with _ | (_ | n)
  · omega
  · omega
  · rw [cycleGraph_adj]
    constructor
    · rintro (h | h)
      · exact Or.inr (by simpa [add_comm] using (sub_eq_iff_eq_add.mp h).symm)
      · exact Or.inl (by simpa [add_comm] using (sub_eq_iff_eq_add.mp h).symm)
    · rintro (h | h)
      · exact Or.inr (sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h.symm))
      · exact Or.inl (sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h.symm))

def pairedCycle (m : ℕ) : SimpleGraph (Fin m × Fin 28) :=
  (cycleGraph (m * 28)).comap finProdFinEquiv

noncomputable def pairedCycleIso (m : ℕ) : pairedCycle m ≃g cycleGraph (m * 28) :=
  SimpleGraph.Iso.comap finProdFinEquiv _

lemma pairedCycle_connected {m : ℕ} (hm : 0 < m) : (pairedCycle m).Connected :=
  (pairedCycleIso m).connected_iff.mpr (cycleGraph_connected_of_pos (by omega))

lemma pairedCycle_regular {m : ℕ} (hm : 0 < m) : (pairedCycle m).IsRegularOfDegree 2 := by
  intro x
  have h := (pairedCycleIso m).degree_eq x
  have hr := cycleGraph_regular_of_three_le (by omega : 3 ≤ m * 28) (pairedCycleIso m x)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h hr ⊢
  omega

def step {m : ℕ} [NeZero m] (x : Fin m × Fin 28) : Fin m × Fin 28 :=
  if x.2.val < 27 then (x.1,x.2 + 1) else (x.1 + 1,0)

lemma product_position {m : ℕ} (x : Fin m × Fin 28) :
    (finProdFinEquiv x).val = x.2.val + 28 * x.1.val := rfl

lemma position_step {m : ℕ} [NeZero m] (x : Fin m × Fin 28) :
    finProdFinEquiv (step x) = (finProdFinEquiv x : Fin (m * 28)) + 1 := by
  apply Fin.ext
  have hm := NeZero.pos m
  have hi := x.1.isLt
  have hj := x.2.isLt
  have he : 1 < m * 28 := by omega
  by_cases h : x.2.val < 27
  · simp only [step,if_pos h,product_position,Fin.val_add,Fin.val_one,
      Fin.val_one',Nat.add_mod_mod]
    rw [Nat.mod_eq_of_lt (by omega : x.2.val + 1 < 28)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have hj27 : x.2.val = 27 := by omega
    simp only [step,if_neg h]
    simp only [product_position,Fin.val_add,Fin.val_one',
      Fin.val_zero,zero_add,Nat.add_mod_mod,hj27]
    by_cases hi' : x.1.val + 1 < m
    · rw [Nat.mod_eq_of_lt hi',Nat.mod_eq_of_lt (by omega)]
      omega
    · have hi' : x.1.val + 1 = m := by omega
      rw [hi',Nat.mod_self,mul_zero]
      have heq : 27 + 28 * x.1.val + 1 = m * 28 := by omega
      rw [heq,Nat.mod_self]

lemma pairedCycle_adj {m : ℕ} [NeZero m] (x y : Fin m × Fin 28) :
    (pairedCycle m).Adj x y ↔ step x = y ∨ step y = x := by
  change (cycleGraph (m * 28)).Adj (finProdFinEquiv x) (finProdFinEquiv y) ↔ _
  rw [cycleGraph_adj_succ (by have := NeZero.pos m; omega),
    ← position_step,← position_step]
  exact or_congr finProdFinEquiv.injective.eq_iff finProdFinEquiv.injective.eq_iff

#print axioms pairedCycle_connected
#print axioms pairedCycle_regular
#print axioms pairedCycle_adj
end Erdos184Work.CyclicPath



/-! An even graph family with bounded fractional cycle cost but unbounded integral
cost. This is an obstruction to multiplicative rounding, not to Erdős 184. -/
open SimpleGraph
open scoped BigOperators
namespace Erdos184Work.EvenRing
open CyclicPath BlockRestriction

def order0 : Equiv.Perm (Fin 28) where
  toFun := ![0,4,10,8,3,1,11,2,6,12,5,9,13,7,14,18,24,22,17,15,25,16,20,26,19,23,27,21]
  invFun := ![0,5,7,4,1,10,8,13,3,11,2,6,9,12,14,19,21,18,15,24,22,27,17,25,16,20,23,26]
  left_inv := by decide
  right_inv := by decide

def order1 : Equiv.Perm (Fin 28) where
  toFun := ![6,8,10,3,13,1,2,12,9,5,4,11,0,7,14,18,24,19,26,23,21,27,17,15,25,16,20,22]
  invFun := ![12,5,6,3,10,9,0,13,1,8,2,11,7,4,14,23,25,22,15,17,26,20,27,19,16,24,18,21]
  left_inv := by decide
  right_inv := by decide

def order2 : Equiv.Perm (Fin 28) where
  toFun := ![0,4,10,5,12,9,7,13,3,1,11,2,6,8,20,22,24,17,27,15,16,26,23,19,18,25,14,21]
  invFun := ![0,9,11,8,1,3,12,6,13,5,2,10,4,7,26,19,20,17,24,23,14,27,15,22,16,25,21,18]
  left_inv := by decide
  right_inv := by decide

def order3 : Equiv.Perm (Fin 28) where
  toFun := ![6,12,2,1,13,9,7,0,11,4,5,10,3,8,20,26,16,15,27,23,21,14,25,18,19,24,17,22]
  invFun := ![7,3,2,12,9,10,0,6,13,5,11,8,1,4,21,17,16,26,23,24,14,20,27,19,25,22,15,18]
  left_inv := by decide
  right_inv := by decide

def order : Fin 4 → Equiv.Perm (Fin 28) := ![order0,order1,order2,order3]

def localVertex (x : Fin 28) : Fin 15 := ⟨x.val % 14 + 1,by omega⟩

def inner (x y : Fin 28) : Prop :=
  (x.val / 14 = y.val / 14 ∧ ThreeCycleObstruction.exampleGraph.Adj (localVertex x) (localVertex y)) ∨
  (x = 7 ∧ y = 14) ∨ (x = 14 ∧ y = 7) ∨ (x = 8 ∧ y = 20) ∨ (x = 20 ∧ y = 8)

def forward (x y : Fin 28) : Prop := (x = 21 ∧ y = 0) ∨ (x = 22 ∧ y = 6)

instance (x y : Fin 28) : Decidable (inner x y) := inferInstanceAs (Decidable (_ ∨ _))
instance (x y : Fin 28) : Decidable (forward x y) := inferInstanceAs (Decidable (_ ∨ _))

lemma inner_symm : Symmetric inner := by
  change ∀ x y, inner x y → inner y x
  decide
lemma inner_irrefl : Irreflexive inner := by
  change ∀ x, ¬ inner x x
  decide
lemma forward_irrefl : Irreflexive forward := by
  change ∀ x, ¬ forward x x
  decide

/-- The ring consists of two fourteen-vertex blocks per superblock. -/
def graph (m : ℕ) [NeZero m] : SimpleGraph (Fin m × Fin 28) where
  Adj x y := (x.1 = y.1 ∧ inner x.2 y.2) ∨
    (x.1 + 1 = y.1 ∧ forward x.2 y.2) ∨ (y.1 + 1 = x.1 ∧ forward y.2 x.2)
  symm := by
    intro x y h
    rcases h with ⟨h,hxy⟩ | h | h
    · exact Or.inl ⟨h.symm,inner_symm hxy⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := by
    intro x h
    rcases h with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
    · exact inner_irrefl _ h
    · exact forward_irrefl _ h
    · exact forward_irrefl _ h

instance (m : ℕ) [NeZero m] : DecidableRel (graph m).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

def cycle (m : ℕ) (i : Fin 4) : SimpleGraph (Fin m × Fin 28) :=
  (pairedCycle m).comap (Equiv.prodCongr (Equiv.refl (Fin m)) (order i).symm)

instance (m : ℕ) (i : Fin 4) : DecidableRel (cycle m i).Adj :=
  inferInstanceAs (DecidableRel (((cycleGraph (m * 28)).comap finProdFinEquiv).comap _).Adj)

noncomputable def cycleIso (m : ℕ) (i : Fin 4) : cycle m i ≃g pairedCycle m :=
  SimpleGraph.Iso.comap (Equiv.prodCongr (Equiv.refl (Fin m)) (order i).symm) _

lemma cycle_property {m : ℕ} (hm : 0 < m) (i : Fin 4) :
    (cycle m i).Connected ∧ (cycle m i).IsRegularOfDegree 2 := by
  refine ⟨(cycleIso m i).connected_iff.mpr (pairedCycle_connected hm),?_⟩
  intro x
  have h := (cycleIso m i).degree_eq x
  have hr := pairedCycle_regular hm (cycleIso m i x)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h hr ⊢
  omega

lemma step_eq {m : ℕ} [NeZero m] (a b : Fin m) (x y : Fin 28) :
    step (a,x) = (b,y) ↔ (a = b ∧ x.val + 1 = y.val) ∨
      (a + 1 = b ∧ x = 27 ∧ y = 0) := by
  by_cases hx : x.val < 27
  · have h27 : x ≠ 27 := by intro h; subst x; norm_num at hx
    have hval : (x + 1).val = x.val + 1 := Fin.val_add_one_of_lt' (by omega)
    simp only [step,if_pos hx,Prod.mk.injEq,h27,false_and,and_false,or_false]
    simp only [Fin.ext_iff,hval]
  · have hx27 : x = 27 := Fin.ext (by omega)
    have hbad : 28 ≠ y.val := by omega
    simp [step,hx27,hbad,eq_comm]

def cycleInner (i : Fin 4) (x y : Fin 28) : Prop :=
  ((order i).symm x).val + 1 = ((order i).symm y).val ∨
  ((order i).symm y).val + 1 = ((order i).symm x).val

def cycleForward (i : Fin 4) (x y : Fin 28) : Prop :=
  (order i).symm x = 27 ∧ (order i).symm y = 0

instance (i : Fin 4) (x y : Fin 28) : Decidable (cycleInner i x y) :=
  inferInstanceAs (Decidable (_ ∨ _))
instance (i : Fin 4) (x y : Fin 28) : Decidable (cycleForward i x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

lemma cycle_adj {m : ℕ} [NeZero m] (i : Fin 4) (a b : Fin m) (x y : Fin 28) :
    (cycle m i).Adj (a,x) (b,y) ↔
      (a = b ∧ cycleInner i x y) ∨
      (a + 1 = b ∧ cycleForward i x y) ∨
      (b + 1 = a ∧ cycleForward i y x) := by
  change (pairedCycle m).Adj (a,(order i).symm x) (b,(order i).symm y) ↔ _
  rw [pairedCycle_adj,step_eq,step_eq]
  simp only [cycleInner,cycleForward]
  constructor
  · rintro (h | h)
    · rcases h with h | h
      · exact Or.inl ⟨h.1,Or.inl h.2⟩
      · exact Or.inr (Or.inl h)
    · rcases h with h | h
      · exact Or.inl ⟨h.1.symm,Or.inr h.2⟩
      · exact Or.inr (Or.inr h)
  · rintro (⟨h,h' | h'⟩ | h | h)
    · exact Or.inl (Or.inl ⟨h,h'⟩)
    · exact Or.inr (Or.inl ⟨h.symm,h'⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma local_twice_cover : ∀ (x y : Fin 28) (a b c : Bool),
    (Finset.univ.filter fun i : Fin 4 =>
      (a = true ∧ cycleInner i x y) ∨ (b = true ∧ cycleForward i x y) ∨
      (c = true ∧ cycleForward i y x)).card =
    if (a = true ∧ inner x y) ∨ (b = true ∧ forward x y) ∨
      (c = true ∧ forward y x) then 2 else 0 := by
  decide
lemma twice_cover {m : ℕ} [NeZero m] (x y : Fin m × Fin 28) :
    (Finset.univ.filter fun i : Fin 4 => (cycle m i).Adj x y).card =
      if (graph m).Adj x y then 2 else 0 := by
  obtain ⟨a,x⟩ := x
  obtain ⟨b,y⟩ := y
  have h := local_twice_cover x y (decide (a = b)) (decide (a + 1 = b)) (decide (b + 1 = a))
  simpa only [cycle_adj,graph,decide_eq_true_eq] using h

lemma cycleInner_le : ∀ (i : Fin 4) (x y : Fin 28), cycleInner i x y → inner x y := by decide
lemma cycleForward_le : ∀ (i : Fin 4) (x y : Fin 28), cycleForward i x y → forward x y := by decide

lemma cycle_le {m : ℕ} [NeZero m] (i : Fin 4) : cycle m i ≤ graph m := by
  rintro ⟨a,x⟩ ⟨b,y⟩ h
  rcases (cycle_adj i a b x y).mp h with ⟨h,h'⟩ | ⟨h,h'⟩ | ⟨h,h'⟩
  · exact Or.inl ⟨h,cycleInner_le i x y h'⟩
  · exact Or.inr (Or.inl ⟨h,cycleForward_le i x y h'⟩)
  · exact Or.inr (Or.inr ⟨h,cycleForward_le i y x h'⟩)

noncomputable def piece (m : ℕ) [NeZero m] (i : Fin 4) : (graph m).Subgraph :=
  SimpleGraph.toSubgraph (cycle m i) (cycle_le i)

lemma piece_cycle {m : ℕ} [NeZero m] (i : Fin 4) :
    (piece m i).coe.Connected ∧ (piece m i).coe.IsRegularOfDegree 2 := by
  have h := cycle_property (NeZero.pos m) i
  simpa only [piece,SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using coe_toSubgraph_cycle (cycle_le (m := m) i) h.1 (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using h.2)

lemma piece_spanning {m : ℕ} [NeZero m] (i : Fin 4) : (piece m i).IsSpanning :=
  SimpleGraph.toSubgraph.isSpanning _ _

open scoped Classical in
lemma fractional_cover {m : ℕ} [NeZero m] (e : Sym2 (Fin m × Fin 28)) :
    (∑ i : Fin 4, if e ∈ (piece m i).edgeSet then (1/2 : ℝ) else 0) =
      if e ∈ (graph m).edgeSet then 1 else 0 := by
  classical
  induction e using Sym2.ind with | _ x y =>
  simp only [piece,SimpleGraph.toSubgraph,SimpleGraph.Subgraph.mem_edgeSet,SimpleGraph.mem_edgeSet,
    Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul]
  rw [twice_cover]
  split_ifs <;> norm_num

#print axioms fractional_cover
def slot (p : Fin 2) (w : BaseVertex) : Fin 28 :=
  ⟨14 * p.val + (w.val.val - 1),by have := w.val.isLt; have := w.property; have := p.isLt; omega⟩

def slotEquiv : Fin 2 × BaseVertex ≃ Fin 28 where
  toFun x := slot x.1 x.2
  invFun x := (⟨x.val / 14,by omega⟩,⟨⟨x.val % 14 + 1,by omega⟩,by intro h; have := congrArg Fin.val h; simp at this⟩)
  left_inv := by
    rintro ⟨p,w⟩
    apply Prod.ext
    · apply Fin.ext
      simp only [slot]
      have := p.isLt
      have := w.val.isLt
      have := w.property
      omega
    · apply Subtype.ext
      apply Fin.ext
      simp only [slot]
      have := p.isLt
      have := w.val.isLt
      have := w.property
      omega
  right_inv := by
    intro x
    apply Fin.ext
    simp only [slot]
    omega

def blockEmb {m : ℕ} (b : Fin m × Fin 2) : BaseVertex ↪ (Fin m × Fin 28) where
  toFun w := (b.1,slot b.2 w)
  inj' := by
    intro w z h
    have hs : slot b.2 w = slot b.2 z := congrArg Prod.snd h
    exact congrArg Prod.snd (slotEquiv.injective (show slotEquiv (b.2,w) = slotEquiv (b.2,z) from hs))

lemma blockEmb_eq_iff {m : ℕ} (b c : Fin m × Fin 2) (w z : BaseVertex) :
    blockEmb b w = blockEmb c z ↔ b = c ∧ w = z := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := slotEquiv.injective (show slotEquiv (b.2,w) = slotEquiv (c.2,z) from congrArg Prod.snd h)
    exact ⟨Prod.ext h1 (congrArg Prod.fst h2),congrArg Prod.snd h2⟩
  · rintro ⟨rfl,rfl⟩
    rfl

lemma blockEmb_disjoint {m : ℕ} :
    Pairwise (fun b c : Fin m × Fin 2 => Disjoint (Set.range (blockEmb b)) (Set.range (blockEmb c))) := by
  intro b c hne
  apply Set.disjoint_left.mpr
  rintro x ⟨w,rfl⟩ ⟨z,hz⟩
  exact hne ((blockEmb_eq_iff _ _ _ _).mp hz).1.symm

lemma exists_block_vertex {m : ℕ} (x : Fin m × Fin 28) :
    ∃ b : Fin m × Fin 2, ∃ w : BaseVertex, blockEmb b w = x := by
  obtain ⟨⟨p,w⟩,h⟩ := slotEquiv.surjective x.2
  exact ⟨(x.1,p),w,Prod.ext rfl h⟩

def rightLeft (w z : BaseVertex) : Prop :=
  (w.val = 8 ∧ z.val = 1) ∨ (w.val = 9 ∧ z.val = 7)

def leftRight (w z : BaseVertex) : Prop := rightLeft z w

instance (w z : BaseVertex) : Decidable (rightLeft w z) := inferInstanceAs (Decidable (_ ∨ _))
instance (w z : BaseVertex) : Decidable (leftRight w z) := inferInstanceAs (Decidable (rightLeft z w))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma inner_slot : ∀ (p q : Fin 2) (w z : BaseVertex),
    inner (slot p w) (slot q z) ↔
      (p = q ∧ ThreeCycleObstruction.exampleGraph.Adj w.val z.val) ∨
      (p = 0 ∧ q = 1 ∧ rightLeft w z) ∨ (p = 1 ∧ q = 0 ∧ leftRight w z) := by decide

lemma forward_slot : ∀ (p q : Fin 2) (w z : BaseVertex),
    forward (slot p w) (slot q z) ↔ p = 1 ∧ q = 0 ∧ rightLeft w z := by decide

lemma rightLeft_symm (w z : BaseVertex) : rightLeft z w ↔ leftRight w z := Iff.rfl
lemma leftRight_symm (w z : BaseVertex) : leftRight z w ↔ rightLeft w z := Iff.rfl

def nextBlock {m : ℕ} [NeZero m] (b : Fin m × Fin 2) : Fin m × Fin 2 :=
  if b.2 = 0 then (b.1,1) else (b.1 + 1,0)

def prevBlock {m : ℕ} [NeZero m] (b : Fin m × Fin 2) : Fin m × Fin 2 :=
  if b.2 = 0 then (b.1 - 1,1) else (b.1,0)

lemma nextBlock_ne {m : ℕ} [NeZero m] (b : Fin m × Fin 2) : nextBlock b ≠ b := by
  intro h
  have hh := congrArg Prod.snd h
  obtain ⟨a,p⟩ := b
  fin_cases p <;> norm_num [nextBlock] at hh

lemma prevBlock_ne {m : ℕ} [NeZero m] (b : Fin m × Fin 2) : prevBlock b ≠ b := by
  intro h
  have hh := congrArg Prod.snd h
  obtain ⟨a,p⟩ := b
  fin_cases p <;> norm_num [prevBlock] at hh

lemma graph_adj_block {m : ℕ} [NeZero m] (b c : Fin m × Fin 2) (w z : BaseVertex) :
    (graph m).Adj (blockEmb b w) (blockEmb c z) ↔
      (b = c ∧ ThreeCycleObstruction.exampleGraph.Adj w.val z.val) ∨
      (c = nextBlock b ∧ rightLeft w z) ∨ (c = prevBlock b ∧ leftRight w z) := by
  obtain ⟨a,p⟩ := b
  obtain ⟨b,q⟩ := c
  change (a = b ∧ inner (slot p w) (slot q z)) ∨
    (a + 1 = b ∧ forward (slot p w) (slot q z)) ∨
    (b + 1 = a ∧ forward (slot q z) (slot p w)) ↔ _
  rw [inner_slot,forward_slot,forward_slot,rightLeft_symm]
  fin_cases p <;> fin_cases q <;>
    simp [nextBlock,prevBlock,Prod.mk.injEq,eq_sub_iff_add_eq,eq_comm,leftRight]
  all_goals tauto

def goRight (w : BaseVertex) : Bool := decide (w.val = 8 ∨ w.val = 9)

def mate (w : BaseVertex) : BaseVertex :=
  if w.val = 1 then ⟨8,by decide⟩ else
  if w.val = 7 then ⟨9,by decide⟩ else
  if w.val = 8 then ⟨1,by decide⟩ else
  if w.val = 9 then ⟨7,by decide⟩ else ⟨1,by decide⟩

def port (w : BaseVertex) : Prop := ThreeCycleObstruction.exampleGraph.Adj w.val 0
instance (w : BaseVertex) : Decidable (port w) := inferInstanceAs (Decidable (ThreeCycleObstruction.exampleGraph.Adj w.val 0))

lemma rightLeft_port : ∀ w z : BaseVertex,
    rightLeft w z ↔ goRight w = true ∧ port w ∧ z = mate w := by decide

lemma leftRight_port : ∀ w z : BaseVertex,
    leftRight w z ↔ goRight w ≠ true ∧ port w ∧ z = mate w := by decide

def outer {m : ℕ} [NeZero m] (b : Fin m × Fin 2) (w : BaseVertex) : Fin m × Fin 28 :=
  if goRight w = true then blockEmb (nextBlock b) (mate w) else blockEmb (prevBlock b) (mate w)

lemma outer_not_in_block {m : ℕ} [NeZero m] (b : Fin m × Fin 2) (w : BaseVertex) :
    outer b w ∉ Set.range (blockEmb b) := by
  rintro ⟨z,hz⟩
  by_cases hr : goRight w = true
  · rw [outer,if_pos hr] at hz
    exact nextBlock_ne b ((blockEmb_eq_iff _ _ _ _).mp hz).1.symm
  · rw [outer,if_neg hr] at hz
    exact prevBlock_ne b ((blockEmb_eq_iff _ _ _ _).mp hz).1.symm

lemma graph_internal {m : ℕ} [NeZero m] (b : Fin m × Fin 2) (w z : BaseVertex) :
    (graph m).Adj (blockEmb b w) (blockEmb b z) ↔
      completedBase.Adj (some w) (some z) := by
  change _ ↔ ThreeCycleObstruction.exampleGraph.Adj w.val z.val
  rw [graph_adj_block]
  simp [Ne.symm (nextBlock_ne b),Ne.symm (prevBlock_ne b)]

lemma graph_boundary {m : ℕ} [NeZero m] (b : Fin m × Fin 2) (w : BaseVertex)
    (x : Fin m × Fin 28) (hx : x ∉ Set.range (blockEmb b)) :
    (graph m).Adj (blockEmb b w) x ↔ x = outer b w ∧ completedBase.Adj (some w) none := by
  obtain ⟨c,z,rfl⟩ := exists_block_vertex x
  have hbc : b ≠ c := by
    intro h
    apply hx
    exact ⟨z,by rw [h]⟩
  change _ ↔ blockEmb c z = outer b w ∧ port w
  rw [graph_adj_block]
  simp only [hbc,false_and,false_or,rightLeft_port,leftRight_port]
  by_cases hr : goRight w = true <;>
    simp [outer,hr,blockEmb_eq_iff] <;> tauto

noncomputable def blockModel (m : ℕ) [NeZero m] (b : Fin m × Fin 2) :
    BlockModel (graph m) completedBase where
  emb := blockEmb b
  outer := outer b
  outside := outer_not_in_block b
  internal := graph_internal b
  boundary := graph_boundary b

lemma trace_top_eq {V W : Type*} {G : SimpleGraph V} {B : SimpleGraph (Option W)}
    (M : BlockModel G B) : M.trace ⊤ = B := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  cases x with
  | none =>
    cases y with
    | none => simp [BlockModel.trace]
    | some y =>
      change G.Adj (M.emb y) (M.outer y) ↔ B.Adj none (some y)
      rw [M.boundary y _ (M.outside y)]
      simp only [true_and]
      exact B.adj_comm _ _
  | some x =>
    cases y with
    | none =>
      change G.Adj (M.emb x) (M.outer x) ↔ B.Adj (some x) none
      rw [M.boundary x _ (M.outside x)]
      simp
    | some y => exact M.internal x y

lemma graph_regular {m : ℕ} [NeZero m] : (graph m).IsRegularOfDegree 4 := by
  classical
  intro x
  obtain ⟨b,w,rfl⟩ := exists_block_vertex x
  have he := (blockModel m b).trace_degree_some ⊤ w
  rw [trace_top_eq] at he
  have hb := completedBaseIso.degree_eq (some w)
  have h4 := ThreeCycleObstruction.exampleGraph_regular (completedBaseIso (some w))
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at he hb h4 ⊢
  change Nat.card (completedBase.neighborSet (some w)) =
    Nat.card ((graph m).neighborSet (blockEmb b w)) at he
  omega

lemma graph_even {m : ℕ} [NeZero m] : ∀ x, Even ((graph m).degree x) := by
  intro x
  rw [graph_regular x]
  decide

lemma integral_lower_bound {m : ℕ} [NeZero m] : 2 * m ≤ Critical.number (graph m) := by
  have h := card_base_blocks_le_number (graph m) (blockModel m) (by
    intro x
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
      graph_even (m := m) x) (by
    intro b c hbc
    exact blockEmb_disjoint hbc)
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using h

#print axioms graph_regular
#print axioms integral_lower_bound
lemma graph_connected {m : ℕ} [NeZero m] : (graph m).Connected :=
  SimpleGraph.Connected.mono (cycle_le (m := m) 0) (cycle_property (NeZero.pos m) 0).1

open scoped Classical in
lemma graph_edge_count {m : ℕ} [NeZero m] : (graph m).edgeFinset.card = 56 * m := by
  classical
  have hs := (graph m).sum_degrees_eq_twice_card_edges
  have hr := graph_regular (m := m)
  simp only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
    SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hr hs ⊢
  simp only [hr,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    Fintype.card_prod,Fintype.card_fin] at hs
  omega

/-- These examples still have a linear integral bound. -/
lemma integral_upper_bound {m : ℕ} [NeZero m] : 3 * Critical.number (graph m) ≤ 56 * m := by
  classical
  obtain ⟨D,hD,hdec,hc⟩ := exists_cycle_decomposition (graph m) (by
    intro x
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
      graph_even (m := m) x)
  have hn := Critical.number_le D (fun H hH => Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD H hH)) hdec
  have he := graph_edge_count (m := m)
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at he hc
  omega

open scoped Classical in
/-- Even connected 4-regular graphs can have unbounded integral decomposition
cost while four Hamilton cycles of coefficient one half cover every edge exactly
once. Hence parity does not rescue a pure multiplicative fractional rounding bound. -/
lemma unbounded_even_integral_cost_at_fractional_cost_two (B : ℝ) :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W) (H : Fin 4 → G.Subgraph),
      G.Connected ∧ G.IsRegularOfDegree 4 ∧ (∀ v, Even (G.degree v)) ∧
      (∀ i, (H i).IsSpanning ∧ (H i).coe.Connected ∧ (H i).coe.IsRegularOfDegree 2) ∧
      (∀ e, (∑ i : Fin 4, if e ∈ (H i).edgeSet then (1/2 : ℝ) else 0) =
        if e ∈ G.edgeSet then 1 else 0) ∧
      (∀ D : Finset G.Subgraph, (∀ K ∈ D, IsCycleOrEdge K.coe) → IsDecomposition G D →
        B * (∑ _i : Fin 4, (1/2 : ℝ)) < (D.card : ℝ)) := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 B)
  have hNpos : 0 < N := by
    have hh : (0 : ℝ) < N := (le_max_left _ _).trans_lt hN
    exact_mod_cast hh
  letI : NeZero N := ⟨by omega⟩
  refine ⟨Fin N × Fin 28,inferInstance,graph N,piece N,graph_connected,?_,?_,?_,?_,?_⟩
  · simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using (graph_regular (m := N))
  · intro x
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
      graph_even (m := N) x
  · intro i
    refine ⟨piece_spanning i,?_⟩
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using piece_cycle (m := N) i
  · intro e
    by_cases he : e ∈ (graph N).edgeSet <;>
      simpa only [he,if_pos,if_neg] using fractional_cover (m := N) e
  · intro D hD hdec
    have hlo := integral_lower_bound (m := N)
    have hn := Critical.number_le D hD hdec
    have hreal : (2 : ℝ) * N ≤ D.card := by exact_mod_cast hlo.trans hn
    have hBN : B < N := (le_max_right _ _).trans_lt hN
    have hsum : (∑ _i : Fin 4, (1/2 : ℝ)) = 2 := by norm_num
    rw [hsum]
    linarith

#print axioms integral_upper_bound
#print axioms unbounded_even_integral_cost_at_fractional_cost_two
end Erdos184Work.EvenRing



/-! A nonseparating rainbow cycle need not improve an even-minimal decomposition.
This is an auxiliary obstruction, not a disproof of Erdős 184. -/

open SimpleGraph
namespace Erdos184Work.RainbowCore
open Critical EvenCore
set_option maxHeartbeats 2000000

def edges : Finset (Sym2 (Fin 7)) :=
  {s(0,1), s(1,2), s(2,0), s(0,3), s(3,1), s(0,4), s(4,1),
    s(1,5), s(5,2), s(1,6), s(6,2)}
def graph : SimpleGraph (Fin 7) := SimpleGraph.fromEdgeSet edges
instance : DecidableRel graph.Adj := by unfold graph; infer_instance

lemma graph_even : ∀ v, Even (graph.degree v) := by decide
lemma graph_degree_one : graph.degree 1 = 6 := by decide
lemma graph_edge_count : graph.edgeFinset.card = 11 := by decide

def cycle₀ : graph.Walk 0 0 :=
  (.cons (show graph.Adj 0 3 by decide)
  (.cons (show graph.Adj 3 1 by decide)
  (.cons (show graph.Adj 1 5 by decide)
  (.cons (show graph.Adj 5 2 by decide)
  (.cons (show graph.Adj 2 0 by decide) .nil)))))
lemma cycle₀_isCycle : cycle₀.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def cycle₁ : graph.Walk 0 0 :=
  (.cons (show graph.Adj 0 1 by decide)
  (.cons (show graph.Adj 1 4 by decide)
  (.cons (show graph.Adj 4 0 by decide) .nil)))
lemma cycle₁_isCycle : cycle₁.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def cycle₂ : graph.Walk 1 1 :=
  (.cons (show graph.Adj 1 2 by decide)
  (.cons (show graph.Adj 2 6 by decide)
  (.cons (show graph.Adj 6 1 by decide) .nil)))
lemma cycle₂_isCycle : cycle₂.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def triangle : graph.Walk 0 0 :=
  (.cons (show graph.Adj 0 1 by decide)
  (.cons (show graph.Adj 1 2 by decide)
  (.cons (show graph.Adj 2 0 by decide) .nil)))
lemma triangle_isCycle : triangle.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def piece : Fin 3 → graph.Subgraph
  | 0 => cycle₀.toSubgraph
  | 1 => cycle₁.toSubgraph
  | 2 => cycle₂.toSubgraph
def pieceEdges : Fin 3 → Finset (Sym2 (Fin 7))
  | 0 => cycle₀.edges.toFinset
  | 1 => cycle₁.edges.toFinset
  | 2 => cycle₂.edges.toFinset
lemma piece_edges (i : Fin 3) :
    (piece i).edgeSet = (pieceEdges i : Set (Sym2 (Fin 7))) := by
  fin_cases i
  all_goals
    ext e
    simp only [piece, pieceEdges, Finset.mem_coe, List.mem_toFinset]
    exact Walk.mem_edges_toSubgraph _

abbrev Rest := {v : Fin 7 // v ≠ 1}
def rest : SimpleGraph Rest := graph.induce {v | v ≠ 1}
instance : DecidableRel rest.Adj := by unfold rest; infer_instance

def root : Rest := ⟨0, by decide⟩
lemma rest_reachable_root (v : Rest) : rest.Reachable v root := by
  obtain ⟨v,hv⟩ := v
  fin_cases v
  · exact .refl _
  · exact (hv rfl).elim
  · exact (show rest.Adj ⟨2,by decide⟩ root by decide).reachable
  · exact (show rest.Adj ⟨3,by decide⟩ root by decide).reachable
  · exact (show rest.Adj ⟨4,by decide⟩ root by decide).reachable
  · exact (show rest.Adj ⟨5,by decide⟩ ⟨2,by decide⟩ by decide).reachable.trans
      (show rest.Adj ⟨2,by decide⟩ root by decide).reachable
  · exact (show rest.Adj ⟨6,by decide⟩ ⟨2,by decide⟩ by decide).reachable.trans
      (show rest.Adj ⟨2,by decide⟩ root by decide).reachable
lemma rest_connected : rest.Connected := by
  letI : Nonempty Rest := ⟨root⟩
  exact ⟨fun u v => (rest_reachable_root u).trans (rest_reachable_root v).symm⟩
lemma rest_tree : rest.IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨rest_connected, ?_⟩
  simp only [Nat.card_eq_fintype_card]
  decide

open scoped Classical

lemma graph_minimal_and_number : EvenMinimal graph ∧ number graph = 3 := by
  have ha : (graph.induce {1}ᶜ).IsAcyclic := by
    exact rest_tree.IsAcyclic
  have he : ∀ w, Even (graph.degree w) := by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using graph_even w
  obtain ⟨hm,hd⟩ := (StarCharacterization.saturated_minimal_iff_feedback_vertex (G := graph) (by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using graph_even w) 1).mpr ha
  have hd' := graph_degree_one
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd hd'
  exact ⟨hm, by omega⟩

lemma piece_cycle (i : Fin 3) :
    (piece i).coe.Connected ∧ (piece i).coe.IsRegularOfDegree 2 := by
  fin_cases i
  · simpa only [piece, SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using cycle_coe_regular graph cycle₀_isCycle
  · simpa only [piece, SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using cycle_coe_regular graph cycle₁_isCycle
  · simpa only [piece, SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using cycle_coe_regular graph cycle₂_isCycle
noncomputable def decomposition : Finset graph.Subgraph := Finset.univ.image piece
lemma decomposition_cycles :
    ∀ H ∈ decomposition, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
  intro H hH
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
  exact piece_cycle i
lemma decomposition_property : IsDecomposition graph decomposition :=
  Compression.finite_family_decomposition piece pieceEdges piece_edges (by decide) (by decide)
lemma decomposition_card : decomposition.card = 3 := by
  have hlo := number_le decomposition (fun H hH => Or.inl (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using decomposition_cycles H hH))
    decomposition_property
  have hhi := Finset.card_image_le (s := (Finset.univ : Finset (Fin 3))) (f := piece)
  rw [graph_minimal_and_number.2] at hlo
  simp only [Finset.card_univ,Fintype.card_fin] at hhi
  exact le_antisymm hhi hlo

lemma triangle_rainbow : Transversal.CycleTransversal decomposition triangle.toSubgraph.edgeSet := by
  intro H hH
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
  rw [piece_edges]
  have ht : triangle.toSubgraph.edgeSet = (triangle.edges.toFinset : Set (Sym2 (Fin 7))) := by
    ext e
    exact triangle.mem_edges_toSubgraph.trans List.mem_toFinset.symm
  rw [ht]
  change ∀ ⦃a⦄, a ∈ (pieceEdges i : Set (Sym2 (Fin 7))) ∩ (triangle.edges.toFinset : Set (Sym2 (Fin 7))) →
    ∀ ⦃b⦄, b ∈ (pieceEdges i : Set (Sym2 (Fin 7))) ∩ (triangle.edges.toFinset : Set (Sym2 (Fin 7))) → a = b
  clear * - i
  revert i
  decide

lemma graph_connected : graph.Connected := by
  have h : ∀ v : Fin 7, v = 0 ∨ graph.Adj v 0 ∨
      ∃ w, graph.Adj v w ∧ graph.Adj w 0 := by decide
  have hr : ∀ v, graph.Reachable v 0 := by
    intro v
    rcases h v with rfl | ha | ⟨w,ha,hb⟩
    · exact .refl _
    · exact ha.reachable
    · exact ha.reachable.trans hb.reachable
  exact ⟨fun u v => (hr u).trans (hr v).symm⟩

lemma triangle_nonseparating : (graph.deleteEdges triangle.toSubgraph.edgeSet).Connected := by
  apply Transversal.delete_transversal_connected graph_connected decomposition
  · intro H hH
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using decomposition_cycles H hH
  · exact decomposition_property
  · exact triangle_rainbow

lemma sparse_union_threshold_is_tight :
    graph.edgeFinset.card + 2 = decomposition.card + Fintype.card (Fin 7) + triangle.length := by
  have hc := graph_edge_count
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc ⊢
  rw [hc, decomposition_card, Nat.card_fin]
  decide

/-- The graph is an even-minimal core, and its optimal decomposition has a
nonseparating rainbow triangle. No smaller cycle-and-edge decomposition exists. -/
lemma even_minimal_rainbow_obstruction :
    EvenMinimal graph ∧ graph.Connected ∧
    (∀ v, Even (graph.degree v)) ∧
    (∀ H ∈ decomposition, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
    IsDecomposition graph decomposition ∧
    decomposition.card = 3 ∧ triangle.IsCycle ∧
    Transversal.CycleTransversal decomposition triangle.toSubgraph.edgeSet ∧
    (graph.deleteEdges triangle.toSubgraph.edgeSet).Connected ∧
    ∀ E : Finset graph.Subgraph, (∀ H ∈ E, IsCycleOrEdge H.coe) →
      IsDecomposition graph E → decomposition.card ≤ E.card := by
  refine ⟨graph_minimal_and_number.1, graph_connected, ?_, decomposition_cycles,
    decomposition_property, decomposition_card, triangle_isCycle,
    triangle_rainbow, triangle_nonseparating, ?_⟩
  · intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using graph_even v
  · intro E hE hdec
    rw [decomposition_card, ← graph_minimal_and_number.2]
    exact number_le E hE hdec

#print axioms graph_minimal_and_number
#print axioms triangle_rainbow
#print axioms even_minimal_rainbow_obstruction
end Erdos184Work.RainbowCore



/-! Strict increase under deletion of an edge from an even graph.
This is a local formula, not a uniform decomposition bound. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.SingleDeletion
open Critical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma even_decomposition_edgePieces_three_le
    (heven : ∀ v, Even (G.degree v))
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D)
    (hsingle : ∃ H ∈ D, H.coe.edgeFinset.card = 1) :
    3 ≤ (edgePieces D).card := by
  classical
  let R := subfamilyGraph (edgePieces D)
  have he : ∀ v, Even (R.degree v) := by
    intro v
    have h := (edgePieces_degree_parity D hD hdec v).mpr (heven v)
    simpa only [R, ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using h
  have hn : R ≠ ⊥ := by
    intro hr
    obtain ⟨H,hHD,hH⟩ := hsingle
    have ha : 0 < (edgePieces D).card := Finset.card_pos.mpr
      ⟨H, Finset.mem_filter.mpr ⟨hHD,hH⟩⟩
    have hc := edgePieces_graph_card D hdec
    change R.edgeFinset.card = _ at hc
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc
    rw [hr] at hc
    simp at hc
    omega
  obtain ⟨u,p,hp⟩ := exists_cycle_of_even_ne_bot R (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using he v) hn
  have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono p.toSubgraph.spanningCoe_le)
  have hc := cycle_edge_count R hp
  have hcR := edgePieces_graph_card D hdec
  have hlen := hp.three_le_length
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hle hc hcR
  change Nat.card R.edgeSet = _ at hcR
  omega

lemma even_decomposition_with_edge_improves_two
    (heven : ∀ v, Even (G.degree v))
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D)
    (hsingle : ∃ H ∈ D, H.coe.edgeFinset.card = 1) :
    ∃ E : Finset G.Subgraph, (∀ H ∈ E, IsCycleOrEdge H.coe) ∧
      IsDecomposition G E ∧ E.card + 2 ≤ D.card := by
  classical
  obtain ⟨E,hE,hdecE,hcE⟩ := cycle_only_decomposition_scaled heven D hD hdec
  let C := D.filter (fun H => H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
  have hcomp : D \ C = edgePieces D := by
    ext H
    simp only [Finset.mem_sdiff, C, Finset.mem_filter, edgePieces]
    constructor
    · rintro ⟨hHD,hn⟩
      rcases hD H hHD with hc | he
      · exact (hn ⟨hHD,by
          simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
            ← Nat.card_eq_fintype_card] using hc⟩).elim
      · exact ⟨hHD,he⟩
    · rintro ⟨hHD,he⟩
      refine ⟨hHD, ?_⟩
      rintro ⟨_,hc,hr⟩
      exact regular_two_not_single_edge H.coe hc (by
        simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hr) he
  have hcard := Finset.card_sdiff_add_card_eq_card (show C ⊆ D from Finset.filter_subset _ _)
  rw [hcomp] at hcard
  have hthree := even_decomposition_edgePieces_three_le heven D hD hdec hsingle
  change 3 * E.card ≤ 2 * C.card + D.card at hcE
  refine ⟨E, ?_, hdecE, by omega⟩
  intro H hH
  left
  simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using hE H hH

/-- Unlike deletion of a cycle, deletion of a single edge from an even graph
always strictly increases the minimum cycle-and-edge decomposition count. -/
lemma delete_edge_from_even_number
    (heven : ∀ v, Even (G.degree v)) (e : G.edgeSet) :
    number G + 1 ≤ number (G.deleteEdges {e.val}) := by
  obtain ⟨D,hD,hdec,hcD⟩ := exists_minimum (G.deleteEdges {e.val})
  obtain ⟨E,hE,hdecE,hcE,H,hHE,_,hsingle⟩ := restore_single_edge G e D hD hdec
  obtain ⟨A,hA,hdecA,hcA⟩ := even_decomposition_with_edge_improves_two heven E hE hdecE
    ⟨H,hHE,hsingle⟩
  have hn := number_le A hA hdecA
  omega

/-- A nonempty even graph has a proper edge-critical subgraph with strictly
larger optimum. Edge-critical and even-minimal reductions therefore behave
differently; no monotonicity under arbitrary deletions is being claimed. -/
lemma exists_proper_critical_with_larger_number
    (heven : ∀ v, Even (G.degree v)) (hnonempty : G ≠ ⊥) :
    ∃ R : SimpleGraph V, R ≤ G ∧
      R.edgeFinset.card < G.edgeFinset.card ∧
      EdgeCritical R ∧ number G < number R := by
  classical
  obtain ⟨u,v,huv⟩ : ∃ u v, G.Adj u v := by
    by_contra! h
    apply hnonempty
    apply le_antisymm _ bot_le
    intro u v huv
    exact (h u v huv).elim
  let e : G.edgeSet := ⟨s(u,v),huv⟩
  obtain ⟨R,hRG,hcrit,hnum⟩ := exists_critical_subgraph (G.deleteEdges {e.val})
  have hlt := delete_edge_from_even_number heven e
  have hcard := delete_edge_card_lt G e
  have hc := Finset.card_le_card (SimpleGraph.edgeFinset_mono hRG)
  refine ⟨R,hRG.trans (G.deleteEdges_le _), ?_,hcrit,?_⟩
  · simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc hcard ⊢
    omega
  · omega

#print axioms even_decomposition_edgePieces_three_le
#print axioms even_decomposition_with_edge_improves_two
#print axioms delete_edge_from_even_number
#print axioms exists_proper_critical_with_larger_number
end Erdos184Work.SingleDeletion



/-! Exchanges that increase the number of cycles. These constrain maximum,
not minimum, decompositions and do not settle Erdős 184. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.MaximumCycles
set_option maxHeartbeats 1500000

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma regular_two_card_edges (H : G.Subgraph) (hH : H.coe.IsRegularOfDegree 2) :
    H.spanningCoe.edgeFinset.card = H.verts.ncard := by
  have hs := H.coe.sum_degrees_eq_twice_card_edges
  have hc := subgraph_edge_card H
  change H.spanningCoe.edgeFinset.card = Nat.card H.verts
  simp only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
    SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hH hs hc ⊢
  simp only [hH, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card] at hs
  omega

omit [Fintype V] in
lemma two_piece_sdiff (H K : G.Subgraph) (hd : Disjoint H.edgeSet K.edgeSet) :
    (H.spanningCoe ⊔ K.spanningCoe) \ H.spanningCoe = K.spanningCoe := by
  ext x y
  change (H.Adj x y ∨ K.Adj x y) ∧ ¬ H.Adj x y ↔ K.Adj x y
  have hn : ¬ (H.Adj x y ∧ K.Adj x y) := fun h =>
    Set.disjoint_left.mp hd (show s(x,y) ∈ H.edgeSet from h.1) h.2
  tauto

lemma two_piece_degree (H K : G.Subgraph) (hd : Disjoint H.edgeSet K.edgeSet) (v : V) :
    (H.spanningCoe ⊔ K.spanningCoe).degree v =
      H.spanningCoe.degree v + K.spanningCoe.degree v := by
  have h := degree_sdiff_add (H.spanningCoe ⊔ K.spanningCoe) H.spanningCoe le_sup_left v
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
  rw [two_piece_sdiff H K hd] at h
  omega

lemma two_regular_pieces_intersection_bound_of_feedback
    (H K : G.Subgraph) (hH : H.coe.IsRegularOfDegree 2)
    (hK : K.coe.IsRegularOfDegree 2) (hd : Disjoint H.edgeSet K.edgeSet)
    (v : V) (hvH : v ∈ H.verts) (hvK : v ∈ K.verts)
    (hacy : ((H.spanningCoe ⊔ K.spanningCoe).induce {v}ᶜ).IsAcyclic) :
    (H.verts ∩ K.verts).ncard ≤ 2 := by
  classical
  let R := H.spanningCoe ⊔ K.spanningCoe
  let S := H.verts ∪ K.verts
  let T := S \ {v}
  have hsupp : R.support ⊆ S := by
    rintro x ⟨y,hxy⟩
    rcases hxy with h | h
    · exact Or.inl (H.edge_vert h)
    · exact Or.inr (K.edge_vert h)
  have hsupp' : (R.deleteIncidenceSet v).support ⊆ T := by
    intro x hx
    obtain ⟨hx,hxv⟩ := R.support_deleteIncidenceSet_subset v hx
    exact ⟨hsupp hx,hxv⟩
  have hacyT : (R.induce T).IsAcyclic := by
    let f : R.induce T →g R.induce {v}ᶜ :=
      ⟨fun x => ⟨x.val,x.property.2⟩, fun h => h⟩
    apply hacy.comap f
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : ({v}ᶜ : Set V) => z.val) h
  have hedgeT : (R.induce T).edgeFinset.card = R.edgeFinset.card - R.degree v := by
    have hnot : v ∉ T := fun h => h.2 (Set.mem_singleton _)
    have h1 := SimpleGraph.card_edgeFinset_induce_of_support_subset hsupp'
    have h2 := R.card_edgeFinset_deleteIncidenceSet v
    simp only [SimpleGraph.edgeFinset_card, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at h1 h2 ⊢
    rw [R.induce_deleteIncidenceSet_of_notMem hnot] at h1
    omega
  have hdegree : R.degree v = 4 := by
    have h := two_piece_degree H K hd v
    have hh := regular_two_spanning_degree H hH v
    have hk := regular_two_spanning_degree K hK v
    simp only [if_pos hvH, if_pos hvK] at hh hk
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      at h hh hk ⊢
    exact h.trans (by omega)
  have hcardR : R.edgeFinset.card = H.verts.ncard + K.verts.ncard := by
    have hd' : Disjoint H.spanningCoe.edgeFinset K.spanningCoe.edgeFinset := by
      apply Finset.disjoint_left.mpr
      intro e heH heK
      exact Set.disjoint_left.mp hd (SimpleGraph.mem_edgeFinset.mp heH)
        (SimpleGraph.mem_edgeFinset.mp heK)
    change (H.spanningCoe ⊔ K.spanningCoe).edgeFinset.card = _
    rw [SimpleGraph.edgeFinset_sup, Finset.card_union_of_disjoint hd',
      regular_two_card_edges H hH, regular_two_card_edges K hK]
  have hverts : S.ncard + (H.verts ∩ K.verts).ncard = H.verts.ncard + K.verts.ncard :=
    Set.ncard_union_add_ncard_inter _ _
  have hcardT : T.ncard + 1 = S.ncard := Set.ncard_diff_singleton_add_one (Or.inl hvH)
  by_contra! hbig
  have hSpos : 3 ≤ S.ncard := (show 3 ≤ (H.verts ∩ K.verts).ncard by omega).trans
    (Set.ncard_le_ncard (show H.verts ∩ K.verts ⊆ S from fun _ h => Or.inl h.1))
  have hTne : T.Nonempty := (Set.ncard_pos (s := T)).mp (by omega)
  letI : Nonempty T := hTne.to_subtype
  have hforest := acyclic_card_edges_lt (R.induce T) hacyT
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hedgeT hdegree hcardR hforest
  change Nat.card T + 1 = Nat.card S at hcardT
  change Nat.card S + (H.verts ∩ K.verts).ncard = _ at hverts
  omega


omit [Fintype V] in
lemma liftSubgraph_injective {Q : SimpleGraph V} (h : Q ≤ G) :
    Function.Injective (liftSubgraph h) := by
  intro H K he
  apply SimpleGraph.Subgraph.ext
  · exact congrArg (fun J : G.Subgraph => J.verts) he
  · exact congrArg (fun J : G.Subgraph => J.Adj) he

lemma lift_cycle_decomposition_exact {Q : SimpleGraph V} (h : Q ≤ G)
    (D : Finset Q.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition Q D) :
    ∃ A : Finset G.Subgraph,
      (∀ H ∈ A, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet) ∧
      (⋃ H ∈ A, H.edgeSet) = Q.edgeSet ∧ A.card = D.card := by
  classical
  let A := D.image (liftSubgraph h)
  refine ⟨A, ?_, ?_, ?_, Finset.card_image_of_injective _ (liftSubgraph_injective h)⟩
  · intro H hH
    obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD K hK
  · intro H hH K hK hne
    obtain ⟨H',hH',rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨K',hK',rfl⟩ := Finset.mem_image.mp hK
    exact hdec.1 hH' hK' (fun he => hne (congrArg (liftSubgraph h) he))
  · rw [← hdec.2]
    ext e
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨H,hH,he⟩
      obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
      exact ⟨K,hK,he⟩
    · rintro ⟨K,hK,he⟩
      exact ⟨liftSubgraph h K,Finset.mem_image.mpr ⟨K,hK,rfl⟩,he⟩

lemma cycle_extension_exact (heven : ∀ v, Even (G.degree v))
    {u : V} (p : G.Walk u u) (hp : p.IsCycle) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧
      E.card = Critical.number (G \ p.toSubgraph.spanningCoe) + 1 := by
  classical
  have he := EvenCore.delete_cycle_even heven hp
  obtain ⟨D,hD,hdec,hcard⟩ := Critical.exists_minimum (G \ p.toSubgraph.spanningCoe)
  have hDc := minimal_even_decomposition_cycles (G := G \ p.toSubgraph.spanningCoe) (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using he v) D hD hdec (by
    intro A hA hdecA
    rw [hcard]
    exact Critical.number_le A hA hdecA)
  obtain ⟨A,hA,hpA,heA,hcA⟩ := lift_cycle_decomposition_exact (G := G) sdiff_le D hDc hdec
  have hdis : ∀ H ∈ A, Disjoint p.toSubgraph.edgeSet H.edgeSet := by
    intro H hH
    apply Set.disjoint_left.mpr
    intro e heC heH
    have heR : e ∈ (G \ p.toSubgraph.spanningCoe).edgeSet := by
      rw [← heA]
      exact Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hH,heH⟩⟩
    rw [SimpleGraph.edgeSet_sdiff] at heR
    exact heR.2 heC
  have hnot : p.toSubgraph ∉ A := by
    intro h
    have he : s(u,p.snd) ∈ p.toSubgraph.edgeSet := p.toSubgraph_adj_snd hp.not_nil
    exact Set.disjoint_left.mp (hdis _ h) he he
  refine ⟨insert p.toSubgraph A, ?_, ⟨?_,?_⟩,?_⟩
  · intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH
    · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using cycle_coe_regular G hp
    · exact hA H hH
  · rw [Finset.coe_insert]
    apply hpA.insert
    intro H hH _
    exact hdis H hH
  · rw [Finset.set_biUnion_insert,heA,SimpleGraph.edgeSet_sdiff]
    exact Set.union_diff_cancel (SimpleGraph.edgeSet_mono p.toSubgraph.spanningCoe_le)
  · rw [Finset.card_insert_of_notMem hnot,hcA,hcard]

lemma two_cycles_exchange
    (H K : G.Subgraph) (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hd : Disjoint H.edgeSet K.edgeSet) (hbig : 3 ≤ (H.verts ∩ K.verts).ncard) :
    ∃ D : Finset (H.spanningCoe ⊔ K.spanningCoe).Subgraph,
      (∀ L ∈ D, L.coe.Connected ∧ L.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (H.spanningCoe ⊔ K.spanningCoe) D ∧ 3 ≤ D.card := by
  classical
  obtain ⟨v,hvH,hvK⟩ : (H.verts ∩ K.verts).Nonempty :=
    (Set.ncard_pos (s := H.verts ∩ K.verts)).mp (by omega)
  let R := H.spanningCoe ⊔ K.spanningCoe
  have hacy : ¬ (R.induce {v}ᶜ).IsAcyclic := by
    intro ha
    have h := two_regular_pieces_intersection_bound_of_feedback H K (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hH.2) (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hK.2) hd v hvH hvK ha
    omega
  have hnotall := mt (StarCore.cycle_hits_iff_induce_acyclic (G := R) v).mp hacy
  push_neg at hnotall
  obtain ⟨u,p,hp,hvp⟩ := hnotall
  have heven : ∀ w, Even (R.degree w) := by
    intro w
    have hs := two_piece_degree H K hd w
    have hh := regular_two_spanning_even H (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hH.2) w
    have hk := regular_two_spanning_even K (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hK.2) w
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hs hh hk ⊢
    rw [hs]
    exact hh.add hk
  have hdv : R.degree v = 4 := by
    change (H.spanningCoe ⊔ K.spanningCoe).degree v = 4
    have hs := two_piece_degree H K hd v
    have hh := regular_two_spanning_degree H (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hH.2) v
    have hk := regular_two_spanning_degree K (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hK.2) v
    simp only [if_pos hvH,if_pos hvK] at hh hk
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hs hh hk ⊢
    omega
  have hpdeg : p.toSubgraph.spanningCoe.degree v = 0 := by
    have h := regular_two_spanning_degree p.toSubgraph (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using (cycle_coe_regular R hp).2) v
    have hv : v ∉ p.toSubgraph.verts := fun h => hvp (p.mem_verts_toSubgraph.mp h)
    simpa only [if_neg hv, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using h
  have hrest := degree_sdiff_add R p.toSubgraph.spanningCoe p.toSubgraph.spanningCoe_le v
  have hlo := StarCore.number_degree_bound (R \ p.toSubgraph.spanningCoe) v
  obtain ⟨D,hD,hdec,hcard⟩ := cycle_extension_exact (G := R) (by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using heven w) p hp
  refine ⟨D,?_,hdec,?_⟩
  · intro L hL
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD L hL
  · simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdv hpdeg hrest hlo
    omega


lemma cycle_piece_edgeSet_nonempty (H : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) : H.edgeSet.Nonempty := by
  classical
  have hn : H.coe ≠ ⊥ := by
    intro he
    apply SingleAddition.regular_two_not_acyclic H.coe hH.1 (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hH.2)
    rw [he]
    exact SimpleGraph.isAcyclic_bot
  obtain ⟨e,he⟩ := SimpleGraph.edgeSet_nonempty.mpr hn
  refine ⟨Sym2.map Subtype.val e,?_⟩
  simpa only [SimpleGraph.Subgraph.edgeSet_coe,Set.mem_preimage] using he

lemma replace_cycle_subfamily_exact (D A B : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) (hAD : A ⊆ D)
    (hB : ∀ H ∈ B, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hpB : Set.PairwiseDisjoint (B : Set G.Subgraph) (fun H => H.edgeSet))
    (hcover : (⋃ H ∈ A, H.edgeSet) = ⋃ H ∈ B, H.edgeSet) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card + A.card = D.card + B.card := by
  classical
  let C := D \ A
  have hpC : Set.PairwiseDisjoint (C : Set G.Subgraph) (fun H => H.edgeSet) := by
    intro H hH K hK hne
    exact hdec.1 (Finset.mem_sdiff.mp hH).1 (Finset.mem_sdiff.mp hK).1 hne
  have hcross : ∀ H ∈ C, ∀ K ∈ B, Disjoint H.edgeSet K.edgeSet := by
    intro H hH K hK
    apply Set.disjoint_left.mpr
    intro e heH heK
    have heU : e ∈ ⋃ K ∈ B, K.edgeSet :=
      Set.mem_iUnion.mpr ⟨K,Set.mem_iUnion.mpr ⟨hK,heK⟩⟩
    rw [← hcover] at heU
    obtain ⟨L,heL⟩ := Set.mem_iUnion.mp heU
    obtain ⟨hLA,heL⟩ := Set.mem_iUnion.mp heL
    have hHL : H ≠ L := by
      rintro rfl
      exact (Finset.mem_sdiff.mp hH).2 hLA
    exact Set.disjoint_left.mp (hdec.1 (Finset.mem_sdiff.mp hH).1 (hAD hLA) hHL) heH heL
  have hdis : Disjoint C B := by
    apply Finset.disjoint_left.mpr
    intro H hHC hHB
    obtain ⟨e,he⟩ := cycle_piece_edgeSet_nonempty H (hB H hHB)
    exact Set.disjoint_left.mp (hcross H hHC H hHB) he he
  refine ⟨C ∪ B, ?_, ⟨?_,?_⟩,?_⟩
  · intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · exact hD H (Finset.mem_sdiff.mp hH).1
    · exact hB H hH
  · rw [Finset.coe_union]
    exact hpC.union hpB (fun H hH K hK _ => hcross H hH K hK)
  · ext e
    simp only [Set.mem_iUnion,exists_prop]
    constructor
    · rintro ⟨H,_,he⟩
      exact H.edgeSet_subset he
    · intro he
      have heD : e ∈ ⋃ H ∈ D, H.edgeSet := hdec.2.symm ▸ he
      obtain ⟨H,h⟩ := Set.mem_iUnion.mp heD
      obtain ⟨hHD,heH⟩ := Set.mem_iUnion.mp h
      by_cases hHA : H ∈ A
      · have heA : e ∈ ⋃ H ∈ A, H.edgeSet :=
          Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hHA,heH⟩⟩
        rw [hcover] at heA
        obtain ⟨K,h⟩ := Set.mem_iUnion.mp heA
        obtain ⟨hKB,heK⟩ := Set.mem_iUnion.mp h
        exact ⟨K,Finset.mem_union_right _ hKB,heK⟩
      · exact ⟨H,Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hHD,hHA⟩),heH⟩
  · rw [Finset.card_union_of_disjoint hdis]
    have h := Finset.card_sdiff_add_card_eq_card hAD
    change C.card + A.card = D.card at h
    omega

/-- Maximum-cardinality cycle decompositions have pairwise vertex intersections
of size at most two. This is not asserted for minimum decompositions. -/
lemma maximum_decomposition_intersection_le_two (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D)
    (hmax : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → E.card ≤ D.card)
    (H K : G.Subgraph) (hHD : H ∈ D) (hKD : K ∈ D) (hHK : H ≠ K) :
    (H.verts ∩ K.verts).ncard ≤ 2 := by
  classical
  by_contra! hbig
  have hdis := hdec.1 hHD hKD hHK
  obtain ⟨I,hI,hdecI,hcardI⟩ := two_cycles_exchange H K (hD H hHD) (hD K hKD) hdis (by omega)
  obtain ⟨B,hB,hpB,heB,hcB⟩ := lift_cycle_decomposition_exact
    (sup_le H.spanningCoe_le K.spanningCoe_le) I (by
      intro L hL
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hI L hL) hdecI
  let A : Finset G.Subgraph := {H,K}
  have hAD : A ⊆ D := by
    intro L hL
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact hHD
    · exact Finset.mem_singleton.mp hL ▸ hKD
  have hcover : (⋃ L ∈ A, L.edgeSet) = ⋃ L ∈ B, L.edgeSet := by
    rw [heB,SimpleGraph.edgeSet_sup]
    simp only [A,Finset.set_biUnion_insert,Finset.set_biUnion_singleton]
    rfl
  obtain ⟨E,hE,hdecE,hcE⟩ := replace_cycle_subfamily_exact D A B hD hdec hAD hB hpB hcover
  have hcA : A.card = 2 := by simp [A,hHK]
  have h := hmax E hE hdecE
  omega

#print axioms two_regular_pieces_intersection_bound_of_feedback
#print axioms cycle_extension_exact
#print axioms two_cycles_exchange
#print axioms replace_cycle_subfamily_exact
#print axioms maximum_decomposition_intersection_le_two
end Erdos184Work.MaximumCycles



/-! Cycle rigidity and hereditary even minimality. No general rigidity of
even-minimal cores is assumed or proved here. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.Rigidity
open Critical EvenCore MaximumCycles StarCharacterization

set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- All cycle-only decompositions have minimum cardinality. This is not assumed
for arbitrary even-minimal graphs. -/
def CycleRigid (G : SimpleGraph V) : Prop :=
  ∀ D : Finset G.Subgraph,
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
    IsDecomposition G D → D.card = number G

lemma sdiff_even (heven : ∀ v, Even (G.degree v))
    {R : SimpleGraph V} (hRG : R ≤ G) (hR : ∀ v, Even (R.degree v)) :
    ∀ v, Even ((G \ R).degree v) := by
  intro v
  have hd := degree_sdiff_add G R hRG v
  have hg := Nat.even_iff.mp (heven v)
  have hr := Nat.even_iff.mp (hR v)
  apply Nat.even_iff.mpr
  omega

lemma minimum_cycles (heven : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card = number G := by
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum G
  refine ⟨D,?_,hdec,hcard⟩
  exact minimal_even_decomposition_cycles heven D hD hdec (by
    intro E hE hdecE
    rw [hcard]
    exact number_le E hE hdecE)

lemma combine_cycles_exact {R S : SimpleGraph V} (hRG : R ≤ G) (hSG : S ≤ G)
    (hdis : Disjoint R.edgeSet S.edgeSet) (hcover : R.edgeSet ∪ S.edgeSet = G.edgeSet)
    (D : Finset R.Subgraph) (F : Finset S.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdD : IsDecomposition R D)
    (hF : ∀ H ∈ F, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdF : IsDecomposition S F) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card = D.card + F.card := by
  obtain ⟨A,hA,hpA,heA,hcA⟩ := lift_cycle_decomposition_exact hRG D hD hdD
  obtain ⟨B,hB,hpB,heB,hcB⟩ := lift_cycle_decomposition_exact hSG F hF hdF
  have hcross : ∀ H ∈ A, ∀ K ∈ B, Disjoint H.edgeSet K.edgeSet := by
    intro H hH K hK
    apply hdis.mono
    · rw [← heA]
      exact fun e he => Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hH,he⟩⟩
    · rw [← heB]
      exact fun e he => Set.mem_iUnion.mpr ⟨K,Set.mem_iUnion.mpr ⟨hK,he⟩⟩
  have hab : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro H hHA hHB
    obtain ⟨e,he⟩ := cycle_piece_edgeSet_nonempty H (hA H hHA)
    exact Set.disjoint_left.mp (hcross H hHA H hHB) he he
  refine ⟨A ∪ B,?_,⟨?_,?_⟩,?_⟩
  · intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · exact hA H hH
    · exact hB H hH
  · rw [Finset.coe_union]
    exact hpA.union hpB (fun H hH K hK _ => hcross H hH K hK)
  · rw [← hcover,← heA,← heB]
    ext e
    simp only [Set.mem_iUnion,exists_prop,Finset.mem_union,Set.mem_union]
    aesop
  · rw [Finset.card_union_of_disjoint hab,hcA,hcB]

lemma extend_cycles_exact (heven : ∀ v, Even (G.degree v))
    {R : SimpleGraph V} (hRG : R ≤ G) (hR : ∀ v, Even (R.degree v))
    (D : Finset R.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition R D) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card = D.card + number (G \ R) := by
  have hS := sdiff_even heven hRG hR
  obtain ⟨F,hF,hdF,hcF⟩ := minimum_cycles (G := G \ R) (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hS v)
  have hdis : Disjoint R.edgeSet (G \ R).edgeSet := by
    rw [SimpleGraph.edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  have hcover : R.edgeSet ∪ (G \ R).edgeSet = G.edgeSet := by
    rw [SimpleGraph.edgeSet_sdiff]
    exact Set.union_diff_cancel (SimpleGraph.edgeSet_mono hRG)
  obtain ⟨E,hE,hdE,hcE⟩ := combine_cycles_exact hRG sdiff_le hdis hcover D F hD hdec hF hdF
  exact ⟨E,hE,hdE,by omega⟩

lemma CycleRigid.number_sdiff_add (hrig : CycleRigid G)
    (heven : ∀ v, Even (G.degree v))
    {R : SimpleGraph V} (hRG : R ≤ G) (hR : ∀ v, Even (R.degree v)) :
    number R + number (G \ R) = number G := by
  obtain ⟨D,hD,hdD,hcD⟩ := minimum_cycles hR
  obtain ⟨E,hE,hdE,hcE⟩ := extend_cycles_exact heven hRG hR D hD hdD
  have hc := hrig E hE hdE
  omega

lemma CycleRigid.mono (hrig : CycleRigid G) (heven : ∀ v, Even (G.degree v))
    {R : SimpleGraph V} (hRG : R ≤ G) (hR : ∀ v, Even (R.degree v)) : CycleRigid R := by
  intro D hD hdD
  obtain ⟨E,hE,hdE,hcE⟩ := extend_cycles_exact heven hRG hR D hD hdD
  have hc := hrig E hE hdE
  have hadd := hrig.number_sdiff_add heven hRG hR
  omega

lemma sdiff_ne_bot_of_card_lt {R : SimpleGraph V} (hRG : R ≤ G)
    (hcard : R.edgeFinset.card < G.edgeFinset.card) : G \ R ≠ ⊥ := by
  intro h
  have hGR : G ≤ R := by
    intro x y hxy
    by_contra hn
    have hs : (G \ R).Adj x y := ⟨hxy,hn⟩
    simp only [h,SimpleGraph.bot_adj] at hs
  have heq := le_antisymm hRG hGR
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hcard
  rw [heq] at hcard
  omega

lemma CycleRigid.evenMinimal (hrig : CycleRigid G)
    (heven : ∀ v, Even (G.degree v)) : EvenMinimal G := by
  intro R hRG hR hcard
  have hadd := hrig.number_sdiff_add heven hRG (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hR v)
  have hne := sdiff_ne_bot_of_card_lt hRG hcard
  have hnum : number (G \ R) ≠ 0 := fun h => hne ((number_eq_zero_iff _).mp h)
  omega

omit [Fintype V] in
lemma subfamilyGraph_mono {A B : Finset G.Subgraph} (hAB : A ⊆ B) :
    subfamilyGraph A ≤ subfamilyGraph B :=
  Finset.sup_mono hAB

lemma card_le_number_of_hereditary_minimal
    (hmin : ∀ R ≤ G, (∀ v, Even (R.degree v)) → EvenMinimal R)
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hpD : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    D.card ≤ number (subfamilyGraph D) := by
  have aux : ∀ A ⊆ D, A.card ≤ number (subfamilyGraph A) := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp
    | @insert H A hnot ih =>
      intro hAD
      have hHD : H ∈ D := hAD (Finset.mem_insert_self _ _)
      have haD : A ⊆ D := (Finset.subset_insert _ _).trans hAD
      have ha := ih haD
      have hpA : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet) :=
        fun _ hH _ hK hne => hpD (haD hH) (haD hK) hne
      have hpB : Set.PairwiseDisjoint ((insert H A : Finset G.Subgraph) : Set G.Subgraph) (fun H => H.edgeSet) :=
        fun _ hH _ hK hne => hpD (hAD hH) (hAD hK) hne
      have heA := cycle_subfamily_even A (fun K hK => hD K (haD hK)) hpA
      have heB := cycle_subfamily_even (insert H A) (fun K hK => hD K (hAD hK)) hpB
      have hBmin := hmin (subfamilyGraph (insert H A)) (subfamilyGraph_le _) (by
        intro v
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
          using heB v)
      have hcA := subfamilyGraph_card_edges A hpA
      have hcB := subfamilyGraph_card_edges (insert H A) hpB
      have hpos : 0 < H.coe.edgeFinset.card := by
        have hn : H.coe ≠ ⊥ := by
          intro heq
          apply SingleAddition.regular_two_not_acyclic H.coe (hD H hHD).1 (by
            simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
              ← Nat.card_eq_fintype_card] using (hD H hHD).2)
          rw [heq]
          exact SimpleGraph.isAcyclic_bot
        exact Finset.card_pos.mpr (SimpleGraph.edgeFinset_nonempty.mpr hn)
      rw [Finset.sum_insert hnot] at hcB
      have hlt : (subfamilyGraph A).edgeFinset.card <
          (subfamilyGraph (insert H A)).edgeFinset.card := by
        simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hcA hcB hpos ⊢
        omega
      have hn := hBmin (subfamilyGraph A)
        (subfamilyGraph_mono (Finset.subset_insert _ _)) (by
          intro v
          simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
            using heA v) hlt
      rw [Finset.card_insert_of_notMem hnot]
      omega
  exact aux D (Finset.Subset.refl _)

/-- Rigidity is equivalent to minimality of EVERY even subgraph, not merely
minimality of the full graph. The missing hereditary assertion is explicit. -/
lemma rigid_iff_hereditarily_evenMinimal (heven : ∀ v, Even (G.degree v)) :
    CycleRigid G ↔ ∀ R ≤ G, (∀ v, Even (R.degree v)) → EvenMinimal R := by
  constructor
  · intro hrig R hRG hR
    exact (hrig.mono heven hRG hR).evenMinimal hR
  · intro hmin D hD hdD
    have hlo := number_le D (fun H hH => Or.inl (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hD H hH)) hdD
    have hhi := card_le_number_of_hereditary_minimal hmin D hD hdD.1
    have hg : subfamilyGraph D = G :=
      SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdD.2)
    rw [hg] at hhi
    omega

/-- Under an explicit rigidity hypothesis, the maximum-decomposition
intersection bound also applies to every cycle decomposition. -/
lemma CycleRigid.intersection_le_two (hrig : CycleRigid G)
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdD : IsDecomposition G D)
    (H K : G.Subgraph) (hHD : H ∈ D) (hKD : K ∈ D) (hHK : H ≠ K) :
    (H.verts ∩ K.verts).ncard ≤ 2 := by
  apply maximum_decomposition_intersection_le_two D hD hdD _ H K hHD hKD hHK
  intro E hE hdE
  exact le_of_eq ((hrig E hE hdE).trans (hrig D hD hdD).symm)

universe u

/-- The proposed global inheritance theorem for minimal even cores is
EQUIVALENT to their proposed rigidity. Neither side is proved here. -/
lemma minimal_core_rigidity_iff_heredity :
    (∀ {W : Type u} [Fintype W] (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) → EvenMinimal R → CycleRigid R) ↔
    (∀ {W : Type u} [Fintype W] (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) → EvenMinimal R →
      ∀ S ≤ R, (∀ v, Even (S.degree v)) → EvenMinimal S) := by
  constructor
  · intro h W _ R hR hmin
    exact (rigid_iff_hereditarily_evenMinimal hR).mp (h R hR hmin)
  · intro h W _ R hR hmin
    exact (rigid_iff_hereditarily_evenMinimal hR).mpr (h R hR hmin)

#print axioms combine_cycles_exact
#print axioms CycleRigid.mono
#print axioms CycleRigid.evenMinimal
#print axioms rigid_iff_hereditarily_evenMinimal
#print axioms CycleRigid.intersection_le_two
#print axioms minimal_core_rigidity_iff_heredity
end Erdos184Work.Rigidity


/-! Rigidity for the first two optimum values and for saturated minimal cores. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.Rigidity
open Critical EvenCore MaximumCycles StarCharacterization

set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma twice_card_eq_degree_of_cycle_hits (v : V)
    (hhit : ∀ u (p : G.Walk u u), p.IsCycle → v ∈ p.support)
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) : 2 * D.card = G.degree v := by
  have hvH : ∀ H ∈ D, v ∈ H.verts := by
    intro H hH
    obtain ⟨w⟩ := (hD H hH).1.nonempty
    obtain ⟨p,hp,hpH⟩ := LongRing.regular_cycle_walk_at H (hD H hH).1 (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using (hD H hH).2) w.val w.property
    have hvp := p.mem_verts_toSubgraph.mpr (hhit w.val p hp)
    rwa [hpH] at hvp
  have hsum := subfamilyGraph_degree D hdec.1 v
  have hgraph : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  rw [hgraph] at hsum
  have hdeg : ∀ H ∈ D, H.spanningCoe.degree v = 2 := by
    intro H hH
    rw [regular_two_spanning_degree H (by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using (hD H hH).2),if_pos (hvH H hH)]
  have heq : (∑ H ∈ D, H.spanningCoe.degree v) = D.card * 2 := by
    calc
      _ = ∑ H ∈ D, 2 := Finset.sum_congr rfl hdeg
      _ = _ := by simp
  omega

lemma rigid_of_cycle_hits (heven : ∀ w, Even (G.degree w)) (v : V)
    (hhit : ∀ u (p : G.Walk u u), p.IsCycle → v ∈ p.support) : CycleRigid G := by
  intro D hD hdD
  have h1 := twice_card_eq_degree_of_cycle_hits v hhit D hD hdD
  have h2 := StarCore.twice_number_eq_degree_of_cycle_hits heven v hhit
  omega

lemma rigid_bot : CycleRigid (⊥ : SimpleGraph V) := by
  intro D hD hdD
  have hD0 : D = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro H hH
    obtain ⟨e,he⟩ := cycle_piece_edgeSet_nonempty H (hD H hH)
    have heG := H.edgeSet_subset he
    simpa using heG
  simp [hD0,number_bot]

lemma cycle_hits_of_single_cycle (H : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hHG : H.spanningCoe = G) (v : H.verts) :
    ∀ u (p : G.Walk u u), p.IsCycle → v.val ∈ p.support := by
  have hcyc : G.IsCycles := by
    rw [← hHG]
    intro x hx
    obtain ⟨y,hxy⟩ := hx
    have hverts : x ∈ H.verts := H.edge_vert hxy
    have h := regular_two_spanning_degree H (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hH.2) x
    rw [if_pos hverts] at h
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h
  intro u p hp
  have huH : u ∈ H.verts := by
    have h := p.toSubgraph.adj_sub (p.toSubgraph_adj_snd hp.not_nil)
    exact H.edge_vert (hHG.ge h)
  obtain ⟨q⟩ := hH.1.preconnected v ⟨u,huH⟩
  have hvp := SingleAddition.cycle_closed_under_walk hcyc p hp (q.map H.hom) (by
    change u ∈ p.toSubgraph.verts
    simp)
  exact p.mem_verts_toSubgraph.mp hvp

lemma rigid_of_number_le_one (heven : ∀ v, Even (G.degree v))
    (hnum : number G ≤ 1) : CycleRigid G := by
  by_cases hzero : number G = 0
  · have heq := (number_eq_zero_iff G).mp hzero
    subst G
    exact rigid_bot
  have hone : number G = 1 := by omega
  obtain ⟨D,hD,hdD,hcD⟩ := minimum_cycles heven
  obtain ⟨H,rfl⟩ := Finset.card_eq_one.mp (hcD.trans hone)
  have hH := hD H (Finset.mem_singleton_self _)
  have he : H.spanningCoe = G := by
    apply SimpleGraph.edgeSet_injective
    simpa only [Finset.set_biUnion_singleton] using hdD.2
  obtain ⟨v⟩ := hH.1.nonempty
  exact rigid_of_cycle_hits heven v.val (cycle_hits_of_single_cycle H hH he v)

lemma rigid_of_evenMinimal_number_le_two (heven : ∀ v, Even (G.degree v))
    (hmin : EvenMinimal G) (hnum : number G ≤ 2) : CycleRigid G := by
  apply (rigid_iff_hereditarily_evenMinimal heven).mpr
  intro R hRG hR
  by_cases heq : R = G
  · subst R
    exact hmin
  have hc : R.edgeFinset.card < G.edgeFinset.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨SimpleGraph.edgeFinset_mono hRG,?_⟩
    intro he
    exact heq (SimpleGraph.edgeFinset_inj.mp he)
  have hlt := hmin R hRG hR hc
  have hRnum : number R ≤ 1 := by omega
  exact (rigid_of_number_le_one hR hRnum).evenMinimal hR

lemma rigid_of_saturated_evenMinimal (heven : ∀ v, Even (G.degree v))
    (hmin : EvenMinimal G) (v : V) (hsat : G.degree v = 2 * number G) : CycleRigid G := by
  have hacy := (StarCore.EvenMinimal.saturated_vertex hmin heven v hsat).1
  exact rigid_of_cycle_hits heven v ((StarCore.cycle_hits_iff_induce_acyclic v).mpr hacy)

#print axioms rigid_of_evenMinimal_number_le_two
#print axioms rigid_of_saturated_evenMinimal
end Erdos184Work.Rigidity



/-! Unit cycle-weight certificates. These are sufficient conditions; no
certificate is asserted for arbitrary rigid or even-minimal graphs. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleCertificates
open Critical Rigidity Weighted

set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- All simple cycles have weight exactly one. Edge weights may be signed. -/
def UnitCycleWeight (G : SimpleGraph V) (w : Sym2 V → ℝ) : Prop :=
  ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p = 1

lemma subfamily_weight (D : Finset G.Subgraph)
    (hp : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    (w : Sym2 V → ℝ) :
    (∑ e ∈ (subfamilyGraph D).edgeFinset, w e) =
      ∑ H ∈ D, ∑ e ∈ H.spanningCoe.edgeFinset, w e := by
  have hcover : (subfamilyGraph D).edgeFinset =
      D.biUnion (fun H => H.spanningCoe.edgeFinset) := by
    ext e
    simpa only [Finset.mem_biUnion, SimpleGraph.mem_edgeFinset,
      Set.mem_iUnion, exists_prop] using Set.ext_iff.mp (subfamilyGraph_edges D) e
  have hdis : (D : Set G.Subgraph).PairwiseDisjoint
      (fun H => H.spanningCoe.edgeFinset) := by
    intro H hH K hK hne
    apply Finset.disjoint_left.mpr
    intro e heH heK
    exact Set.disjoint_left.mp (hp hH hK hne)
      (SimpleGraph.mem_edgeFinset.mp heH) (SimpleGraph.mem_edgeFinset.mp heK)
  rw [hcover, Finset.sum_biUnion hdis]

lemma cycle_edge_weight {u : V} (p : G.Walk u u) (hp : p.IsCycle) (w : Sym2 V → ℝ) :
    (∑ e ∈ p.toSubgraph.spanningCoe.edgeFinset, w e) = walkWeight w p := by
  have he : p.toSubgraph.spanningCoe.edgeFinset = p.edges.toFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, List.mem_toFinset]
    exact p.mem_edges_toSubgraph
  rw [he, List.sum_toFinset _ hp.isTrail.edges_nodup]
  rfl

lemma UnitCycleWeight.piece_weight {w : Sym2 V → ℝ} (hw : UnitCycleWeight G w)
    (H : G.Subgraph) (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    (∑ e ∈ H.spanningCoe.edgeFinset, w e) = 1 := by
  obtain ⟨v⟩ := hH.1.nonempty
  obtain ⟨p,hp,hpH⟩ := LongRing.regular_cycle_walk_at H hH.1 (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hH.2) v.val v.property
  have he := cycle_edge_weight p hp w
  rw [hpH] at he
  exact he.trans (hw v.val p hp)

lemma UnitCycleWeight.card_eq_total {w : Sym2 V → ℝ} (hw : UnitCycleWeight G w)
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdD : IsDecomposition G D) : (D.card : ℝ) = ∑ e ∈ G.edgeFinset, w e := by
  have hgraph : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdD.2)
  have h := subfamily_weight D hdD.1 w
  rw [hgraph] at h
  rw [h]
  simpa using (Finset.sum_congr rfl (fun H hH => hw.piece_weight H (hD H hH))).symm

lemma UnitCycleWeight.number_eq_total {w : Sym2 V → ℝ} (hw : UnitCycleWeight G w)
    (heven : ∀ v, Even (G.degree v)) : (number G : ℝ) = ∑ e ∈ G.edgeFinset, w e := by
  obtain ⟨D,hD,hdD,hcD⟩ := minimum_cycles heven
  simpa only [hcD] using hw.card_eq_total D hD hdD

lemma UnitCycleWeight.rigid {w : Sym2 V → ℝ} (hw : UnitCycleWeight G w)
    (heven : ∀ v, Even (G.degree v)) : CycleRigid G := by
  intro D hD hdD
  have h := (hw.card_eq_total D hD hdD).trans (hw.number_eq_total heven).symm
  exact_mod_cast h

lemma UnitCycleWeight.number_le {w : Sym2 V → ℝ} (hw : UnitCycleWeight G w)
    (heven : ∀ v, Even (G.degree v)) (hedge : ∀ e ∈ G.edgeSet, w e ≤ 1) :
    number G ≤ Fintype.card V - 1 := by
  have hb := signed_total_weight_le G w 1 (by norm_num) hedge
    (fun u p hp => (hw u p hp).le)
  rw [one_mul,← hw.number_eq_total heven] at hb
  exact_mod_cast hb

omit [Fintype V] in
lemma UnitCycleWeight.mono {w : Sym2 V → ℝ} (hw : UnitCycleWeight G w)
    {R : SimpleGraph V} (hRG : R ≤ G) : UnitCycleWeight R w := by
  intro u p hp
  simpa only [walkWeight,Walk.edges_mapLe_eq_edges] using
    hw u (p.mapLe hRG) (hp.mapLe hRG)

omit [Fintype V] in
lemma constant_length_certificate (L : ℕ) (hL : 0 < L)
    (hlen : ∀ u (p : G.Walk u u), p.IsCycle → p.length = L) :
    UnitCycleWeight G (fun _ => (L : ℝ)⁻¹) := by
  intro u p hp
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hL)
  simp [walkWeight, List.map_const', hlen u p hp, hL0]

lemma constant_length_rigid_and_bound (heven : ∀ v, Even (G.degree v))
    (L : ℕ) (hL : 0 < L)
    (hlen : ∀ u (p : G.Walk u u), p.IsCycle → p.length = L) :
    CycleRigid G ∧ number G ≤ Fintype.card V - 1 := by
  have hw := constant_length_certificate L hL hlen
  refine ⟨hw.rigid heven, hw.number_le heven ?_⟩
  intro e he
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  exact inv_le_one_of_one_le₀ hL1

/-- A bounded unit-cycle weighting on every minimal even core would prove a
linear bound. This hypothesis is not established here. -/
lemma even_number_bound_of_core_certificates
    (hcert : ∀ R : SimpleGraph V, (∀ v, Even (R.degree v)) → EvenCore.EvenMinimal R →
      ∃ w : Sym2 V → ℝ, UnitCycleWeight R w ∧ (∀ e ∈ R.edgeSet, w e ≤ 1))
    (heven : ∀ v, Even (G.degree v)) : number G ≤ Fintype.card V - 1 := by
  obtain ⟨R,_,hR,hnum,hmin,_⟩ := EvenCore.exists_even_minimal_core G heven
  obtain ⟨w,hw,he⟩ := hcert R (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hR v) hmin
  rw [← hnum]
  exact hw.number_le (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hR v) he

/-- Give each edge incident with v weight one half, and all other edges zero. -/
noncomputable def feedbackWeight (v : V) (e : Sym2 V) : ℝ := if v ∈ e then 1 / 2 else 0

lemma feedbackWeight_total (R : SimpleGraph V) (v : V) :
    (∑ e ∈ R.edgeFinset, feedbackWeight v e) = (R.degree v : ℝ) / 2 := by
  calc
    _ = ∑ e ∈ R.incidenceFinset v, (1 / 2 : ℝ) := by
      rw [SimpleGraph.incidenceFinset_eq_filter, Finset.sum_filter]
      rfl
    _ = _ := by simp [SimpleGraph.card_incidenceFinset_eq_degree, div_eq_mul_inv]

lemma feedbackWeight_certificate (v : V)
    (hhit : ∀ u (p : G.Walk u u), p.IsCycle → v ∈ p.support) :
    UnitCycleWeight G (feedbackWeight v) := by
  intro u p hp
  have hreg := (cycle_coe_regular G hp).2
  have hd := regular_two_spanning_degree p.toSubgraph (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hreg) v
  have hv := p.mem_verts_toSubgraph.mpr (hhit u p hp)
  rw [if_pos hv] at hd
  rw [← cycle_edge_weight p hp, feedbackWeight_total, hd]
  norm_num

omit [Fintype V] in
lemma feedbackWeight_le_one (v : V) (e : Sym2 V) : feedbackWeight v e ≤ 1 := by
  unfold feedbackWeight
  split_ifs <;> norm_num

lemma saturated_core_certificate (heven : ∀ v, Even (G.degree v))
    (hmin : EvenCore.EvenMinimal G) (v : V) (hsat : G.degree v = 2 * number G) :
    ∃ w : Sym2 V → ℝ, UnitCycleWeight G w ∧ (∀ e ∈ G.edgeSet, w e ≤ 1) := by
  have hacy := (StarCore.EvenMinimal.saturated_vertex hmin heven v hsat).1
  exact ⟨feedbackWeight v, feedbackWeight_certificate v
    ((StarCore.cycle_hits_iff_induce_acyclic v).mpr hacy),
    fun e _ => feedbackWeight_le_one v e⟩

/-- A half-weight certificate supported on the edges of R. -/
noncomputable def markerWeight (R : SimpleGraph V) (e : Sym2 V) : ℝ :=
  if e ∈ R.edgeSet then 1 / 2 else 0

lemma markerWeight_total {R : SimpleGraph V} (hRG : R ≤ G) :
    (∑ e ∈ G.edgeFinset, markerWeight R e) = (R.edgeFinset.card : ℝ) / 2 := by
  have hsum := Finset.sum_subset (SimpleGraph.edgeFinset_mono hRG)
    (f := markerWeight R) (by
      intro e _ he
      exact if_neg (fun h => he (SimpleGraph.mem_edgeFinset.mpr h)))
  rw [← hsum]
  calc
    _ = ∑ e ∈ R.edgeFinset, (1 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      exact if_pos (SimpleGraph.mem_edgeFinset.mp he)
    _ = _ := by simp [div_eq_mul_inv]

omit [Fintype V] in
lemma marker_certificate_acyclic {R : SimpleGraph V} (hRG : R ≤ G)
    (hw : UnitCycleWeight G (markerWeight R)) : R.IsAcyclic := by
  intro u p hp
  have h := hw u (p.mapLe hRG) (hp.mapLe hRG)
  have hmap : p.edges.map (markerWeight R) = p.edges.map (fun _ => (1 / 2 : ℝ)) := by
    apply List.map_congr_left
    intro e he
    exact if_pos (p.edges_subset_edgeSet he)
  simp only [walkWeight,Walk.edges_mapLe_eq_edges,hmap] at h
  simp only [List.map_const',Walk.length_edges,List.sum_replicate,nsmul_eq_mul] at h
  have hlen : (3 : ℝ) ≤ p.length := by exact_mod_cast hp.three_le_length
  linarith

lemma acyclic_edge_count_pred (R : SimpleGraph V) (hR : R.IsAcyclic) :
    R.edgeFinset.card ≤ Fintype.card V - 1 := by
  by_cases hn : Fintype.card V = 0
  · have h := acyclic_card_edges_le R hR
    omega
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
    have h := acyclic_card_edges_lt R hR
    omega

lemma marker_certificate_number_bound (heven : ∀ v, Even (G.degree v))
    {R : SimpleGraph V} (hRG : R ≤ G) (hw : UnitCycleWeight G (markerWeight R)) :
    2 * number G = R.edgeFinset.card ∧ 2 * number G ≤ Fintype.card V - 1 := by
  have h := hw.number_eq_total heven
  rw [markerWeight_total hRG] at h
  have heqR : (2 : ℝ) * number G = R.edgeFinset.card := by linarith
  have heq : 2 * number G = R.edgeFinset.card := by exact_mod_cast heqR
  exact ⟨heq,heq.le.trans (acyclic_edge_count_pred R (marker_certificate_acyclic hRG hw))⟩

/-- This stronger certificate on every minimal core would yield the Hajós-type
half-linear bound for all even simple graphs. Existence is left as an explicit
hypothesis, not promoted to a theorem. -/
lemma even_half_bound_of_core_marker_certificates
    (hcert : ∀ R : SimpleGraph V, (∀ v, Even (R.degree v)) → EvenCore.EvenMinimal R →
      ∃ F : SimpleGraph V, F ≤ R ∧ UnitCycleWeight R (markerWeight F))
    (heven : ∀ v, Even (G.degree v)) : 2 * number G ≤ Fintype.card V - 1 := by
  obtain ⟨R,_,hR,hnum,hmin,_⟩ := EvenCore.exists_even_minimal_core G heven
  obtain ⟨F,hFR,hw⟩ := hcert R (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hR v) hmin
  rw [← hnum]
  exact (marker_certificate_number_bound (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hR v) hFR hw).2

universe u

/-- The original asymptotic conclusion, conditional on a bounded unit-cycle
weight certificate for every even-minimal core. The certificate hypothesis
remains unproved. -/
lemma asymptotic_of_core_certificates
    (hcert : ∀ {W : Type u} [Fintype W] (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) → EvenCore.EvenMinimal R →
      ∃ w : Sym2 W → ℝ, UnitCycleWeight R w ∧ (∀ e ∈ R.edgeSet, w e ≤ 1)) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition R D ∧
        (D.card : ℝ) ≤ f (Fintype.card W) := by
  apply asymptotic_iff_even_cycle_uniform.mpr
  refine ⟨1,?_⟩
  intro W _ _ R hR
  obtain ⟨D,hD,hdD,hcD⟩ := minimum_cycles hR
  refine ⟨D,hD,hdD,?_⟩
  have hb := even_number_bound_of_core_certificates
    (fun S hS hmin => hcert S hS hmin) hR
  have hle : D.card ≤ Fintype.card W := by omega
  simpa only [one_mul] using (show (D.card : ℝ) ≤ (Fintype.card W : ℝ) by exact_mod_cast hle)

#print axioms asymptotic_of_core_certificates
#print axioms marker_certificate_acyclic
#print axioms marker_certificate_number_bound
#print axioms even_half_bound_of_core_marker_certificates

end Erdos184Work.CycleCertificates

namespace Erdos184Work.CycleDeletion
open Critical Rigidity CycleCertificates

lemma base_cycle_length {u : Fin 9} (p : baseGraph.Walk u u) (hp : p.IsCycle) :
    p.length = 3 := by
  have hP : IsCycleOrEdge p.toSubgraph.coe := Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular baseGraph hp)
  have hle := base_piece_edge_bound p.toSubgraph hP
  have he := cycle_edge_count baseGraph hp
  have hs := subgraph_edge_card p.toSubgraph
  have hthree := hp.three_le_length
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hle he hs
  omega

lemma base_rigid : CycleRigid baseGraph := by
  apply (constant_length_certificate 3 (by omega) (fun _ p hp => base_cycle_length p hp)).rigid
  intro v
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    using base_even v

lemma base_evenMinimal : EvenCore.EvenMinimal baseGraph := by
  apply base_rigid.evenMinimal
  intro v
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    using base_even v

/-- The smaller graph in the existing cycle-deletion obstruction is itself
rigid and even-minimal. This does not refute rigidity of minimal cores. -/
lemma cycle_deletion_to_rigid_core :
    CycleRigid (fullGraph \ removedCycle.toSubgraph.spanningCoe) ∧
    EvenCore.EvenMinimal (fullGraph \ removedCycle.toSubgraph.spanningCoe) ∧
    number fullGraph < number (fullGraph \ removedCycle.toSubgraph.spanningCoe) := by
  rw [remaining_graph]
  exact ⟨base_rigid,base_evenMinimal,by rw [full_number,base_number]; omega⟩

#print axioms base_rigid
#print axioms cycle_deletion_to_rigid_core
end Erdos184Work.CycleDeletion

namespace Erdos184Work.CycleCertificates
#print axioms UnitCycleWeight.rigid
#print axioms UnitCycleWeight.number_le
#print axioms constant_length_rigid_and_bound
#print axioms even_number_bound_of_core_certificates
end Erdos184Work.CycleCertificates



/-! A seven-vertex obstruction to diminishing returns for cycle addition.
This is not a counterexample to Erdős 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.DiminishingReturns
open Critical Rigidity EvenCore

set_option maxHeartbeats 2000000

lemma number_le_cycle_family {V I : Type*} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (u : I → V) (p : ∀ i, G.Walk (u i) (u i))
    (hp : ∀ i, (p i).IsCycle)
    (hdis : ∀ i j, i ≠ j → Disjoint (p i).edges.toFinset (p j).edges.toFinset)
    (hcover : ∀ a b, G.Adj a b ↔ ∃ i, s(a,b) ∈ (p i).edges.toFinset) :
    number G ≤ Fintype.card I := by
  let piece := fun i => (p i).toSubgraph
  have he : ∀ i, (piece i).edgeSet = ((p i).edges.toFinset : Set (Sym2 V)) := by
    intro i
    ext e
    exact (p i).mem_edges_toSubgraph.trans List.mem_toFinset.symm
  have hdec := Compression.finite_family_decomposition piece (fun i => (p i).edges.toFinset)
    he hdis hcover
  have hprop : ∀ H ∈ Finset.univ.image piece, IsCycleOrEdge H.coe := by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact Or.inl (by
      simpa only [piece,SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using cycle_coe_regular G (hp i))
  exact (number_le _ hprop hdec).trans (by simpa using Finset.card_image_le (s := Finset.univ) (f := piece))

def baseEdges : Finset (Sym2 (Fin 7)) :=
  {s(0,1),s(0,2),s(1,2),s(0,3),s(3,4),s(1,4),s(0,5),s(5,6),s(1,6)}
def leftEdges : Finset (Sym2 (Fin 7)) := {s(2,3),s(3,5),s(2,5)}
def rightEdges : Finset (Sym2 (Fin 7)) := {s(2,4),s(4,6),s(2,6)}
def base : SimpleGraph (Fin 7) := SimpleGraph.fromEdgeSet baseEdges
def left : SimpleGraph (Fin 7) := SimpleGraph.fromEdgeSet leftEdges
def right : SimpleGraph (Fin 7) := SimpleGraph.fromEdgeSet rightEdges
def withLeft : SimpleGraph (Fin 7) := base ⊔ left
def withRight : SimpleGraph (Fin 7) := base ⊔ right
def full : SimpleGraph (Fin 7) := base ⊔ left ⊔ right

instance : DecidableRel base.Adj := by unfold base; infer_instance
instance : DecidableRel left.Adj := by unfold left; infer_instance
instance : DecidableRel right.Adj := by unfold right; infer_instance
instance : DecidableRel withLeft.Adj := by unfold withLeft; infer_instance
instance : DecidableRel withRight.Adj := by unfold withRight; infer_instance
instance : DecidableRel full.Adj := by unfold full; infer_instance

lemma base_even : ∀ v, Even (base.degree v) := by decide
lemma left_even : ∀ v, Even (left.degree v) := by decide
lemma right_even : ∀ v, Even (right.degree v) := by decide
lemma full_even : ∀ v, Even (full.degree v) := by decide
lemma base_degree : base.degree 0 = 4 := by decide
lemma withLeft_degree : withLeft.degree 0 = 4 := by decide
lemma full_degree : full.degree 2 = 6 := by decide

lemma base_connected : base.Connected := by
  have hr : ∀ v : Fin 7, v = 0 ∨ base.Adj v 0 ∨ ∃ w, base.Adj v w ∧ base.Adj w 0 := by decide
  have hreach : ∀ v : Fin 7, base.Reachable v 0 := by
    intro v
    rcases hr v with rfl | h | ⟨w,h,h'⟩
    · exact .refl _
    · exact h.reachable
    · exact h.reachable.trans h'.reachable
  exact ⟨fun u v => (hreach u).trans (hreach v).symm⟩

abbrev Rest := {v : Fin 7 // v ≠ 0}
def rest : SimpleGraph Rest := base.induce {v | v ≠ 0}
instance : DecidableRel rest.Adj := by unfold rest; infer_instance

def root : Rest := ⟨1,by decide⟩
lemma rest_connected : rest.Connected := by
  letI : Nonempty Rest := ⟨root⟩
  have hr : ∀ v : Rest, v = root ∨ rest.Adj v root ∨
      ∃ w, rest.Adj v w ∧ rest.Adj w root := by decide
  have hreach : ∀ v : Rest, rest.Reachable v root := by
    intro v
    rcases hr v with rfl | h | ⟨w,h,h'⟩
    · exact .refl _
    · exact h.reachable
    · exact h.reachable.trans h'.reachable
  exact ⟨fun u v => (hreach u).trans (hreach v).symm⟩

lemma rest_tree : rest.IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨rest_connected,?_⟩
  simp only [Nat.card_eq_fintype_card]
  decide

lemma base_core_and_number : EvenMinimal base ∧ number base = 2 ∧ CycleRigid base := by
  have he : ∀ v, Even (base.degree v) := by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using base_even v
  have ha : (base.induce {0}ᶜ).IsAcyclic := rest_tree.IsAcyclic
  obtain ⟨hm,hd⟩ := (StarCharacterization.saturated_minimal_iff_feedback_vertex (G := base) (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using he v) 0).mpr ha
  have hdeg := base_degree
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hdeg
  refine ⟨hm,by omega,?_⟩
  exact rigid_of_cycle_hits (G := base) (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using he v) 0 ((StarCore.cycle_hits_iff_induce_acyclic 0).mpr ha)

def first : withLeft.Walk 0 0 :=
  .cons (show withLeft.Adj 0 5 by decide)
  (.cons (show withLeft.Adj 5 3 by decide)
  (.cons (show withLeft.Adj 3 2 by decide)
  (.cons (show withLeft.Adj 2 1 by decide)
  (.cons (show withLeft.Adj 1 0 by decide) .nil))))
def second : withLeft.Walk 0 0 :=
  .cons (show withLeft.Adj 0 3 by decide)
  (.cons (show withLeft.Adj 3 4 by decide)
  (.cons (show withLeft.Adj 4 1 by decide)
  (.cons (show withLeft.Adj 1 6 by decide)
  (.cons (show withLeft.Adj 6 5 by decide)
  (.cons (show withLeft.Adj 5 2 by decide)
  (.cons (show withLeft.Adj 2 0 by decide) .nil))))))

lemma first_cycle : first.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide
lemma second_cycle : second.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def pair : Fin 2 → withLeft.Walk 0 0 := ![first,second]
lemma withLeft_number : number withLeft = 2 := by
  have hhi := number_le_cycle_family (fun _ : Fin 2 => (0 : Fin 7)) pair (by
    intro i
    fin_cases i
    · exact first_cycle
    · exact second_cycle) (by
      simp only [Finset.disjoint_left,List.mem_toFinset]
      decide) (by
      simp only [List.mem_toFinset]
      decide)
  have hlo := StarCore.number_degree_bound withLeft 0
  have hd := withLeft_degree
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hlo hd
  simp only [Fintype.card_fin] at hhi
  omega

def reflect : Equiv.Perm (Fin 7) where
  toFun := ![1,0,2,4,3,6,5]
  invFun := ![1,0,2,4,3,6,5]
  left_inv := by decide
  right_inv := by decide

def reflectIso : withLeft ≃g withRight where
  toEquiv := reflect
  map_rel_iff' := by
    intro u v
    revert u v
    decide

lemma withRight_number : number withRight = 2 :=
  (BlockRestriction.number_eq_of_iso reflectIso).symm.trans withLeft_number

def triangleLeft : full.Walk 2 2 :=
  .cons (show full.Adj 2 3 by decide)
  (.cons (show full.Adj 3 5 by decide)
  (.cons (show full.Adj 5 2 by decide) .nil))
def triangleRight : full.Walk 2 2 :=
  .cons (show full.Adj 2 4 by decide)
  (.cons (show full.Adj 4 6 by decide)
  (.cons (show full.Adj 6 2 by decide) .nil))
lemma triangleLeft_cycle : triangleLeft.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide
lemma triangleRight_cycle : triangleRight.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide
lemma triangleRight_graph : triangleRight.toSubgraph.spanningCoe = right := by
  ext u v
  change s(u,v) ∈ triangleRight.toSubgraph.edgeSet ↔ right.Adj u v
  rw [triangleRight.mem_edges_toSubgraph]
  revert u v
  decide
lemma triangleLeft_graph : triangleLeft.toSubgraph.spanningCoe = left := by
  ext u v
  change s(u,v) ∈ triangleLeft.toSubgraph.edgeSet ↔ left.Adj u v
  rw [triangleLeft.mem_edges_toSubgraph]
  revert u v
  decide
lemma delete_right : full \ triangleRight.toSubgraph.spanningCoe = withLeft := by
  rw [triangleRight_graph]
  ext u v
  revert u v
  decide
lemma full_number : number full = 3 := by
  have hhi := EvenCore.number_restore_cycle triangleRight_cycle
  rw [delete_right,withLeft_number] at hhi
  have hlo := StarCore.number_degree_bound full 2
  have hd := full_degree
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hlo hd
  omega

lemma increments_disjoint :
    Disjoint base.edgeSet left.edgeSet ∧ Disjoint base.edgeSet right.edgeSet ∧
      Disjoint left.edgeSet right.edgeSet := by
  repeat' apply And.intro
  all_goals
    rw [Set.disjoint_left]
    decide

/-- Strict failure of the submodular inequality on three edge-disjoint even
subgraphs. The shared base is connected, rigid, and even-minimal. -/
lemma strict_failure :
    base.Connected ∧ CycleRigid base ∧ EvenMinimal base ∧
    (∀ v, Even (base.degree v)) ∧ (∀ v, Even (left.degree v)) ∧
    (∀ v, Even (right.degree v)) ∧
    Disjoint base.edgeSet left.edgeSet ∧ Disjoint base.edgeSet right.edgeSet ∧
    Disjoint left.edgeSet right.edgeSet ∧
    number (base ⊔ left) + number (base ⊔ right) <
      number base + number (base ⊔ left ⊔ right) := by
  refine ⟨base_connected,base_core_and_number.2.2,base_core_and_number.1,
    base_even,left_even,right_even,increments_disjoint.1,increments_disjoint.2.1,
    increments_disjoint.2.2,?_⟩
  change number withLeft + number withRight < number base + number full
  rw [withLeft_number,withRight_number,base_core_and_number.2.1,full_number]
  omega

def avoidingCycle : full.Walk 0 0 :=
  .cons (show full.Adj 0 3 by decide)
  (.cons (show full.Adj 3 4 by decide)
  (.cons (show full.Adj 4 1 by decide)
  (.cons (show full.Adj 1 0 by decide) .nil)))
lemma avoidingCycle_isCycle : avoidingCycle.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

/-- The final graph in this obstruction is NOT even-minimal. The example
therefore does not disprove the proposed rigidity of minimal cores. -/
lemma full_not_evenMinimal : ¬ EvenMinimal full := by
  intro hmin
  have he : ∀ v, Even (full.degree v) := by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using full_even v
  have hs : full.degree 2 = 2 * number full := by rw [full_degree,full_number]
  have ha := (StarCore.EvenMinimal.saturated_vertex (G := full) hmin (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using he v) 2 (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hs)).1
  have hhit := (StarCore.cycle_hits_iff_induce_acyclic (G := full) 2).mpr ha
  have h := hhit 0 avoidingCycle avoidingCycle_isCycle
  exact (show (2 : Fin 7) ∉ avoidingCycle.support by decide) h

lemma full_not_rigid : ¬ CycleRigid full := by
  intro hr
  apply full_not_evenMinimal
  apply hr.evenMinimal
  intro v
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    using full_even v

#print axioms full_not_evenMinimal
#print axioms base_core_and_number
#print axioms full_number
#print axioms strict_failure
end Erdos184Work.DiminishingReturns



/-! Mod-two cycle/cut duality and the cut structure of marker certificates.
Certificate existence for arbitrary minimal cores remains unproved. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleCertificates
open Weighted Critical

variable {V : Type*} {G R : SimpleGraph V}

lemma marker_certificate_complement_acyclic
    (hw : UnitCycleWeight G (markerWeight R)) : (G \ R).IsAcyclic := by
  intro u p hp
  have h := hw u (p.mapLe sdiff_le) (hp.mapLe sdiff_le)
  have hmap : p.edges.map (markerWeight R) = p.edges.map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro e he
    have hnot : e ∉ R.edgeSet := by
      have hmem := p.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_sdiff] at hmem
      exact hmem.2
    exact if_neg hnot
  simp only [walkWeight, Walk.edges_mapLe_eq_edges, hmap] at h
  simpa using h

lemma marker_certificate_edge_bound [Fintype V] (hRG : R ≤ G)
    (hw : UnitCycleWeight G (markerWeight R)) :
    G.edgeFinset.card ≤ 2 * (Fintype.card V - 1) := by
  have hR := acyclic_edge_count_pred R (marker_certificate_acyclic hRG hw)
  have hcomp := acyclic_edge_count_pred (G \ R) (marker_certificate_complement_acyclic hw)
  have hsum : (G \ R).edgeFinset.card + R.edgeFinset.card = G.edgeFinset.card := by
    rw [SimpleGraph.edgeFinset_sdiff]
    exact Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hRG)
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hR hcomp hsum ⊢
  omega

end Erdos184Work.CycleCertificates

namespace Erdos184Work.CutParity
variable {V : Type*} {G : SimpleGraph V} {u v z : V}

def weight (w : Sym2 V → ZMod 2) (p : G.Walk u v) : ZMod 2 :=
  (p.edges.map w).sum

@[simp] lemma weight_nil (w : Sym2 V → ZMod 2) (u : V) :
    weight w (.nil : G.Walk u u) = 0 := by simp [weight]

@[simp] lemma weight_cons (w : Sym2 V → ZMod 2) (h : G.Adj u v) (p : G.Walk v z) :
    weight w (.cons h p) = w s(u,v) + weight w p := by simp [weight]

@[simp] lemma weight_append (w : Sym2 V → ZMod 2) (p : G.Walk u v) (q : G.Walk v z) :
    weight w (p.append q) = weight w p + weight w q := by simp [weight]

@[simp] lemma weight_reverse (w : Sym2 V → ZMod 2) (p : G.Walk u v) :
    weight w p.reverse = weight w p := by simp [weight]

@[simp] lemma weight_copy (w : Sym2 V → ZMod 2) (p : G.Walk u v)
    {u' v' : V} (hu : u = u') (hv : v = v') : weight w (p.copy hu hv) = weight w p := by
  subst_vars; rfl

lemma self_add (a : ZMod 2) : a + a = 0 := CharTwo.add_self_eq_zero a

lemma close_path_weight_zero (w : Sym2 V → ZMod 2)
    (hw : ∀ x (p : G.Walk x x), p.IsCycle → weight w p = 0)
    (p : G.Walk v u) (hp : p.IsPath) (h : G.Adj u v) :
    w s(u,v) + weight w p = 0 := by
  by_cases hn : 2 ≤ p.length
  · have he : s(u,v) ∉ p.edges := by
      rw [Sym2.eq_swap]
      exact endpoint_edge_notMem hp hn
    exact hw u (.cons h p) ((Walk.cons_isCycle_iff p h).mpr ⟨hp,he⟩)
  · cases p with
    | nil => exact (h.ne rfl).elim
    | cons h' p =>
      have hl : p.length = 0 := by simp only [Walk.length_cons] at hn; omega
      have hp0 : p.Nil := Walk.nil_iff_length_eq.mpr hl
      cases p with
      | nil =>
        simp only [weight_cons, weight_nil, add_zero, Sym2.eq_swap]
        exact self_add _
      | cons _ _ => simp only [Walk.length_cons] at hl; omega

lemma weight_bypass (w : Sym2 V → ZMod 2)
    (hw : ∀ x (p : G.Walk x x), p.IsCycle → weight w p = 0)
    (p : G.Walk u v) : weight w p.bypass = weight w p := by
  induction p with
  | nil => rfl
  | @cons u v z h p ih =>
    simp only [Walk.bypass]
    split_ifs with hs
    · have hzero := close_path_weight_zero w hw (p.bypass.takeUntil u hs)
        (p.bypass_isPath.takeUntil hs) h
      have hsum := congrArg (weight w) (p.bypass.take_spec hs)
      simp only [weight_append] at hsum
      rw [weight_cons, ← ih, ← hsum, ← add_assoc, hzero, zero_add]
    · simpa only [weight_cons, ih]

lemma closed_weight_zero (w : Sym2 V → ZMod 2)
    (hw : ∀ x (p : G.Walk x x), p.IsCycle → weight w p = 0)
    (p : G.Walk u u) : weight w p = 0 := by
  rw [← weight_bypass w hw p]
  have hp : p.bypass = .nil := (Walk.isPath_iff_eq_nil _).mp p.bypass_isPath
  rw [hp, weight_nil]

lemma weight_eq_of_endpoints (w : Sym2 V → ZMod 2)
    (hw : ∀ x (p : G.Walk x x), p.IsCycle → weight w p = 0)
    (p q : G.Walk u v) : weight w p = weight w q := by
  have h := closed_weight_zero w hw (p.append q.reverse)
  simpa only [weight_append, weight_reverse, CharTwo.add_eq_iff_eq_add, zero_add] using h

/-- A mod-two edge function vanishing on every simple cycle is a vertex coboundary. -/
lemma exists_label (w : Sym2 V → ZMod 2)
    (hw : ∀ x (p : G.Walk x x), p.IsCycle → weight w p = 0) :
    ∃ label : V → ZMod 2, ∀ u v, G.Adj u v → w s(u,v) = label u + label v := by
  let root : V → V := fun v => (G.connectedComponentMk v).out
  have hr : ∀ v, G.Reachable (root v) v := by
    intro v
    exact ConnectedComponent.exact (Quot.out_eq (G.connectedComponentMk v))
  let p : ∀ v, G.Walk (root v) v := fun v => (hr v).some
  refine ⟨fun v => weight w (p v), ?_⟩
  intro u v huv
  have heq : root u = root v := congrArg Quot.out
    (ConnectedComponent.connectedComponentMk_eq_of_adj huv)
  have h := weight_eq_of_endpoints w hw ((p u).append (.cons huv .nil))
      ((p v).copy heq.symm rfl)
  simp only [weight_append, weight_cons, weight_nil, add_zero, weight_copy] at h
  rw [add_comm, CharTwo.add_eq_iff_eq_add, add_comm] at h
  exact h

#print axioms exists_label
end Erdos184Work.CutParity

namespace Erdos184Work.CycleCertificates
open CutParity
variable {V : Type*} {G R : SimpleGraph V} {u v : V}

noncomputable def markerCount (R : SimpleGraph V) (p : G.Walk u v) : ℕ :=
  (p.edges.filter (fun e => e ∈ R.edgeSet)).length

lemma marker_weight_count (R : SimpleGraph V) (p : G.Walk u v) :
    Weighted.walkWeight (markerWeight R) p = (markerCount R p : ℝ) / 2 := by
  induction p with
  | nil => simp [markerCount]
  | @cons u v z h p ih =>
    simp only [Weighted.walkWeight_cons, markerWeight, markerCount, Walk.edges_cons,
      List.filter_cons] at *
    split_ifs <;> simp_all <;> ring

lemma marker_parity_count (R : SimpleGraph V) (p : G.Walk u v) :
    weight (fun e => if e ∈ R.edgeSet then 1 else 0) p = (markerCount R p : ZMod 2) := by
  induction p with
  | nil => simp [markerCount]
  | @cons u v z h p ih =>
    simp only [weight_cons, markerCount, Walk.edges_cons, List.filter_cons] at *
    split_ifs <;> simp_all [add_comm]

/-- Every marker certificate is the edge cut associated with a vertex labeling. -/
lemma marker_certificate_cut (hRG : R ≤ G) (hw : UnitCycleWeight G (markerWeight R)) :
    ∃ label : V → ZMod 2, ∀ u v,
      R.Adj u v ↔ G.Adj u v ∧ label u ≠ label v := by
  have hc : ∀ u (p : G.Walk u u), p.IsCycle →
      weight (fun e => if e ∈ R.edgeSet then 1 else 0) p = 0 := by
    intro u p hp
    have h := hw u p hp
    rw [marker_weight_count] at h
    have hn : markerCount R p = 2 := by
      have he : (markerCount R p : ℝ) = 2 := by linarith
      exact_mod_cast he
    rw [marker_parity_count, hn]
    exact CharTwo.two_eq_zero
  obtain ⟨label, hl⟩ := exists_label (fun e => if e ∈ R.edgeSet then 1 else 0) hc
  refine ⟨label, ?_⟩
  intro u v
  constructor
  · intro huv
    refine ⟨hRG huv, ?_⟩
    have h := hl u v (hRG huv)
    simp only [SimpleGraph.mem_edgeSet, if_pos huv] at h
    intro heq
    rw [heq, CharTwo.add_self_eq_zero] at h
    exact one_ne_zero h
  · rintro ⟨huv,hne⟩
    by_contra hnot
    have h := hl u v huv
    simp only [SimpleGraph.mem_edgeSet, if_neg hnot] at h
    apply hne
    simpa only [CharTwo.add_eq_iff_eq_add, zero_add] using h.symm

#print axioms marker_certificate_cut
#print axioms marker_certificate_edge_bound
end Erdos184Work.CycleCertificates



/-! A rigid graph for which every unit-cycle weighting has a negative edge.
This is an obstruction to marker-certificate existence, not to Erdős 184. -/
open SimpleGraph
namespace Erdos184Work.NegativeCertificate
open Weighted CycleCertificates Rigidity Critical
set_option maxRecDepth 4096
set_option maxHeartbeats 10000000

abbrev Vertex := Fin 13

def left : Fin 9 → Vertex := ![0,0,0,1,1,1,2,2,2]
def right : Fin 9 → Vertex := ![1,1,1,2,2,2,3,3,3]
def middle : Fin 9 → Vertex := ![4,5,6,7,8,9,10,11,12]
def branchEdges (i : Fin 9) : Finset (Sym2 Vertex) :=
  {s(left i,middle i),s(middle i,right i)}
def modelEdges (B : Finset (Fin 9)) (b : Bool) : Finset (Sym2 Vertex) :=
  B.biUnion branchEdges ∪ if b then {s(0,3)} else ∅
def model (B : Finset (Fin 9)) (b : Bool) : SimpleGraph Vertex :=
  .fromEdgeSet (modelEdges B b)
def graph : SimpleGraph Vertex := model Finset.univ true
instance (B : Finset (Fin 9)) (b : Bool) : DecidableRel (model B b).Adj := by
  unfold model; infer_instance
instance : DecidableRel graph.Adj := by unfold graph; infer_instance

def count (B : Finset (Fin 9)) (j : Fin 3) : ℕ :=
  (B.filter (fun i => i.val / 3 = j.val)).card

def intWeight (e : Sym2 Vertex) : ℤ :=
  if e = s(0,3) then -1 else
    if e ∈ Finset.univ.image (fun i => s(left i,middle i)) then 1 else 0
noncomputable def certWeight (e : Sym2 Vertex) : ℝ := (intWeight e : ℝ) / 2

open scoped Classical in
lemma even_subgraph_full_neighbors {V : Type*} [Fintype V]
    {G R : SimpleGraph V} (hRG : R ≤ G) (v : V) (he : Even (R.degree v))
    (hd : G.degree v = 2) {a : V} (ha : R.Adj v a) :
    ∀ b, G.Adj v b → R.Adj v b := by
  classical
  have hpos := ha.degree_pos_left
  have hle := R.degree_le_of_le (v := v) hRG
  have heq : R.degree v = G.degree v := by
    rw [Nat.even_iff] at he
    omega
  have hsub : R.neighborFinset v ⊆ G.neighborFinset v := by
    intro b hb
    exact (G.mem_neighborFinset v b).mpr (hRG ((R.mem_neighborFinset v b).mp hb))
  have hneigh : R.neighborFinset v = G.neighborFinset v :=
    Finset.eq_of_subset_of_card_le hsub heq.ge
  intro b hb
  apply (R.mem_neighborFinset v b).mp
  rw [hneigh]
  exact (G.mem_neighborFinset v b).mpr hb

open scoped Classical in
lemma cycle_endpoints_reachable {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u : V} (p : G.Walk u u) (hp : p.IsCycle) (a b : V)
    (ha : p.toSubgraph.spanningCoe.degree a ≠ 0)
    (hb : p.toSubgraph.spanningCoe.degree b ≠ 0) :
    p.toSubgraph.spanningCoe.Reachable a b := by
  classical
  have hr := (cycle_coe_regular G hp).2
  have hva : a ∈ p.toSubgraph.verts := by
    have h := regular_two_spanning_degree p.toSubgraph hr a
    split_ifs at h with hmem
    · exact hmem
    · exact (ha h).elim
  have hvb : b ∈ p.toSubgraph.verts := by
    have h := regular_two_spanning_degree p.toSubgraph hr b
    split_ifs at h with hmem
    · exact hmem
    · exact (hb h).elim
  obtain ⟨q⟩ := (cycle_coe_regular G hp).1.preconnected ⟨a,hva⟩ ⟨b,hvb⟩
  exact ⟨q.map ⟨Subtype.val, fun h => h⟩⟩

lemma branch_valid : ∀ i : Fin 9,
    graph.Adj (middle i) (left i) ∧ graph.Adj (middle i) (right i) ∧
    graph.degree (middle i) = 2 := by decide

lemma graph_edge_membership : ∀ e : Sym2 Vertex,
    e ∈ graph.edgeSet ↔ e = s(0,3) ∨ ∃ i : Fin 9, e ∈ branchEdges i := by decide

lemma model_edgeSet (B : Finset (Fin 9)) (b : Bool) :
    (model B b).edgeSet = (modelEdges B b : Set (Sym2 Vertex)) := by
  have hsub : (modelEdges B b : Set (Sym2 Vertex)) ⊆ graph.edgeSet := by
    intro e he
    simp only [Finset.mem_coe, modelEdges, Finset.mem_union, Finset.mem_biUnion] at he
    apply (graph_edge_membership e).mpr
    rcases he with ⟨i,hi,he⟩ | he
    · exact Or.inr ⟨i,he⟩
    · cases b <;> simp_all
  rw [model, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_diff, and_iff_left_iff_imp]
  intro he
  exact graph.edgeSet_subset_setOf_not_isDiag (hsub he)

open scoped Classical in
lemma even_subgraph_model {R : SimpleGraph Vertex} (hRG : R ≤ graph)
    (heven : ∀ v, Even (R.degree v)) :
    ∃ (B : Finset (Fin 9)) (b : Bool), R = model B b := by
  classical
  let B := Finset.univ.filter (fun i : Fin 9 => R.Adj (left i) (middle i))
  let b : Bool := decide (R.Adj 0 3)
  have hbr : ∀ i : Fin 9, R.Adj (left i) (middle i) ↔ R.Adj (middle i) (right i) := by
    intro i
    obtain ⟨hL,hR,hd⟩ := branch_valid i
    have hd' : graph.degree (middle i) = 2 := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hd
    constructor
    · intro h
      exact even_subgraph_full_neighbors hRG (middle i) (heven _) (by
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hd) h.symm _ hR
    · intro h
      exact (even_subgraph_full_neighbors hRG (middle i) (heven _) (by
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hd) h _ hL).symm
  refine ⟨B,b,SimpleGraph.edgeSet_injective ?_⟩
  rw [model_edgeSet]
  ext e
  constructor
  · intro he
    have hG := SimpleGraph.edgeSet_mono hRG he
    rcases (graph_edge_membership e).mp hG with rfl | ⟨i,hi⟩
    · have hb : b = true := by simpa [b] using he
      simp [modelEdges,hb]
    · have hB : i ∈ B := by
        simp only [B,Finset.mem_filter,Finset.mem_univ,true_and]
        simp only [branchEdges,Finset.mem_insert,Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact he
        · exact (hbr i).mpr he
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i,hB,hi⟩)
  · intro he
    simp only [Finset.mem_coe,modelEdges,Finset.mem_union,Finset.mem_biUnion] at he
    rcases he with ⟨i,hi,he⟩ | he
    · have hi' : R.Adj (left i) (middle i) := (Finset.mem_filter.mp hi).2
      simp only [branchEdges,Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hi'
      · exact (hbr i).mp hi'
    · have he' : e = s(0,3) ∧ b = true := by cases hb : b <;> simp_all
      rw [he'.1]
      simpa only [b,decide_eq_true_eq] using he'.2


lemma model_edgeFinset (B : Finset (Fin 9)) (b : Bool) :
    (model B b).edgeFinset = modelEdges B b := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset,model_edgeSet,Finset.mem_coe]

lemma branch_disjoint : ∀ i j : Fin 9, i ≠ j → Disjoint (branchEdges i) (branchEdges j) := by decide
lemma branch_no_closing : ∀ i : Fin 9, s(0,3) ∉ branchEdges i := by decide
lemma branch_edges_distinct : ∀ i : Fin 9, s(left i,middle i) ≠ s(middle i,right i) := by decide

lemma model_sum {M : Type*} [AddCommMonoid M] (w : Sym2 Vertex → M)
    (B : Finset (Fin 9)) (b : Bool) :
    (∑ e ∈ (model B b).edgeFinset, w e) =
      (∑ i ∈ B, (w s(left i,middle i) + w s(middle i,right i))) +
        (if b then w s(0,3) else 0) := by
  rw [model_edgeFinset,modelEdges,Finset.sum_union]
  · rw [Finset.sum_biUnion]
    · have hsum : (∑ i ∈ B, ∑ e ∈ branchEdges i, w e) =
          ∑ i ∈ B, (w s(left i,middle i) + w s(middle i,right i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [branchEdges,branch_edges_distinct i]
      rw [hsum]
      cases b <;> simp
    · intro i _ j _ hij
      exact branch_disjoint i j hij
  · cases b
    · simp
    · apply Finset.disjoint_singleton_right.mpr
      simp only [Finset.mem_biUnion,not_exists,not_and]
      exact fun i _ => branch_no_closing i

lemma counts_card (B : Finset (Fin 9)) : count B 0 + count B 1 + count B 2 = B.card := by
  simp only [count,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  fin_cases i <;> decide

lemma intWeight_branch : ∀ i : Fin 9,
    intWeight s(left i,middle i) + intWeight s(middle i,right i) = 1 := by decide
lemma model_weight_table (B : Finset (Fin 9)) (b : Bool) :
    (∑ e ∈ (model B b).edgeFinset, intWeight e) = (B.card : ℤ) - (if b then 1 else 0) := by
  rw [model_sum]
  simp only [intWeight_branch,Finset.sum_const]
  cases b <;> norm_num [intWeight,sub_eq_add_neg]

def incidence (v : Vertex) (e : Sym2 Vertex) : ℕ := if v ∈ e then 1 else 0

lemma degree_incidence (R : SimpleGraph Vertex) [DecidableRel R.Adj] (v : Vertex) :
    R.degree v = ∑ e ∈ R.edgeFinset, incidence v e := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  rw [SimpleGraph.incidenceFinset_eq_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
  rfl

lemma branch_incidence : ∀ i : Fin 9,
    (incidence 0 s(left i,middle i) + incidence 0 s(middle i,right i) =
      (if i.val / 3 = 0 then 1 else 0)) ∧
    (incidence 1 s(left i,middle i) + incidence 1 s(middle i,right i) =
      (if i.val / 3 = 0 then 1 else 0) + (if i.val / 3 = 1 then 1 else 0)) ∧
    (incidence 2 s(left i,middle i) + incidence 2 s(middle i,right i) =
      (if i.val / 3 = 1 then 1 else 0) + (if i.val / 3 = 2 then 1 else 0)) ∧
    (incidence 3 s(left i,middle i) + incidence 3 s(middle i,right i) =
      (if i.val / 3 = 2 then 1 else 0)) := by decide

lemma count_sum (B : Finset (Fin 9)) (j : Fin 3) :
    count B j = ∑ i ∈ B, if i.val / 3 = j.val then 1 else 0 := by
  simp only [count,Finset.card_eq_sum_ones,Finset.sum_filter]

lemma model_degree_table (B : Finset (Fin 9)) (b : Bool) :
    (model B b).degree 0 = count B 0 + (if b then 1 else 0) ∧
    (model B b).degree 1 = count B 0 + count B 1 ∧
    (model B b).degree 2 = count B 1 + count B 2 ∧
    (model B b).degree 3 = count B 2 + (if b then 1 else 0) := by
  have hd (v : Vertex) := degree_incidence (model B b) v
  simp only [model_sum] at hd
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have h3 := hd 3
  simp_rw [(branch_incidence _).1] at h0
  simp_rw [(branch_incidence _).2.1] at h1
  simp_rw [(branch_incidence _).2.2.1] at h2
  simp_rw [(branch_incidence _).2.2.2] at h3
  simp only [Finset.sum_add_distrib] at h1 h2
  simp only [count_sum,Fin.val_zero,Fin.val_one]
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h0 h1 h2 h3 ⊢
  cases b <;> simp_all [incidence]


def leftSide : Finset Vertex := {0,1,4,5,6}
lemma branch_crosses : ∀ (i : Fin 9) (u v : Vertex), s(u,v) ∈ branchEdges i →
    u ∈ leftSide → v ∉ leftSide → i.val / 3 = 1 := by decide

lemma model_no_crossing (B : Finset (Fin 9)) (hc : count B 1 = 0) :
    ¬ (model B false).Reachable 0 3 := by
  rintro ⟨p⟩
  obtain ⟨d,_,hd0,hd3⟩ := p.exists_boundary_dart (leftSide : Set Vertex) (by decide) (by decide)
  have hd : s(d.fst,d.snd) ∈ (model B false).edgeSet := d.adj
  rw [model_edgeSet] at hd
  simp only [Finset.mem_coe,modelEdges,Bool.false_eq_true,↓reduceIte,Finset.union_empty,
    Finset.mem_biUnion] at hd
  obtain ⟨i,hi,hie⟩ := hd
  have hci := branch_crosses i d.fst d.snd hie hd0 hd3
  have hn : 0 < count B 1 := Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hci⟩⟩
  omega

open scoped Classical in
lemma cycle_model_count {u : Vertex} (p : graph.Walk u u) (hp : p.IsCycle)
    (B : Finset (Fin 9)) (b : Bool) (heq : p.toSubgraph.spanningCoe = model B b) :
    B.card = if b then 3 else 2 := by
  classical
  have hdeg : ∀ v, (model B b).degree v = 0 ∨ (model B b).degree v = 2 := by
    intro v
    have h := regular_two_spanning_degree p.toSubgraph (cycle_coe_regular graph hp).2 v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h ⊢
    rw [heq] at h
    split_ifs at h <;> omega
  obtain ⟨h0,h1,h2,h3⟩ := model_degree_table B b
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hdeg h0 h1 h2 h3
  have d0 := hdeg 0
  have d1 := hdeg 1
  have d2 := hdeg 2
  have d3 := hdeg 3
  have hcard := counts_card B
  cases b with
  | true => simp only [↓reduceIte] at h0 h3 ⊢; omega
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,add_zero] at h0 h3 ⊢
    have hpos : 0 < B.card := by
      by_contra hn
      have hB : B = ∅ := Finset.card_eq_zero.mp (by omega)
      have hb : model B false = ⊥ := by simp [hB,model,modelEdges]
      have hc := cycle_edge_count graph hp
      simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hc
      rw [heq,hb] at hc
      simp at hc
      have hl := hp.three_le_length
      omega
    by_cases hm : count B 1 = 0
    · have hnot : ¬ (count B 0 = 2 ∧ count B 2 = 2) := by
        rintro ⟨hc0,hc2⟩
        apply model_no_crossing B hm
        apply (cycle_endpoints_reachable p hp 0 3 ?_ ?_).mono heq.le
        · simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
          rw [heq]
          omega
        · simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
          rw [heq]
          omega
      omega
    · omega

lemma model_weight_real (B : Finset (Fin 9)) (b : Bool) :
    (∑ e ∈ (model B b).edgeFinset, certWeight e) =
      ((B.card : ℝ) - (if b then 1 else 0)) / 2 := by
  have h := model_weight_table B b
  have hh := congrArg (fun z : ℤ => (z : ℝ)) h
  simp only [Int.cast_sum,Int.cast_sub,Int.cast_natCast] at hh
  simp only [certWeight,← Finset.sum_div]
  rw [hh]
  cases b <;> norm_num

lemma certificate : UnitCycleWeight graph certWeight := by
  classical
  intro u p hp
  obtain ⟨B,b,heq⟩ := even_subgraph_model p.toSubgraph.spanningCoe_le (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using cycle_spanning_even graph hp v)
  have hc := cycle_model_count p hp B b heq
  have he : p.toSubgraph.spanningCoe.edgeFinset = (model B b).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [heq]
  rw [← cycle_edge_weight p hp,he,model_weight_real,hc]
  cases b <;> norm_num

lemma graph_even : ∀ v, Even (graph.degree v) := by decide
lemma graph_rigid : CycleRigid graph := certificate.rigid (by
  intro v
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    using graph_even v)
lemma graph_minimal : EvenCore.EvenMinimal graph := graph_rigid.evenMinimal (by
  intro v
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    using graph_even v)
lemma graph_number : number graph = 4 := by
  have h := certificate.number_eq_total (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using graph_even v)
  have hs : (number graph : ℝ) = ∑ e ∈ graph.edgeFinset, certWeight e := by
    convert h using 1
    congr 1
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
  change (number graph : ℝ) = ∑ e ∈ (model Finset.univ true).edgeFinset, certWeight e at hs
  rw [model_weight_real] at hs
  norm_num at hs
  exact_mod_cast hs

#print axioms certificate
#print axioms graph_rigid
#print axioms graph_minimal
#print axioms graph_number
def local00 : graph.Walk 0 0 :=
  .cons (show graph.Adj 0 4 by decide) (.cons (show graph.Adj 4 1 by decide) (.cons (show graph.Adj 1 5 by decide) (.cons (show graph.Adj 5 0 by decide) (.nil))))

lemma local00_cycle : local00.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def local01 : graph.Walk 0 0 :=
  .cons (show graph.Adj 0 4 by decide) (.cons (show graph.Adj 4 1 by decide) (.cons (show graph.Adj 1 6 by decide) (.cons (show graph.Adj 6 0 by decide) (.nil))))

lemma local01_cycle : local01.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def local02 : graph.Walk 0 0 :=
  .cons (show graph.Adj 0 5 by decide) (.cons (show graph.Adj 5 1 by decide) (.cons (show graph.Adj 1 6 by decide) (.cons (show graph.Adj 6 0 by decide) (.nil))))

lemma local02_cycle : local02.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def local10 : graph.Walk 1 1 :=
  .cons (show graph.Adj 1 7 by decide) (.cons (show graph.Adj 7 2 by decide) (.cons (show graph.Adj 2 8 by decide) (.cons (show graph.Adj 8 1 by decide) (.nil))))

lemma local10_cycle : local10.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def local11 : graph.Walk 1 1 :=
  .cons (show graph.Adj 1 7 by decide) (.cons (show graph.Adj 7 2 by decide) (.cons (show graph.Adj 2 9 by decide) (.cons (show graph.Adj 9 1 by decide) (.nil))))

lemma local11_cycle : local11.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def local12 : graph.Walk 1 1 :=
  .cons (show graph.Adj 1 8 by decide) (.cons (show graph.Adj 8 2 by decide) (.cons (show graph.Adj 2 9 by decide) (.cons (show graph.Adj 9 1 by decide) (.nil))))

lemma local12_cycle : local12.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def local20 : graph.Walk 2 2 :=
  .cons (show graph.Adj 2 10 by decide) (.cons (show graph.Adj 10 3 by decide) (.cons (show graph.Adj 3 11 by decide) (.cons (show graph.Adj 11 2 by decide) (.nil))))

lemma local20_cycle : local20.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def local21 : graph.Walk 2 2 :=
  .cons (show graph.Adj 2 10 by decide) (.cons (show graph.Adj 10 3 by decide) (.cons (show graph.Adj 3 12 by decide) (.cons (show graph.Adj 12 2 by decide) (.nil))))

lemma local21_cycle : local21.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def local22 : graph.Walk 2 2 :=
  .cons (show graph.Adj 2 11 by decide) (.cons (show graph.Adj 11 3 by decide) (.cons (show graph.Adj 3 12 by decide) (.cons (show graph.Adj 12 2 by decide) (.nil))))

lemma local22_cycle : local22.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def globalCycle : graph.Walk 0 0 :=
  .cons (show graph.Adj 0 4 by decide) (.cons (show graph.Adj 4 1 by decide) (.cons (show graph.Adj 1 7 by decide) (.cons (show graph.Adj 7 2 by decide) (.cons (show graph.Adj 2 10 by decide) (.cons (show graph.Adj 10 3 by decide) (.cons (show graph.Adj 3 0 by decide) (.nil)))))))

lemma globalCycle_cycle : globalCycle.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

lemma every_unit_weight_negative (w : Sym2 Vertex → ℝ) (hw : UnitCycleWeight graph w) :
    w s(0,3) = -(1/2) := by
  have h00 := hw 0 local00 local00_cycle
  have h01 := hw 0 local01 local01_cycle
  have h02 := hw 0 local02 local02_cycle
  have h10 := hw 1 local10 local10_cycle
  have h11 := hw 1 local11 local11_cycle
  have h12 := hw 1 local12 local12_cycle
  have h20 := hw 2 local20 local20_cycle
  have h21 := hw 2 local21 local21_cycle
  have h22 := hw 2 local22 local22_cycle
  have hg := hw 0 globalCycle globalCycle_cycle
  simp only [walkWeight, local00, local01, local02, local10, local11, local12, local20, local21, local22, globalCycle, Walk.edges_cons, Walk.edges_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at *
  simp only [Sym2.eq_swap] at *
  linarith


lemma no_nonnegative_certificate : ¬ ∃ w : Sym2 Vertex → ℝ,
    UnitCycleWeight graph w ∧ ∀ e ∈ graph.edgeSet, 0 ≤ w e := by
  rintro ⟨w,hw,hpos⟩
  have hn := every_unit_weight_negative w hw
  have he : s(0,3) ∈ graph.edgeSet := by decide
  have hp := hpos _ he
  linarith

lemma no_marker_certificate : ¬ ∃ R : SimpleGraph Vertex,
    UnitCycleWeight graph (markerWeight R) := by
  rintro ⟨R,hR⟩
  apply no_nonnegative_certificate
  refine ⟨markerWeight R,hR,?_⟩
  intro e he
  unfold markerWeight
  split_ifs <;> norm_num

lemma bounded_signed_certificate :
    ∃ w : Sym2 Vertex → ℝ, UnitCycleWeight graph w ∧ ∀ e ∈ graph.edgeSet, w e ≤ 1 := by
  refine ⟨certWeight,certificate,?_⟩
  intro e he
  unfold certWeight intWeight
  split_ifs <;> norm_num

lemma graph_connected : graph.Connected := by
  have hr : ∀ v : Vertex, v = 0 ∨ graph.Adj v 0 ∨
      (∃ w, graph.Adj v w ∧ graph.Adj w 0) ∨
      (∃ w z, graph.Adj v w ∧ graph.Adj w z ∧ graph.Adj z 0) := by decide
  have hreach : ∀ v : Vertex, graph.Reachable v 0 := by
    intro v
    rcases hr v with rfl | h | ⟨w,h,h'⟩ | ⟨w,z,h,h',h''⟩
    · exact .refl _
    · exact h.reachable
    · exact h.reachable.trans h'.reachable
    · exact h.reachable.trans (h'.reachable.trans h''.reachable)
  exact ⟨fun u v => (hreach u).trans (hreach v).symm⟩

lemma rigid_minimal_without_nonnegative_certificate :
    graph.Connected ∧ (∀ v, Even (graph.degree v)) ∧
    CycleRigid graph ∧ EvenCore.EvenMinimal graph ∧ number graph = 4 ∧
    ¬ (∃ w : Sym2 Vertex → ℝ, UnitCycleWeight graph w ∧ ∀ e ∈ graph.edgeSet, 0 ≤ w e) :=
  ⟨graph_connected,graph_even,graph_rigid,graph_minimal,graph_number,no_nonnegative_certificate⟩

#print axioms every_unit_weight_negative
#print axioms no_marker_certificate
#print axioms no_nonnegative_certificate
#print axioms bounded_signed_certificate

open scoped Classical in
lemma core_marker_existence_false :
    ¬ (∀ R : SimpleGraph Vertex, (∀ v, Even (R.degree v)) → EvenCore.EvenMinimal R →
      ∃ F : SimpleGraph Vertex, F ≤ R ∧ UnitCycleWeight R (markerWeight F)) := by
  intro h
  obtain ⟨F,hF,hw⟩ := h graph (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using graph_even v) graph_minimal
  exact no_marker_certificate ⟨F,hw⟩

#print axioms core_marker_existence_false

/-- The vertex map identifies exactly the endpoints of the closing edge. -/
def merge : Vertex → Fin 12 := ![0,1,2,0,3,4,5,6,7,8,9,10,11]
def mergedEdges : Finset (Sym2 (Fin 12)) :=
  {s(0,3),s(3,1),s(0,4),s(4,1),s(0,5),s(5,1),
   s(1,6),s(6,2),s(1,7),s(7,2),s(1,8),s(8,2),
   s(2,9),s(9,0),s(2,10),s(10,0),s(2,11),s(11,0)}
def merged : SimpleGraph (Fin 12) := .fromEdgeSet mergedEdges
instance : DecidableRel merged.Adj := by unfold merged; infer_instance
lemma merge_fibers : ∀ u v : Vertex, merge u = merge v ↔
    u = v ∨ (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 0) := by decide
lemma merge_surjective : Function.Surjective merge := by decide
lemma merged_adjacency : ∀ a b : Fin 12, merged.Adj a b ↔
    a ≠ b ∧ ∃ u v : Vertex, graph.Adj u v ∧ merge u = a ∧ merge v = b := by decide
lemma merged_even : ∀ v, Even (merged.degree v) := by decide
lemma merged_degree : merged.degree 0 = 6 := by decide
def mergedGlobal0 : merged.Walk 0 0 :=
  .cons (show merged.Adj 0 3 by decide) (.cons (show merged.Adj 3 1 by decide) (.cons (show merged.Adj 1 6 by decide) (.cons (show merged.Adj 6 2 by decide) (.cons (show merged.Adj 2 9 by decide) (.cons (show merged.Adj 9 0 by decide) (.nil))))))

lemma mergedGlobal0_cycle : mergedGlobal0.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def mergedGlobal1 : merged.Walk 0 0 :=
  .cons (show merged.Adj 0 4 by decide) (.cons (show merged.Adj 4 1 by decide) (.cons (show merged.Adj 1 7 by decide) (.cons (show merged.Adj 7 2 by decide) (.cons (show merged.Adj 2 10 by decide) (.cons (show merged.Adj 10 0 by decide) (.nil))))))

lemma mergedGlobal1_cycle : mergedGlobal1.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def mergedGlobal2 : merged.Walk 0 0 :=
  .cons (show merged.Adj 0 5 by decide) (.cons (show merged.Adj 5 1 by decide) (.cons (show merged.Adj 1 8 by decide) (.cons (show merged.Adj 8 2 by decide) (.cons (show merged.Adj 2 11 by decide) (.cons (show merged.Adj 11 0 by decide) (.nil))))))

lemma mergedGlobal2_cycle : mergedGlobal2.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def mergedAvoiding : merged.Walk 1 1 :=
  .cons (show merged.Adj 1 6 by decide) (.cons (show merged.Adj 6 2 by decide) (.cons (show merged.Adj 2 7 by decide) (.cons (show merged.Adj 7 1 by decide) (.nil))))

lemma mergedAvoiding_cycle : mergedAvoiding.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide

def mergedFamily : Fin 3 → merged.Walk 0 0 := ![mergedGlobal0,mergedGlobal1,mergedGlobal2]
lemma merged_number : number merged = 3 := by
  have hhi := DiminishingReturns.number_le_cycle_family (fun _ : Fin 3 => (0 : Fin 12))
    mergedFamily (by
      intro i
      fin_cases i
      · exact mergedGlobal0_cycle
      · exact mergedGlobal1_cycle
      · exact mergedGlobal2_cycle) (by
        simp only [Finset.disjoint_left,List.mem_toFinset]
        decide) (by
        simp only [List.mem_toFinset]
        decide)
  have hlo := StarCore.number_degree_bound merged 0
  have hd := merged_degree
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hlo hd
  simp only [Fintype.card_fin] at hhi
  omega

lemma merged_not_minimal : ¬ EvenCore.EvenMinimal merged := by
  intro hmin
  have hs : merged.degree 0 = 2 * number merged := by rw [merged_degree,merged_number]
  have ha := (StarCore.EvenMinimal.saturated_vertex (G := merged) hmin (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using merged_even v) 0 (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hs)).1
  have hh := (StarCore.cycle_hits_iff_induce_acyclic (G := merged) 0).mpr ha
  have h := hh 1 mergedAvoiding mergedAvoiding_cycle
  exact (show (0 : Fin 12) ∉ mergedAvoiding.support by decide) h

lemma merged_not_rigid : ¬ CycleRigid merged := by
  intro h
  apply merged_not_minimal
  apply h.evenMinimal
  intro v
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    using merged_even v

/-- Identifying the endpoints of one edge can destroy rigidity, even in this
connected even-minimal simple graph. The displayed adjacency formula specifies
ordinary edge contraction, with loops discarded. -/
lemma contraction_failure :
    graph.Connected ∧ (∀ v, Even (graph.degree v)) ∧
    CycleRigid graph ∧ EvenCore.EvenMinimal graph ∧
    graph.Adj 0 3 ∧ Function.Surjective merge ∧
    (∀ u v : Vertex, merge u = merge v ↔
      u = v ∨ (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 0)) ∧
    (∀ a b : Fin 12, merged.Adj a b ↔
      a ≠ b ∧ ∃ u v : Vertex, graph.Adj u v ∧ merge u = a ∧ merge v = b) ∧
    ¬ CycleRigid merged := by
  exact ⟨graph_connected,graph_even,graph_rigid,graph_minimal,by decide,
    merge_surjective,merge_fibers,merged_adjacency,merged_not_rigid⟩

#print axioms contraction_failure
#print axioms rigid_minimal_without_nonnegative_certificate
end Erdos184Work.NegativeCertificate



/-! Structural obstructions to signed unit-cycle certificates. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.CertificateStructure
open Weighted CycleCertificates
variable {V : Type*} {G : SimpleGraph V} {a b c v : V}
set_option maxHeartbeats 2000000

lemma hub_path_weight {w : Sym2 V → ℝ} (hw : UnitCycleWeight G w)
    (p : G.Walk a b) (hp : p.IsPath) (hab : a ≠ b)
    (hv : v ∉ p.support) (hva : G.Adj v a) (hvb : G.Adj v b) :
    w s(v,a) + walkWeight w p + w s(v,b) = 1 := by
  let q := p.concat hvb.symm
  have hq : q.IsPath := hp.concat hv hvb.symm
  have hlen : 2 ≤ q.length := by
    have hpos := Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hab : ¬p.Nil)
    simp only [q,Walk.length_concat]
    omega
  have he : s(v,a) ∉ q.edges := by
    rw [Sym2.eq_swap]
    exact endpoint_edge_notMem hq hlen
  have hc := (Walk.cons_isCycle_iff q hva).mpr ⟨hq,he⟩
  have hh := hw v (.cons hva q) hc
  simpa [q,Walk.concat_eq_append,Sym2.eq_swap,add_assoc] using hh

lemma no_three_spokes {w : Sym2 V → ℝ} (hw : UnitCycleWeight G w)
    (hab : G.Adj a b) (hbc : G.Adj b c) (p : G.Walk c a)
    (hp : (Walk.cons hab (Walk.cons hbc p)).IsCycle)
    (hv : v ∉ (Walk.cons hbc p).support)
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c) : False := by
  have hpath := ((Walk.cons_isCycle_iff (Walk.cons hbc p) hab).mp hp).1
  have hpc : p.IsPath := ((Walk.cons_isPath_iff hbc p).mp hpath).1
  have hbp : b ∉ p.support := (Walk.cons_isPath_iff hbc p).mp hpath |>.2
  have hac : a ≠ c := by
    intro hac
    subst c
    have hp0 : p = .nil := (Walk.isPath_iff_eq_nil p).mp hpc
    have hl := hp.three_le_length
    simp only [Walk.length_cons] at hl
    have hz : p.length = 0 := by rw [hp0]; rfl
    omega
  have hca : c ≠ a := Ne.symm hac
  have hvp : v ∉ p.support := by
    intro hm
    exact hv (by simp [hm])
  have hpab : (p.concat hab).IsPath := hpc.concat hbp hab
  have hvpab : v ∉ (p.concat hab).support := by
    simp only [Walk.support_concat,List.concat_eq_append,List.mem_append,List.mem_singleton]
    exact fun h => h.elim hvp (fun h => hb.ne h)
  let q : G.Walk a c := .cons hab (.cons hbc .nil)
  have hq : q.IsPath := by
    rw [Walk.isPath_def]
    simpa [q,hab.ne,hbc.ne,hac]
  have hvq : v ∉ q.support := by simp [q,ha.ne,hb.ne,hc.ne]
  have h1 := hub_path_weight hw (.cons hbc p) hpath hab.ne.symm hv hb ha
  have h2 := hub_path_weight hw p hpc hca hvp hc ha
  have h3 := hub_path_weight hw (.cons hab .nil) (by simp [hab.ne]) hab.ne
    (by simp [ha.ne,hb.ne]) ha hb
  have h4 := hub_path_weight hw (.cons hbc .nil) (by simp [hbc.ne]) hbc.ne
    (by simp [hb.ne,hc.ne]) hb hc
  have h5 := hub_path_weight hw q hq hac hvq ha hc
  have h6 := hub_path_weight hw (p.concat hab) hpab hbc.ne.symm hvpab hc hb
  have h7 := hw a (.cons hab (.cons hbc p)) hp
  simp only [q,Walk.concat_eq_append,walkWeight_cons,walkWeight_nil,
    walkWeight_append,add_zero] at h1 h2 h3 h4 h5 h6 h7
  linarith

lemma no_cycle_with_hub {w : Sym2 V → ℝ} (hw : UnitCycleWeight G w)
    (p : G.Walk a a) (hp : p.IsCycle) (v : V)
    (hadj : ∀ x ∈ p.support, G.Adj v x) : False := by
  cases p with
  | nil => exact hp.ne_nil rfl
  | @cons a b a hab p =>
    have hpath : p.IsPath := ((Walk.cons_isCycle_iff p hab).mp hp).1
    have hb : G.Adj v b := hadj b (by simp)
    have ha : G.Adj v a := hadj a (by simp)
    have hv : v ∉ p.support := by
      intro hm
      exact G.loopless v (hadj v (by simp [hm]))
    cases p with
    | nil => exact hab.ne rfl
    | @cons b c a hbc p =>
      have hpc : p.IsPath := ((Walk.cons_isPath_iff hbc p).mp hpath).1
      have hbp : b ∉ p.support := (Walk.cons_isPath_iff hbc p).mp hpath |>.2
      have hc : G.Adj v c := hadj c (by simp)
      have hac : a ≠ c := by
        intro hac
        subst c
        have hp0 : p = .nil := (Walk.isPath_iff_eq_nil p).mp hpc
        have hl := hp.three_le_length
        simp only [Walk.length_cons] at hl
        have hz : p.length = 0 := by rw [hp0]; rfl
        omega
      have hca : c ≠ a := Ne.symm hac
      have hvp : v ∉ p.support := by
        intro hm
        exact hv (by simp [hm])
      have hpab : (p.concat hab).IsPath := hpc.concat hbp hab
      have hvpab : v ∉ (p.concat hab).support := by
        simp only [Walk.support_concat,List.concat_eq_append,List.mem_append,List.mem_singleton]
        exact fun h => h.elim hvp (fun h => hb.ne h)
      let q : G.Walk a c := .cons hab (.cons hbc .nil)
      have hq : q.IsPath := by
        rw [Walk.isPath_def]
        simpa [q,hab.ne,hbc.ne,hac]
      have hvq : v ∉ q.support := by simp [q,ha.ne,hb.ne,hc.ne]
      have h1 := hub_path_weight hw (.cons hbc p) hpath hab.ne.symm hv hb ha
      have h2 := hub_path_weight hw p hpc hca hvp hc ha
      have h3 := hub_path_weight hw (.cons hab .nil) (by simp [hab.ne]) hab.ne
        (by simp [ha.ne,hb.ne]) ha hb
      have h4 := hub_path_weight hw (.cons hbc .nil) (by simp [hbc.ne]) hbc.ne
        (by simp [hb.ne,hc.ne]) hb hc
      have h5 := hub_path_weight hw q hq hac hvq ha hc
      have h6 := hub_path_weight hw (p.concat hab) hpab hbc.ne.symm hvpab hc hb
      have h7 := hw a (.cons hab (.cons hbc p)) hp
      simp only [q,Walk.concat_eq_append,walkWeight_cons,walkWeight_nil,
        walkWeight_append,add_zero] at h1 h2 h3 h4 h5 h6 h7
      linarith

lemma neighbor_induce_acyclic {w : Sym2 V → ℝ} (hw : UnitCycleWeight G w) (v : V) :
    (G.induce (G.neighborSet v)).IsAcyclic := by
  intro a p hp
  let q := p.map (SimpleGraph.Embedding.induce (G := G) (G.neighborSet v)).toHom
  have hq : q.IsCycle := hp.map (SimpleGraph.Embedding.induce (G := G) (G.neighborSet v)).injective
  apply no_cycle_with_hub hw q hq v
  intro x hx
  simp only [q,Walk.support_map,List.mem_map] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  exact y.property

#print axioms hub_path_weight
#print axioms neighbor_induce_acyclic
end Erdos184Work.CertificateStructure



/-! Pulling unit-cycle certificates back through one subdivided edge. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CertificateStructure
open Weighted CycleCertificates
variable {V : Type*} {G H : SimpleGraph V} {a b z : V}
set_option maxHeartbeats 2000000

lemma walkWeight_congr (p : G.Walk a b) {w w' : Sym2 V → ℝ}
    (h : ∀ e ∈ p.edges, w e = w' e) : walkWeight w p = walkWeight w' p := by
  unfold walkWeight
  congr 1
  exact List.map_congr_left h

lemma walkWeight_rotate (w : Sym2 V → ℝ) (p : G.Walk a a) {b : V}
    (hb : b ∈ p.support) : walkWeight w (p.rotate hb) = walkWeight w p := by
  exact List.Perm.sum_eq ((p.rotate_edges hb).perm.map w)

lemma cycle_edge_cons {u : V} (p : H.Walk u u) (hp : p.IsCycle)
    (hab : H.Adj a b) (he : s(a,b) ∈ p.edges) :
    ∃ q : H.Walk b a, (Walk.cons hab q).IsCycle ∧
      (Walk.cons hab q).edges.Perm p.edges := by
  have first : ∀ r : H.Walk a a, r.IsCycle → r.snd = b → r.edges.Perm p.edges →
      ∃ q : H.Walk b a, (Walk.cons hab q).IsCycle ∧
        (Walk.cons hab q).edges.Perm p.edges := by
    intro r hr hs hperm
    cases r with
    | nil => exact (hr.ne_nil rfl).elim
    | @cons a d a had q =>
      have hdb : d = b := by simpa using hs
      subst d
      exact ⟨q,hr,hperm⟩
  have main : ∀ r : H.Walk a a, r.IsCycle → s(a,b) ∈ r.edges →
      r.edges.Perm p.edges →
      ∃ q : H.Walk b a, (Walk.cons hab q).IsCycle ∧
        (Walk.cons hab q).edges.Perm p.edges := by
    intro r hr her hperm
    cases r with
    | nil => exact (hr.ne_nil rfl).elim
    | @cons a c a hac q =>
      have hq := ((Walk.cons_isCycle_iff q hac).mp hr).1
      by_cases hcb : c = b
      · subst c
        exact ⟨q,hr,hperm⟩
      have heq : s(a,b) ∈ q.edges := by
        have hne : s(a,b) ≠ s(a,c) := by simpa [Sym2.eq_iff,hac.ne] using Ne.symm hcb
        simpa only [Walk.edges_cons,List.mem_cons,hne,false_or] using her
      have hend : b = q.penultimate := hq.eq_penultimate_of_mem_edges heq
      apply first (Walk.cons hac q).reverse hr.reverse
      · rw [Walk.snd_reverse,Walk.penultimate_cons_of_not_nil hac q
          (Walk.not_nil_of_isCycle_cons hr)]
        exact hend.symm
      · have hh : (Walk.cons hac q).reverse.edges.Perm (Walk.cons hac q).edges := by
          simpa only [Walk.edges_reverse] using (List.reverse_perm (Walk.cons hac q).edges)
        exact hh.trans hperm
  have ha : a ∈ p.support := p.fst_mem_support_of_mem_edges he
  exact main (p.rotate ha) (hp.rotate ha)
    ((p.rotate_edges ha).perm.mem_iff.mpr he) (p.rotate_edges ha).perm

lemma no_isolated_on_nonempty_walk {u v : V} (p : H.Walk u v) (hp : ¬p.Nil)
    (hz : z ∉ H.support) : z ∉ p.support := by
  intro hs
  obtain ⟨e,he,hze⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hp).mp hs
  have hH := p.edges_subset_edgeSet he
  induction e using Sym2.ind with | h x y =>
    simp only [Sym2.mem_iff] at hze
    rcases hze with rfl | rfl
    · exact hz ⟨y,hH⟩
    · exact hz ⟨x,H.symm hH⟩

noncomputable def replacementWeight (w : Sym2 V → ℝ) (a b z : V) (e : Sym2 V) : ℝ :=
  if e = s(a,b) then w s(a,z) + w s(z,b) else w e

lemma certificate_of_single_edge_expansion {w : Sym2 V → ℝ}
    (hw : UnitCycleWeight G w) (hz : z ∉ H.support)
    (haz : G.Adj a z) (hzb : G.Adj z b)
    (hgood : ∀ e ∈ H.edgeSet, e ≠ s(a,b) → e ∈ G.edgeSet) :
    UnitCycleWeight H (replacementWeight w a b z) := by
  let w' := replacementWeight w a b z
  have hweights : ∀ {u v : V} (p : H.Walk u v), s(a,b) ∉ p.edges →
      walkWeight w' p = walkWeight w p := by
    intro u v p he
    apply walkWeight_congr p
    intro e hep
    have hne : e ≠ s(a,b) := by rintro rfl; exact he hep
    simp [w',replacementWeight,hne]
  intro u p hp
  by_cases he : s(a,b) ∈ p.edges
  · have hab : H.Adj a b := p.adj_of_mem_edges he
    obtain ⟨q,hq,hperm⟩ := cycle_edge_cons p hp hab he
    obtain ⟨hqpath,hqe⟩ := (Walk.cons_isCycle_iff q hab).mp hq
    have hgq : ∀ e ∈ q.edges, e ∈ G.edgeSet := by
      intro e heq
      apply hgood e (q.edges_subset_edgeSet heq)
      rintro rfl
      exact hqe heq
    let r := q.transfer G hgq
    have hr : r.IsPath := hqpath.transfer hgq
    have hzr : z ∉ r.support := by
      simp only [r,Walk.support_transfer]
      exact no_isolated_on_nonempty_walk q (Walk.not_nil_of_ne hab.ne.symm) hz
    have hsum := hub_path_weight hw r hr hab.ne.symm hzr hzb haz.symm
    have hwt := hweights q hqe
    have heq : walkWeight w' (Walk.cons hab q) = walkWeight w' p := by
      exact List.Perm.sum_eq (hperm.map w')
    change walkWeight w' p = 1
    rw [← heq,walkWeight_cons,hwt]
    simp only [w',replacementWeight,ite_true]
    simp only [r,walkWeight,Walk.edges_transfer] at hsum
    simp only [walkWeight,Sym2.eq_swap] at hsum ⊢
    linarith
  · have hgp : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
      intro e hep
      apply hgood e (p.edges_subset_edgeSet hep)
      rintro rfl
      exact he hep
    have h := hw u (p.transfer G hgp) (hp.transfer hgp)
    change walkWeight w' p = 1
    rw [hweights p he]
    simpa only [walkWeight,Walk.edges_transfer] using h

#print axioms cycle_edge_cons
#print axioms certificate_of_single_edge_expansion
end Erdos184Work.CertificateStructure



/-! Subcubic certificate tests and single-edge subdivision. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CertificateStructure
open Weighted CycleCertificates
variable {V : Type*} [Fintype V] {G H : SimpleGraph V} {a b z : V}
set_option maxHeartbeats 2000000

/-- Every subgraph of maximum degree three has a unit-cycle certificate. -/
def SubcubicCertificates (G : SimpleGraph V) : Prop :=
  ∀ H ≤ G, (∀ v, H.degree v ≤ 3) → ∃ w : Sym2 V → ℝ, UnitCycleWeight H w

lemma subcubicCertificates_of_certificate {w : Sym2 V → ℝ} (hw : UnitCycleWeight G w) :
    SubcubicCertificates G := fun H hHG _ => ⟨w,hw.mono hHG⟩

lemma SubcubicCertificates.mono (hG : SubcubicCertificates G) (hHG : H ≤ G) :
    SubcubicCertificates H := fun K hKH hdeg => hG K (hKH.trans hHG) hdeg

lemma UnitCycleWeight.of_injective_hom {W : Type*} {K : SimpleGraph W}
    {w : Sym2 V → ℝ} (hw : UnitCycleWeight G w) (f : K →g G)
    (hf : Function.Injective f) : UnitCycleWeight K (w ∘ Sym2.map f) := by
  intro u p hp
  have h := hw (f u) (p.map f) (hp.map hf)
  simpa only [walkWeight,Walk.edges_map,List.map_map] using h

lemma SubcubicCertificates.of_iso {W : Type*} [Fintype W] {K : SimpleGraph W}
    (hG : SubcubicCertificates G) (e : K ≃g G) : SubcubicCertificates K := by
  intro R hRK hd
  let S := R.map e.toEquiv.toEmbedding
  have hSG : S ≤ G := by
    rw [SimpleGraph.map_le_iff_le_comap]
    intro x y hxy
    exact e.toHom.map_adj (hRK hxy)
  let f : R ≃g S := SimpleGraph.Iso.map e.toEquiv R
  have hds : ∀ y, S.degree y ≤ 3 := by
    intro y
    obtain ⟨x,rfl⟩ := f.surjective y
    rw [f.degree_eq]
    exact hd x
  obtain ⟨w,hw⟩ := hG S hSG (by
    intro y
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hds y)
  exact ⟨w ∘ Sym2.map f, UnitCycleWeight.of_injective_hom hw f.toHom f.injective⟩

def subdivide (H : SimpleGraph V) (a b z : V) : SimpleGraph V :=
  (H \ SimpleGraph.edge a b) ⊔ SimpleGraph.edge a z ⊔ SimpleGraph.edge z b

lemma subdivide_symm : subdivide H a b z = subdivide H b a z := by
  unfold subdivide
  rw [SimpleGraph.edge_comm a b,SimpleGraph.edge_comm a z,SimpleGraph.edge_comm z b]
  ac_rfl

lemma subdivide_neighbors_a (hab : H.Adj a b) (hz : z ∉ H.support) :
    (subdivide H a b z).neighborFinset a = insert z ((H.neighborFinset a).erase b) := by
  have haz : a ≠ z := by rintro rfl; exact hz ⟨b,hab⟩
  have hbz : b ≠ z := by rintro rfl; exact hz ⟨a,hab.symm⟩
  have hnz : ¬H.Adj a z := fun h => hz ⟨a,h.symm⟩
  ext y
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,Finset.mem_erase,
    subdivide,SimpleGraph.sup_adj,SimpleGraph.sdiff_adj,SimpleGraph.edge_adj]
  simp only [hab.ne,haz,hbz,Ne.symm haz,Ne.symm hbz,Ne.symm hab.ne]
  by_cases hya : y = a <;> by_cases hyb : y = b <;> by_cases hyz : y = z <;>
    simp_all [hab.ne,Ne.symm haz,Ne.symm hbz]

lemma subdivide_neighbors_z (hab : H.Adj a b) (hz : z ∉ H.support) :
    (subdivide H a b z).neighborFinset z = {a,b} := by
  have haz : a ≠ z := by rintro rfl; exact hz ⟨b,hab⟩
  have hbz : b ≠ z := by rintro rfl; exact hz ⟨a,hab.symm⟩
  have hnz : ∀ y, ¬H.Adj z y := fun y h => hz ⟨y,h⟩
  ext y
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,Finset.mem_singleton,
    subdivide,SimpleGraph.sup_adj,SimpleGraph.sdiff_adj,SimpleGraph.edge_adj]
  by_cases hya : y = a <;> by_cases hyb : y = b <;> simp_all [hab.ne,Ne.symm haz,Ne.symm hbz]

lemma subdivide_neighbors_other (hxa : z ≠ a) (hxb : z ≠ b) (hxz : z ≠ c) :
    (subdivide H a b c).neighborFinset z = H.neighborFinset z := by
  ext y
  simp [subdivide,SimpleGraph.edge_adj,hxa,hxb,hxz]

lemma subdivide_degree_le_three (hab : H.Adj a b) (hz : z ∉ H.support)
    (hdeg : ∀ x, H.degree x ≤ 3) : ∀ x, (subdivide H a b z).degree x ≤ 3 := by
  intro x
  by_cases hxa : x = a
  · subst x
    rw [← SimpleGraph.card_neighborFinset_eq_degree,subdivide_neighbors_a hab hz]
    have hnz : z ∉ (H.neighborFinset a).erase b := by
      intro hh
      exact hz ⟨a,((H.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hh).2).symm⟩
    rw [Finset.card_insert_of_notMem hnz,Finset.card_erase_of_mem
      ((H.mem_neighborFinset _ _).mpr hab)]
    have hda := hdeg a
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hda
    omega
  by_cases hxb : x = b
  · subst x
    rw [subdivide_symm]
    rw [← SimpleGraph.card_neighborFinset_eq_degree,subdivide_neighbors_a hab.symm hz]
    have hnz : z ∉ (H.neighborFinset b).erase a := by
      intro hh
      exact hz ⟨b,((H.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hh).2).symm⟩
    rw [Finset.card_insert_of_notMem hnz,Finset.card_erase_of_mem
      ((H.mem_neighborFinset _ _).mpr hab.symm)]
    have hdb := hdeg b
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdb
    omega
  by_cases hxz : x = z
  · subst x
    rw [← SimpleGraph.card_neighborFinset_eq_degree,subdivide_neighbors_z hab hz]
    simp [hab.ne]
  · rw [← SimpleGraph.card_neighborFinset_eq_degree,
      subdivide_neighbors_other hxa hxb hxz]
    exact hdeg x

lemma certificate_of_subdivide {w : Sym2 V → ℝ}
    (hab : H.Adj a b) (hz : z ∉ H.support)
    (hw : UnitCycleWeight (subdivide H a b z) w) :
    UnitCycleWeight H (replacementWeight w a b z) := by
  have haz : a ≠ z := by rintro rfl; exact hz ⟨b,hab⟩
  have hbz : b ≠ z := by rintro rfl; exact hz ⟨a,hab.symm⟩
  apply certificate_of_single_edge_expansion hw hz
  · simp [subdivide,SimpleGraph.edge_adj,haz]
  · simp [subdivide,SimpleGraph.edge_adj,hbz,Ne.symm hbz]
  · intro e he hne
    induction e using Sym2.ind with | h x y =>
      apply Or.inl
      apply Or.inl
      refine ⟨he,?_⟩
      intro hh
      apply hne
      exact ((SimpleGraph.adj_edge a b).mp hh).1.symm

#print axioms subdivide_degree_le_three
#print axioms certificate_of_subdivide
end Erdos184Work.CertificateStructure



/-! Contraction of a non-loop edge, and a minor-stable certificate test. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CertificateStructure
open Weighted CycleCertificates
variable {V : Type*} [Fintype V] {G H : SimpleGraph V} {a b : V}
set_option maxHeartbeats 2000000

def contract (G : SimpleGraph V) (a b : V) : SimpleGraph V where
  Adj x y := x ≠ b ∧ y ≠ b ∧ x ≠ y ∧
    (G.Adj x y ∨ (x = a ∧ G.Adj b y) ∨ (y = a ∧ G.Adj x b))
  symm := by
    intro x y h
    refine ⟨h.2.1,h.1,Ne.symm h.2.2.1,?_⟩
    rcases h.2.2.2 with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h.1,h.2.symm⟩)
    · exact Or.inr (Or.inl ⟨h.1,h.2.symm⟩)
  loopless := by intro x h; exact h.2.2.1 rfl

lemma contract_not_support : b ∉ (contract G a b).support := by
  rintro ⟨x,hx⟩
  exact hx.1 rfl

lemma subcubic_contraction_one_side (hG : SubcubicCertificates G) (hab : G.Adj a b)
    (hH : H ≤ contract G a b) (hd : ∀ v, H.degree v ≤ 3)
    (hbad : {x | H.Adj a x ∧ ¬G.Adj a x}.Subsingleton) :
    ∃ w : Sym2 V → ℝ, UnitCycleWeight H w := by
  have hb : b ∉ H.support := fun hh => contract_not_support (SimpleGraph.support_mono hH hh)
  by_cases he : ∃ c, H.Adj a c ∧ ¬G.Adj a c
  · obtain ⟨c,hac,hnac⟩ := he
    have hbc : G.Adj b c := by
      rcases (hH hac).2.2.2 with h | h | h
      · exact (hnac h).elim
      · exact h.2
      · exact (hac.ne h.1.symm).elim
    have hgood : ∀ e ∈ H.edgeSet, e ≠ s(a,c) → e ∈ G.edgeSet := by
      intro e he hne
      induction e using Sym2.ind with | h x y =>
        by_contra hn
        rcases (hH he).2.2.2 with h | h | h
        · exact hn h
        · obtain ⟨rfl,hy⟩ := h
          have hyc : y = c := hbad ⟨he,hn⟩ ⟨hac,hnac⟩
          exact hne (by rw [hyc])
        · obtain ⟨rfl,hx⟩ := h
          have hxc : x = c := hbad ⟨he.symm,fun hh => hn hh.symm⟩ ⟨hac,hnac⟩
          exact hne (by rw [hxc,Sym2.eq_swap])
    have hLG : subdivide H a c b ≤ G := by
      intro x y hxy
      rcases hxy with h | h
      · rcases h with h | h
        · apply hgood s(x,y) h.1
          intro heq
          apply h.2
          exact (SimpleGraph.adj_edge a c).mpr ⟨heq.symm,h.1.ne⟩
        · obtain ⟨heq,_⟩ := (SimpleGraph.adj_edge a b).mp h
          exact (G.adj_congr_of_sym2 heq).mp hab
      · obtain ⟨heq,_⟩ := (SimpleGraph.adj_edge b c).mp h
        exact (G.adj_congr_of_sym2 heq).mp hbc
    obtain ⟨w,hw⟩ := hG (subdivide H a c b) hLG
      (subdivide_degree_le_three hac hb hd)
    exact ⟨_,certificate_of_subdivide hac hb hw⟩
  · have hHG : H ≤ G := by
      intro x y hxy
      rcases (hH hxy).2.2.2 with h | h | h
      · exact h
      · obtain ⟨rfl,hy⟩ := h
        by_contra hn
        exact he ⟨y,hxy,hn⟩
      · obtain ⟨rfl,hx⟩ := h
        by_contra hn
        exact he ⟨x,hxy.symm,fun hh => hn hh.symm⟩
    exact hG H hHG hd

lemma contract_swap (hab : a ≠ b) :
    contract (G.comap (Equiv.swap a b)) a b = contract G a b := by
  ext x y
  by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    by_cases hya : y = a <;> by_cases hyb : y = b <;>
    simp_all [contract,Equiv.swap_apply_def,SimpleGraph.comap_adj,SimpleGraph.adj_comm,
      hab,Ne.symm hab] <;> tauto

lemma cover_three_subsingleton (N A B : Finset V) (hN : N.card ≤ 3)
    (hAN : A ⊆ N) (hBN : B ⊆ N) (hd : Disjoint A B) :
    (A : Set V).Subsingleton ∨ (B : Set V).Subsingleton := by
  have hcard : A.card + B.card ≤ 3 := by
    rw [← Finset.card_union_of_disjoint hd]
    exact (Finset.card_le_card (Finset.union_subset hAN hBN)).trans hN
  have h : A.card ≤ 1 ∨ B.card ≤ 1 := by omega
  rcases h with h | h
  · exact Or.inl (Finset.card_le_one.mp h)
  · exact Or.inr (Finset.card_le_one.mp h)

lemma SubcubicCertificates.contract_closed (hG : SubcubicCertificates G) (hab : G.Adj a b) :
    SubcubicCertificates (contract G a b) := by
  intro H hH hd
  let G' := G.comap (Equiv.swap a b)
  have hG' : SubcubicCertificates G' :=
    SubcubicCertificates.of_iso hG (SimpleGraph.Iso.comap (Equiv.swap a b) G)
  have hab' : G'.Adj a b := by simpa [G',SimpleGraph.comap_adj] using hab.symm
  have hH' : H ≤ contract G' a b := by
    simpa only [G',contract_swap hab.ne] using hH
  let A := (H.neighborFinset a).filter fun x => ¬G.Adj a x
  let B := (H.neighborFinset a).filter fun x => ¬G'.Adj a x
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    obtain ⟨hx,hn⟩ := Finset.mem_filter.mp hxA
    obtain ⟨_,hn'⟩ := Finset.mem_filter.mp hxB
    have hax : H.Adj a x := (H.mem_neighborFinset _ _).mp hx
    have hxb : x ≠ b := (hH hax).2.1
    have hxa : x ≠ a := hax.ne.symm
    apply hn'
    change G.Adj ((Equiv.swap a b) a) ((Equiv.swap a b) x)
    rw [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne hxa hxb]
    rcases (hH hax).2.2.2 with h | h | h
    · exact (hn h).elim
    · exact h.2
    · exact (hxa h.1).elim
  have hcard : (H.neighborFinset a).card ≤ 3 := hd a
  obtain hA | hB := cover_three_subsingleton (H.neighborFinset a) A B hcard
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) hAB
  · apply subcubic_contraction_one_side hG hab hH hd
    intro x hx y hy
    apply hA
    · exact Finset.mem_filter.mpr ⟨(H.mem_neighborFinset _ _).mpr hx.1,hx.2⟩
    · exact Finset.mem_filter.mpr ⟨(H.mem_neighborFinset _ _).mpr hy.1,hy.2⟩
  · apply subcubic_contraction_one_side hG' hab' hH' hd
    intro x hx y hy
    apply hB
    · exact Finset.mem_filter.mpr ⟨(H.mem_neighborFinset _ _).mpr hx.1,hx.2⟩
    · exact Finset.mem_filter.mpr ⟨(H.mem_neighborFinset _ _).mpr hy.1,hy.2⟩

#print axioms subcubic_contraction_one_side
#print axioms SubcubicCertificates.contract_closed
end Erdos184Work.CertificateStructure



/-! The minor-stable certificate test excludes wheels. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CertificateStructure
open Weighted CycleCertificates
variable {V : Type*} [Fintype V] {G R : SimpleGraph V} {a b c v : V}
set_option maxHeartbeats 2000000

def threeSpokes (R : SimpleGraph V) (v a b c : V) : SimpleGraph V :=
  R ⊔ SimpleGraph.edge v a ⊔ SimpleGraph.edge v b ⊔ SimpleGraph.edge v c

lemma threeSpokes_degree_le_three (hR : ∀ x, R.degree x ≤ 2) (hv : v ∉ R.support) :
    ∀ x, (threeSpokes R v a b c).degree x ≤ 3 := by
  intro x
  by_cases hxv : x = v
  · subst x
    have hs : (threeSpokes R v a b c).neighborFinset v ⊆ {a,b,c} := by
      intro y hy
      have hxy := ((threeSpokes R v a b c).mem_neighborFinset _ _).mp hy
      simp only [threeSpokes,SimpleGraph.sup_adj,SimpleGraph.edge_adj] at hxy
      rcases hxy with ((h | h) | h) | h
      · exact (hv ⟨y,h⟩).elim
      · rcases h.1 with h | h <;> simp_all
      · rcases h.1 with h | h <;> simp_all
      · rcases h.1 with h | h <;> simp_all
    have hc : ({a,b,c} : Finset V).card ≤ 3 := by
      exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_insert_le _ _).trans (by simp)) _)
    exact (Finset.card_le_card hs).trans hc
  · have hs : (threeSpokes R v a b c).neighborFinset x ⊆ insert v (R.neighborFinset x) := by
      intro y hy
      have hxy := ((threeSpokes R v a b c).mem_neighborFinset _ _).mp hy
      simp only [threeSpokes,SimpleGraph.sup_adj,SimpleGraph.edge_adj] at hxy
      rcases hxy with ((h | h) | h) | h
      · exact Finset.mem_insert_of_mem ((R.mem_neighborFinset _ _).mpr h)
      all_goals
        rcases h.1 with h | h
        · exact (hxv h.1).elim
        · exact Finset.mem_insert.mpr (Or.inl h.2)
    have hc : (insert v (R.neighborFinset x)).card ≤ 3 :=
      (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hR x) 1)
    exact (Finset.card_le_card hs).trans hc

lemma SubcubicCertificates.neighbor_acyclic (hG : SubcubicCertificates G) (v : V) :
    (G.induce (G.neighborSet v)).IsAcyclic := by
  intro u q hq
  let f := (SimpleGraph.Embedding.induce (G.neighborSet v) (G := G)).toHom
  let p := q.map f
  have hp : p.IsCycle := hq.map Subtype.val_injective
  have hall : ∀ x ∈ p.support, G.Adj v x := by
    intro x hx
    simp only [p,Walk.support_map,List.mem_map] at hx
    obtain ⟨y,_,rfl⟩ := hx
    exact y.property
  have hv : v ∉ p.support := by
    intro hh
    exact G.loopless v (hall v hh)
  have main : ∀ a (p : G.Walk a a), p.IsCycle → v ∉ p.support →
      (∀ x ∈ p.support, G.Adj v x) → False := by
    intro a p hp hv hall
    cases p with
    | nil => exact hp.ne_nil rfl
    | @cons a b a hab p =>
      cases p with
      | nil => exact hab.ne rfl
      | @cons b c a hbc p =>
        let C := (Walk.cons hab (Walk.cons hbc p)).toSubgraph.spanningCoe
        let L := threeSpokes C v a b c
        have hC : C ≤ L := by
          exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
        have hvC : v ∉ C.support := by
          rintro ⟨y,hy⟩
          exact hv ((Walk.cons hab (Walk.cons hbc p)).mem_verts_toSubgraph.mp
            ((Walk.cons hab (Walk.cons hbc p)).toSubgraph.edge_vert hy))
        have hCd : ∀ x, C.degree x ≤ 2 := by
          intro x
          have hd := regular_two_spanning_degree (Walk.cons hab (Walk.cons hbc p)).toSubgraph
            (cycle_coe_regular G hp).2 x
          simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd ⊢
          change Nat.card (C.neighborSet x) ≤ 2
          change Nat.card (C.neighborSet x) = _ at hd
          split_ifs at hd <;> omega
        have ha : G.Adj v a := hall a (by simp)
        have hb : G.Adj v b := hall b (by simp)
        have hc : G.Adj v c := hall c (by simp)
        have hLG : L ≤ G := by
          apply sup_le
          · apply sup_le
            · exact sup_le (Walk.cons hab (Walk.cons hbc p)).toSubgraph.spanningCoe_le
                ((SimpleGraph.edge_le_iff G).mpr (Or.inr ha))
            · exact (SimpleGraph.edge_le_iff G).mpr (Or.inr hb)
          · exact (SimpleGraph.edge_le_iff G).mpr (Or.inr hc)
        obtain ⟨w,hw⟩ := hG L hLG (threeSpokes_degree_le_three hCd hvC)
        have hpL : ∀ e ∈ (Walk.cons hab (Walk.cons hbc p)).edges, e ∈ L.edgeSet := by
          intro e he
          exact SimpleGraph.edgeSet_mono hC
            ((Walk.cons hab (Walk.cons hbc p)).mem_edges_toSubgraph.mpr he)
        have hpt : ∀ e ∈ p.edges, e ∈ L.edgeSet := by
          intro e he
          exact hpL e (by simp [he])
        have habL : L.Adj a b := hpL s(a,b) (by simp)
        have hbcL : L.Adj b c := hpL s(b,c) (by simp)
        let r := p.transfer L hpt
        apply no_three_spokes hw habL hbcL r
        · simpa only [r,Walk.transfer] using hp.transfer hpL
        · simp only [r,Walk.support_cons,Walk.support_transfer]
          exact fun hh => hv (by simpa using Or.inr hh)
        · simp [L,threeSpokes,SimpleGraph.edge_adj,ha.ne]
        · simp [L,threeSpokes,SimpleGraph.edge_adj,hb.ne]
        · simp [L,threeSpokes,SimpleGraph.edge_adj,hc.ne]
  exact main _ p hp hv hall

#print axioms threeSpokes_degree_le_three
#print axioms SubcubicCertificates.neighbor_acyclic
end Erdos184Work.CertificateStructure



/-! An edge-count bound for the minor-stable subcubic certificate test. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CertificateStructure
open Weighted CycleCertificates
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
set_option maxHeartbeats 2000000

lemma forest_low_degree [Nonempty V] (hG : G.IsAcyclic) : ∃ v, G.degree v ≤ 1 := by
  by_contra! hn
  have hc := acyclic_card_edges_lt G hG
  have hs := G.sum_degrees_eq_twice_card_edges
  have hsum : 2 * Fintype.card V ≤ ∑ v : V, G.degree v := by
    calc
      _ = ∑ _v : V, 2 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hn v)
  omega

lemma SubcubicCertificates.exists_sparse_edge (hG : SubcubicCertificates G) (hne : G ≠ ⊥) :
    ∃ a b, G.Adj a b ∧ (G.commonNeighbors a b).Subsingleton := by
  obtain ⟨a,b,hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  let N := G.induce (G.neighborSet a)
  letI : Nonempty (G.neighborSet a) := ⟨⟨b,hab⟩⟩
  obtain ⟨v,hv⟩ := forest_low_degree (SubcubicCertificates.neighbor_acyclic hG a)
  refine ⟨a,v.val,v.property,?_⟩
  intro x hx y hy
  have hcard : (N.neighborFinset v).card ≤ 1 := hv
  have heq : (⟨x,hx.1⟩ : G.neighborSet a) = ⟨y,hy.1⟩ := by
    apply Finset.card_le_one.mp hcard
    · exact (N.mem_neighborFinset _ _).mpr hx.2
    · exact (N.mem_neighborFinset _ _).mpr hy.2
  exact congrArg Subtype.val heq

lemma contract_support_subset (hab : G.Adj a b) :
    (contract G a b).support ⊆ G.support \ {b} := by
  rintro x ⟨y,hxy⟩
  refine ⟨?_,hxy.1⟩
  rcases hxy.2.2.2 with h | h | h
  · exact ⟨y,h⟩
  · obtain ⟨rfl,_⟩ := h
    exact ⟨b,hab⟩
  · exact ⟨b,h.2⟩

noncomputable def mergeVertex (a b : V) (x : V) : V := if x = b then a else x

lemma merge_pair_fixed (e : Sym2 V) (he : b ∉ e) :
    Sym2.map (mergeVertex a b) e = e := by
  induction e using Sym2.ind with | h x y =>
    simp only [Sym2.mem_iff,not_or] at he
    simp [mergeVertex,Ne.symm he.1,Ne.symm he.2]

noncomputable def discarded (G : SimpleGraph V) (a b : V) : Finset (Sym2 V) :=
  insert s(a,b) ((G.commonNeighbors a b).toFinset.image fun x => s(b,x))

lemma discarded_subset (hab : G.Adj a b) : discarded G a b ⊆ G.edgeFinset := by
  intro e he
  rcases Finset.mem_insert.mp he with rfl | he
  · exact G.mem_edgeFinset.mpr hab
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
    exact G.mem_edgeFinset.mpr ((Set.mem_toFinset.mp hx).2)

lemma discarded_card_le (hs : (G.commonNeighbors a b).Subsingleton) :
    (discarded G a b).card ≤ 2 := by
  have hc : (G.commonNeighbors a b).toFinset.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact hs (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy)
  exact (Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right ((Finset.card_image_le).trans hc) 1)

lemma retained_edge_cases {e : Sym2 V} (he : e ∈ G.edgeFinset \ discarded G a b) :
    (b ∉ e) ∨ ∃ y, e = s(b,y) ∧ y ≠ a ∧ G.Adj b y ∧ ¬G.Adj a y := by
  by_cases hb : b ∈ e
  · right
    induction e using Sym2.ind with | h x y =>
      obtain ⟨he,hd⟩ := Finset.mem_sdiff.mp he
      have hxy := G.mem_edgeFinset.mp he
      simp only [Sym2.mem_iff] at hb
      have main : ∀ y, G.Adj b y → s(b,y) ∉ discarded G a b →
          ∃ z, s(b,y) = s(b,z) ∧ z ≠ a ∧ G.Adj b z ∧ ¬G.Adj a z := by
        intro y hby hnot
        refine ⟨y,rfl,?_,hby,?_⟩
        · intro hya
          subst y
          apply hnot
          rw [Sym2.eq_swap]
          exact Finset.mem_insert_self _ _
        · intro hay
          apply hnot
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
            ⟨y,Set.mem_toFinset.mpr ⟨hay,hby⟩,rfl⟩)
      rcases hb with rfl | rfl
      · exact main y hxy hd
      · simpa only [Sym2.eq_swap] using main x hxy.symm (by simpa only [Sym2.eq_swap] using hd)
  · exact Or.inl hb

lemma merge_retained_mem {e : Sym2 V} (he : e ∈ G.edgeFinset \ discarded G a b)
    (hab : G.Adj a b) : Sym2.map (mergeVertex a b) e ∈ (contract G a b).edgeFinset := by
  rcases retained_edge_cases he with hn | ⟨y,rfl,hya,hby,hnay⟩
  · rw [merge_pair_fixed e hn]
    induction e using Sym2.ind with | h x y =>
      have hxy := G.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
      simp only [Sym2.mem_iff,not_or] at hn
      exact (contract G a b).mem_edgeFinset.mpr
        ⟨Ne.symm hn.1,Ne.symm hn.2,hxy.ne,Or.inl hxy⟩
  · simp only [Sym2.map_pair_eq,mergeVertex,ite_true,if_neg hby.ne.symm]
    exact (contract G a b).mem_edgeFinset.mpr
      ⟨hab.ne,hby.ne.symm,Ne.symm hya,Or.inr (Or.inl ⟨rfl,hby⟩)⟩

lemma merge_retained_injective : Set.InjOn (Sym2.map (mergeVertex a b))
    (↑(G.edgeFinset \ discarded G a b) : Set (Sym2 V)) := by
  intro e he f hf heq
  have heG := G.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
  have hfG := G.mem_edgeFinset.mp (Finset.mem_sdiff.mp hf).1
  rcases retained_edge_cases he with hn | ⟨y,rfl,hya,hby,hnay⟩
  · rcases retained_edge_cases hf with hm | ⟨z,rfl,hza,hbz,hnaz⟩
    · simpa only [merge_pair_fixed e hn,merge_pair_fixed f hm] using heq
    · rw [merge_pair_fixed e hn] at heq
      have hz : e = s(a,z) := by
        simpa only [Sym2.map_pair_eq,mergeVertex,ite_true,if_neg hbz.ne.symm] using heq
      apply (hnaz ?_).elim
      change s(a,z) ∈ G.edgeSet
      rw [← hz]
      exact heG
  · rcases retained_edge_cases hf with hm | ⟨z,rfl,hza,hbz,hnaz⟩
    · rw [merge_pair_fixed f hm] at heq
      have hy : s(a,y) = f := by
        simpa only [Sym2.map_pair_eq,mergeVertex,ite_true,if_neg hby.ne.symm] using heq
      apply (hnay ?_).elim
      change s(a,y) ∈ G.edgeSet
      rw [hy]
      exact hfG
    · simp only [Sym2.map_pair_eq,mergeVertex,ite_true,if_neg hby.ne.symm,
        if_neg hbz.ne.symm] at heq
      have hyz : y = z := by simpa [Sym2.eq_iff,hya] using heq
      rw [hyz]

lemma contract_edge_count_lower (hab : G.Adj a b)
    (hs : (G.commonNeighbors a b).Subsingleton) :
    G.edgeFinset.card ≤ (contract G a b).edgeFinset.card + 2 := by
  have hsum := Finset.card_sdiff_add_card_eq_card (discarded_subset hab)
  have hd := discarded_card_le hs
  have hret : (G.edgeFinset \ discarded G a b).card ≤
      (contract G a b).edgeFinset.card := by
    calc
      _ = ((G.edgeFinset \ discarded G a b).image (Sym2.map (mergeVertex a b))).card :=
        (Finset.card_image_of_injOn merge_retained_injective).symm
      _ ≤ _ := Finset.card_le_card (Finset.image_subset_iff.mpr fun e he => merge_retained_mem he hab)
  omega

lemma contract_support_card_lt (hab : G.Adj a b) :
    (contract G a b).support.toFinset.card < G.support.toFinset.card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro x hx
    exact Set.mem_toFinset.mpr ((contract_support_subset hab (Set.mem_toFinset.mp hx)).1)
  · intro heq
    have hbG : b ∈ G.support.toFinset := Set.mem_toFinset.mpr ⟨a,hab.symm⟩
    rw [← heq] at hbG
    exact contract_not_support (Set.mem_toFinset.mp hbG)

lemma SubcubicCertificates.edge_bound (hG : SubcubicCertificates G) :
    G.edgeFinset.card ≤ 2 * G.support.toFinset.card := by
  have main : ∀ n (G : SimpleGraph V), SubcubicCertificates G → G.support.toFinset.card = n →
      G.edgeFinset.card ≤ 2*n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hG hn
      by_cases hbot : G = ⊥
      · subst G
        simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card,
          SimpleGraph.edgeSet_bot,Nat.card_of_isEmpty]
        exact Nat.zero_le _
      obtain ⟨a,b,hab,hs⟩ := SubcubicCertificates.exists_sparse_edge hG hbot
      have hlt : (contract G a b).support.toFinset.card < n := by
        rw [← hn]
        exact contract_support_card_lt hab
      have hP := SubcubicCertificates.contract_closed hG hab
      have hC := ih (contract G a b).support.toFinset.card hlt (contract G a b) hP rfl
      have hE := contract_edge_count_lower hab hs
      omega
  exact main _ G hG rfl

lemma UnitCycleWeight.edge_bound {w : Sym2 V → ℝ} (hw : UnitCycleWeight G w) :
    G.edgeFinset.card ≤ 2 * Fintype.card V := by
  have h := SubcubicCertificates.edge_bound (subcubicCertificates_of_certificate hw)
  have hv : G.support.toFinset.card ≤ Fintype.card V := Finset.card_le_univ _
  omega

lemma UnitCycleWeight.number_bound {w : Sym2 V → ℝ} (hw : UnitCycleWeight G w)
    (heven : ∀ v, Even (G.degree v)) : Critical.number G ≤ Fintype.card V - 1 := by
  obtain ⟨D,hD,hdec,hc⟩ := exists_cycle_decomposition G heven
  have hn := Critical.number_le D (fun H hH => Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD H hH)) hdec
  have he := UnitCycleWeight.edge_bound hw
  omega

#print axioms SubcubicCertificates.exists_sparse_edge
#print axioms merge_retained_mem
#print axioms SubcubicCertificates.edge_bound
#print axioms UnitCycleWeight.number_bound
end Erdos184Work.CertificateStructure



/-! The original conclusion from unbounded signed certificates on minimal cores.
The certificate-existence hypothesis remains unproved. -/
open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.CertificateStructure
open Critical Rigidity Weighted CycleCertificates
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 2000000

lemma SubcubicCertificates.number_bound (hG : SubcubicCertificates G)
    (heven : ∀ v, Even (G.degree v)) : number G ≤ Fintype.card V - 1 := by
  obtain ⟨D,hD,hdec,hc⟩ := exists_cycle_decomposition G heven
  have hn := number_le D (fun H hH => Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD H hH)) hdec
  have he := SubcubicCertificates.edge_bound hG
  have hv : G.support.toFinset.card ≤ Fintype.card V := Finset.card_le_univ _
  omega

lemma even_bound_of_core_subcubic_certificates
    (hcert : ∀ R : SimpleGraph V, (∀ v, Even (R.degree v)) → EvenCore.EvenMinimal R →
      SubcubicCertificates R) (heven : ∀ v, Even (G.degree v)) :
    number G ≤ Fintype.card V - 1 := by
  obtain ⟨R,_,hR,hnum,hmin,_⟩ := EvenCore.exists_even_minimal_core G heven
  have hP := hcert R (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hR v) hmin
  rw [← hnum]
  exact SubcubicCertificates.number_bound hP (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hR v)

lemma even_bound_of_core_unit_weights
    (hcert : ∀ R : SimpleGraph V, (∀ v, Even (R.degree v)) → EvenCore.EvenMinimal R →
      ∃ w : Sym2 V → ℝ, UnitCycleWeight R w) (heven : ∀ v, Even (G.degree v)) :
    number G ≤ Fintype.card V - 1 := by
  apply even_bound_of_core_subcubic_certificates (G := G) ?_ heven
  intro R hR hmin
  obtain ⟨w,hw⟩ := hcert R hR hmin
  exact subcubicCertificates_of_certificate hw

universe u

lemma asymptotic_of_core_subcubic_certificates
    (hcert : ∀ {W : Type u} [Fintype W] (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) → EvenCore.EvenMinimal R → SubcubicCertificates R) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition R D ∧
        (D.card : ℝ) ≤ f (Fintype.card W) := by
  apply asymptotic_iff_even_cycle_uniform.mpr
  refine ⟨1,?_⟩
  intro W _ _ R hR
  obtain ⟨D,hD,hdD,hcD⟩ := minimum_cycles hR
  refine ⟨D,hD,hdD,?_⟩
  have hb := even_bound_of_core_subcubic_certificates
    (fun S hS hmin => hcert S hS hmin) hR
  have hle : D.card ≤ Fintype.card W := by omega
  simpa only [one_mul] using (show (D.card : ℝ) ≤ (Fintype.card W : ℝ) by exact_mod_cast hle)

/-- No edge-wise upper or lower bound on the signed certificate is required.
Existence of the certificate on an arbitrary minimal even core is still an
explicit hypothesis, not an established theorem. -/
lemma asymptotic_of_core_unit_weights
    (hcert : ∀ {W : Type u} [Fintype W] (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) → EvenCore.EvenMinimal R →
      ∃ w : Sym2 W → ℝ, UnitCycleWeight R w) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition R D ∧
        (D.card : ℝ) ≤ f (Fintype.card W) := by
  apply asymptotic_of_core_subcubic_certificates
  intro W _ R hR hmin
  obtain ⟨w,hw⟩ := hcert R hR hmin
  exact subcubicCertificates_of_certificate hw

#print axioms SubcubicCertificates.number_bound
#print axioms asymptotic_of_core_subcubic_certificates
#print axioms asymptotic_of_core_unit_weights
end Erdos184Work.CertificateStructure



/-! An exact additive-gap lower bound for the rounding investigation.
This file does not prove or disprove the original Erdős conjecture. -/
open SimpleGraph
open scoped Classical BigOperators Fin.NatCast
namespace Erdos184Work.AdditiveGap

abbrev V (p k : ℕ) := Fin p ⊕ (Fin k × Fin p)
abbrev graph (p k : ℕ) : SimpleGraph (V p k) :=
  completeBipartiteGraph (Fin p) (Fin k × Fin p)

variable {p k : ℕ} [NeZero p]

def blockHom (j : Fin k) : completeBipartiteGraph (Fin p) (Fin p) →g graph p k where
  toFun := Sum.map id (fun a => (j,a))
  map_rel' := by
    intro x y h
    cases x <;> cases y <;> simp_all [graph, completeBipartiteGraph]

omit [NeZero p] in
lemma blockHom_injective (j : Fin k) : Function.Injective (blockHom (p := p) j) := by
  intro x y h
  cases x <;> cases y <;> simp_all [blockHom]

noncomputable def piece (i : Fin k × Fin p) : (graph p k).Subgraph :=
  (SimpleGraph.toSubgraph (matchingPair i.2) (matchingPair_le i.2)).map (blockHom i.1)

lemma piece_cycle (hp : 2 ≤ p) (i : Fin k × Fin p) :
    (piece i).coe.Connected ∧ (piece i).coe.IsRegularOfDegree 2 := by
  have h := coe_toSubgraph_cycle (matchingPair_le i.2)
    (matchingPair_connected i.2) (matchingPair_regular hp i.2)
  simpa only [piece, SimpleGraph.IsRegularOfDegree,
    ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using
    cycle_property_map_injective (blockHom i.1) (blockHom_injective i.1)
      (SimpleGraph.toSubgraph (matchingPair i.2) (matchingPair_le i.2)) (by
        simpa only [SimpleGraph.IsRegularOfDegree,
          ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using h)

lemma piece_cross (i : Fin k × Fin p) (x : Fin p) (j : Fin k) (y : Fin p) :
    (piece i).Adj (.inl x) (.inr (j,y)) ↔
      i.1 = j ∧ (y = x + i.2 ∨ y = x + i.2 + 1) := by
  change (∃ u v, (matchingPair i.2).Adj u v ∧
    blockHom i.1 u = Sum.inl x ∧ blockHom i.1 v = Sum.inr (j,y)) ↔ _
  simp [Sum.exists, matchingPair, blockHom]
  aesop

lemma offset_sum (hp : 2 ≤ p) (x y : Fin p) :
    (∑ t : Fin p, if y = x + t ∨ y = x + t + 1 then (1/2 : ℝ) else 0) = 1 := by
  have h10 : (1 : Fin p) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (show 1 < p by omega)] at hv
    omega
  have hne : y - x ≠ y - x - 1 := by
    intro h
    exact h10 (sub_eq_self.mp h.symm)
  have heq : ∀ t : Fin p, (y = x + t ∨ y = x + t + 1) ↔
      (t = y - x ∨ t = y - x - 1) := by
    intro t
    constructor
    · rintro (h | h)
      · exact Or.inl (by rw [h]; abel)
      · exact Or.inr (by rw [h]; abel)
    · rintro (rfl | rfl)
      · exact Or.inl (by abel)
      · exact Or.inr (by abel)
  simp_rw [heq]
  have hsplit : ∀ t : Fin p,
      (if t = y - x ∨ t = y - x - 1 then (1/2 : ℝ) else 0) =
        (if t = y - x then (1/2 : ℝ) else 0) +
        (if t = y - x - 1 then (1/2 : ℝ) else 0) := by
    intro t
    by_cases h : t = y - x
    · subst t; simp [hne]
    · simp [h]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  norm_num

lemma fractional_cover_cross (hp : 2 ≤ p) (x : Fin p) (j : Fin k) (y : Fin p) :
    (∑ i : Fin k × Fin p,
      if s(Sum.inl x,Sum.inr (j,y)) ∈ (piece i).edgeSet then (1/2 : ℝ) else 0) = 1 := by
  simp only [SimpleGraph.Subgraph.mem_edgeSet, piece_cross, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · simpa only [true_and] using offset_sum hp x y
  · intro i _ hij
    simp [hij]
  · simp

lemma fractional_cover (hp : 2 ≤ p) (e : Sym2 (V p k)) :
    (∑ i : Fin k × Fin p, if e ∈ (piece i).edgeSet then (1/2 : ℝ) else 0) =
      if e ∈ (graph p k).edgeSet then 1 else 0 := by
  induction e using Sym2.ind with | _ x y =>
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        have hn : ∀ i : Fin k × Fin p, ¬ (piece i).Adj (.inl x) (.inl y) := by
          intro i h
          simpa [graph,completeBipartiteGraph] using (piece i).adj_sub h
        simp [SimpleGraph.Subgraph.mem_edgeSet, hn, graph, completeBipartiteGraph]
      | inr y =>
        simpa [graph,completeBipartiteGraph] using fractional_cover_cross hp x y.1 y.2
    | inr x =>
      cases y with
      | inr y =>
        have hn : ∀ i : Fin k × Fin p, ¬ (piece i).Adj (.inr x) (.inr y) := by
          intro i h
          simpa [graph,completeBipartiteGraph] using (piece i).adj_sub h
        simp [SimpleGraph.Subgraph.mem_edgeSet, hn, graph, completeBipartiteGraph]
      | inl y =>
        rw [show s(Sum.inr x,Sum.inl y) = s(Sum.inl y,Sum.inr x) from Sym2.eq_swap]
        simpa [graph,completeBipartiteGraph] using fractional_cover_cross hp y x.1 x.2

lemma degree_eq_sum_adj {W : Type*} [Fintype W] (G : SimpleGraph W) (v : W) :
    (G.degree v : ℝ) = ∑ x : W, if G.Adj v x then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole, ← G.card_neighborFinset_eq_degree v]
  congr 1
  congr 1
  ext x
  simp

lemma fractional_degree_identity {W I : Type*} [Fintype W] [Fintype I]
    (G : SimpleGraph W) (H : I → G.Subgraph) (c : I → ℝ)
    (hcov : ∀ e, (∑ i, if e ∈ (H i).edgeSet then c i else 0) =
      if e ∈ G.edgeSet then 1 else 0) (v : W) :
    (∑ i, c i * ((H i).spanningCoe.degree v : ℝ)) = G.degree v := by
  simp_rw [degree_eq_sum_adj,Finset.mul_sum,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun x _ => hcov s(v,x))

lemma fractional_degree_bound {W I : Type*} [Fintype W] [Fintype I]
    (G : SimpleGraph W) (H : I → G.Subgraph) (c : I → ℝ)
    (hH : ∀ i, IsCycleOrEdge (H i).coe) (hc : ∀ i, 0 ≤ c i)
    (hcov : ∀ e, (∑ i, if e ∈ (H i).edgeSet then c i else 0) =
      if e ∈ G.edgeSet then 1 else 0) (v : W) :
    (G.degree v : ℝ) ≤ 2 * ∑ i, c i := by
  have hdeg : ∀ i, (H i).spanningCoe.degree v ≤ 2 := by
    intro i
    rcases hH i with hcyc | he
    · rw [regular_two_spanning_degree (H i) (by
        simpa only [SimpleGraph.IsRegularOfDegree,
          ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hcyc.2)]
      split_ifs <;> omega
    · have hb := (H i).spanningCoe.degree_le_card_edgeFinset v
      have he' := subgraph_edge_card (H i)
      simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
        hb.trans (he'.trans he).le |>.trans (by decide : 1 ≤ 2)
  rw [← fractional_degree_identity G H c hcov v]
  calc
    _ ≤ ∑ i, c i * 2 := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (by exact_mod_cast hdeg i) (hc i))
    _ = _ := by rw [← Finset.sum_mul,mul_comm]

/-- The explicit cover is fractionally optimal, even when competing covers may
use single edges and arbitrary nonnegative real coefficients. -/
lemma fractional_cost_lower_bound {I : Type*} [Fintype I]
    (H : I → (graph p k).Subgraph) (c : I → ℝ)
    (hH : ∀ i, IsCycleOrEdge (H i).coe) (hc : ∀ i, 0 ≤ c i)
    (hcov : ∀ e, (∑ i, if e ∈ (H i).edgeSet then c i else 0) =
      if e ∈ (graph p k).edgeSet then 1 else 0) :
    (k : ℝ) * p / 2 ≤ ∑ i, c i := by
  have h := fractional_degree_bound (graph p k) H c hH hc hcov (.inl 0)
  rw [BipartiteLower.complete_degree_left] at h
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] at h
  linarith

omit [NeZero p] in
lemma fractional_cost : (∑ _i : Fin k × Fin p, (1/2 : ℝ)) = (k : ℝ) * p / 2 := by
  simp [div_eq_mul_inv]

omit [NeZero p] in
lemma integral_lower_bound (m : ℕ) (hp : p = 2 * m + 1)
    (D : Finset (graph p k).Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition (graph p k) D) :
    (6 * m + 2) * (k * p) ≤ (4 * m + 2) * D.card := by
  simpa only [Fintype.card_prod,Fintype.card_fin] using
    BipartiteLower.decomposition_lower_bound m (by simpa only [Fintype.card_fin] using hp) D hD hdec

lemma integral_lower_bound_simplified (m : ℕ) (hp : p = 2 * m + 1)
    (D : Finset (graph p k).Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition (graph p k) D) :
    k * (3 * m + 1) ≤ D.card := by
  have hb := integral_lower_bound m hp D hD hdec
  have hp0 : 0 < p := NeZero.pos p
  have hmul : p * (k * (3 * m + 1)) ≤ p * D.card := by nlinarith
  exact Nat.le_of_mul_le_mul_left hmul hp0

/-- Any universal additive rounding bound with coefficient one on fractional cost
must have additive coefficient at least one on the vertex count. An arbitrary
fixed additive constant cannot repair a smaller coefficient. This is NOT a
counterexample to a bound with additive coefficient one, or to Erdős 184. -/
lemma no_additive_coefficient_below_one (c B : ℝ) (hc : c < 1) :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W)
      (I : Type) (_ : Fintype I) (H : I → G.Subgraph),
      (∀ i, (H i).coe.Connected ∧ (H i).coe.IsRegularOfDegree 2) ∧
      (∀ e, (∑ i, if e ∈ (H i).edgeSet then (1/2 : ℝ) else 0) =
        if e ∈ G.edgeSet then 1 else 0) ∧
      (∀ D : Finset G.Subgraph, (∀ K ∈ D, IsCycleOrEdge K.coe) →
        IsDecomposition G D →
        (∑ _i : I, (1/2 : ℝ)) + c * Fintype.card W + B < (D.card : ℝ)) := by
  obtain ⟨m,hm⟩ := exists_nat_gt ((|B| + |c| + 2) / (1-c))
  have hpos : 0 < 1-c := by linarith
  have hm' : |B| + |c| + 2 < (m : ℝ) * (1-c) := (div_lt_iff₀ hpos).mp hm
  have hm0 : 0 < (m : ℝ) := by
    nlinarith [abs_nonneg B,abs_nonneg c]
  have hmnat : 0 < m := by exact_mod_cast hm0
  let p := 2 * m + 1
  letI : NeZero p := ⟨by dsimp [p]; omega⟩
  have hp2 : 2 ≤ p := by dsimp [p]; omega
  refine ⟨V p p,inferInstance,graph p p,Fin p × Fin p,inferInstance,piece,?_,
    fractional_cover hp2,?_⟩
  · intro i
    simpa only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using piece_cycle hp2 i
  · intro D hD hdec
    have hDnat := integral_lower_bound_simplified m (show p = 2*m+1 from rfl) D hD hdec
    have hDreal : (p : ℝ) * (3*(m : ℝ)+1) ≤ D.card := by exact_mod_cast hDnat
    have hpreal : (p : ℝ) = 2*(m : ℝ)+1 := by simp [p]
    have hp1 : (1 : ℝ) ≤ p := by linarith
    have hcoef : |B| < (p : ℝ)*(1-c)-c-1/2 := by
      nlinarith [le_abs_self c,abs_nonneg B,abs_nonneg c]
    have hmul := mul_le_mul_of_nonneg_right hp1 (le_trans (abs_nonneg B) hcoef.le)
    have hgap : B < (p : ℝ) * ((p : ℝ)*(1-c)-c-1/2) := by
      have := le_abs_self B
      nlinarith
    rw [fractional_cost]
    simp only [V,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Nat.cast_add,Nat.cast_mul]
    nlinarith

#print axioms fractional_cover
#print axioms fractional_cost_lower_bound
#print axioms integral_lower_bound_simplified
#print axioms no_additive_coefficient_below_one
end Erdos184Work.AdditiveGap



/-! Exact local obstructions to proposed minimal-core reductions.
These do not disprove the original conjecture. -/
open SimpleGraph
namespace Erdos184Work.LocalObstruction
open Critical EvenCore ThreeCycleObstruction CycleCertificates Weighted
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

def ends : Fin 10 → Fin 15 × Fin 15 :=
  ![(2,12), (1,12), (5,12), (2,4), (0,1), (5,11), (4,11), (4,9), (0,9), (9,11)]

def maskGraph (b : Fin 10 → Bool) : SimpleGraph (Fin 15) where
  Adj x y := ∃ i : Fin 10, b i = true ∧
    ((x = (ends i).1 ∧ y = (ends i).2) ∨ (y = (ends i).1 ∧ x = (ends i).2))
  symm := by intro x y h; obtain ⟨i,hi,h⟩ := h; exact ⟨i,hi,h.symm⟩
  loopless := by
    intro x h
    obtain ⟨i,hi,h⟩ := h
    have hn : (ends i).1 ≠ (ends i).2 := by fin_cases i <;> decide
    rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> exact hn (h1.symm.trans h2)

instance (b : Fin 10 → Bool) : DecidableRel (maskGraph b).Adj := by
  intro x y
  change Decidable (∃ i : Fin 10, b i = true ∧ _)
  infer_instance

abbrev localGraph := maskGraph (fun _ => true)
lemma local_le : localGraph ≤ exampleGraph := by
  change ∀ x y, localGraph.Adj x y → exampleGraph.Adj x y
  decide
lemma local_subcubic : ∀ v, localGraph.degree v ≤ 3 := by decide

def pattern : Fin 7 → Fin 10 → Bool :=
  ![![false,false,false,false,false,false,true,true,false,true],
    ![true,false,true,true,false,true,true,false,false,false],
    ![true,false,true,true,false,true,false,true,false,true],
    ![false,true,true,false,true,true,false,false,true,true],
    ![true,true,false,true,true,false,false,true,true,false],
    ![false,true,true,false,true,true,true,true,true,false],
    ![true,true,false,true,true,false,true,false,true,true]]

lemma degree_sum_adj (G : SimpleGraph (Fin 15)) [DecidableRel G.Adj] (v : Fin 15) :
    G.degree v = ∑ x : Fin 15, if G.Adj v x then 1 else 0 := by
  classical
  rw [Finset.sum_boole,← G.card_neighborFinset_eq_degree v]
  congr 1
  ext x
  simp

lemma degree_0 (b : Fin 10 → Bool) :
    (maskGraph b).degree 0 = (if b 4 then 1 else 0) + (if b 8 then 1 else 0) := by
  rw [degree_sum_adj]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp [maskGraph,Fin.exists_fin_succ,ends]

lemma degree_1 (b : Fin 10 → Bool) :
    (maskGraph b).degree 1 = (if b 1 then 1 else 0) + (if b 4 then 1 else 0) := by
  rw [degree_sum_adj]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp [maskGraph,Fin.exists_fin_succ,ends]
  omega

lemma degree_2 (b : Fin 10 → Bool) :
    (maskGraph b).degree 2 = (if b 0 then 1 else 0) + (if b 3 then 1 else 0) := by
  rw [degree_sum_adj]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp [maskGraph,Fin.exists_fin_succ,ends]
  omega

lemma degree_4 (b : Fin 10 → Bool) :
    (maskGraph b).degree 4 = (if b 3 then 1 else 0) + (if b 6 then 1 else 0) + (if b 7 then 1 else 0) := by
  rw [degree_sum_adj]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp [maskGraph,Fin.exists_fin_succ,ends]
  omega

lemma degree_5 (b : Fin 10 → Bool) :
    (maskGraph b).degree 5 = (if b 2 then 1 else 0) + (if b 5 then 1 else 0) := by
  rw [degree_sum_adj]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp [maskGraph,Fin.exists_fin_succ,ends]
  omega

lemma degree_9 (b : Fin 10 → Bool) :
    (maskGraph b).degree 9 = (if b 7 then 1 else 0) + (if b 8 then 1 else 0) + (if b 9 then 1 else 0) := by
  rw [degree_sum_adj]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp [maskGraph,Fin.exists_fin_succ,ends]
  omega

lemma degree_11 (b : Fin 10 → Bool) :
    (maskGraph b).degree 11 = (if b 5 then 1 else 0) + (if b 6 then 1 else 0) + (if b 9 then 1 else 0) := by
  rw [degree_sum_adj]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp [maskGraph,Fin.exists_fin_succ,ends]
  omega

lemma degree_12 (b : Fin 10 → Bool) :
    (maskGraph b).degree 12 = (if b 0 then 1 else 0) + (if b 1 then 1 else 0) + (if b 2 then 1 else 0) := by
  rw [degree_sum_adj]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp [maskGraph,Fin.exists_fin_succ,ends]
  omega

lemma even_two_bits (x y : Bool) :
    Even ((if x then 1 else 0 : ℕ) + (if y then 1 else 0)) ↔ x = y := by
  cases x <;> cases y <;> decide
lemma even_three_bits (x y z : Bool) :
    Even ((if x then 1 else 0 : ℕ) + (if y then 1 else 0) + (if z then 1 else 0)) ↔
      z = (x ^^ y) := by
  cases x <;> cases y <;> cases z <;> decide

lemma even_mask_classification (b : Fin 10 → Bool)
    (h : ∀ v, Even ((maskGraph b).degree v)) :
      b = (fun _ => false) ∨ ∃ i : Fin 7, b = pattern i := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h4 := h 4
  have h5 := h 5
  have h11 := h 11
  have h12 := h 12
  rw [degree_0,even_two_bits] at h0
  rw [degree_1,even_two_bits] at h1
  rw [degree_2,even_two_bits] at h2
  rw [degree_4,even_three_bits] at h4
  rw [degree_5,even_two_bits] at h5
  rw [degree_11,even_three_bits] at h11
  rw [degree_12,even_three_bits] at h12
  have heq : b = ![b 0,b 1,(b 0 ^^ b 1),b 0,b 1,(b 0 ^^ b 1),b 6,
      (b 0 ^^ b 6),b 1,((b 0 ^^ b 1) ^^ b 6)] := by
    ext i
    fin_cases i <;> simp_all
  rw [heq]
  generalize b 0 = x, b 1 = y, b 6 = z
  cases x <;> cases y <;> cases z <;> decide

lemma number_le_two_cycles {W : Type*} [Fintype W] {G : SimpleGraph W}
    {u v : W} (p : G.Walk u u) (q : G.Walk v v) (hp : p.IsCycle) (hq : q.IsCycle)
    (hd : p.edges.Disjoint q.edges)
    (hcov : ∀ a b, G.Adj a b ↔ s(a,b) ∈ p.edges ∨ s(a,b) ∈ q.edges) :
    number G ≤ 2 := by
  classical
  let P : Fin 2 → G.Subgraph := ![p.toSubgraph,q.toSubgraph]
  let E : Fin 2 → Finset (Sym2 W) := ![p.edges.toFinset,q.edges.toFinset]
  have hdec : IsDecomposition G (Finset.univ.image P) := by
    apply Compression.finite_family_decomposition P E
    · intro i; fin_cases i <;> ext e <;> simp [P,E]
    · intro i j hij; fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · change Disjoint p.edges.toFinset q.edges.toFinset
        exact List.disjoint_toFinset_iff_disjoint.mpr hd
      · change Disjoint q.edges.toFinset p.edges.toFinset
        exact List.disjoint_toFinset_iff_disjoint.mpr hd.symm
      · exact (hij rfl).elim
    · intro a b
      simpa [E,Fin.exists_fin_succ] using hcov a b
  have hprop : ∀ H ∈ Finset.univ.image P, IsCycleOrEdge H.coe := by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    fin_cases i
    · exact Or.inl (by
        simpa only [P,SimpleGraph.IsRegularOfDegree,
          ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
          using cycle_coe_regular G hp)
    · exact Or.inl (by
        simpa only [P,SimpleGraph.IsRegularOfDegree,
          ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
          using cycle_coe_regular G hq)
  exact (number_le _ hprop hdec).trans (Finset.card_image_le.trans (by simp))

def cycle0 : localGraph.Walk 4 4 :=
  .cons (show localGraph.Adj 4 9 by decide) (.cons (show localGraph.Adj 9 11 by decide) (.cons (show localGraph.Adj 11 4 by decide) (.nil)))

lemma cycle0_cycle : cycle0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

abbrev rest0 := exampleGraph \ maskGraph (pattern 0)

def rest0p0 : rest0.Walk 0 0 :=
  .cons (show rest0.Adj 0 1 by decide) (.cons (show rest0.Adj 1 8 by decide) (.cons (show rest0.Adj 8 14 by decide) (.cons (show rest0.Adj 14 2 by decide) (.cons (show rest0.Adj 2 12 by decide) (.cons (show rest0.Adj 12 5 by decide) (.cons (show rest0.Adj 5 6 by decide) (.cons (show rest0.Adj 6 10 by decide) (.cons (show rest0.Adj 10 13 by decide) (.cons (show rest0.Adj 13 3 by decide) (.cons (show rest0.Adj 3 7 by decide) (.cons (show rest0.Adj 7 0 by decide) (.nil))))))))))))

lemma rest0p0_cycle : rest0p0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def rest0p1 : rest0.Walk 0 0 :=
  .cons (show rest0.Adj 0 8 by decide) (.cons (show rest0.Adj 8 10 by decide) (.cons (show rest0.Adj 10 14 by decide) (.cons (show rest0.Adj 14 4 by decide) (.cons (show rest0.Adj 4 2 by decide) (.cons (show rest0.Adj 2 3 by decide) (.cons (show rest0.Adj 3 12 by decide) (.cons (show rest0.Adj 12 1 by decide) (.cons (show rest0.Adj 1 5 by decide) (.cons (show rest0.Adj 5 11 by decide) (.cons (show rest0.Adj 11 6 by decide) (.cons (show rest0.Adj 6 13 by decide) (.cons (show rest0.Adj 13 7 by decide) (.cons (show rest0.Adj 7 9 by decide) (.cons (show rest0.Adj 9 0 by decide) (.nil)))))))))))))))

lemma rest0p1_cycle : rest0p1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma rest0_bound : number rest0 ≤ 2 := by
  apply number_le_two_cycles rest0p0 rest0p1 rest0p0_cycle rest0p1_cycle
  · apply List.disjoint_toFinset_iff_disjoint.mp
    decide
  · decide

def cycle1 : localGraph.Walk 2 2 :=
  .cons (show localGraph.Adj 2 4 by decide) (.cons (show localGraph.Adj 4 11 by decide) (.cons (show localGraph.Adj 11 5 by decide) (.cons (show localGraph.Adj 5 12 by decide) (.cons (show localGraph.Adj 12 2 by decide) (.nil)))))

lemma cycle1_cycle : cycle1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

abbrev rest1 := exampleGraph \ maskGraph (pattern 1)

def rest1p0 : rest1.Walk 0 0 :=
  .cons (show rest1.Adj 0 8 by decide) (.cons (show rest1.Adj 8 1 by decide) (.cons (show rest1.Adj 1 12 by decide) (.cons (show rest1.Adj 12 3 by decide) (.cons (show rest1.Adj 3 2 by decide) (.cons (show rest1.Adj 2 14 by decide) (.cons (show rest1.Adj 14 10 by decide) (.cons (show rest1.Adj 10 6 by decide) (.cons (show rest1.Adj 6 13 by decide) (.cons (show rest1.Adj 13 7 by decide) (.cons (show rest1.Adj 7 9 by decide) (.cons (show rest1.Adj 9 0 by decide) (.nil))))))))))))

lemma rest1p0_cycle : rest1p0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def rest1p1 : rest1.Walk 0 0 :=
  .cons (show rest1.Adj 0 1 by decide) (.cons (show rest1.Adj 1 5 by decide) (.cons (show rest1.Adj 5 6 by decide) (.cons (show rest1.Adj 6 11 by decide) (.cons (show rest1.Adj 11 9 by decide) (.cons (show rest1.Adj 9 4 by decide) (.cons (show rest1.Adj 4 14 by decide) (.cons (show rest1.Adj 14 8 by decide) (.cons (show rest1.Adj 8 10 by decide) (.cons (show rest1.Adj 10 13 by decide) (.cons (show rest1.Adj 13 3 by decide) (.cons (show rest1.Adj 3 7 by decide) (.cons (show rest1.Adj 7 0 by decide) (.nil)))))))))))))

lemma rest1p1_cycle : rest1p1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma rest1_bound : number rest1 ≤ 2 := by
  apply number_le_two_cycles rest1p0 rest1p1 rest1p0_cycle rest1p1_cycle
  · apply List.disjoint_toFinset_iff_disjoint.mp
    decide
  · decide

def cycle2 : localGraph.Walk 2 2 :=
  .cons (show localGraph.Adj 2 4 by decide) (.cons (show localGraph.Adj 4 9 by decide) (.cons (show localGraph.Adj 9 11 by decide) (.cons (show localGraph.Adj 11 5 by decide) (.cons (show localGraph.Adj 5 12 by decide) (.cons (show localGraph.Adj 12 2 by decide) (.nil))))))

lemma cycle2_cycle : cycle2.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

abbrev rest2 := exampleGraph \ maskGraph (pattern 2)

def rest2p0 : rest2.Walk 0 0 :=
  .cons (show rest2.Adj 0 7 by decide) (.cons (show rest2.Adj 7 13 by decide) (.cons (show rest2.Adj 13 6 by decide) (.cons (show rest2.Adj 6 10 by decide) (.cons (show rest2.Adj 10 14 by decide) (.cons (show rest2.Adj 14 2 by decide) (.cons (show rest2.Adj 2 3 by decide) (.cons (show rest2.Adj 3 12 by decide) (.cons (show rest2.Adj 12 1 by decide) (.cons (show rest2.Adj 1 8 by decide) (.cons (show rest2.Adj 8 0 by decide) (.nil)))))))))))

lemma rest2p0_cycle : rest2p0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def rest2p1 : rest2.Walk 0 0 :=
  .cons (show rest2.Adj 0 1 by decide) (.cons (show rest2.Adj 1 5 by decide) (.cons (show rest2.Adj 5 6 by decide) (.cons (show rest2.Adj 6 11 by decide) (.cons (show rest2.Adj 11 4 by decide) (.cons (show rest2.Adj 4 14 by decide) (.cons (show rest2.Adj 14 8 by decide) (.cons (show rest2.Adj 8 10 by decide) (.cons (show rest2.Adj 10 13 by decide) (.cons (show rest2.Adj 13 3 by decide) (.cons (show rest2.Adj 3 7 by decide) (.cons (show rest2.Adj 7 9 by decide) (.cons (show rest2.Adj 9 0 by decide) (.nil)))))))))))))

lemma rest2p1_cycle : rest2p1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma rest2_bound : number rest2 ≤ 2 := by
  apply number_le_two_cycles rest2p0 rest2p1 rest2p0_cycle rest2p1_cycle
  · apply List.disjoint_toFinset_iff_disjoint.mp
    decide
  · decide

def cycle3 : localGraph.Walk 0 0 :=
  .cons (show localGraph.Adj 0 1 by decide) (.cons (show localGraph.Adj 1 12 by decide) (.cons (show localGraph.Adj 12 5 by decide) (.cons (show localGraph.Adj 5 11 by decide) (.cons (show localGraph.Adj 11 9 by decide) (.cons (show localGraph.Adj 9 0 by decide) (.nil))))))

lemma cycle3_cycle : cycle3.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

abbrev rest3 := exampleGraph \ maskGraph (pattern 3)

def rest3p0 : rest3.Walk 2 2 :=
  .cons (show rest3.Adj 2 12 by decide) (.cons (show rest3.Adj 12 3 by decide) (.cons (show rest3.Adj 3 7 by decide) (.cons (show rest3.Adj 7 9 by decide) (.cons (show rest3.Adj 9 4 by decide) (.cons (show rest3.Adj 4 11 by decide) (.cons (show rest3.Adj 11 6 by decide) (.cons (show rest3.Adj 6 13 by decide) (.cons (show rest3.Adj 13 10 by decide) (.cons (show rest3.Adj 10 8 by decide) (.cons (show rest3.Adj 8 14 by decide) (.cons (show rest3.Adj 14 2 by decide) (.nil))))))))))))

lemma rest3p0_cycle : rest3p0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def rest3p1 : rest3.Walk 0 0 :=
  .cons (show rest3.Adj 0 7 by decide) (.cons (show rest3.Adj 7 13 by decide) (.cons (show rest3.Adj 13 3 by decide) (.cons (show rest3.Adj 3 2 by decide) (.cons (show rest3.Adj 2 4 by decide) (.cons (show rest3.Adj 4 14 by decide) (.cons (show rest3.Adj 14 10 by decide) (.cons (show rest3.Adj 10 6 by decide) (.cons (show rest3.Adj 6 5 by decide) (.cons (show rest3.Adj 5 1 by decide) (.cons (show rest3.Adj 1 8 by decide) (.cons (show rest3.Adj 8 0 by decide) (.nil))))))))))))

lemma rest3p1_cycle : rest3p1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma rest3_bound : number rest3 ≤ 2 := by
  apply number_le_two_cycles rest3p0 rest3p1 rest3p0_cycle rest3p1_cycle
  · apply List.disjoint_toFinset_iff_disjoint.mp
    decide
  · decide

def cycle4 : localGraph.Walk 0 0 :=
  .cons (show localGraph.Adj 0 1 by decide) (.cons (show localGraph.Adj 1 12 by decide) (.cons (show localGraph.Adj 12 2 by decide) (.cons (show localGraph.Adj 2 4 by decide) (.cons (show localGraph.Adj 4 9 by decide) (.cons (show localGraph.Adj 9 0 by decide) (.nil))))))

lemma cycle4_cycle : cycle4.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

abbrev rest4 := exampleGraph \ maskGraph (pattern 4)

def rest4p0 : rest4.Walk 3 3 :=
  .cons (show rest4.Adj 3 12 by decide) (.cons (show rest4.Adj 12 5 by decide) (.cons (show rest4.Adj 5 6 by decide) (.cons (show rest4.Adj 6 10 by decide) (.cons (show rest4.Adj 10 8 by decide) (.cons (show rest4.Adj 8 14 by decide) (.cons (show rest4.Adj 14 4 by decide) (.cons (show rest4.Adj 4 11 by decide) (.cons (show rest4.Adj 11 9 by decide) (.cons (show rest4.Adj 9 7 by decide) (.cons (show rest4.Adj 7 13 by decide) (.cons (show rest4.Adj 13 3 by decide) (.nil))))))))))))

lemma rest4p0_cycle : rest4p0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def rest4p1 : rest4.Walk 0 0 :=
  .cons (show rest4.Adj 0 7 by decide) (.cons (show rest4.Adj 7 3 by decide) (.cons (show rest4.Adj 3 2 by decide) (.cons (show rest4.Adj 2 14 by decide) (.cons (show rest4.Adj 14 10 by decide) (.cons (show rest4.Adj 10 13 by decide) (.cons (show rest4.Adj 13 6 by decide) (.cons (show rest4.Adj 6 11 by decide) (.cons (show rest4.Adj 11 5 by decide) (.cons (show rest4.Adj 5 1 by decide) (.cons (show rest4.Adj 1 8 by decide) (.cons (show rest4.Adj 8 0 by decide) (.nil))))))))))))

lemma rest4p1_cycle : rest4p1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma rest4_bound : number rest4 ≤ 2 := by
  apply number_le_two_cycles rest4p0 rest4p1 rest4p0_cycle rest4p1_cycle
  · apply List.disjoint_toFinset_iff_disjoint.mp
    decide
  · decide

def cycle5 : localGraph.Walk 0 0 :=
  .cons (show localGraph.Adj 0 1 by decide) (.cons (show localGraph.Adj 1 12 by decide) (.cons (show localGraph.Adj 12 5 by decide) (.cons (show localGraph.Adj 5 11 by decide) (.cons (show localGraph.Adj 11 4 by decide) (.cons (show localGraph.Adj 4 9 by decide) (.cons (show localGraph.Adj 9 0 by decide) (.nil)))))))

lemma cycle5_cycle : cycle5.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

abbrev rest5 := exampleGraph \ maskGraph (pattern 5)

def rest5p0 : rest5.Walk 1 1 :=
  .cons (show rest5.Adj 1 5 by decide) (.cons (show rest5.Adj 5 6 by decide) (.cons (show rest5.Adj 6 13 by decide) (.cons (show rest5.Adj 13 7 by decide) (.cons (show rest5.Adj 7 3 by decide) (.cons (show rest5.Adj 3 12 by decide) (.cons (show rest5.Adj 12 2 by decide) (.cons (show rest5.Adj 2 14 by decide) (.cons (show rest5.Adj 14 10 by decide) (.cons (show rest5.Adj 10 8 by decide) (.cons (show rest5.Adj 8 1 by decide) (.nil)))))))))))

lemma rest5p0_cycle : rest5p0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def rest5p1 : rest5.Walk 0 0 :=
  .cons (show rest5.Adj 0 7 by decide) (.cons (show rest5.Adj 7 9 by decide) (.cons (show rest5.Adj 9 11 by decide) (.cons (show rest5.Adj 11 6 by decide) (.cons (show rest5.Adj 6 10 by decide) (.cons (show rest5.Adj 10 13 by decide) (.cons (show rest5.Adj 13 3 by decide) (.cons (show rest5.Adj 3 2 by decide) (.cons (show rest5.Adj 2 4 by decide) (.cons (show rest5.Adj 4 14 by decide) (.cons (show rest5.Adj 14 8 by decide) (.cons (show rest5.Adj 8 0 by decide) (.nil))))))))))))

lemma rest5p1_cycle : rest5p1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma rest5_bound : number rest5 ≤ 2 := by
  apply number_le_two_cycles rest5p0 rest5p1 rest5p0_cycle rest5p1_cycle
  · apply List.disjoint_toFinset_iff_disjoint.mp
    decide
  · decide

def cycle6 : localGraph.Walk 0 0 :=
  .cons (show localGraph.Adj 0 1 by decide) (.cons (show localGraph.Adj 1 12 by decide) (.cons (show localGraph.Adj 12 2 by decide) (.cons (show localGraph.Adj 2 4 by decide) (.cons (show localGraph.Adj 4 11 by decide) (.cons (show localGraph.Adj 11 9 by decide) (.cons (show localGraph.Adj 9 0 by decide) (.nil)))))))

lemma cycle6_cycle : cycle6.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

abbrev rest6 := exampleGraph \ maskGraph (pattern 6)

def rest6p0 : rest6.Walk 3 3 :=
  .cons (show rest6.Adj 3 7 by decide) (.cons (show rest6.Adj 7 9 by decide) (.cons (show rest6.Adj 9 4 by decide) (.cons (show rest6.Adj 4 14 by decide) (.cons (show rest6.Adj 14 8 by decide) (.cons (show rest6.Adj 8 10 by decide) (.cons (show rest6.Adj 10 13 by decide) (.cons (show rest6.Adj 13 6 by decide) (.cons (show rest6.Adj 6 5 by decide) (.cons (show rest6.Adj 5 12 by decide) (.cons (show rest6.Adj 12 3 by decide) (.nil)))))))))))

lemma rest6p0_cycle : rest6p0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def rest6p1 : rest6.Walk 0 0 :=
  .cons (show rest6.Adj 0 7 by decide) (.cons (show rest6.Adj 7 13 by decide) (.cons (show rest6.Adj 13 3 by decide) (.cons (show rest6.Adj 3 2 by decide) (.cons (show rest6.Adj 2 14 by decide) (.cons (show rest6.Adj 14 10 by decide) (.cons (show rest6.Adj 10 6 by decide) (.cons (show rest6.Adj 6 11 by decide) (.cons (show rest6.Adj 11 5 by decide) (.cons (show rest6.Adj 5 1 by decide) (.cons (show rest6.Adj 1 8 by decide) (.cons (show rest6.Adj 8 0 by decide) (.nil))))))))))))

lemma rest6p1_cycle : rest6p1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma rest6_bound : number rest6 ≤ 2 := by
  apply number_le_two_cycles rest6p0 rest6p1 rest6p0_cycle rest6p1_cycle
  · apply List.disjoint_toFinset_iff_disjoint.mp
    decide
  · decide

lemma cycle0_mask : cycle0.toSubgraph.spanningCoe = maskGraph (pattern 0) := by
  ext x y
  change s(x,y) ∈ cycle0.toSubgraph.edgeSet ↔ _
  rw [Walk.mem_edges_toSubgraph]
  revert x y
  decide

lemma cycle1_mask : cycle1.toSubgraph.spanningCoe = maskGraph (pattern 1) := by
  ext x y
  change s(x,y) ∈ cycle1.toSubgraph.edgeSet ↔ _
  rw [Walk.mem_edges_toSubgraph]
  revert x y
  decide

lemma cycle2_mask : cycle2.toSubgraph.spanningCoe = maskGraph (pattern 2) := by
  ext x y
  change s(x,y) ∈ cycle2.toSubgraph.edgeSet ↔ _
  rw [Walk.mem_edges_toSubgraph]
  revert x y
  decide

lemma cycle3_mask : cycle3.toSubgraph.spanningCoe = maskGraph (pattern 3) := by
  ext x y
  change s(x,y) ∈ cycle3.toSubgraph.edgeSet ↔ _
  rw [Walk.mem_edges_toSubgraph]
  revert x y
  decide

lemma cycle4_mask : cycle4.toSubgraph.spanningCoe = maskGraph (pattern 4) := by
  ext x y
  change s(x,y) ∈ cycle4.toSubgraph.edgeSet ↔ _
  rw [Walk.mem_edges_toSubgraph]
  revert x y
  decide

lemma cycle5_mask : cycle5.toSubgraph.spanningCoe = maskGraph (pattern 5) := by
  ext x y
  change s(x,y) ∈ cycle5.toSubgraph.edgeSet ↔ _
  rw [Walk.mem_edges_toSubgraph]
  revert x y
  decide

lemma cycle6_mask : cycle6.toSubgraph.spanningCoe = maskGraph (pattern 6) := by
  ext x y
  change s(x,y) ∈ cycle6.toSubgraph.edgeSet ↔ _
  rw [Walk.mem_edges_toSubgraph]
  revert x y
  decide

lemma mapLe_spanning {W : Type*} {G H : SimpleGraph W} (h : G ≤ H)
    {u v : W} (p : G.Walk u v) :
    (p.mapLe h).toSubgraph.spanningCoe = p.toSubgraph.spanningCoe := by
  ext x y
  simp only [SimpleGraph.Subgraph.spanningCoe_adj,Walk.adj_toSubgraph_mapLe]

lemma pattern_cycle (i : Fin 7) :
    ∃ (u : Fin 15) (p : exampleGraph.Walk u u), p.IsCycle ∧ p.toSubgraph.spanningCoe = maskGraph (pattern i) := by
  fin_cases i
  · exact ⟨4,cycle0.mapLe local_le,cycle0_cycle.mapLe local_le,
      (mapLe_spanning local_le cycle0).trans cycle0_mask⟩
  · exact ⟨2,cycle1.mapLe local_le,cycle1_cycle.mapLe local_le,
      (mapLe_spanning local_le cycle1).trans cycle1_mask⟩
  · exact ⟨2,cycle2.mapLe local_le,cycle2_cycle.mapLe local_le,
      (mapLe_spanning local_le cycle2).trans cycle2_mask⟩
  · exact ⟨0,cycle3.mapLe local_le,cycle3_cycle.mapLe local_le,
      (mapLe_spanning local_le cycle3).trans cycle3_mask⟩
  · exact ⟨0,cycle4.mapLe local_le,cycle4_cycle.mapLe local_le,
      (mapLe_spanning local_le cycle4).trans cycle4_mask⟩
  · exact ⟨0,cycle5.mapLe local_le,cycle5_cycle.mapLe local_le,
      (mapLe_spanning local_le cycle5).trans cycle5_mask⟩
  · exact ⟨0,cycle6.mapLe local_le,cycle6_cycle.mapLe local_le,
      (mapLe_spanning local_le cycle6).trans cycle6_mask⟩

lemma pattern_rest_bound (i : Fin 7) : number (exampleGraph \ maskGraph (pattern i)) ≤ 2 := by
  fin_cases i
  · exact rest0_bound
  · exact rest1_bound
  · exact rest2_bound
  · exact rest3_bound
  · exact rest4_bound
  · exact rest5_bound
  · exact rest6_bound

lemma subgraph_is_mask (R : SimpleGraph (Fin 15)) (hR : R ≤ localGraph) :
    ∃ b : Fin 10 → Bool, R = maskGraph b := by
  classical
  let b : Fin 10 → Bool := fun i => decide (R.Adj (ends i).1 (ends i).2)
  refine ⟨b,?_⟩
  ext x y
  constructor
  · intro h
    obtain ⟨i,_,hi | hi⟩ := hR h
    · rcases hi with ⟨rfl,rfl⟩
      exact ⟨i,by simpa only [b,decide_eq_true_eq] using h,Or.inl ⟨rfl,rfl⟩⟩
    · rcases hi with ⟨rfl,rfl⟩
      exact ⟨i,by simpa only [b,decide_eq_true_eq] using h.symm,Or.inr ⟨rfl,rfl⟩⟩
  · rintro ⟨i,hi,h | h⟩
    · rcases h with ⟨rfl,rfl⟩
      exact of_decide_eq_true hi
    · rcases h with ⟨rfl,rfl⟩
      exact (of_decide_eq_true hi).symm

lemma even_subgraph_classification (R : SimpleGraph (Fin 15)) (hRK : R ≤ localGraph)
    (heven : ∀ v, Even (R.degree v)) (hne : R ≠ ⊥) :
    ∃ i : Fin 7, R = maskGraph (pattern i) := by
  classical
  obtain ⟨b,rfl⟩ := subgraph_is_mask R hRK
  have he : ∀ v, Even ((maskGraph b).degree v) := by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heven v
  rcases even_mask_classification b he with hb | ⟨i,hi⟩
  · exfalso
    apply hne
    rw [hb]
    ext x y
    simp [maskGraph]
  · exact ⟨i,congrArg maskGraph hi⟩

/-- All seven cycles of the local K4-subdivision are exposable in optimal
partitions of the ambient graph. In fact, every nonempty even local subgraph
has this property. This is a local, not global, criticality statement. -/
lemma every_local_cycle_exposable (R : SimpleGraph (Fin 15)) (hRK : R ≤ localGraph)
    (heven : ∀ v, Even (R.degree v)) (hne : R ≠ ⊥) :
    number (exampleGraph \ R) + 1 = number exampleGraph := by
  classical
  obtain ⟨i,rfl⟩ := even_subgraph_classification R hRK heven hne
  have hu := pattern_rest_bound i
  obtain ⟨u,p,hp,heq⟩ := pattern_cycle i
  have hl := number_restore_cycle hp
  rw [heq] at hl
  rw [EvenFractionalBase.number_eq_three] at hl ⊢
  omega

lemma no_unit_certificate : ¬ ∃ w : Sym2 (Fin 15) → ℝ, UnitCycleWeight localGraph w := by
  rintro ⟨w,hw⟩
  have h0 := hw 4 cycle0 cycle0_cycle
  have h1 := hw 2 cycle1 cycle1_cycle
  have h2 := hw 2 cycle2 cycle2_cycle
  have h3 := hw 0 cycle3 cycle3_cycle
  have h4 := hw 0 cycle4 cycle4_cycle
  have h5 := hw 0 cycle5 cycle5_cycle
  have h6 := hw 0 cycle6 cycle6_cycle
  simp only [walkWeight,cycle0,cycle1,cycle2,cycle3,cycle4,cycle5,cycle6,Walk.edges_cons,Walk.edges_nil,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at h0 h1 h2 h3 h4 h5 h6
  simp only [(show s((9:Fin 15),0) = s(0,9) from Sym2.eq_swap),
    (show s((11:Fin 15),4) = s(4,11) from Sym2.eq_swap),
    (show s((11:Fin 15),5) = s(5,11) from Sym2.eq_swap),
    (show s((11:Fin 15),9) = s(9,11) from Sym2.eq_swap),
    (show s((12:Fin 15),2) = s(2,12) from Sym2.eq_swap),
    (show s((12:Fin 15),5) = s(5,12) from Sym2.eq_swap)] at h0 h1 h2 h3 h4 h5 h6
  linarith

open scoped Classical in
lemma local_obstruction :
    (∀ v, Even (exampleGraph.degree v)) ∧ localGraph ≤ exampleGraph ∧
    (∀ v, localGraph.degree v ≤ 3) ∧
    (¬ ∃ w : Sym2 (Fin 15) → ℝ, UnitCycleWeight localGraph w) ∧
    (∀ R ≤ localGraph, (∀ v, Even (R.degree v)) → R ≠ ⊥ →
      number (exampleGraph \ R) + 1 = number exampleGraph) := by
  refine ⟨?_,local_le,?_,no_unit_certificate,?_⟩
  · intro v
    rw [exampleGraph_regular v]
    decide
  · intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using local_subcubic v
  · intro R hR he hn
    apply every_local_cycle_exposable R hR ?_ hn
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he v

open scoped Classical in
/-- An uncertifiable subcubic subgraph does not by itself supply an even
subgraph whose deletion preserves the ambient optimum. -/
lemma local_deletion_principle_false :
    ¬ (∀ {W : Type} [Fintype W] (G K : SimpleGraph W),
      (∀ v, Even (G.degree v)) → K ≤ G → (∀ v, K.degree v ≤ 3) →
      (¬ ∃ w : Sym2 W → ℝ, UnitCycleWeight K w) →
      ∃ R ≤ K, (∀ v, Even (R.degree v)) ∧ R ≠ ⊥ ∧ number G ≤ number (G \ R)) := by
  intro h
  obtain ⟨he,hKG,hdeg,hnocert,hlocal⟩ := local_obstruction
  have ht := h exampleGraph localGraph
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at ht he hdeg hlocal
  obtain ⟨R,hRK,hR,hne,hn⟩ := ht he hKG hdeg hnocert
  have heq := hlocal R hRK hR hne
  omega

#print axioms even_mask_classification
#print axioms every_local_cycle_exposable
#print axioms no_unit_certificate
#print axioms local_obstruction
#print axioms local_deletion_principle_false
end Erdos184Work.LocalObstruction
