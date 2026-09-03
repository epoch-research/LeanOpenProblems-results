import Submission.InvariantTrianglePaths
import Submission.TwoTerminalGluing

/-!
Every simple path in a finite even graph has an edge-disjoint return path.
Combined with the invariant-triangle restriction, this gives cycle completion
inside the triangle-deleted remainder. No uniform decomposition bound follows.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.InvariantPathCompletion
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 800000

lemma reachable_of_two_odd (H : SimpleGraph V) {a b : V}
    (hpar : ∀ x, Even (H.degree x) ↔ x ≠ a ∧ x ≠ b) : H.Reachable a b := by
  let c := H.connectedComponentMk a
  let aa : c := ⟨a, (c.mem_supp_iff a).mpr rfl⟩
  have hd (x : c) : c.toSimpleGraph.degree x = H.degree x.val := by
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using component_degree H c x
  have ha : Odd (c.toSimpleGraph.degree aa) := by
    rw [hd]
    apply Nat.not_even_iff_odd.mp
    intro hh
    exact ((hpar a).mp hh).1 rfl
  obtain ⟨w,hw,ho⟩ := c.toSimpleGraph.exists_ne_odd_degree_of_exists_odd_degree aa ha
  have hwa : w.val ≠ a := by
    intro hh
    exact hw (Subtype.ext hh)
  have hwb : w.val = b := by
    by_contra hh
    have he := (hpar w.val).mpr ⟨hwa,hh⟩
    rw [hd] at ho
    exact Nat.not_even_iff_odd.mpr ho he
  apply ConnectedComponent.exact
  have hwc : H.connectedComponentMk w.val = H.connectedComponentMk a :=
    (c.mem_supp_iff _).mp w.property
  simpa only [hwb] using hwc.symm

lemma path_spanning_even_iff {H : SimpleGraph V} {a b : V} (p : H.Walk a b)
    (hp : p.IsPath) (hab : a ≠ b) (x : V) :
    Even (p.toSubgraph.spanningCoe.degree x) ↔ x ≠ a ∧ x ≠ b := by
  let P := p.toSubgraph.spanningCoe
  have hm : ∀ e ∈ p.edges, e ∈ P.edgeSet := by
    intro e he
    exact p.mem_edges_toSubgraph.mpr he
  let q := p.transfer P hm
  have hq : q.IsPath := hp.transfer hm
  have hE : q.IsEulerian := by
    apply hq.isTrail.isEulerian_of_forall_mem
    intro e he
    simpa only [q,Walk.edges_transfer] using p.mem_edges_toSubgraph.mp he
  have hh := hE.even_degree_iff (x := x)
  exact ⟨fun hx => hh.mp hx hab, fun hx => hh.mpr (fun _ => hx)⟩

/-- Removing a prescribed simple terminal path leaves precisely its two
endpoints odd, so they remain connected in the edge complement. -/
lemma residual_path_reachable (H : SimpleGraph V) (he : ∀ x, Even (H.degree x))
    {a b : V} (hab : a ≠ b) (p : H.Walk a b) (hp : p.IsPath) :
    (H \ p.toSubgraph.spanningCoe).Reachable a b := by
  apply reachable_of_two_odd _
  intro x
  have hd := degree_sdiff_of_le p.toSubgraph.spanningCoe_le x
  have hle : p.toSubgraph.spanningCoe.degree x ≤ H.degree x :=
    degree_le_of_le p.toSubgraph.spanningCoe_le
  have hh := path_spanning_even_iff p hp hab x
  have hx := he x
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    at hd hle hh hx ⊢
  rw [hd,Nat.even_sub hle]
  simpa only [hx,true_iff] using hh

/-- The return path is genuinely simple and avoids all edges of the
specified path. The ambient graph need not be connected. -/
lemma exists_edge_disjoint_path (H : SimpleGraph V) (he : ∀ x, Even (H.degree x))
    {a b : V} (hab : a ≠ b) (p : H.Walk a b) (hp : p.IsPath) :
    ∃ q : H.Walk a b, q.IsPath ∧ p.edges.Disjoint q.edges := by
  obtain ⟨q,hq⟩ := (residual_path_reachable H he hab p hp).exists_isPath
  let hRH : H \ p.toSubgraph.spanningCoe ≤ H := sdiff_le
  refine ⟨q.mapLe hRH,hq.mapLe hRH,?_⟩
  intro e hep heq
  rw [Walk.edges_mapLe_eq_edges] at heq
  have hr := q.edges_subset_edgeSet heq
  rw [edgeSet_sdiff] at hr
  exact hr.2 (p.mem_edges_toSubgraph.mpr hep)

/-- In an even restriction outside a triangle, invariance forces every simple
path between the two remaining triangle vertices to complete to a simple cycle.
This is stronger than merely finding an edge-disjoint return path. -/
lemma residual_path_cycle_completion {G : SimpleGraph V}
    (he : ∀ x, Even (G.degree x)) (hi : InvariantPartitions.HasInvariantCount G)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hab : G.Adj a b)
    {A : SimpleGraph V} (hA : A ≤ G.deleteIncidenceSet v) (hnab : ¬ A.Adj a b)
    (heA : ∀ x, Even (A.degree x)) (p : A.Walk a b) (hp : p.IsPath) :
    ∃ q : A.Walk a b, q.IsPath ∧ p.edges.Disjoint q.edges ∧
      (p.append q.reverse).IsCycle := by
  obtain ⟨q,hq,hd⟩ := exists_edge_disjoint_path A heA hab.ne p hp
  have hinter := InvariantTrianglePaths.residual_paths_intersect_only_at_ends
    he hi hva hvb hab hA hnab p q hp hq hd
  refine ⟨q,hq,hd,TwoTerminalGluing.append_isCycle_of_paths p q.reverse hp hq.reverse
    hab.ne ?_ ?_⟩
  · simpa only [Walk.edges_reverse,List.disjoint_reverse_right] using hd
  · simpa only [Walk.support_reverse,List.mem_reverse] using hinter

end Erdos184.InvariantPathCompletion
