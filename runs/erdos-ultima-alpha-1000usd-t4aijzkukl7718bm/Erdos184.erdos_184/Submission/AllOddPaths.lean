import Submission.EndpointDefectAbsorption

/-! The all-odd simple-path decomposition theorem, with no degree restriction. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The residual of a maximal endpoint-path packing is acyclic. -/
lemma Maximal.residual_acyclic {L : List (Piece G)}
    (hL : Maximal L) :
    (G \ coveredGraph L).IsAcyclic := by
  intro z c hc
  have hle : G \ coveredGraph L ≤ G := sdiff_le
  apply OccurrenceFan.no_unused_cycle hL (c.mapLe hle) (hc.mapLe hle)
  intro e he hc'
  have hcr : e ∈ (G \ coveredGraph L).edgeSet :=
    c.edges_subset_edgeSet (by simpa only [Walk.edges_mapLe_eq_edges] using hc')
  rw [SimpleGraph.edgeSet_sdiff] at hcr
  exact hcr.2 ((coveredGraph_edgeSet L e).mpr he)

/-- In an all-odd graph the maximal family covers every edge. -/
lemma Maximal.covers_all_odd {L : List (Piece G)} (hL : Maximal L)
    (hodd : ∀ v, Odd (Nat.card (G.neighborSet v))) :
    ∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList L := by
  have hb : G \ coveredGraph L = ⊥ := by
    apply acyclic_even_eq_bot (G \ coveredGraph L) (hL.residual_acyclic)
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
      hL.1.residual_even hodd v
  have hle : G ≤ coveredGraph L := sdiff_eq_bot_iff.mp hb
  intro e
  refine ⟨fun he => (coveredGraph_edgeSet L e).mp (SimpleGraph.edgeSet_mono hle he),?_⟩
  intro he
  exact edgeList_mem_edgeSet he

/-- Every all-odd finite graph has a simple-path
partition with exactly half as many paths as vertices, and unique endpoints. -/
lemma all_odd_path_partition (G : SimpleGraph V)
    (hodd : ∀ v, Odd (Nat.card (G.neighborSet v))) :
    ∃ L : List (Piece G),
      Admissible L ∧ (∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList L) ∧
      2 * L.length = Fintype.card V := by
  obtain ⟨L,hL⟩ := exists_maximal G hodd
  exact ⟨L,hL.1,hL.covers_all_odd hodd,hL.1.path_count⟩

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.all_odd_path_partition
