import Submission.MinimalSingletons

/-! The arbitrary-edge hull of an even-minimal graph differs from its own
minimum decomposition number by at most the order minus two. This bounds
the possible additive gain, not the decomposition number itself. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.EvenCoreHullGap
open Critical EvenCore EdgeHull MaximumCycles
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V]

lemma proper_subgraph_bound {G R : SimpleGraph V} (hm : EvenMinimal G)
    (hRG : R ≤ G) (hne : R ≠ G) :
    number R + 2 ≤ number G + Fintype.card V := by
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum R
  obtain ⟨E,F,hER,hE,hunion,hnum,hFcard⟩ :=
    MinimalSingletons.minimum_split D hD hdec hcard
  have hEG : E ≤ G := hER.trans hRG
  have hEne : E ≠ G := by
    intro heq
    exact hne (le_antisymm hRG (heq ▸ hER))
  have hc := hm E hEG (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hE) (edge_card_lt_of_ne hEG hEne)
  have hs := CycleCertificates.acyclic_edge_count_pred
    (subfamilyGraph (edgePieces D)) (minimal_edge_pieces_acyclic D hD hdec hcard)
  have he := edgePieces_graph_card D hdec
  have hGne : G ≠ ⊥ := by
    intro heq
    have hRbot : R = ⊥ := le_bot_iff.mp (heq ▸ hRG)
    exact hne (hRbot.trans heq.symm)
  obtain ⟨a,b,hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hGne
  have hn : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨a,b,hab.ne⟩
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hs he hn ⊢
  omega

lemma hull_le_number_add_order_sub_two {G : SimpleGraph V} (hm : EvenMinimal G) :
    value G ≤ number G + (Fintype.card V - 2) := by
  apply (value_le_iff G _).mpr
  intro R hRG
  by_cases heq : R = G
  · rw [heq]
    exact Nat.le_add_right _ _
  · have h := proper_subgraph_bound hm hRG heq
    omega

/-- A fixed relative hull gain on a core already forces a linear bound on
that core. No such relative gain is supplied by this theorem. -/
lemma number_bound_of_relative_gain {G : SimpleGraph V} (hm : EvenMinimal G)
    (t : ℕ) (hgain : (t + 1) * number G ≤ t * value G) :
    number G ≤ t * (Fintype.card V - 2) := by
  have hu := Nat.mul_le_mul_left t (hull_le_number_add_order_sub_two hm)
  nlinarith

/-- The previously proved support boost and the upper gap bound coexist;
neither supplies an unconditional estimate of the decomposition number. -/
lemma gap_sandwich {G : SimpleGraph V} (hm : EvenMinimal G)
    (he : ∀ v, Even (Nat.card (G.neighborSet v))) :
    G.support.ncard ≤ 6 * (value G - number G) ∧
      value G - number G ≤ Fintype.card V - 2 := by
  have hl := StarHullBoost.supported_order_boost G he
  have hu := hull_le_number_add_order_sub_two hm
  have hk := number_le_value G
  omega

end Erdos184Work.EvenCoreHullGap
#print axioms Erdos184Work.EvenCoreHullGap.proper_subgraph_bound
#print axioms Erdos184Work.EvenCoreHullGap.hull_le_number_add_order_sub_two
#print axioms Erdos184Work.EvenCoreHullGap.number_bound_of_relative_gain
#print axioms Erdos184Work.EvenCoreHullGap.gap_sandwich
