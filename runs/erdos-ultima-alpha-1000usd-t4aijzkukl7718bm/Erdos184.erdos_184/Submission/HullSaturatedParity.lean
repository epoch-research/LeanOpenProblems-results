import Submission.MinimalParityCorrection
import Submission.MaximizerReachability

/-! Parity-correction support bounds require hull saturation, not strict
minimality. These bounds do not control the decomposition number. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.HullSaturatedParity
open Critical EdgeHull MinimalSingletons
set_option maxHeartbeats 800000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma even_support_bound (hG : value G = number G)
    (T : SimpleGraph V) (hTG : T ≤ G)
    (he : ∀ v, Even (Nat.card ((G \ T).neighborSet v))) :
    (G \ T).support.ncard ≤ 6 * Nat.card T.edgeSet := by
  have hb := StarHullBoost.supported_order_boost (G \ T) he
  have hh := EdgeHull.monotone (show G \ T ≤ G from sdiff_le)
  rw [hG] at hh
  have hu := number_sdiff_add_le G T hTG
  have ht := number_le_edges T
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at ht
  omega

lemma support_bound (hG : value G = number G)
    (T : SimpleGraph V) (hTG : T ≤ G)
    (he : ∀ v, Even (Nat.card ((G \ T).neighborSet v))) :
    G.support.ncard ≤ 8 * Nat.card T.edgeSet := by
  have hE := even_support_bound hG T hTG he
  have hT := support_card_le_twice_edges T
  have hs := support_sup_le (G \ T) T
  rw [sdiff_sup_cancel hTG] at hs
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hT
  omega

/-- Cycle cofactors of globally minimal graphs meet the weaker hypothesis. -/
lemma cycle_cofactor_support_bound (hm : Minimal G)
    {u : V} (p : G.Walk u u) (hp : p.IsCycle)
    (T : SimpleGraph V) (hT : T ≤ G \ p.toSubgraph.spanningCoe)
    (he : ∀ v, Even (Nat.card (((G \ p.toSubgraph.spanningCoe) \ T).neighborSet v))) :
    (G \ p.toSubgraph.spanningCoe).support.ncard ≤ 8 * Nat.card T.edgeSet :=
  support_bound (hm.cycle_cofactor_hull hp) T hT he

end Erdos184Work.HullSaturatedParity
#print axioms Erdos184Work.HullSaturatedParity.support_bound
#print axioms Erdos184Work.HullSaturatedParity.cycle_cofactor_support_bound
