import Submission.MinimalSingletons

/-! Every parity correction in a nonempty globally edge-minimal graph has
linear size in the support. This does not bound its decomposition number. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.MinimalParityCorrection
open Critical EdgeHull MinimalSingletons
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma correction_even_support_bound (hm : Minimal G) (hne : G ≠ ⊥)
    (T : SimpleGraph V) (hTG : T ≤ G)
    (he : ∀ v, Even (Nat.card ((G \ T).neighborSet v))) :
    (G \ T).support.ncard + 6 ≤ 6 * Nat.card T.edgeSet := by
  have hp : G \ T ≠ G := by
    intro h
    apply hne
    apply hm.edgeCritical.eq_bot_of_even
    simpa only [h,← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he
  have hg := even_support_gap hm (sdiff_le : G \ T ≤ G) hp he
  have hu := number_sdiff_add_le G T hTG
  have ht := number_le_edges T
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at ht
  omega

lemma correction_support_bound (hm : Minimal G) (hne : G ≠ ⊥)
    (T : SimpleGraph V) (hTG : T ≤ G)
    (he : ∀ v, Even (Nat.card ((G \ T).neighborSet v))) :
    G.support.ncard + 6 ≤ 8 * Nat.card T.edgeSet := by
  have hE := correction_even_support_bound hm hne T hTG he
  have hT := support_card_le_twice_edges T
  have hs := support_sup_le (G \ T) T
  rw [sdiff_sup_cancel hTG] at hs
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hT
  omega

lemma correction_nonempty (hm : Minimal G) (hne : G ≠ ⊥)
    (T : SimpleGraph V) (hTG : T ≤ G)
    (he : ∀ v, Even (Nat.card ((G \ T).neighborSet v))) :
    0 < Nat.card T.edgeSet := by
  have h := correction_support_bound hm hne T hTG he
  omega

end Erdos184Work.MinimalParityCorrection
#print axioms Erdos184Work.MinimalParityCorrection.correction_support_bound
#print axioms Erdos184Work.MinimalParityCorrection.correction_even_support_bound
