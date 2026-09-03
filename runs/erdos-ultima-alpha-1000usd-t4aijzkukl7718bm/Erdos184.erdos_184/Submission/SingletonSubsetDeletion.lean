import Submission.OptimalSingletonDeletion

/-! Exact deletion and inheritance along an optimal singleton forest.
These lemmas do not assert that global minimality survives deletion, nor
that a uniform vertex-deletion loss bound holds. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SingletonExchange
open Critical EdgeHull
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V]

lemma singleton_sdiff_card {F T : SimpleGraph V} (hTF : T ≤ F) :
    Nat.card (F \ T).edgeSet + Nat.card T.edgeSet = Nat.card F.edgeSet := by
  have h := Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hTF)
  rw [← SimpleGraph.edgeFinset_sdiff] at h
  simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using h

lemma singleton_sup_card {R T : SimpleGraph V} (hd : Disjoint R.edgeSet T.edgeSet) :
    Nat.card (R ⊔ T).edgeSet = Nat.card R.edgeSet + Nat.card T.edgeSet := by
  have hf : Disjoint R.edgeFinset T.edgeFinset := by
    apply Finset.disjoint_left.mpr
    intro e heR heT
    exact Set.disjoint_left.mp hd (R.mem_edgeFinset.mp heR) (T.mem_edgeFinset.mp heT)
  have h := Finset.card_union_of_disjoint hf
  rw [← SimpleGraph.edgeFinset_sup] at h
  simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using h

lemma Optimal.delete_subset {G F T : SimpleGraph V}
    (h : Optimal G F) (hTF : T ≤ F) :
    Optimal (G \ T) (F \ T) ∧
      number (G \ T) + Nat.card T.edgeSet = number G := by
  have hTG := hTF.trans h.1
  have hFG : F \ T ≤ G \ T := sdiff_le_sdiff_right h.1
  have heq : (G \ T) \ (F \ T) = G \ F := by
    ext x y
    simp only [SimpleGraph.sdiff_adj]
    have ht : T.Adj x y → F.Adj x y := fun ht => hTF ht
    tauto
  have hc := singleton_sdiff_card hTF
  have hlo := split_lower_bound hTG
  have hhi := split_lower_bound hFG
  rw [heq] at hhi
  have hn := h.2.2
  have hdel : number (G \ T) + Nat.card T.edgeSet = number G := by omega
  refine ⟨⟨hFG, ?_, ?_⟩, hdel⟩
  · simpa only [heq] using h.2.1
  · rw [heq]
    omega

/-- Restoring singleton edges transports an optimum when the counts add. -/
lemma Optimal.extend_singletons {G T R : SimpleGraph V}
    (hTG : T ≤ G)
    (hadd : number (G \ T) + Nat.card T.edgeSet = number G)
    (hR : Optimal (G \ T) R) : Optimal G (R ⊔ T) := by
  have hRG : R ≤ G := hR.1.trans sdiff_le
  have hd : Disjoint R.edgeSet T.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heR heT
    have he := SimpleGraph.edgeSet_mono hR.1 heR
    rw [SimpleGraph.edgeSet_sdiff] at he
    exact he.2 heT
  have heq : G \ (R ⊔ T) = (G \ T) \ R := by
    ext x y
    simp only [SimpleGraph.sdiff_adj, SimpleGraph.sup_adj]
    tauto
  have hc := singleton_sup_card hd
  refine ⟨sup_le hRG hTG, ?_, ?_⟩
  · simpa only [heq] using hR.2.1
  · rw [heq, hc]
    have hn := hR.2.2
    omega

lemma Best.delete_subset {G F T : SimpleGraph V}
    (h : Best G F) (hTF : T ≤ F) : Best (G \ T) (F \ T) := by
  obtain ⟨ho, hn⟩ := h.1.delete_subset hTF
  refine ⟨ho, ?_⟩
  intro R hR
  have he := hR.extend_singletons (hTF.trans h.1.1) hn
  have hb := h.2 (R ⊔ T) he
  have hd : Disjoint R.edgeSet T.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heR heT
    have he := SimpleGraph.edgeSet_mono hR.1 heR
    rw [SimpleGraph.edgeSet_sdiff] at he
    exact he.2 heT
  rw [singleton_sup_card hd] at hb
  have hc := singleton_sdiff_card hTF
  omega

/-- A single optimal singleton deletion is hull-saturated if the source is
strictly minimal. The theorem deliberately does not claim strict minimality
of the cofactor. -/
lemma Best.single_deletion_saturated {G F T : SimpleGraph V}
    (h : Best G F) (hm : Minimal G) (hTF : T ≤ F)
    (hcard : Nat.card T.edgeSet = 1) :
    Best (G \ T) (F \ T) ∧
      value (G \ T) = number (G \ T) ∧
      number (G \ T) + 1 = number G := by
  have hn := (h.1.delete_subset hTF).2
  rw [hcard] at hn
  have hne : G \ T ≠ G := by
    intro he
    rw [he] at hn
    omega
  have hh := MinimalSingletons.proper_hull_lt hm sdiff_le hne
  have hlo := number_le_value (G \ T)
  exact ⟨h.delete_subset hTF, by omega, hn⟩

/-- Deleting several optimal singleton edges need not preserve saturation.
The difference between hull and raw number is bounded here, not set to zero. -/
lemma Best.deletion_hull_gap {G F T : SimpleGraph V}
    (h : Best G F) (hm : Minimal G) (hTF : T ≤ F)
    (hpos : 0 < Nat.card T.edgeSet) :
    value (G \ T) + 1 ≤ number (G \ T) + Nat.card T.edgeSet := by
  have hn := (h.1.delete_subset hTF).2
  have hne : G \ T ≠ G := by
    intro he
    rw [he] at hn
    omega
  have hh := MinimalSingletons.proper_hull_lt hm sdiff_le hne
  omega

end Erdos184Work.SingletonExchange
#print axioms Erdos184Work.SingletonExchange.Optimal.delete_subset
#print axioms Erdos184Work.SingletonExchange.Best.delete_subset
#print axioms Erdos184Work.SingletonExchange.Best.single_deletion_saturated
#print axioms Erdos184Work.SingletonExchange.Best.deletion_hull_gap
