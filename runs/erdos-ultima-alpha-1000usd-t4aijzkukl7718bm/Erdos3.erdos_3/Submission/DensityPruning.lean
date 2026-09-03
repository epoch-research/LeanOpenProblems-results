import FormalConjecturesUtil

/-! Removing a small part of a finite set preserves a positive density gain. -/
namespace Erdos3DensityPruning
open Finset
open scoped Classical
set_option maxHeartbeats 1000000

variable {X : Type*}

lemma filter_card_le_after_pruning (S T : Finset X) (P : X → Prop) [DecidablePred P] :
    (S.filter P).card ≤ (T.filter P).card + (S \ T).card := by
  calc
    _ ≤ ((T.filter P) ∪ (S \ T)).card := by
      apply card_le_card
      intro x hx
      by_cases ht : x ∈ T
      · exact mem_union_left _ (mem_filter.mpr ⟨ht,(mem_filter.mp hx).2⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨(mem_filter.mp hx).1,ht⟩)
    _ ≤ _ := card_union_le _ _

/-- A loss of at most half the gain times the original size preserves half
of the density gain, as well as at least half of the original cardinality. -/
theorem density_increment_pruning (S T : Finset X) (P : X → Prop) [DecidablePred P]
    (hS : S.Nonempty) (hTS : T ⊆ S) {α g : ℝ} (hα : 0 ≤ α) (hg : 0 < g)
    (hinc : α+g ≤ ((S.filter P).card : ℝ)/(S.card : ℝ))
    (hloss : ((S \ T).card : ℝ) ≤ g/2*(S.card : ℝ)) :
    T.Nonempty ∧ (S.card : ℝ)/2 ≤ (T.card : ℝ) ∧
      α+g/2 ≤ ((T.filter P).card : ℝ)/(T.card : ℝ) := by
  have hSc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTc : (T.card : ℝ) ≤ S.card := by exact_mod_cast card_le_card hTS
  have hPc : ((S.filter P).card : ℝ) ≤ S.card := by
    exact_mod_cast card_le_card (filter_subset P S)
  have hinc' := (le_div_iff₀ hSc).mp hinc
  have hg1 : g ≤ 1 := by nlinarith
  have he : ((S \ T).card : ℝ)+(T.card : ℝ) = S.card := by
    exact_mod_cast card_sdiff_add_card_eq_card hTS
  have hhalf : (S.card : ℝ)/2 ≤ T.card := by nlinarith
  have hTpos : (0 : ℝ) < T.card := lt_of_lt_of_le (half_pos hSc) hhalf
  have hT : T.Nonempty := card_pos.mp (by exact_mod_cast hTpos)
  have hP : ((S.filter P).card : ℝ) ≤ (T.filter P).card+(S \ T).card := by
    exact_mod_cast filter_card_le_after_pruning S T P
  have hlower : (α+g/2)*(S.card : ℝ) ≤ (T.filter P).card := by nlinarith
  refine ⟨hT,hhalf,(le_div_iff₀ hTpos).mpr ?_⟩
  exact (mul_le_mul_of_nonneg_left hTc (by positivity)).trans hlower

#print axioms density_increment_pruning
end Erdos3DensityPruning
