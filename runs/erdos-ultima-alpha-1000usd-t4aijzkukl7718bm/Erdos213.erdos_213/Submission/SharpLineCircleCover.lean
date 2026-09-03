import Submission.CircleCoverReduction

/-! A sharp geometric bound for a line-plus-generalized-circle cover.
No claim that arbitrary integral-distance sets admit such a cover. -/
open EuclideanGeometry
namespace Erdos213.CircleCoverReduction
open InversionReduction
set_option maxHeartbeats 2000000

/-- General position allows at most two points on the line and at most
three on the generalized circle. This uses no distance arithmetic. -/
theorem general_position_line_generalized_card_le_five {S : Finset ℝ²}
    (hS : InGeneralPosition (S : Set ℝ²)) {L C : Set ℝ²}
    (hL : Collinear ℝ L) (hC : OnGeneralizedCircle C)
    (hcover : (S : Set ℝ²)⊆L∪C) : S.card≤5 := by
  classical
  let A := S.filter (fun p => p∈L)
  let B := S.filter (fun p => p∈C)
  have hA : A.card≤2 := by
    by_contra! h
    have hn : 3≤(A : Set ℝ²).ncard := by
      rw [Set.ncard_coe_finset]
      omega
    obtain ⟨Q,hQA,hQ⟩ := Set.exists_subset_card_eq hn
    obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Set.ncard_eq_three.mp hQ
    have ha : a∈A := hQA (by simp)
    have hb : b∈A := hQA (by simp)
    have hc : c∈A := hQA (by simp)
    have hline : Collinear ℝ ({a,b,c} : Set ℝ²) :=
      hL.subset (fun p hp => (Finset.mem_filter.mp (hQA hp)).2)
    exact hS.1 (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
      (Finset.mem_filter.mp hc).1 hab hbc hac hline
  have hB : B.card≤3 := by
    have hweak : NoFourGeneralized (B : Set ℝ²) := by
      intro Q hQB hn
      exact noFour_of_general_position hS Q
        (fun p hp => (Finset.mem_filter.mp (hQB hp)).1) hn
    have hgen : OnGeneralizedCircle (B : Set ℝ²) :=
      generalized_mono hC (fun p hp => (Finset.mem_filter.mp hp).2)
    simpa using weak_card_le_three_mul_cover hweak (coveredBy_one hgen)
  have hsub : S⊆A∪B := by
    intro p hp
    rcases hcover hp with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,h⟩)
  calc
    S.card≤(A∪B).card := Finset.card_le_card hsub
    _ ≤A.card+B.card := Finset.card_union_le _ _
    _ ≤5 := by omega

/-- The corresponding weak-general-position cap is six. -/
theorem weak_line_generalized_card_le_six {S : Finset ℝ²}
    (hS : NoFourGeneralized (S : Set ℝ²)) {L C : Set ℝ²}
    (hL : Collinear ℝ L) (hC : OnGeneralizedCircle C)
    (hcover : (S : Set ℝ²)⊆L∪C) : S.card≤6 := by
  have hc : CoveredBy (S : Set ℝ²) 2 :=
    ((coveredBy_one (generalized_of_collinear hL)).union (coveredBy_one hC)).mono hcover
  simpa using weak_card_le_three_mul_cover hS hc

#print axioms general_position_line_generalized_card_le_five
#print axioms weak_line_generalized_card_le_six
end Erdos213.CircleCoverReduction
