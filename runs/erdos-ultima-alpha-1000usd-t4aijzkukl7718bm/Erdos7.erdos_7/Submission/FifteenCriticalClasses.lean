import Submission.SixDistinctObstruction
import Submission.SixDefectCollision

/-! Class-count consequences of the six-exception obstruction. These do not
settle the odd covering problem: arbitrary larger residual families remain. -/
namespace Erdos7FifteenCriticalClasses
open Erdos7Reduction Erdos7TernaryResidualBranches Erdos7SixDistinctObstruction
open Erdos7SixDefectCollision Erdos7TwelveTernaryClasses Erdos7CriticalTernaryClasses
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem defect_card_seven {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r : ℤ) (hno : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3) :
    7 ≤ Fintype.card {j : Branch m a r // Defect m a r j} := by
  classical
  obtain ⟨b,hb⟩ := Erdos7SmallTernaryBranches.restrict_ternary_branch m a hc r
  obtain ⟨hdi,hd⟩ := quotient_properties m a hc r hno
  exact residual_card_seven (fun i : Base m => m i) b
    (hc.1.comp Subtype.val_injective) (fun i => hc.2.1 i) (fun i => i.property)
    (fun j : Branch m a r => m j/3) (fun j => (a j-r)/3) hdi hd hb

lemma branch_card_seven {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r : ℤ) (hno : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3) :
    7 ≤ (branch m a r).card := by
  classical
  rw [branch_card]
  exact (defect_card_seven m a hc r hno).trans (Fintype.card_subtype_le _)

theorem twenty_one_without_three {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hno : ∀ j, m j≠3) : 21 ≤ Fintype.card {j // 3 ∣ m j} := by
  classical
  have h0 := branch_card_seven m a hc 0 (fun j _ => hno j)
  have h1 := branch_card_seven m a hc 1 (fun j _ => hno j)
  have h2 := branch_card_seven m a hc 2 (fun j _ => hno j)
  have hh := three_branch_sum_le m a 0
  norm_num only [zero_add] at hh
  omega

theorem arithmetic_fifteen_ternary {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a) :
    15 ≤ Fintype.card {j // 3 ∣ m j} := by
  classical
  by_cases hex : ∃ j, m j=3
  · obtain ⟨j,hj⟩ := hex
    have hno (r : ℤ) (hr : ¬ (3 : ℤ) ∣ a j-r) :
        ∀ k, (3 : ℤ) ∣ a k-r → m k≠3 := by
      intro k hk hmk
      have he : k=j := hc.1 (hmk.trans hj.symm)
      subst k
      exact hr hk
    have h1 := branch_card_seven m a hc (a j+1) (hno _ (by omega))
    have h2 := branch_card_seven m a hc (a j+2) (hno _ (by omega))
    have h0 : 1 ≤ (branch m a (a j)).card := by
      apply Finset.one_le_card.mpr
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hj],by simp⟩⟩
    have hh := three_branch_sum_le m a (a j)
    omega
  · have hh := twenty_one_without_three m a hc (by simpa using hex)
    omega

theorem fifteen_critical {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a) :
    15 ≤ Fintype.card {j // Critical m j} := by
  classical
  have hh := arithmetic_fifteen_ternary (normalized m) a (normalized_cover m a hc)
  simpa only [normalized_three_iff m hc.2.1] using hh

theorem twenty_one_critical_without_three {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hno : ∀ j, m j≠3) : 21 ≤ Fintype.card {j // Critical m j} := by
  classical
  have hh := twenty_one_without_three (normalized m) a (normalized_cover m a hc)
    (normalized_ne_three m hc.2.1 hno)
  simpa only [normalized_three_iff m hc.2.1] using hh

theorem strict_fifteen_ternary (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    15 ≤ Fintype.card {j // 3 ∣ (C.moduli j).absNorm} := by
  letI := C.fintypeIndex
  exact arithmetic_fifteen_ternary (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C,fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩,arithmetic_cover C⟩

#print axioms fifteen_critical
#print axioms twenty_one_critical_without_three
#print axioms strict_fifteen_ternary
end Erdos7FifteenCriticalClasses
