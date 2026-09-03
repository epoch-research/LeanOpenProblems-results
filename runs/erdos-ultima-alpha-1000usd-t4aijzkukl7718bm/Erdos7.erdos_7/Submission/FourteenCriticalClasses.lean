import Submission.FiveDistinctObstruction
import Submission.SixDefectCollision

/-! Class-count consequences of the five-exception obstruction. These do not
settle the odd covering problem: arbitrary larger residual families remain. -/
namespace Erdos7FourteenCriticalClasses
open Erdos7Reduction Erdos7TernaryResidualBranches Erdos7FiveDistinctObstruction
open Erdos7SixDefectCollision Erdos7TwelveTernaryClasses Erdos7CriticalTernaryClasses
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem defect_card_six {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r : ℤ) (hno : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3) :
    6 ≤ Fintype.card {j : Branch m a r // Defect m a r j} := by
  classical
  obtain ⟨b,hb⟩ := Erdos7SmallTernaryBranches.restrict_ternary_branch m a hc r
  obtain ⟨hdi,hd⟩ := quotient_properties m a hc r hno
  exact residual_card_six (fun i : Base m => m i) b
    (hc.1.comp Subtype.val_injective) (fun i => hc.2.1 i) (fun i => i.property)
    (fun j : Branch m a r => m j/3) (fun j => (a j-r)/3) hdi hd hb

lemma branch_card_six {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r : ℤ) (hno : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3) :
    6 ≤ (branch m a r).card := by
  classical
  rw [branch_card]
  exact (defect_card_six m a hc r hno).trans (Fintype.card_subtype_le _)

lemma one_branch_seven {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r s : ℤ) (hrs : ¬ (3 : ℤ) ∣ r-s)
    (hr : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3)
    (hs : ∀ j, (3 : ℤ) ∣ a j-s → m j≠3) :
    7 ≤ (branch m a r).card ∨ 7 ≤ (branch m a s).card := by
  classical
  by_contra! hn
  apply hrs
  apply six_defect_branches_congruent m a hc r s hr hs
  · apply (Fintype.card_subtype_le _).trans
    change Fintype.card (Branch m a r) ≤ 6
    rw [← branch_card]
    omega
  · apply (Fintype.card_subtype_le _).trans
    change Fintype.card (Branch m a s) ≤ 6
    rw [← branch_card]
    omega

lemma two_branch_sum_thirteen {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r s : ℤ) (hrs : ¬ (3 : ℤ) ∣ r-s)
    (hr : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3)
    (hs : ∀ j, (3 : ℤ) ∣ a j-s → m j≠3) :
    13 ≤ (branch m a r).card+(branch m a s).card := by
  have h1 := branch_card_six m a hc r hr
  have h2 := branch_card_six m a hc s hs
  have hh := one_branch_seven m a hc r s hrs hr hs
  omega

theorem twenty_without_three {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hno : ∀ j, m j≠3) : 20 ≤ Fintype.card {j // 3 ∣ m j} := by
  classical
  have h0 := branch_card_six m a hc 0 (fun j _ => hno j)
  have h1 := branch_card_six m a hc 1 (fun j _ => hno j)
  have h2 := branch_card_six m a hc 2 (fun j _ => hno j)
  have h01 := one_branch_seven m a hc 0 1 (by norm_num) (fun j _ => hno j) (fun j _ => hno j)
  have h02 := one_branch_seven m a hc 0 2 (by norm_num) (fun j _ => hno j) (fun j _ => hno j)
  have h12 := one_branch_seven m a hc 1 2 (by norm_num) (fun j _ => hno j) (fun j _ => hno j)
  have hh := three_branch_sum_le m a 0
  norm_num only [zero_add] at hh
  omega

theorem arithmetic_fourteen_ternary {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a) :
    14 ≤ Fintype.card {j // 3 ∣ m j} := by
  classical
  by_cases hex : ∃ j, m j=3
  · obtain ⟨j,hj⟩ := hex
    have hno (r : ℤ) (hr : ¬ (3 : ℤ) ∣ a j-r) :
        ∀ k, (3 : ℤ) ∣ a k-r → m k≠3 := by
      intro k hk hmk
      have he : k=j := hc.1 (hmk.trans hj.symm)
      subst k
      exact hr hk
    have h12 := two_branch_sum_thirteen m a hc (a j+1) (a j+2) (by omega)
      (hno _ (by omega)) (hno _ (by omega))
    have h0 : 1 ≤ (branch m a (a j)).card := by
      apply Finset.one_le_card.mpr
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hj],by simp⟩⟩
    have hh := three_branch_sum_le m a (a j)
    omega
  · have hh := twenty_without_three m a hc (by simpa using hex)
    omega

theorem fourteen_critical {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a) :
    14 ≤ Fintype.card {j // Critical m j} := by
  classical
  have hh := arithmetic_fourteen_ternary (normalized m) a (normalized_cover m a hc)
  simpa only [normalized_three_iff m hc.2.1] using hh

theorem twenty_critical_without_three {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hno : ∀ j, m j≠3) : 20 ≤ Fintype.card {j // Critical m j} := by
  classical
  have hh := twenty_without_three (normalized m) a (normalized_cover m a hc)
    (normalized_ne_three m hc.2.1 hno)
  simpa only [normalized_three_iff m hc.2.1] using hh

theorem strict_fourteen_ternary (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    14 ≤ Fintype.card {j // 3 ∣ (C.moduli j).absNorm} := by
  letI := C.fintypeIndex
  exact arithmetic_fourteen_ternary (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C,fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩,arithmetic_cover C⟩

#print axioms fourteen_critical
#print axioms twenty_critical_without_three
#print axioms strict_fourteen_ternary
end Erdos7FourteenCriticalClasses
