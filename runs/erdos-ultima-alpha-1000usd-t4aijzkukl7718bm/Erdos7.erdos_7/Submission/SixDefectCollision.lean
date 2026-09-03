import Submission.SixDistinctWithoutFive
import Submission.CriticalTernaryClasses

/-! Every branch with at most six residual obstructions reserves the same
modulus15 label. These are necessary conditions only. -/
namespace Erdos7SixDefectCollision
open Erdos7Reduction Erdos7TernaryResidualBranches
open Erdos7SixDistinctWithoutFive Erdos7TwelveTernaryClasses
open Erdos7FourDistinctExceptions Erdos7CriticalTernaryClasses
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- At most six defects force an actual original collision pair5,15. -/
theorem six_defects_collision_five {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r : ℤ) (hno : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3)
    (hsize : Fintype.card {j : Branch m a r // Defect m a r j} ≤ 6) :
    ∃ i j, m i=5 ∧ m j=15 ∧ (3 : ℤ) ∣ a j-r := by
  classical
  obtain ⟨b,hb⟩ := Erdos7SmallTernaryBranches.restrict_ternary_branch m a hc r
  obtain ⟨hdi,hd⟩ := quotient_properties m a hc r hno
  obtain ⟨i,j,hi,hj⟩ := six_residual_collision_five (fun i : Base m => m i) b
    (hc.1.comp Subtype.val_injective) (fun i => hc.2.1 i) (fun i => i.property)
    (fun j : Branch m a r => m j/3) (fun j => (a j-r)/3) hdi hd hsize hb
  have hh := Nat.mul_div_cancel' j.property.1
  change m j/3=5 at hj
  exact ⟨i,j,hi,by omega,j.property.2⟩

theorem six_defect_branches_congruent {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r s : ℤ)
    (hr : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3)
    (hs : ∀ j, (3 : ℤ) ∣ a j-s → m j≠3)
    (hcr : Fintype.card {j : Branch m a r // Defect m a r j} ≤ 6)
    (hcs : Fintype.card {j : Branch m a s // Defect m a s j} ≤ 6) :
    (3 : ℤ) ∣ r-s := by
  obtain ⟨_,j,_,hj,hjr⟩ := six_defects_collision_five m a hc r hr hcr
  obtain ⟨_,k,_,hk,hks⟩ := six_defects_collision_five m a hc s hs hcs
  have he : j=k := hc.1 (hj.trans hk.symm)
  subst k
  omega

lemma two_branch_sum_twelve {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r s : ℤ) (hrs : ¬ (3 : ℤ) ∣ r-s)
    (hr : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3)
    (hs : ∀ j, (3 : ℤ) ∣ a j-s → m j≠3) :
    12 ≤ (branch m a r).card+(branch m a s).card := by
  classical
  have h1 := ternary_branch_card_five m a hc r hr
  have h2 := ternary_branch_card_five m a hc s hs
  have hh : 7 ≤ (branch m a r).card ∨ 7 ≤ (branch m a s).card := by
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
  simp only [← branch_card] at h1 h2
  omega

/-- Without actual modulus3, at most one ternary branch can have six or
fewer classes. Consequently the three branch sizes total at least19. -/
theorem nineteen_without_three {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hno : ∀ j, m j≠3) : 19 ≤ Fintype.card {j // 3 ∣ m j} := by
  classical
  have h0 := ternary_branch_card_five m a hc 0 (fun j _ => hno j)
  have h1 := ternary_branch_card_five m a hc 1 (fun j _ => hno j)
  have h2 := ternary_branch_card_five m a hc 2 (fun j _ => hno j)
  simp only [← branch_card] at h0 h1 h2
  have hp (r s : ℤ) (hrs : ¬ (3 : ℤ) ∣ r-s) :
      7 ≤ (branch m a r).card ∨ 7 ≤ (branch m a s).card := by
    by_contra! hn
    apply hrs
    apply six_defect_branches_congruent m a hc r s (fun j _ => hno j) (fun j _ => hno j)
    · apply (Fintype.card_subtype_le _).trans
      change Fintype.card (Branch m a r) ≤ 6
      rw [← branch_card]
      omega
    · apply (Fintype.card_subtype_le _).trans
      change Fintype.card (Branch m a s) ≤ 6
      rw [← branch_card]
      omega
  have h01 := hp 0 1 (by norm_num)
  have h02 := hp 0 2 (by norm_num)
  have h12 := hp 1 2 (by norm_num)
  have hh := three_branch_sum_le m a 0
  norm_num only [zero_add] at hh
  omega

theorem nineteen_critical_without_three {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hno : ∀ j, m j≠3) : 19 ≤ Fintype.card {j // Critical m j} := by
  classical
  have hh := nineteen_without_three (normalized m) a (normalized_cover m a hc)
    (normalized_ne_three m hc.2.1 hno)
  simpa only [normalized_three_iff m hc.2.1] using hh

#print axioms six_defects_collision_five
#print axioms six_defect_branches_congruent
#print axioms two_branch_sum_twelve
#print axioms nineteen_critical_without_three
end Erdos7SixDefectCollision
