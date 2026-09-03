import Submission.SixDistinctExceptions
import Submission.TernaryResidualBranches

/-! Interaction of five- and six-obstruction ternary branches. -/
namespace Erdos7SixTernaryBranches
open Erdos7Reduction Erdos7TernaryResidualBranches
open Erdos7SixDistinctExceptions Erdos7FiveDistinctExceptions
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- If neither modulus15 nor modulus21 is in a branch, a nine-divisible
class forces at least seven residual obstructions in that branch. -/
theorem seven_defects_of_nine {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r : ℤ) (hno : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3)
    (h15 : ∀ j, (3 : ℤ) ∣ a j-r → m j≠15)
    (h21 : ∀ j, (3 : ℤ) ∣ a j-r → m j≠21)
    (hex : ∃ j, (3 : ℤ) ∣ a j-r ∧ 9 ∣ m j) :
    7 ≤ Fintype.card {j : Branch m a r // Defect m a r j} := by
  classical
  obtain ⟨b,hb⟩ := Erdos7SmallTernaryBranches.restrict_ternary_branch m a hc r
  obtain ⟨hdi,hd⟩ := quotient_properties m a hc r hno
  apply residual_card_seven (fun i : Base m => m i) b
    (hc.1.comp Subtype.val_injective) (fun i => hc.2.1 i) (fun i => i.property)
    (fun j : Branch m a r => m j/3) (fun j => (a j-r)/3) hdi hd
  · intro j hj
    have hh := Nat.mul_div_cancel' j.property.1
    apply h15 j j.property.2
    change m j/3=5 at hj
    omega
  · intro j hj
    have hh := Nat.mul_div_cancel' j.property.1
    apply h21 j j.property.2
    change m j/3=7 at hj
    omega
  · obtain ⟨j,hj,hj9⟩ := hex
    have hj3 : 3 ∣ m j := (by decide : 3 ∣ 9).trans hj9
    refine ⟨⟨j,hj3,hj⟩,?_⟩
    obtain ⟨k,hk⟩ := hj9
    have hh := Nat.mul_div_cancel' hj3
    exact ⟨k,by change m j/3=3*k; omega⟩
  · exact hb

/-- A five-defect branch reserves15 and21. A different branch containing
any multiple of nine consequently needs at least seven defects. -/
theorem seven_defects_next_to_five {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r s : ℤ) (hrs : ¬ (3 : ℤ) ∣ r-s)
    (hr : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3)
    (hs : ∀ j, (3 : ℤ) ∣ a j-s → m j≠3)
    (hcr : Fintype.card {j : Branch m a r // Defect m a r j} ≤ 5)
    (hex : ∃ j, (3 : ℤ) ∣ a j-s ∧ 9 ∣ m j) :
    7 ≤ Fintype.card {j : Branch m a s // Defect m a s j} := by
  obtain ⟨_,⟨_,j15,_,hj15,hr15⟩,⟨_,j21,_,hj21,hr21⟩⟩ := five_defect_rigidity m a hc r hr hcr
  apply seven_defects_of_nine m a hc s hs ?_ ?_ hex
  · intro j hj hmj
    have he : j=j15 := hc.1 (hmj.trans hj15.symm)
    subst j
    apply hrs
    omega
  · intro j hj hmj
    have he : j=j21 := hc.1 (hmj.trans hj21.symm)
    subst j
    apply hrs
    omega

/-- The corresponding statement with total branch cardinalities. -/
theorem six_branch_next_to_five_no_nine {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r s : ℤ) (hrs : ¬ (3 : ℤ) ∣ r-s)
    (hr : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3)
    (hs : ∀ j, (3 : ℤ) ∣ a j-s → m j≠3)
    (hcr : Fintype.card (Branch m a r) ≤ 5)
    (hcs : Fintype.card (Branch m a s) ≤ 6) :
    ∀ j, (3 : ℤ) ∣ a j-s → ¬ 9 ∣ m j := by
  classical
  intro j hj hj9
  have hh := seven_defects_next_to_five m a hc r s hrs hr hs
    ((Fintype.card_subtype_le _).trans hcr) ⟨j,hj,hj9⟩
  have hle : Fintype.card {j : Branch m a s // Defect m a s j} ≤ Fintype.card (Branch m a s) :=
    Fintype.card_subtype_le _
  omega

#print axioms seven_defects_next_to_five
#print axioms six_branch_next_to_five_no_nine
end Erdos7SixTernaryBranches
