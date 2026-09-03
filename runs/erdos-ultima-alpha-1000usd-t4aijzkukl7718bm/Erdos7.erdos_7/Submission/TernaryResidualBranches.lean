import Submission.ExceptionAbsorption

/-! Ternary branch obstructions after absorbing every new no-three quotient.
The bounds are independent of the number of harmless classes in a branch.
They do not provide the universal descent needed to settle Erdős Problem 7. -/
namespace Erdos7TernaryResidualBranches
open Erdos7Reduction Erdos7ExceptionAbsorption
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev Base {I : Type*} (m : I → ℕ) := {i // ¬ 3 ∣ m i}
abbrev Branch {I : Type*} (m : I → ℕ) (a : I → ℤ) (r : ℤ) :=
  {j // 3 ∣ m j ∧ (3 : ℤ) ∣ a j-r}
abbrev Defect {I : Type*} (m : I → ℕ) (a : I → ℤ) (r : ℤ)
    (j : Branch m a r) :=
  Residual (fun i : Base m => m i) (fun k : Branch m a r => m k/3) j

lemma defect_iff {I : Type*} (m : I → ℕ) (a : I → ℤ) (r : ℤ)
    (j : Branch m a r) :
    Defect m a r j ↔ 9 ∣ m j ∨ ∃ i, ¬ 3 ∣ m i ∧ m j=3*m i := by
  have he := Nat.mul_div_cancel' j.property.1
  have hthree : 3 ∣ m j/3 ↔ 9 ∣ m j := by
    constructor
    · rintro ⟨k,hk⟩
      exact ⟨k,by omega⟩
    · rintro ⟨k,hk⟩
      exact ⟨k,by omega⟩
  constructor
  · rintro (hh | ⟨i,hi⟩)
    · exact Or.inl (hthree.mp hh)
    · change m i=m j/3 at hi
      exact Or.inr ⟨i,i.property,by omega⟩
  · rintro (hh | ⟨i,hi,hij⟩)
    · exact Or.inl (hthree.mpr hh)
    · exact Or.inr ⟨⟨i,hi⟩,by change m i=m j/3; omega⟩

lemma quotient_properties {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r : ℤ) (hno : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3) :
    Function.Injective (fun j : Branch m a r => m j/3) ∧
      ∀ j : Branch m a r, 1 < m j/3 ∧ Odd (m j/3) := by
  constructor
  · intro j k hjk
    apply Subtype.ext
    apply hc.1
    have hj := Nat.mul_div_cancel' j.property.1
    have hk := Nat.mul_div_cancel' k.property.1
    change m j/3=m k/3 at hjk
    omega
  · intro j
    have he := Nat.mul_div_cancel' j.property.1
    have hm := hc.2.1 j
    have hn := hno j j.property.2
    exact ⟨by omega,hm.2.of_dvd_nat (Nat.div_dvd_of_dvd j.property.1)⟩

/-- Only collision labels and labels divisible by nine count toward this
lower bound. An arbitrary number of other branch classes can be absorbed. -/
theorem defect_card_five {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r : ℤ) (hno : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3) :
    5 ≤ Fintype.card {j : Branch m a r // Defect m a r j} := by
  classical
  obtain ⟨b,hb⟩ := Erdos7SmallTernaryBranches.restrict_ternary_branch m a hc r
  obtain ⟨hdi,hd⟩ := quotient_properties m a hc r hno
  exact residual_card_five (fun i : Base m => m i) b
    (hc.1.comp Subtype.val_injective) (fun i => hc.2.1 i) (fun i => i.property)
    (fun j : Branch m a r => m j/3) (fun j => (a j-r)/3) hdi hd hb

/-- Five residual labels force actual collision pairs (5,15) and (7,21),
and exclude every nine-divisible label throughout the branch. -/
theorem five_defect_rigidity {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r : ℤ) (hno : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3)
    (hsize : Fintype.card {j : Branch m a r // Defect m a r j} ≤ 5) :
    (∀ j, (3 : ℤ) ∣ a j-r → ¬ 9 ∣ m j) ∧
    (∃ i j, m i=5 ∧ m j=15 ∧ (3 : ℤ) ∣ a j-r) ∧
    (∃ i j, m i=7 ∧ m j=21 ∧ (3 : ℤ) ∣ a j-r) := by
  classical
  obtain ⟨b,hb⟩ := Erdos7SmallTernaryBranches.restrict_ternary_branch m a hc r
  obtain ⟨hdi,hd⟩ := quotient_properties m a hc r hno
  obtain ⟨hn3,h5,h7⟩ := residual_five_rigidity (fun i : Base m => m i) b
    (hc.1.comp Subtype.val_injective) (fun i => hc.2.1 i) (fun i => i.property)
    (fun j : Branch m a r => m j/3) (fun j => (a j-r)/3) hdi hd hb hsize
  refine ⟨?_,?_,?_⟩
  · intro j hj hj9
    have hj3 : 3 ∣ m j := (by decide : 3 ∣ 9).trans hj9
    apply hn3 ⟨j,hj3,hj⟩
    obtain ⟨k,hk⟩ := hj9
    have hh := Nat.mul_div_cancel' hj3
    exact ⟨k,by change m j/3=3*k; omega⟩
  · obtain ⟨i,j,hi,hj⟩ := h5
    have hh := Nat.mul_div_cancel' j.property.1
    change m j/3=5 at hj
    exact ⟨i,j,hi,by omega,j.property.2⟩
  · obtain ⟨i,j,hi,hj⟩ := h7
    have hh := Nat.mul_div_cancel' j.property.1
    change m j/3=7 at hj
    exact ⟨i,j,hi,by omega,j.property.2⟩

/-- In particular, a branch reaching the next ternary level needs at least
six residual obstructions, not merely six classes. -/
theorem defect_card_six_of_nine {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r : ℤ) (hno : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3)
    (hex : ∃ j, (3 : ℤ) ∣ a j-r ∧ 9 ∣ m j) :
    6 ≤ Fintype.card {j : Branch m a r // Defect m a r j} := by
  classical
  by_contra hsmall
  have hh := (five_defect_rigidity m a hc r hno (by omega)).1
  obtain ⟨j,hj,hj9⟩ := hex
  exact hh j hj hj9

/-- At most one coarse branch without modulus three can have only five
residual obstructions, even if those branches have many more total classes. -/
theorem five_defect_branches_congruent {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r s : ℤ)
    (hr : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3)
    (hs : ∀ j, (3 : ℤ) ∣ a j-s → m j≠3)
    (hcr : Fintype.card {j : Branch m a r // Defect m a r j} ≤ 5)
    (hcs : Fintype.card {j : Branch m a s // Defect m a s j} ≤ 5) :
    (3 : ℤ) ∣ r-s := by
  obtain ⟨_,j,_,hj,hjr⟩ := (five_defect_rigidity m a hc r hr hcr).2.1
  obtain ⟨_,k,_,hk,hks⟩ := (five_defect_rigidity m a hc s hs hcs).2.1
  have he : j=k := hc.1 (hj.trans hk.symm)
  subst k
  omega

#print axioms defect_card_five
#print axioms five_defect_rigidity
#print axioms defect_card_six_of_nine
#print axioms five_defect_branches_congruent
end Erdos7TernaryResidualBranches
