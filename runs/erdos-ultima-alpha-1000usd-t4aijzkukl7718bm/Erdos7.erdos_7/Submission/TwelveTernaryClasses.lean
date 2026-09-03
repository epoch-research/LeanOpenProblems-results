import Submission.FiveDistinctExceptions

/-! Global class-count consequences of five-exception rigidity. These remain
necessary conditions for a hypothetical odd covering, not a nonexistence proof. -/
namespace Erdos7TwelveTernaryClasses
open Erdos7Reduction Erdos7MinimumTernaryClass
open Erdos7FourDistinctExceptions Erdos7FiveDistinctExceptions
set_option autoImplicit false
set_option maxHeartbeats 4000000

def branch {I : Type*} [Fintype I] (m : I → ℕ) (a : I → ℤ) (r : ℤ) : Finset I :=
  Finset.univ.filter (fun j => 3 ∣ m j ∧ (3 : ℤ) ∣ a j-r)

lemma branch_card {I : Type*} [Fintype I] (m : I → ℕ) (a : I → ℤ) (r : ℤ) :
    (branch m a r).card=Fintype.card {j // 3 ∣ m j ∧ (3 : ℤ) ∣ a j-r} := by
  classical
  simp only [Fintype.card_subtype,branch]

lemma two_branch_sum {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r s : ℤ) (hrs : ¬ (3 : ℤ) ∣ r-s)
    (hr : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3)
    (hs : ∀ j, (3 : ℤ) ∣ a j-s → m j≠3) :
    11 ≤ (branch m a r).card+(branch m a s).card := by
  classical
  have h1 := ternary_branch_card_five m a hc r hr
  have h2 := ternary_branch_card_five m a hc s hs
  have hh : 6 ≤ (branch m a r).card ∨ 6 ≤ (branch m a s).card := by
    by_contra! hn
    apply hrs
    apply five_class_branches_congruent m a hc r s hr hs
    · rw [← branch_card]; omega
    · rw [← branch_card]; omega
  simp only [← branch_card] at h1 h2
  omega

lemma three_branch_sum_le {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (r : ℤ) :
    (branch m a r).card+(branch m a (r+1)).card+(branch m a (r+2)).card ≤
      Fintype.card {j // 3 ∣ m j} := by
  classical
  let A := branch m a r
  let B := branch m a (r+1)
  let C := branch m a (r+2)
  have hdis (s t : ℤ) (hst : ¬ (3 : ℤ) ∣ s-t) :
      Disjoint (branch m a s) (branch m a t) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have ha := (Finset.mem_filter.mp hj).2.2
    have hb := (Finset.mem_filter.mp hk).2.2
    apply hst
    omega
  have hAB : Disjoint A B := hdis r (r+1) (by omega)
  have hAC : Disjoint A C := hdis r (r+2) (by omega)
  have hBC : Disjoint B C := hdis (r+1) (r+2) (by omega)
  have hABC : Disjoint (A∪B) C := Finset.disjoint_union_left.mpr ⟨hAC,hBC⟩
  have hsub : (A∪B)∪C ⊆ Finset.univ.filter (fun j => 3 ∣ m j) := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2.1⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2.1⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hABC,Finset.card_union_of_disjoint hAB] at hh
  simpa only [A,B,C,Fintype.card_subtype] using hh

/-- If actual modulus three is absent, at least seventeen labels are divisible
by three. At most one of the three branches can have only five classes. -/
theorem seventeen_without_three {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hno : ∀ j, m j≠3) : 17 ≤ Fintype.card {j // 3 ∣ m j} := by
  classical
  have h01 := two_branch_sum m a hc 0 1 (by norm_num) (fun j _ => hno j) (fun j _ => hno j)
  have h02 := two_branch_sum m a hc 0 2 (by norm_num) (fun j _ => hno j) (fun j _ => hno j)
  have h12 := two_branch_sum m a hc 1 2 (by norm_num) (fun j _ => hno j) (fun j _ => hno j)
  have hh := three_branch_sum_le m a 0
  norm_num only [zero_add] at hh
  omega

/-- Every distinct odd arithmetic cover has at least twelve classes whose
moduli have a factor of three. -/
theorem arithmetic_twelve_ternary {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a) :
    12 ≤ Fintype.card {j // 3 ∣ m j} := by
  classical
  by_cases hex : ∃ j, m j=3
  · obtain ⟨j,hj⟩ := hex
    have hno (r : ℤ) (hr : ¬ (3 : ℤ) ∣ a j-r) :
        ∀ k, (3 : ℤ) ∣ a k-r → m k≠3 := by
      intro k hk hmk
      have he : k=j := hc.1 (hmk.trans hj.symm)
      subst k
      exact hr hk
    have h12 := two_branch_sum m a hc (a j+1) (a j+2) (by omega)
      (hno _ (by omega)) (hno _ (by omega))
    have h0 : 1 ≤ (branch m a (a j)).card := by
      apply Finset.one_le_card.mpr
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hj],by simp⟩⟩
    have hh := three_branch_sum_le m a (a j)
    omega
  · have hh := seventeen_without_three m a hc (by simpa using hex)
    omega

theorem strict_twelve_ternary (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    12 ≤ Fintype.card {j // 3 ∣ (C.moduli j).absNorm} := by
  letI := C.fintypeIndex
  exact arithmetic_twelve_ternary (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C,fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩,arithmetic_cover C⟩

#print axioms strict_twelve_ternary
#print axioms two_branch_sum
#print axioms seventeen_without_three
#print axioms arithmetic_twelve_ternary
end Erdos7TwelveTernaryClasses
