import Submission.FiveExceptionThreePart

/-! Five-exception rigidity. A hypothetical repair by five distinct odd labels
must use no factors of three and must contain actual moduli five and seven.
This does not exclude arbitrarily large exceptional families. -/
namespace Erdos7FiveDistinctExceptions
open Erdos7Reduction Erdos7MinimumTernaryClass Erdos7DoubleExceptionOdd
open Erdos7FourDistinctExceptions Erdos7FourExceptionArithmetic
open Erdos7FiveExceptionWeights Erdos7FiveExceptionThreePart
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem not_cover_when_three_divides {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (hJ : Fintype.card J ≤ 5)
    (hex : ∃ j, 3 ∣ d j) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) := by
  classical
  obtain ⟨jinit,hinit⟩ := hex
  let T := {j : J // 3 ∣ d j}
  let K := {j : J // ¬ 3 ∣ d j}
  have hcards : Fintype.card T+Fintype.card K=Fintype.card J := by
    have ht := Fintype.card_subtype_le (fun j : J => 3 ∣ d j)
    have hk := Fintype.card_subtype_compl (fun j : J => 3 ∣ d j)
    simp only [T,K,Fintype.card_subtype] at ht hk ⊢
    omega
  by_cases hT : Fintype.card T ≤ 2
  · have hK : Fintype.card K ≤ 4 := by
      have hh := Fintype.card_subtype_lt (p := fun j : J => ¬ 3 ∣ d j) (x := jinit) (by simpa using hinit)
      simp only [K,Fintype.card_subtype] at hh ⊢
      omega
    obtain ⟨r,hr⟩ := Erdos7SmallTernaryBranches.free_ternary_residue (fun j : T => b j) hT
    choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) r
    choose b' hb' using fun j : K => affine_residue (d j) j.property (b j) r
    intro hcover
    apply not_cover_four_distinct_no_three m a' hinj hm h3
      (fun j : K => d j) b' (hdi.comp Subtype.val_injective)
      (fun j => hd j) (fun j => j.property) hK
    intro x
    rcases hcover (3*x+r) with ⟨i,hi⟩ | ⟨j,hj⟩
    · exact Or.inl ⟨i,ha' i x hi⟩
    · have hj3 : ¬ 3 ∣ d j := by
        intro hh
        have hz := (Int.natCast_dvd_natCast.mpr hh).trans hj
        apply hr ⟨j,hh⟩
        change (3 : ℤ) ∣ b j-r
        omega
      exact Or.inr ⟨⟨j,hj3⟩,hb' ⟨j,hj3⟩ x hj⟩
  by_cases hT3 : Fintype.card T=3
  · have hK : Fintype.card K ≤ 2 := by omega
    intro hcover
    apply not_cover_three_ternary_exceptions m a hinj hm h3
      (fun j : K => d j) (fun j => b j) (hdi.comp Subtype.val_injective)
      (fun j => hd j) (fun j => j.property) hK
      (fun j : T => d j) (fun j => b j) (hdi.comp Subtype.val_injective)
      (fun j => hd j) (fun j => j.property) hT3
    intro x
    rcases hcover x with hh | ⟨j,hj⟩
    · exact Or.inl hh
    · by_cases hj3 : 3 ∣ d j
      · exact Or.inr (Or.inr ⟨⟨j,hj3⟩,hj⟩)
      · exact Or.inr (Or.inl ⟨⟨j,hj3⟩,hj⟩)
  · have hK : Fintype.card K ≤ 1 := by omega
    obtain ⟨r,hr,hA⟩ := small_branch_bound (fun j : T => d j) (fun j => b j)
      (hdi.comp Subtype.val_injective) (2-Fintype.card K) (by omega) ⟨jinit,hinit⟩
    let A := {j : T // 3 ∣ d j ∧ (3 : ℤ) ∣ b j-r}
    choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) r
    choose b' hb' using fun j : K => affine_residue (d j) j.property (b j) r
    have hdA (j : A) : 1 < d j.val/3 ∧ Odd (d j.val/3) := by
      have hmul := Nat.mul_div_cancel' j.property.1
      have hpos := (hd j.val).1
      have hne := hr j.val j.property.2
      exact ⟨by omega,(hd j.val).2.of_dvd_nat (Nat.div_dvd_of_dvd j.property.1)⟩
    let d' : K ⊕ A → ℕ := Sum.elim (fun j => d j) (fun j => d j.val/3)
    let b'' : K ⊕ A → ℤ := Sum.elim b' (fun j => (b j.val-r)/3)
    have hd' (j : K ⊕ A) : 1 < d' j ∧ Odd (d' j) := by
      cases j with
      | inl j => exact hd j
      | inr j => exact hdA j
    have hsize : Fintype.card (K ⊕ A) ≤ 2 := by
      rw [Fintype.card_sum]
      have hA' : Fintype.card A ≤ 2-Fintype.card K := hA
      omega
    intro hcover
    apply not_cover_with_at_most_two_odd_exceptions m a' hinj hm h3 d' hd' b'' hsize
    intro x
    rcases hcover (3*x+r) with ⟨i,hi⟩ | ⟨j,hj⟩
    · exact Or.inl ⟨i,ha' i x hi⟩
    · by_cases hj3 : 3 ∣ d j
      · have hres : (3 : ℤ) ∣ b j-r := by
          have hh := (Int.natCast_dvd_natCast.mpr hj3).trans hj
          omega
        exact Or.inr ⟨Sum.inr ⟨⟨j,hj3⟩,hj3,hres⟩,
          Erdos7SmallTernaryBranches.quotient_residue (d j) (b j) r hj3 hres x hj⟩
      · exact Or.inr ⟨Sum.inl ⟨j,hj3⟩,hb' ⟨j,hj3⟩ x hj⟩

/-- Necessary shape of a repair with at most five distinct odd extra moduli. -/
theorem prime_constraints {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (hJ : Fintype.card J ≤ 5)
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) :
    (∀ j, ¬ 3 ∣ d j) ∧ (∃ j, d j=5) ∧ (∃ j, d j=7) := by
  classical
  have hn3 (j : J) : ¬ 3 ∣ d j := by
    intro hj
    exact not_cover_when_three_divides m a hinj hm h3 d b hdi hd hJ ⟨j,hj⟩ hcover
  refine ⟨hn3,?_,?_⟩
  · by_contra! hn
    exact Erdos7FourExceptionArithmetic.not_cover_with_weighted_exceptions
      m a hinj hm h3 d b (fun j => ⟨by have := (hd j).1; omega,(hd j).2⟩) hn3
      (five_missing_five_weight d hdi hd hn3 hn hJ) hcover
  · by_contra! hn
    exact Erdos7FourExceptionArithmetic.not_cover_with_weighted_exceptions
      m a hinj hm h3 d b (fun j => ⟨by have := (hd j).1; omega,(hd j).2⟩) hn3
      (five_missing_seven_weight d hdi hd hn3 hn hJ) hcover

/-- A ternary branch with at most five classes and no actual modulus three
contains moduli15 and21, and contains no modulus divisible by9. -/
theorem five_class_branch {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r : ℤ) (hno : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3)
    (hsize : Fintype.card {j // 3 ∣ m j ∧ (3 : ℤ) ∣ a j-r} ≤ 5) :
    (∀ j, (3 : ℤ) ∣ a j-r → ¬ 9 ∣ m j) ∧
    (∃ j, m j=15 ∧ (3 : ℤ) ∣ a j-r) ∧
    (∃ j, m j=21 ∧ (3 : ℤ) ∣ a j-r) := by
  classical
  let K := {i : I // ¬ 3 ∣ m i}
  let J := {j : I // 3 ∣ m j ∧ (3 : ℤ) ∣ a j-r}
  obtain ⟨b,hb⟩ := Erdos7SmallTernaryBranches.restrict_ternary_branch m a hc r
  have hd (j : J) : 1 < m j/3 ∧ Odd (m j/3) := by
    have he : 3*(m j/3)=m j := Nat.mul_div_cancel' j.property.1
    have hm := hc.2.1 j
    have hne := hno j j.property.2
    refine ⟨by omega,hm.2.of_dvd_nat (Nat.div_dvd_of_dvd j.property.1)⟩
  have hdi : Function.Injective (fun j : J => m j/3) := by
    intro j k hjk
    change m j/3=m k/3 at hjk
    apply Subtype.ext
    apply hc.1
    have hj := Nat.mul_div_cancel' j.property.1
    have hk := Nat.mul_div_cancel' k.property.1
    omega
  obtain ⟨hn3,h5,h7⟩ := prime_constraints
    (fun i : K => m i) b (hc.1.comp Subtype.val_injective)
    (fun i => hc.2.1 i) (fun i => i.property)
    (fun j : J => m j/3) (fun j => (a j-r)/3) hdi hd hsize hb
  refine ⟨?_,?_,?_⟩
  · intro j hj hj9
    have hj3 : 3 ∣ m j := (by decide : 3 ∣ 9).trans hj9
    apply hn3 ⟨j,hj3,hj⟩
    obtain ⟨t,ht⟩ := hj9
    have hh := Nat.mul_div_cancel' hj3
    exact ⟨t,by change m j/3=3*t; omega⟩
  · obtain ⟨j,hj⟩ := h5
    have hh := Nat.mul_div_cancel' j.property.1
    change m j/3=5 at hj
    exact ⟨j,by omega,j.property.2⟩
  · obtain ⟨j,hj⟩ := h7
    have hh := Nat.mul_div_cancel' j.property.1
    change m j/3=7 at hj
    exact ⟨j,by omega,j.property.2⟩

/-- Two different ternary branches without modulus three cannot both have
only five classes: both would require the unique modulus15 label. -/
theorem five_class_branches_congruent {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r s : ℤ)
    (hr : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3)
    (hs : ∀ j, (3 : ℤ) ∣ a j-s → m j≠3)
    (hcr : Fintype.card {j // 3 ∣ m j ∧ (3 : ℤ) ∣ a j-r} ≤ 5)
    (hcs : Fintype.card {j // 3 ∣ m j ∧ (3 : ℤ) ∣ a j-s} ≤ 5) :
    (3 : ℤ) ∣ r-s := by
  obtain ⟨j,hj,hjr⟩ := (five_class_branch m a hc r hr hcr).2.1
  obtain ⟨k,hk,hks⟩ := (five_class_branch m a hc s hs hcs).2.1
  have he : j=k := hc.1 (hj.trans hk.symm)
  subst k
  omega

#print axioms not_cover_when_three_divides
#print axioms prime_constraints
#print axioms five_class_branch
#print axioms five_class_branches_congruent
end Erdos7FiveDistinctExceptions
