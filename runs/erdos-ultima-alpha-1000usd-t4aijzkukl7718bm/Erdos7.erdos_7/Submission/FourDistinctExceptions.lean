import Submission.FourExceptionArithmetic

/-! Four distinct odd exceptions and the resulting five-class ternary-branch
bound. These are necessary conditions, not a settlement of Erdős Problem7. -/
namespace Erdos7FourDistinctExceptions
open Erdos7Reduction Erdos7MinimumTernaryClass Erdos7DoubleExceptionOdd
open Erdos7ThreeDistinctExceptions Erdos7FourExceptionArithmetic
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- With at most four labels, some branch away from actual modulus three
has at most one label divisible by three. -/
lemma small_branch {J : Type*} [Fintype J]
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hJ : Fintype.card J ≤ 4) (jinit : J) :
    ∃ r : ℤ, (∀ j, (3 : ℤ) ∣ b j-r → d j≠3) ∧
      Fintype.card {j // 3 ∣ d j ∧ (3 : ℤ) ∣ b j-r} ≤ 1 := by
  classical
  obtain ⟨j₀,hmark⟩ : ∃ j₀ : J, ∀ j, d j=3 → j=j₀ := by
    by_cases hex : ∃ j, d j=3
    · obtain ⟨j₀,hj₀⟩ := hex
      exact ⟨j₀,fun j hj => hdi (hj.trans hj₀.symm)⟩
    · exact ⟨jinit,fun j hj => False.elim (hex ⟨j,hj⟩)⟩
  let A := Finset.univ.filter (fun j : J => (3 : ℤ) ∣ b j-(b j₀+1))
  let B := Finset.univ.filter (fun j : J => (3 : ℤ) ∣ b j-(b j₀+2))
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have ha := (Finset.mem_filter.mp hj).2
    have hb := (Finset.mem_filter.mp hk).2
    omega
  have hsub : A∪B ⊆ Finset.univ.erase j₀ := by
    intro j hj
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_univ _⟩
    intro he
    subst j
    rcases Finset.mem_union.mp hj with hj | hj <;>
      have hh := (Finset.mem_filter.mp hj).2 <;> omega
  have hsum : A.card+B.card ≤ 3 := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ] at hh
    omega
  have hex : ∃ r : ℤ, ¬ (3 : ℤ) ∣ b j₀-r ∧
      (Finset.univ.filter (fun j : J => (3 : ℤ) ∣ b j-r)).card ≤ 1 := by
    by_cases ha : A.card ≤ 1
    · exact ⟨b j₀+1,by omega,ha⟩
    · exact ⟨b j₀+2,by omega,by change B.card ≤ 1; omega⟩
  obtain ⟨r,hr,hcard⟩ := hex
  refine ⟨r,?_,?_⟩
  · intro j hj hd
    exact hr (by simpa only [hmark j hd] using hj)
  · rw [Fintype.card_subtype]
    apply le_trans (Finset.card_le_card ?_) hcard
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2.2⟩

/-- Extra moduli may contain three and may coincide with base moduli. Only
pairwise distinctness within the extra family is required. -/
theorem not_cover_four_distinct_odd {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (hJ : Fintype.card J ≤ 4) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) := by
  classical
  by_cases hn : ∀ j, ¬ 3 ∣ d j
  · exact not_cover_four_distinct_no_three m a hinj hm h3 d b hdi hd hn hJ
  push_neg at hn
  obtain ⟨jinit,hinit⟩ := hn
  let T := {j : J // 3 ∣ d j}
  let K := {j : J // ¬ 3 ∣ d j}
  by_cases hT : Fintype.card T ≤ 2
  · have hK : Fintype.card K ≤ 3 := by
      have hh := Fintype.card_subtype_lt (p := fun j : J => ¬ 3 ∣ d j) (x := jinit) (by simpa using hinit)
      simp only [K,Fintype.card_subtype] at hh ⊢
      omega
    obtain ⟨r,hr⟩ := Erdos7SmallTernaryBranches.free_ternary_residue (fun j : T => b j) hT
    choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) r
    choose b' hb' using fun j : K => affine_residue (d j) j.property (b j) r
    intro hcover
    apply not_cover_three_distinct_no_three m a' hinj hm h3
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
  · have hK : Fintype.card K ≤ 1 := by
      have hh := Fintype.card_subtype_compl (fun j : J => 3 ∣ d j)
      simp only [T,K,Fintype.card_subtype] at hh hT ⊢
      omega
    obtain ⟨r,hr,hA⟩ := small_branch d b hdi hJ jinit
    let A := {j : J // 3 ∣ d j ∧ (3 : ℤ) ∣ b j-r}
    choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) r
    choose b' hb' using fun j : K => affine_residue (d j) j.property (b j) r
    have hdA (j : A) : 1 < d j/3 ∧ Odd (d j/3) := by
      have hmul := Nat.mul_div_cancel' j.property.1
      have hpos := (hd j).1
      have hne := hr j j.property.2
      exact ⟨by omega,(hd j).2.of_dvd_nat (Nat.div_dvd_of_dvd j.property.1)⟩
    let d' : K ⊕ A → ℕ := Sum.elim (fun j => d j) (fun j => d j/3)
    let b'' : K ⊕ A → ℤ := Sum.elim b' (fun j => (b j-r)/3)
    have hd' (j : K ⊕ A) : 1 < d' j ∧ Odd (d' j) := by
      cases j with
      | inl j => exact hd j
      | inr j => exact hdA j
    have hsize : Fintype.card (K ⊕ A) ≤ 2 := by
      rw [Fintype.card_sum]
      change Fintype.card K + Fintype.card A ≤ 2
      have hA' : Fintype.card A ≤ 1 := hA
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
        exact Or.inr ⟨Sum.inr ⟨j,hj3,hres⟩,
          Erdos7SmallTernaryBranches.quotient_residue (d j) (b j) r hj3 hres x hj⟩
      · exact Or.inr ⟨Sum.inl ⟨j,hj3⟩,hb' ⟨j,hj3⟩ x hj⟩

/-- Every coarse ternary branch not containing actual modulus three has at
least five classes. No irredundance or minimality is assumed. -/
theorem ternary_branch_card_five {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r : ℤ) (hno : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3) :
    5 ≤ Fintype.card {j // 3 ∣ m j ∧ (3 : ℤ) ∣ a j-r} := by
  classical
  by_contra hsmall
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
  apply not_cover_four_distinct_odd
    (fun i : K => m i) b (hc.1.comp Subtype.val_injective)
    (fun i => hc.2.1 i) (fun i => i.property)
    (fun j : J => m j/3) (fun j => (a j-r)/3) hdi hd _ hb
  simp only [J,Fintype.card_subtype] at hsmall ⊢
  omega

#print axioms not_cover_four_distinct_odd
#print axioms ternary_branch_card_five
end Erdos7FourDistinctExceptions
