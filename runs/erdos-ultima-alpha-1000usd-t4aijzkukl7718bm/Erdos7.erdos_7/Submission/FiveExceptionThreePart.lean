import Submission.FiveExceptionWeights

/-! A ternary restriction obstruction for five distinct exceptional labels. -/
namespace Erdos7FiveExceptionThreePart
open Erdos7Reduction Erdos7MinimumTernaryClass Erdos7DoubleExceptionOdd
open Erdos7FiveExceptionWeights
set_option autoImplicit false
set_option maxHeartbeats 4000000

lemma small_branch_bound {J : Type*} [Fintype J]
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (k : ℕ) (hJ : Fintype.card J ≤ 2*k+2) (jinit : J) :
    ∃ r : ℤ, (∀ j, (3 : ℤ) ∣ b j-r → d j≠3) ∧
      Fintype.card {j // 3 ∣ d j ∧ (3 : ℤ) ∣ b j-r} ≤ k := by
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
  have hsum : A.card+B.card ≤ 2*k+1 := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ] at hh
    omega
  have hex : ∃ r : ℤ, ¬ (3 : ℤ) ∣ b j₀-r ∧
      (Finset.univ.filter (fun j : J => (3 : ℤ) ∣ b j-r)).card ≤ k := by
    by_cases ha : A.card ≤ k
    · exact ⟨b j₀+1,by omega,ha⟩
    · exact ⟨b j₀+2,by omega,by change B.card ≤ k; omega⟩
  obtain ⟨r,hr,hcard⟩ := hex
  refine ⟨r,?_,?_⟩
  · intro j hj hd
    exact hr (by simpa only [hmark j hd] using hj)
  · rw [Fintype.card_subtype]
    apply le_trans (Finset.card_le_card ?_) hcard
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2.2⟩

theorem not_cover_three_ternary_exceptions {I K T : Type*}
    [Fintype I] [Fintype K] [Fintype T]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : K → ℕ) (b : K → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (hd3 : ∀ j, ¬ 3 ∣ d j)
    (hK : Fintype.card K ≤ 2)
    (n : T → ℕ) (c : T → ℤ) (hni : Function.Injective n)
    (hn : ∀ j, 1 < n j ∧ Odd (n j)) (hn3 : ∀ j, 3 ∣ n j)
    (hT : Fintype.card T=3) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨
      (∃ j, (d j : ℤ) ∣ x-b j) ∨ ∃ j, (n j : ℤ) ∣ x-c j) := by
  classical
  intro hcover
  have hres (r : ℤ) : ∃ j : T, (3 : ℤ) ∣ c j-r := by
    by_contra hh
    choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) r
    choose b' hb' using fun j => affine_residue (d j) (hd3 j) (b j) r
    apply not_cover_with_at_most_two_odd_exceptions m a' hinj hm h3 d hd b' hK
    intro x
    rcases hcover (3*x+r) with ⟨i,hi⟩ | ⟨j,hj⟩ | ⟨j,hj⟩
    · exact Or.inl ⟨i,ha' i x hi⟩
    · exact Or.inr ⟨j,hb' j x hj⟩
    · have hz := (Int.natCast_dvd_natCast.mpr (hn3 j)).trans hj
      exact False.elim (hh ⟨j,by omega⟩)
  let f : T → ZMod 3 := fun j => (c j : ZMod 3)
  have hsur : Function.Surjective f := by
    intro r
    obtain ⟨j,hj⟩ := hres (r.val : ℤ)
    refine ⟨j,?_⟩
    have hh := (ZMod.intCast_eq_intCast_iff_dvd_sub (r.val : ℤ) (c j) 3).mpr hj
    simpa [f] using hh.symm
  have hf : Function.Injective f := hsur.injective_of_finite
    (Fintype.equivOfCardEq (by simpa only [ZMod.card] using hT))
  have hnval (j : T) : n j=3 ∨ n j=15 := by
    let q := n j/3
    have hmul : 3*q=n j := Nat.mul_div_cancel' (hn3 j)
    have hpos : 0 < q := by have := (hn j).1; omega
    by_cases hq1 : q=1
    · left; omega
    · right
      have hq : 1 < q ∧ Odd q :=
        ⟨by omega,(hn j).2.of_dvd_nat (Nat.div_dvd_of_dvd (hn3 j))⟩
      choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) (c j)
      choose b' hb' using fun k => affine_residue (d k) (hd3 k) (b k) (c j)
      have hq5 := singleton_repair_is_five m a' hinj hm h3 d b' hdi hd hd3 hK q hq 0 (by
        intro x
        rcases hcover (3*x+c j) with ⟨i,hi⟩ | ⟨k,hk⟩ | ⟨k,hk⟩
        · exact Or.inl ⟨i,ha' i x hi⟩
        · exact Or.inr (Or.inl ⟨k,hb' k x hk⟩)
        · have h3k : (3 : ℤ) ∣ c k-c j := by
            have hh := (Int.natCast_dvd_natCast.mpr (hn3 k)).trans hk
            omega
          have hkj : k=j := by
            apply hf
            exact ((ZMod.intCast_eq_intCast_iff_dvd_sub (c j) (c k) 3).mpr h3k).symm
          subst k
          right; right
          simpa only [sub_self,zero_div] using
            Erdos7SmallTernaryBranches.quotient_residue (n j) (c j) (c j)
              (hn3 j) (by simp) x hk)
      omega
  have hsub : Finset.univ.image n ⊆ ({3,15} : Finset ℕ) := by
    intro z hz
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hz
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hnval j
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hni,Finset.card_univ,hT] at hh
  norm_num at hh

#print axioms small_branch_bound
#print axioms not_cover_three_ternary_exceptions
end Erdos7FiveExceptionThreePart
