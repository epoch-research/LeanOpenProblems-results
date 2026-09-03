import Submission.SharpDirectFiveGroups

/-! Three ternary exceptions cannot coexist with a small repair containing five. -/
namespace Erdos7SixExceptionThreePart
open Erdos7Reduction Erdos7MinimumTernaryClass Erdos7SharpDirectFiveGroups
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem not_cover_three_ternary_exceptions {I K T : Type*}
    [Fintype I] [Fintype K] [Fintype T]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : K → ℕ) (b : K → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (hd3 : ∀ j, ¬ 3 ∣ d j)
    (hK : Fintype.card K ≤ 3) (hex5 : ∃ k, d k=5)
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
    apply Erdos7SixNoThreeObstruction.not_cover_six_distinct_no_three m a' hinj hm h3 d b' hdi hd hd3 (by omega)
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
      have hq5 := singleton_repair_is_five m a' hinj hm h3 d b' hdi hd hd3 hex5 hK q hq 0 (by
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

#print axioms not_cover_three_ternary_exceptions
end Erdos7SixExceptionThreePart
