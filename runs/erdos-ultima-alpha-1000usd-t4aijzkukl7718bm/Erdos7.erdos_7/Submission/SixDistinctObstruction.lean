import Submission.SixExceptionThreePart

/-! Six distinct odd exceptions cannot complete a distinct no-three base.
This remains a finite-exception theorem, not a universal odd-cover disproof. -/
namespace Erdos7SixDistinctObstruction
open Erdos7SharpDirectFiveGroups Erdos7FiveExceptionThreePart Erdos7MinimumTernaryClass
open Erdos7ExceptionAbsorption
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem not_cover_six_distinct_odd {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (hJ : Fintype.card J ≤ 6) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) := by
  classical
  intro hcover
  obtain ⟨j₀,hj₀⟩ := Erdos7SixNoThreeObstruction.six_contains_three m a hinj hm h3 d b hdi hd hJ hcover
  obtain ⟨j₅,hj₅⟩ := Erdos7SixDistinctWithoutFive.six_contains_five m a hinj hm h3 d b hdi hd hJ hcover
  let T := {j : J // 3 ∣ d j}
  let K := {j : J // ¬ 3 ∣ d j}
  have hex5 : ∃ j : K, d j=5 := ⟨⟨j₅,by rw [hj₅]; decide⟩,hj₅⟩
  have hcards : Fintype.card T+Fintype.card K=Fintype.card J := by
    have hh := Fintype.card_subtype_compl (fun j : J => 3 ∣ d j)
    have ht := Fintype.card_subtype_le (fun j : J => 3 ∣ d j)
    simp only [T,K,Fintype.card_subtype] at hh ht ⊢
    omega
  by_cases hT : Fintype.card T ≤ 2
  · have hK : Fintype.card K ≤ 5 := by
      have hh := Fintype.card_subtype_lt (p := fun j : J => ¬ 3 ∣ d j) (x := j₀) (by simpa using hj₀)
      simp only [K,Fintype.card_subtype] at hh ⊢
      omega
    obtain ⟨r,hr⟩ := Erdos7SmallTernaryBranches.free_ternary_residue (fun j : T => b j) hT
    choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) r
    choose b' hb' using fun j : K => affine_residue (d j) j.property (b j) r
    have hcov : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a' i) ∨
        ∃ j : K, (d j : ℤ) ∣ x-b' j := by
      intro x
      rcases hcover (3*x+r) with ⟨i,hi⟩ | ⟨j,hj⟩
      · exact Or.inl ⟨i,ha' i x hi⟩
      · have hj3 : ¬ 3 ∣ d j := by
          intro hh
          have hz := (Int.natCast_dvd_natCast.mpr hh).trans hj
          exact hr ⟨j,hh⟩ (by change (3 : ℤ) ∣ b j-r; omega)
        exact Or.inr ⟨⟨j,hj3⟩,hb' ⟨j,hj3⟩ x hj⟩
    exact Erdos7SixNoThreeObstruction.not_cover_six_distinct_no_three m a' hinj hm h3
      (fun j : K => d j) b' (hdi.comp Subtype.val_injective)
      (fun j => hd j) (fun j => j.property) (by omega) hcov
  by_cases hT3 : Fintype.card T=3
  · have hK : Fintype.card K ≤ 3 := by omega
    apply Erdos7SixExceptionThreePart.not_cover_three_ternary_exceptions m a hinj hm h3
      (fun j : K => d j) (fun j => b j) (hdi.comp Subtype.val_injective)
      (fun j => hd j) (fun j => j.property) hK hex5
      (fun j : T => d j) (fun j => b j) (hdi.comp Subtype.val_injective)
      (fun j => hd j) (fun j => j.property) hT3
    intro x
    rcases hcover x with hh | ⟨j,hj⟩
    · exact Or.inl hh
    · by_cases hj3 : 3 ∣ d j
      · exact Or.inr (Or.inr ⟨⟨j,hj3⟩,hj⟩)
      · exact Or.inr (Or.inl ⟨⟨j,hj3⟩,hj⟩)
  have hK : Fintype.card K ≤ 2 := by omega
  let k : ℕ := if Fintype.card T ≤ 4 then 1 else 2
  have hk2 : k ≤ 2 := by unfold k; split_ifs <;> omega
  have hTk : Fintype.card T ≤ 2*k+2 := by unfold k; split_ifs <;> omega
  obtain ⟨r,hr,hA⟩ := small_branch_bound (fun j : T => d j) (fun j => b j)
    (hdi.comp Subtype.val_injective) k hTk ⟨j₀,hj₀⟩
  let A := {j : T // 3 ∣ d j ∧ (3 : ℤ) ∣ b j-r}
  have hsize : Fintype.card A ≤ 2 := hA.trans hk2
  have hshape : (Fintype.card K ≤ 2 ∧ Fintype.card A ≤ 1) ∨
      (Fintype.card K ≤ 1 ∧ Fintype.card A ≤ 2) ∨
      (Fintype.card K ≤ 3 ∧ Fintype.card A ≤ 1 ∧ ∀ j : A, d j.val/3≠5) := by
    by_cases ht : Fintype.card T ≤ 4
    · exact Or.inl ⟨hK,by simpa only [k,if_pos ht] using hA⟩
    · exact Or.inr (Or.inl ⟨by omega,hsize⟩)
  choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) r
  choose b' hb' using fun j : K => affine_residue (d j) j.property (b j) r
  have hdA (j : A) : 1 < d j.val/3 ∧ Odd (d j.val/3) := by
    have he := Nat.mul_div_cancel' j.property.1
    have hp := (hd j.val).1
    have hn := hr j.val j.property.2
    exact ⟨by omega,(hd j.val).2.of_dvd_nat (Nat.div_dvd_of_dvd j.property.1)⟩
  have hiA : Function.Injective (fun j : A => d j.val/3) := by
    intro j l hjl
    apply Subtype.ext
    apply Subtype.ext
    apply hdi
    have hj := Nat.mul_div_cancel' j.property.1
    have hl := Nat.mul_div_cancel' l.property.1
    change d j.val/3=d l.val/3 at hjl
    omega
  apply not_cover_small_groups m a' hinj hm h3
    (fun j : K => d j) b' (hdi.comp Subtype.val_injective) (fun j => hd j) (fun j => j.property)
    hex5
    (fun j : A => d j.val/3) (fun j => (b j.val-r)/3) hiA hdA hshape
  intro x
  rcases hcover (3*x+r) with ⟨i,hi⟩ | ⟨j,hj⟩
  · exact Or.inl ⟨i,ha' i x hi⟩
  · by_cases hj3 : 3 ∣ d j
    · have hres : (3 : ℤ) ∣ b j-r := by
        have hz := (Int.natCast_dvd_natCast.mpr hj3).trans hj
        omega
      exact Or.inr (Or.inr ⟨⟨⟨j,hj3⟩,hj3,hres⟩,
        Erdos7SmallTernaryBranches.quotient_residue (d j) (b j) r hj3 hres x hj⟩)
    · exact Or.inr (Or.inl ⟨⟨j,hj3⟩,hb' ⟨j,hj3⟩ x hj⟩)

/-- At least seven residual exceptions remain after absorbing every harmless
new no-three label into the base. -/
theorem residual_card_seven {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j))
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) :
    7 ≤ Fintype.card {j // Residual m d j} := by
  classical
  obtain ⟨n,c,hni,hn,hn3,hcov⟩ := absorb m a hinj hm h3 d b hdi hd hcover
  by_contra hsmall
  exact not_cover_six_distinct_odd n c hni hn hn3
    (fun j : {j // Residual m d j} => d j) (fun j => b j)
    (hdi.comp Subtype.val_injective) (fun j => hd j) (by omega) hcov

#print axioms not_cover_six_distinct_odd
#print axioms residual_card_seven
end Erdos7SixDistinctObstruction
