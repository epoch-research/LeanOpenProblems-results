import Submission.SharpDirectFiveArithmetic
import Submission.SixDistinctWithoutFive

/-! Six distinct no-three exceptions cannot complete a distinct no-three base.
The forced modulus-five exception is charged in the first sieve stage,
rather than as a box against the final hole law. This is still not an
unrestricted nonexistence theorem for odd covering systems. -/
namespace Erdos7SixNoThreeObstruction
open Erdos7Reduction Erdos7FiveDistinctExceptions
open Erdos7SharpDirectFiveArithmetic Erdos7SharpDirectFiveWeight
open Erdos7ExceptionAbsorption
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem not_cover_six_distinct_no_three {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (hd3 : ∀ j, ¬ 3 ∣ d j) (hJ : Fintype.card J ≤ 6) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) := by
  classical
  intro hcover
  obtain ⟨j₀,hj₀⟩ := Erdos7SixDistinctWithoutFive.six_contains_five m a hinj hm h3 d b hdi hd hJ hcover
  let K := {j : J // j≠j₀}
  have hK : Fintype.card K ≤ 5 := by
    have hh := Fintype.card_subtype_lt (p := fun j : J => j≠j₀) (x := j₀) (by simp)
    simp only [K,Fintype.card_subtype] at hh ⊢
    omega
  have h5 (j : K) : d j≠5 := by
    intro hj
    exact j.property (hdi (hj.trans hj₀.symm))
  have hweight := five_missing_five_weight (fun j : K => d j)
    (hdi.comp Subtype.val_injective) (fun j => hd j) (fun j => hd3 j) h5 hK
  apply not_cover_with_weighted_exceptions m a hinj hm h3
    (fun j : K => d j) (fun j => b j) (b j₀)
    (fun j => ⟨by change 0 < d j; have := (hd j).1; omega,(hd j).2⟩) (fun j => hd3 j) hweight
  intro x
  rcases hcover x with hi | ⟨j,hj⟩
  · exact Or.inl hi
  · by_cases he : j=j₀
    · subst j
      exact Or.inr (Or.inl (by simpa only [hj₀] using hj))
    · exact Or.inr (Or.inr ⟨⟨j,he⟩,hj⟩)

/-- Any repair using at most six distinct odd exceptions must contain a
three-divisible label. This is a rigidity statement, not a nonexistence theorem. -/
theorem six_contains_three {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (hJ : Fintype.card J ≤ 6)
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) :
    ∃ j, 3 ∣ d j := by
  by_contra! hn
  exact not_cover_six_distinct_no_three m a hinj hm h3 d b hdi hd hn hJ hcover

/-- The original exceptional family must contain a three-divisible label even
when its total size is arbitrary, provided at most six residual labels remain. -/
theorem six_residual_contains_three {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j))
    (hcard : Fintype.card {j // Residual m d j} ≤ 6)
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) :
    ∃ j, 3 ∣ d j := by
  classical
  obtain ⟨n,c,hni,hn,hn3,hcov⟩ := absorb m a hinj hm h3 d b hdi hd hcover
  obtain ⟨j,hj⟩ := six_contains_three n c hni hn hn3
    (fun j : {j // Residual m d j} => d j) (fun j => b j)
    (hdi.comp Subtype.val_injective) (fun j => hd j) hcard hcov
  exact ⟨j,hj⟩

#print axioms not_cover_six_distinct_no_three
#print axioms six_contains_three
#print axioms six_residual_contains_three
end Erdos7SixNoThreeObstruction
