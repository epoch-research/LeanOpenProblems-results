import Submission.DirectFiveArithmetic
import Submission.FiveDistinctExceptions
import Submission.ExceptionAbsorption

/-! Five distinct odd exceptions cannot complete a distinct no-three base.
The forced modulus-five exception is charged in the first sieve stage,
rather than as a box against the final hole law. This is still not an
unrestricted nonexistence theorem for odd covering systems. -/
namespace Erdos7FiveDistinctObstruction
open Erdos7Reduction Erdos7FiveDistinctExceptions
open Erdos7DirectFiveArithmetic Erdos7DirectFiveWeight
open Erdos7ExceptionAbsorption
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem not_cover_five_distinct_odd {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (hJ : Fintype.card J ≤ 5) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) := by
  classical
  intro hcover
  obtain ⟨hd3,⟨j₀,hj₀⟩,_⟩ := prime_constraints m a hinj hm h3 d b hdi hd hJ hcover
  let K := {j : J // j≠j₀}
  have hK : Fintype.card K ≤ 4 := by
    have hh := Fintype.card_subtype_lt (p := fun j : J => j≠j₀) (x := j₀) (by simp)
    simp only [K,Fintype.card_subtype] at hh ⊢
    omega
  have h5 (j : K) : d j≠5 := by
    intro hj
    exact j.property (hdi (hj.trans hj₀.symm))
  have hweight := four_missing_five_weight (fun j : K => d j)
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

/-- At least six residual exceptions remain after absorbing every harmless
new no-three label into the base. -/
theorem residual_card_six {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j))
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) :
    6 ≤ Fintype.card {j // Residual m d j} := by
  classical
  obtain ⟨n,c,hni,hn,hn3,hcov⟩ := absorb m a hinj hm h3 d b hdi hd hcover
  by_contra hsmall
  exact not_cover_five_distinct_odd n c hni hn hn3
    (fun j : {j // Residual m d j} => d j) (fun j => b j)
    (hdi.comp Subtype.val_injective) (fun j => hd j) (by omega) hcov

#print axioms not_cover_five_distinct_odd
#print axioms residual_card_six
end Erdos7FiveDistinctObstruction
