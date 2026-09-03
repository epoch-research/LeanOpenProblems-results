import Submission.BackwardFamilyBudget

/-! Family budgets are not closed under pointwise minimum, even with the
constant-one budget. Thus clipping a positive tail at one is not justified. -/
namespace Erdos7BudgetMeetObstruction
open scoped BigOperators
open Erdos7BackwardFamilyBudget
set_option autoImplicit false

noncomputable def weight (_ : Fin 2) : ℝ := 1/2
noncomputable def count (_ : Unit) (x : Fin 2) : ℝ := 1+x.val
noncomputable def affine (t : ℝ) : ℝ := 2*t-2

lemma affine_convex : ConvexOn ℝ Set.univ affine := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  dsimp only [affine,smul_eq_mul]
  nlinarith

lemma affine_monotone : Monotone affine := by
  intro x y hxy
  dsimp only [affine]
  linarith

lemma budget_affine : HasBudget weight count affine 1 2 := by
  refine ⟨Unit,inferInstance,0,(fun _ => ()),(fun _ => affine),?_,?_,?_⟩
  · intro i
    exact ⟨affine_convex,affine_monotone⟩
  · intro t ht
    simp
  · norm_num [weight,count,affine,Fin.sum_univ_two]

lemma budget_one {Ω α : Type} [Fintype Ω] (μ : Ω → ℝ) (X : α → Ω → ℝ)
    (lo hi : ℝ) : HasBudget μ X (fun _ => 1) lo hi := by
  refine ⟨PEmpty,inferInstance,1,PEmpty.elim,PEmpty.elim,?_,?_,?_⟩
  · intro i
    exact i.elim
  · simp
  · simp

lemma not_budget_min : ¬HasBudget weight count (fun t => min (affine t) 1) 1 2 := by
  rintro ⟨ι,inst,b,pick,φ,hφ,hdiag,hbudget⟩
  letI : Fintype ι := inst
  have h1 := hdiag 1 (by constructor <;> norm_num)
  have h2 := hdiag 2 (by constructor <;> norm_num)
  norm_num [affine] at h1 h2
  norm_num [weight,count,Fin.sum_univ_two] at hbudget
  linarith

/-- A concrete obstruction to combining a tail budget with trivial stopping
by taking the pointwise minimum of their potentials. -/
theorem not_closed_under_min :
    HasBudget weight count affine 1 2 ∧
    HasBudget weight count (fun _ => 1) 1 2 ∧
    ¬HasBudget weight count (fun t => min (affine t) 1) 1 2 :=
  ⟨budget_affine,budget_one _ _ _ _,not_budget_min⟩

#print axioms not_closed_under_min
end Erdos7BudgetMeetObstruction
