import FormalConjectures.Util.ProblemImports
import Submission.Spec

open scoped Real

theorem test_contradiction (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) : False := by
  have h1 := h_int 1
  rcases h1 with ⟨y, hy⟩
  change ((y : ℤ) : ℝ) = a 1 at hy
  rw [a_one_eq_128] at hy
  have h_y_eq : y = 128 := by
    apply Int.cast_injective (α := ℝ)
    push_cast
    exact hy
  sorry
