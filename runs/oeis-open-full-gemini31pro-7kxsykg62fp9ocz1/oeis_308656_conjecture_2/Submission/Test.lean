import FormalConjectures.Util.ProblemImports
import Submission.Spec

theorem test_1 : ∃ f : ℤ → ℤ, f ∈ set_of_polynomials_F ∧ 
  ∃ a b : ℕ, ∃ c d : ℤ, (1 : ℤ) = square_term a b + f c + poly_g d := by
  use poly_f1
  constructor
  · simp [set_of_polynomials_F]
  · use 0, 0, 0, 0
    rfl
