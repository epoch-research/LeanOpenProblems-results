import FormalConjectures.Util.ProblemImports

open QuadraticAlgebra

example : False := by
  -- see if custom Fact instance claims no rational square roots of d for d=1
  have h := (inferInstance : Fact (∀ r : ℚ, r ^ 2 ≠ (1:ℚ) + 0 * r)).out
  exact h 1 (by norm_num)
