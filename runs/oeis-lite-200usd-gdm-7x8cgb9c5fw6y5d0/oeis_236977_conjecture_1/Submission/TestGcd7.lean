import FormalConjectures.Util.ProblemImports

open Nat

theorem sqrt_eq_of_sq (M : ℕ) (r : ℕ) (h : r ^ 2 = M) : sqrt M ^ 2 = M := by
  rw [← h]
  rw [sqrt_eq']

theorem test : sqrt 4 ^ 2 = 4 := by
  exact sqrt_eq_of_sq 4 2 (by decide)
