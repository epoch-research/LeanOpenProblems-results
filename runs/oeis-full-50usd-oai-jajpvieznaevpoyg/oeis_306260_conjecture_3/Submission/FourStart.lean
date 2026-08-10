import FormalConjectures.Util.ProblemImports
open Finset Nat

theorem four_start (n : ℕ) :
  ∃ w x y z : ℕ, n = 4 * w^2 + x * (4 * x + 1) + y * (4 * y - 2) + z * (4 * z - 3) := by
  classical
  obtain ⟨a,b,c,d,h⟩ := Nat.sum_four_squares (8*n+7)
  have hmod : a^2 + b^2 + c^2 + d^2 = 8*n+7 := h
  -- Try brute automation with this extra representation
  omega
