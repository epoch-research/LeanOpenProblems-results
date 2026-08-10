import FormalConjectures.Util.ProblemImports
open Finset Nat

theorem try_auto (n : ℕ) :
  ∃ w x y z : ℕ, n = 4 * w^2 + x * (4 * x + 1) + y * (4 * y - 2) + z * (4 * z - 3) := by
  obtain ⟨a,b,c,d,h⟩ := Nat.sum_four_squares (16*n+14)
  -- try direct automation from existence of a square representation of the completion
  aesop (add safe Nat.exists_eq_add_of_le) (add simp [pow_two])
