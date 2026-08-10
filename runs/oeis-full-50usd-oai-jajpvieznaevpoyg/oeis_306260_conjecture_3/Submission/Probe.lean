import FormalConjectures.Util.ProblemImports

open Finset Nat

example (n : ℕ) :
  ∃ w x y z : ℕ, n = 4 * w^2 + x * (4 * x + 1) + y * (4 * y - 2) + z * (4 * z - 3) := by
  have h4 := Nat.sum_four_squares (16*n + 14)
  rcases h4 with ⟨a,b,c,d,habcd⟩
  -- aesop?
  fail_if_success aesop
  sorry
