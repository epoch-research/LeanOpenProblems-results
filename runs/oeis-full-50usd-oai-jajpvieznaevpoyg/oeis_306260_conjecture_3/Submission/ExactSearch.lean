import FormalConjectures.Util.ProblemImports
open Finset Nat
example (n : ℕ) :
  ∃ w x y z : ℕ, n = 4 * w^2 + x * (4 * x + 1) + y * (4 * y - 2) + z * (4 * z - 3) := by
  exact?
example (n : ℕ) : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 16*n+14 := by
  exact?
