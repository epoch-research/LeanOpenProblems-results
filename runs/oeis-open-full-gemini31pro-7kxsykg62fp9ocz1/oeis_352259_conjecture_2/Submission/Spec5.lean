import FormalConjectures.Util.ProblemImports
open Nat Finset

theorem oeis_352259_conjecture_2 (n : ℕ) :
  ∃ (w x y z : ℕ), n = 2 * w^4 + 3 * x^2 + y^2 + z^2 + x * y * z := by
  aesop
