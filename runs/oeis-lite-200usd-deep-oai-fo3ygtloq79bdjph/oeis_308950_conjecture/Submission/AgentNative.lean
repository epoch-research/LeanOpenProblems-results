import FormalConjectures.Util.ProblemImports

open Nat Finset

example :
  ∀ n : ℕ, 1 < n →
    (∃ (a b : ℕ), 2 ^ a * 3 ^ b ≤ n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1))
    ∨
    (∃ (a b : ℕ), 2 ^ a * 3 ^ b < n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1)) := by
  native_decide
