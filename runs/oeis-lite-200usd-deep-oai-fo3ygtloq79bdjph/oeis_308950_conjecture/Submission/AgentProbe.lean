import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option maxHeartbeats 200000
set_option pp.all false

example :
  ∀ n : ℕ, 1 < n →
    (∃ (a b : ℕ), 2 ^ a * 3 ^ b ≤ n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1))
    ∨
    (∃ (a b : ℕ), 2 ^ a * 3 ^ b < n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1)) := by
  intro n hn
  apply?

example : ¬ (∀ n : ℕ, 1 < n →
    (∃ (a b : ℕ), 2 ^ a * 3 ^ b ≤ n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1))
    ∨
    (∃ (a b : ℕ), 2 ^ a * 3 ^ b < n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1))) := by
  intro h
  apply?
