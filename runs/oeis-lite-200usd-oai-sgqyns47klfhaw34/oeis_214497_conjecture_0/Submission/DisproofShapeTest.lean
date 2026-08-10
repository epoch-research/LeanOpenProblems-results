import FormalConjectures.Util.ProblemImports
open Nat

example :
    (¬ (∀ n > 0, ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1))) ↔
    (∃ n, n > 0 ∧ ∀ k : ℕ, ¬ (Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1))) := by
  classical
  push_neg
  rfl
