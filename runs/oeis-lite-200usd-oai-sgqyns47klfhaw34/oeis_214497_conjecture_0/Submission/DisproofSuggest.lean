import FormalConjectures.Util.ProblemImports
open Nat

example :
  ¬ (∀ n : ℕ, n > 0 →
      ∃ k : ℕ,
        Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧
        Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) := by
  intro H
  exact?

example (H : ∀ n : ℕ, n > 0 →
      ∃ k : ℕ,
        Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧
        Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) : False := by
  apply?
