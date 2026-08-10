import FormalConjectures.Util.ProblemImports
open Nat

partial def decP (P : Prop) : Decidable P := decP P

local instance (P : Prop) : Decidable P := decP P

example : (∀ n : ℕ, n = n) := by
  native_decide

example : (∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) := by
  native_decide
