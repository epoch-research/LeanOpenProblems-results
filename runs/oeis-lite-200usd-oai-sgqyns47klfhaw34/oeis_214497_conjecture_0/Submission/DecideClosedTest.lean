import FormalConjectures.Util.ProblemImports

open Nat

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

#check (inferInstance : Decidable Target)
#eval decide Target

example : Target := by
  decide

example : ¬ Target := by
  decide
