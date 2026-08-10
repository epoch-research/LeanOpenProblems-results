import FormalConjectures.Util.ProblemImports
open Nat

abbrev Target214497D : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

deriving instance Nonempty for Target214497D

example : Target214497D := Classical.choice (inferInstance : Nonempty Target214497D)

#print axioms instNonemptyTarget214497D
