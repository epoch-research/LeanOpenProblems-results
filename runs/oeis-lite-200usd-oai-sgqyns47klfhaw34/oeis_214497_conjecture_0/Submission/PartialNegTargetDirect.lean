import FormalConjectures.Util.ProblemImports
open Nat
abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)
partial def negTarget : ¬ Target := fun h => negTarget h
#print axioms negTarget
