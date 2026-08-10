import FormalConjectures.Util.ProblemImports
abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)
deriving instance Nonempty for Target
#check instNonemptyTarget
#print axioms instNonemptyTarget
example : Target := Classical.choice (inferInstance : Nonempty Target)
#print axioms DeriveNonemptyRetest._example_1
