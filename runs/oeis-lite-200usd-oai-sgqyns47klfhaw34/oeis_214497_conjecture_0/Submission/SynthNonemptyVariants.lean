import FormalConjectures.Util.ProblemImports
abbrev GoalAt (n : ℕ) : Prop := ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)
#synth Nonempty (∀ n : ℕ, n > 0 → GoalAt n)
#synth Inhabited (∀ n : ℕ, n > 0 → GoalAt n)
#synth Nonempty (∀ n : ℕ, False → GoalAt n)
#synth Nonempty (∀ n : ℕ, n = 0 → GoalAt n)
#synth Nonempty (∀ n : ℕ, GoalAt n → GoalAt n)
