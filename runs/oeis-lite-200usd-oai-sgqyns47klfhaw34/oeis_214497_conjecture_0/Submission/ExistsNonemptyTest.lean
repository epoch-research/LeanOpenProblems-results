import FormalConjectures.Util.ProblemImports

#synth Nonempty (∃ n : ℕ, n = n)
#synth Nonempty (∃ n : ℕ, Nat.Prime n)
#synth Nonempty (∃ n : ℕ, False)

example : (∃ n : ℕ, Nat.Prime n) := Classical.choice (inferInstance : Nonempty (∃ n : ℕ, Nat.Prime n))
