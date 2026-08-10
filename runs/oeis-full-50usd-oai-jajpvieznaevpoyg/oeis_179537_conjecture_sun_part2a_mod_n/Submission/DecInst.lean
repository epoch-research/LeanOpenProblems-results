import FormalConjectures.Util.ProblemImports
#synth Decidable ((5:ℤ) ≡ 0 [ZMOD (3:ℤ)])
#synth Decidable (∀ n : ℕ, n = n)
#synth Decidable (∀ n : ℕ, (n:ℤ) ≡ (n:ℤ) [ZMOD (n:ℤ)])
example : ∀ n : ℕ, (n:ℤ) ≡ (n:ℤ) [ZMOD (n:ℤ)] := by native_decide
