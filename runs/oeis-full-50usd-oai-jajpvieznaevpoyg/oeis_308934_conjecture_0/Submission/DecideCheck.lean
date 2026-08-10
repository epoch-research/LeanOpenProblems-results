import FormalConjectures.Util.ProblemImports
example : Decidable (∀ n : ℕ, n > 1 → True) := by infer_instance
example : (∀ n : ℕ, n > 1 → True) := by decide
