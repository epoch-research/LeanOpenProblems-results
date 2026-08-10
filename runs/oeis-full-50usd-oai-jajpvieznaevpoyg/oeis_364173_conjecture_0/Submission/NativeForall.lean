import FormalConjectures.Util.ProblemImports
example : ∀ n : ℕ, n = n := by native_decide
example (P : Prop) : P ∨ ¬ P := by native_decide
