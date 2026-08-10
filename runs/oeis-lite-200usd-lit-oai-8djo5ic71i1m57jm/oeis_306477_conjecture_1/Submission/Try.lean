import FormalConjectures.Util.ProblemImports

def P : Prop := ∀ n : ℕ, n = n
example : P := by decide
