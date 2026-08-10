import FormalConjectures.Util.ProblemImports

def aa (n : ℕ) := n
example : (∀ n : ℕ, aa n = n) := by decide
-- example : (∀ n : ℕ, 0 < aa n) := by decide
