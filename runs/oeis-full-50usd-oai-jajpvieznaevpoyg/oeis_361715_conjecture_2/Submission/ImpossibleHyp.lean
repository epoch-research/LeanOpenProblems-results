import FormalConjectures.Util.ProblemImports

example : ¬ (5 ≤ (3 : ℕ)) := by norm_num
example : 5 ≤ (3 : ℕ) := by omega
