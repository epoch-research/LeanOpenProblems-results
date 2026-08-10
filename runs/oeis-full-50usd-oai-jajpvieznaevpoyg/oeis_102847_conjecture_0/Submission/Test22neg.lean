import FormalConjectures.Util.ProblemImports

def a : ℕ → ℕ
| 0 => 1
| n+1 => (a n)^2 + 2

example : ¬ Nat.Prime (a 22) := by native_decide
