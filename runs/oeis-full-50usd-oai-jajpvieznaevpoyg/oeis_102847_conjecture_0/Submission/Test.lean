import FormalConjectures.Util.ProblemImports

def a : ℕ → ℕ
| 0 => 1
| n+1 => (a n)^2 + 2

example : Nat.Prime (a 4) := by native_decide
example : ¬ Nat.Prime (a 6) := by native_decide
example : ¬ Nat.Prime (a 10) := by native_decide
example : ¬ Nat.Prime (a 14) := by native_decide
