import FormalConjectures.Util.ProblemImports

def a : ℕ → ℕ
| 0 => 1
| n+1 => (a n)^2 + 2

theorem t : ¬ Nat.Prime (a 20) := by native_decide
#print axioms t
