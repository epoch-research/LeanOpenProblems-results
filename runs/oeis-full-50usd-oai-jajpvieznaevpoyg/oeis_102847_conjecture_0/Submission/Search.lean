import FormalConjectures.Util.ProblemImports

def a : ℕ → ℕ
| 0 => 1
| n+1 => (a n)^2 + 2

#eval Nat.Prime (a 16)
#eval Nat.Prime (a 18)
#eval Nat.Prime (a 20)
