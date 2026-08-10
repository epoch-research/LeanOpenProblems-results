import FormalConjectures.Util.ProblemImports

def a : ℕ → ℕ
| 0     => 1
| n + 1 => (a n) ^ 2 + 2

#eval (a 10).minFac
#eval (a 14).minFac
#eval (a 20).minFac
