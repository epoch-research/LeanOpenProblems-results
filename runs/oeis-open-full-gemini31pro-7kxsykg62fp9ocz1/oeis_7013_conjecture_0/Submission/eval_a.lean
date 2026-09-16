import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Nat.recOn n 2 fun _ a_n => 2 ^ a_n - 1

#eval a 0
#eval a 1
#eval a 2
#eval a 3
