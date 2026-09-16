import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Nat.recOn n 2 fun _ a_n => 2 ^ a_n - 1

#check a
