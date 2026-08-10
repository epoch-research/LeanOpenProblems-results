import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

#eval a 0
#eval a 6
#eval a 12
#eval a 18
#eval a 24
#eval a 30
#eval a 36
#eval a 42
