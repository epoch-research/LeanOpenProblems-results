import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

#eval a 18
#eval a 24
#eval a 8
#eval a 5

example : a 8 = 2 := by decide
example : a 18 = 3 := by decide
example : a 24 = 5 := by decide
