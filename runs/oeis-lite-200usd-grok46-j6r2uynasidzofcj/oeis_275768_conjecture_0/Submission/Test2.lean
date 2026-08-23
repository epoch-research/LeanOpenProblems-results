import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

set_option maxRecDepth 10000

example : a 54 ≠ 4 := by decide
example : a 60 ≠ 4 := by decide
example : a 96 ≠ 4 := by decide
example : a 192 ≠ 4 := by decide
