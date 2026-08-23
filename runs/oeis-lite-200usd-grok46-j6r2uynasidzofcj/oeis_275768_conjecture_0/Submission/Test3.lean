import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

example : ∀ n < 80, a n ≠ 4 := by decide
