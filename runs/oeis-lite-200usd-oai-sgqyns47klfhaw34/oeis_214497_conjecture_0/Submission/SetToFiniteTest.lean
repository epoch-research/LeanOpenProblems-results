import FormalConjectures.Util.ProblemImports
open Nat

#check Set.toFinite
#check Set.finite_def

example : ({m : ℕ | Nat.Prime (m - 1) ∧ Nat.Prime (m + 1)} : Set ℕ).Finite := by
  exact Set.toFinite _

#print axioms _example
