import FormalConjectures.Util.ProblemImports

#check Set.toFinite
#print Set.toFinite
#print axioms Set.toFinite

example : ({m : ℕ | Nat.Prime (m - 1) ∧ Nat.Prime (m + 1)} : Set ℕ).Finite := by
  exact Set.toFinite _

#print axioms _example
