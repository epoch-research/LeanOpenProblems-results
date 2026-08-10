import FormalConjectures.Util.ProblemImports

theorem selfref (n : Nat) : n = n := by
  exact selfref n
#print axioms selfref
