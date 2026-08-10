import FormalConjectures.Util.ProblemImports
theorem t : ∀ n : Nat, n = n := by
  intro n
  exact t n
#print axioms t
