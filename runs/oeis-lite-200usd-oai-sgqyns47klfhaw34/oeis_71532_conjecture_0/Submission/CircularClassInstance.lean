import FormalConjectures.Util.ProblemImports

noncomputable instance finiteNatBad : Finite ℕ := finiteNatBad
#print axioms finiteNatBad
example : False := by
  haveI := finiteNatBad
  have h := (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  exact h (Set.finite_univ)
#print axioms CircularClassInstance._example_1
