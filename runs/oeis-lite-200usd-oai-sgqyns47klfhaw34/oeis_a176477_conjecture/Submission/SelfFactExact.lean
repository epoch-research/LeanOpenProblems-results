import FormalConjectures.Util.ProblemImports
theorem T : True := by
  letI : Fact True := ⟨T⟩
  exact Fact.out
#print axioms T
