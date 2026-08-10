import FormalConjectures.Util.ProblemImports
theorem ndtest : (1+1=2) := by native_decide
#check Lean.ofReduceBool
#print axioms ndtest
