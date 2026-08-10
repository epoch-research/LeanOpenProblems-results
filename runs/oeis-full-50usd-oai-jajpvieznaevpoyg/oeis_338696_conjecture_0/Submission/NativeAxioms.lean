import FormalConjectures.Util.ProblemImports

theorem twoeq : 1+1=2 := by native_decide
#print axioms twoeq

theorem twoeq2 : 1+1=2 := by decide
#print axioms twoeq2
