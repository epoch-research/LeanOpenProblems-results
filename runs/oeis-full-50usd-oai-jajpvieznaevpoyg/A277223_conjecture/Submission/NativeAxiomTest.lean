import FormalConjectures.Util.ProblemImports

theorem tnative : (1000 + 2000 = 3000) := by native_decide
#print axioms tnative

theorem tdecide : (1000 + 2000 = 3000) := by decide
#print axioms tdecide
