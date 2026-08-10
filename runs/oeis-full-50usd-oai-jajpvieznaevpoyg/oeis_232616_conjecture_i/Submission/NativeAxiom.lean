import FormalConjectures.Util.ProblemImports

theorem testNative : 1 + 1 = 2 := by native_decide
#print axioms testNative

theorem testDecide : 1 + 1 = 2 := by decide
#print axioms testDecide
