import FormalConjectures.Util.ProblemImports
theorem testNative : (1234567:Nat) < 7654321 := by native_decide
#print axioms testNative
