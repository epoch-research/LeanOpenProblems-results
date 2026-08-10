import FormalConjectures.Util.ProblemImports
theorem natDivFixed : (5^3 : ℕ) ∣ (3116125 : ℕ) := by native_decide
#print axioms natDivFixed
theorem nativeTrue : True := by native_decide
#print axioms nativeTrue
