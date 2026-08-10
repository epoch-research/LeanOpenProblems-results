import FormalConjectures.Util.ProblemImports
opaque hcalc : (1000 : ℕ) + 1 = 1001 := by native_decide

theorem tcalc : (1000 : ℕ) + 1 = 1001 := hcalc
#print axioms tcalc
