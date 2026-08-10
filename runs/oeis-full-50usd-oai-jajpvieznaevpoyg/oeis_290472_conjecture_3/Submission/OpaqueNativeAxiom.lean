import FormalConjectures.Util.ProblemImports
opaque hnat : (1000 : Nat) + 1 = 1001 := by native_decide
theorem thnat : (1000 : Nat) + 1 = 1001 := hnat
#print axioms hnat
#print axioms thnat
