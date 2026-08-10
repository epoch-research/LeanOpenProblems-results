import FormalConjectures.Util.ProblemImports
open Lean.Grind.CommRing
#reduce one_eq_zero_unsat_cert (Poly.num 2)
#reduce one_eq_zero_unsat_cert (Poly.num (-2))
example : False := by
  have hcert : one_eq_zero_unsat_cert (Poly.num 2) = true := by native_decide
  have hden : Poly.denote (α:=ZMod 2) (Lean.RArray.empty) (Poly.num 2) = 0 := by native_decide
  exact one_eq_zero_unsat (α:=ZMod 2) Lean.RArray.empty (Poly.num 2) hcert hden
#print axioms _example
