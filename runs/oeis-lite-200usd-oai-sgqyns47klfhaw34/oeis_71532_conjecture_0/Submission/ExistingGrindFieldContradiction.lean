import FormalConjectures.Util.ProblemImports
open Lean.Grind.CommRing

#check inferInstanceAs (Lean.Grind.Field ℚ)
#check inferInstanceAs (Lean.Grind.Field (ZMod 2))
#check inferInstanceAs (Lean.Grind.Field (ZMod 1))
#check inferInstanceAs (Lean.Grind.Field PUnit)
#check inferInstanceAs (Lean.Grind.Field Unit)

-- Try impossible if ZMod 1 has instance
example : False := by
  have hcert : one_eq_zero_unsat_cert (Poly.num 1) = true := by native_decide
  have hden : Poly.denote (α:=ZMod 1) (Lean.RArray.ofFn (n:=0) (fun i => 0) (by omega)) (Poly.num 1) = 0 := by native_decide
  exact one_eq_zero_unsat (α:=ZMod 1) (Lean.RArray.ofFn (n:=0) (fun i => 0) (by omega)) (Poly.num 1) hcert hden
#print axioms _example
