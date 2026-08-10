import FormalConjectures.Util.ProblemImports
open Lean.Grind.CommRing
open Lean.Grind.CommRing.Stepwise

#reduce unsat_eq_certC (Poly.num 0) 1 2
#reduce unsat_eq_certC (Poly.num 1) 1 2
#reduce unsat_eq_certC (Poly.num 2) 1 2
#reduce unsat_eq_certC (Poly.num 2) 0 2
#reduce unsat_eq_certC (Poly.num 2) 1 0
#reduce unsat_eq_cert (Poly.num 0) 1
#reduce unsat_eq_cert (Poly.num 1) 1
#reduce unsat_eq_cert (Poly.num 2) 1

example : False := by
  have hcert : unsat_eq_certC (Poly.num 2) 1 2 = true := by native_decide
  let ctx : Context (ZMod 2) := Lean.RArray.ofFn (n:=0) (fun i => 0) (by omega)
  have hden : Poly.denote ctx (Poly.num 2) = 0 := by native_decide
  exact unsat_eqC (α:=ZMod 2) (c:=2) ctx (Poly.num 2) 1 hcert hden
#print axioms _example
