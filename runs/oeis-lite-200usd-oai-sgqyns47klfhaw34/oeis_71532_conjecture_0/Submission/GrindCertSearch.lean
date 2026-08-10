import FormalConjectures.Util.ProblemImports
open Lean.Grind.CommRing
#reduce one_eq_zero_unsat_cert (Poly.num 0)
#reduce one_eq_zero_unsat_cert (Poly.num 1)
#reduce one_eq_zero_unsat_cert (Poly.num (-1))
#reduce Lean.Grind.CommRing.Poly.denote (α:=ZMod 2) (.ofFn fun _ => 0) (Poly.num 0)
#reduce Lean.Grind.CommRing.Poly.denote (α:=ZMod 2) (.ofFn fun _ => 0) (Poly.num 2)
