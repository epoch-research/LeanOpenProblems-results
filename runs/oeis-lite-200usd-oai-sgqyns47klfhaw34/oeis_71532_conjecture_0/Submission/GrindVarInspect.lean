import FormalConjectures.Util.ProblemImports
open Lean.Grind.CommRing
#print Var
#check (0 : Var)
def x0 : Mon := Mon.mult (Power.mk (0 : Var) 1) Mon.unit
#reduce one_eq_zero_unsat_cert (Poly.add 1 x0 (Poly.num 1))
#reduce one_eq_zero_unsat_cert (Poly.add 1 x0 (Poly.num (-1)))
#reduce one_eq_zero_unsat_cert (Poly.add 2 x0 (Poly.num 1))
#reduce one_eq_zero_unsat_cert (Poly.add 2 x0 (Poly.num 2))
