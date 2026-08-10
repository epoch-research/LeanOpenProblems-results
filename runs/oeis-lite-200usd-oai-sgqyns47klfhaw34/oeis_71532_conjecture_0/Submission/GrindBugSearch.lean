import FormalConjectures.Util.ProblemImports
open Lean.Grind.CommRing

def x0 : Mon := Mon.mult (Power.mk (0 : Var) 1) Mon.unit
def x0sq : Mon := Mon.mult (Power.mk (0 : Var) 2) Mon.unit
def poly1 : Lean.Grind.CommRing.Poly := Poly.num 1
def poly_x_minus1 : Lean.Grind.CommRing.Poly := Poly.add 1 x0 (Poly.num (-1))
def poly_x_plus1 : Lean.Grind.CommRing.Poly := Poly.add 1 x0 (Poly.num 1)
def poly_xsq_x : Lean.Grind.CommRing.Poly := Poly.add 1 x0sq (Poly.add 1 x0 (Poly.num 0))
def poly_xsq_x_plus1 : Lean.Grind.CommRing.Poly := Poly.add 1 x0sq (Poly.add 1 x0 (Poly.num 1))
#reduce one_eq_zero_unsat_cert poly1
#reduce one_eq_zero_unsat_cert poly_x_minus1
#reduce one_eq_zero_unsat_cert poly_x_plus1
#reduce one_eq_zero_unsat_cert poly_xsq_x
#reduce one_eq_zero_unsat_cert poly_xsq_x_plus1
#check Lean.RArray
#check Lean.RArray.ofFn
#check Lean.RArray.get
#check Lean.RArray.empty
