import FormalConjectures.Util.ProblemImports
open Lean.Grind.CommRing
#reduce one_eq_zero_unsat_cert (Poly.num 0)
#reduce one_eq_zero_unsat_cert (Poly.num 1)
#reduce one_eq_zero_unsat_cert (Poly.num (-1))
#eval one_eq_zero_unsat_cert (Poly.num 0)
#eval one_eq_zero_unsat_cert (Poly.num 1)
