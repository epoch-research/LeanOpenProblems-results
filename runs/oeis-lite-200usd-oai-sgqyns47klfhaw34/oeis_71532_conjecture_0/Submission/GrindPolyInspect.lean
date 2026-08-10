import FormalConjectures.Util.ProblemImports
open Lean.Grind.CommRing
#print Mon
#check Mon.unit
#check Mon.var
#check Poly.add
#reduce one_eq_zero_unsat_cert (Poly.add 1 (Mon.var 0) (Poly.num 0))
#reduce one_eq_zero_unsat_cert (Poly.add 1 (Mon.var 0) (Poly.num 1))
#reduce one_eq_zero_unsat_cert (Poly.add 2 (Mon.var 0) (Poly.num 1))
#reduce one_eq_zero_unsat_cert (Poly.add 1 (Mon.var 0) (Poly.num (-1)))
