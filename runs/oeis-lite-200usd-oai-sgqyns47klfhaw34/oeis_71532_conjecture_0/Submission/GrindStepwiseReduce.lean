import FormalConjectures.Util.ProblemImports
open Lean.Grind.CommRing
open Lean.Grind.CommRing.Stepwise
#reduce unsat_eq_certC (Poly.num 0) 1 2
#reduce unsat_eq_certC (Poly.num 1) 1 2
#reduce unsat_eq_certC (Poly.num 2) 1 2
#reduce unsat_eq_cert (Poly.num 0) 1
#reduce unsat_eq_cert (Poly.num 1) 1
#reduce unsat_eq_cert (Poly.num 2) 1
