import FormalConjectures.Util.ProblemImports

#check Lean.Grind.CommRing.one_eq_zero_unsat
#check Lean.Grind.CommRing.Poly
#check Lean.Grind.CommRing.Poly.denote
#check Lean.Grind.CommRing.Context
#check Lean.Grind.CommRing.one_eq_zero_unsat_cert
#check Grind.Linarith.Poly.nil
#check Lean.Grind.Linarith.diseq_unsat

open Lean.Grind

-- just print what can be evaluated / inferred
#eval Lean.Grind.CommRing.one_eq_zero_unsat_cert (α := Int) ?_  -- likely impossible syntax
