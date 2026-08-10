import FormalConjectures.Util.ProblemImports
#check Lean.Grind.CommRing.one_eq_zero_unsat
#check Lean.Grind.CommRing.Context
#check Lean.Grind.CommRing.Poly
#check Lean.Grind.CommRing.Poly.denote
#check Lean.Grind.CommRing.one_eq_zero_unsat_cert
#synth Lean.Grind.Field ℚ
#synth Lean.Grind.Field (ZMod 2)
#synth Lean.Grind.Field PUnit
#eval Lean.Grind.CommRing.one_eq_zero_unsat_cert (by exact (default : Lean.Grind.CommRing.Poly))
