import FormalConjectures.Util.ProblemImports

#check Lean.Grind.Linarith.diseq_unsat
#check Lean.Grind.Linarith.lt_unsat
#check Lean.Grind.Linarith.Context
#check Lean.Grind.Linarith.Poly.nil
#check Lean.Grind.Linarith.Poly.denote

-- Try common degenerate or unusual types.
#synth Lean.Grind.IntModule PUnit
#synth LE PUnit
#synth LT PUnit
#synth Std.LawfulOrderLT PUnit
#synth Std.IsPreorder PUnit

#synth Lean.Grind.IntModule Empty
#synth LE Empty
#synth LT Empty
#synth Std.LawfulOrderLT Empty
#synth Std.IsPreorder Empty

#synth Lean.Grind.IntModule Bool
#synth LE Bool
#synth LT Bool
#synth Std.LawfulOrderLT Bool
#synth Std.IsPreorder Bool

-- If context has an Inhabited instance, try default.
#synth Inhabited (Lean.Grind.Linarith.Context PUnit)
#synth Inhabited (Lean.Grind.Linarith.Context ℤ)

example : False := by
  let ctx : Lean.Grind.Linarith.Context PUnit := default
  exact Lean.Grind.Linarith.diseq_unsat ctx (by decide)

example : False := by
  let ctx : Lean.Grind.Linarith.Context PUnit := default
  exact Lean.Grind.Linarith.lt_unsat ctx (by decide)
