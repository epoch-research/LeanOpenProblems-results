import FormalConjectures.Util.ProblemImports

#synth Lean.Grind.Field ℚ
#synth Lean.Grind.Field (ZMod 1)
#synth Lean.Grind.Field PUnit
#synth Lean.Grind.IntModule PUnit
#synth Grind.Ring PUnit

example : False := by
  let ctx : Lean.Grind.CommRing.Context (ZMod 1) := default
  exact Lean.Grind.CommRing.one_eq_zero_unsat ctx (.num 1) (by native_decide) (by simp)
