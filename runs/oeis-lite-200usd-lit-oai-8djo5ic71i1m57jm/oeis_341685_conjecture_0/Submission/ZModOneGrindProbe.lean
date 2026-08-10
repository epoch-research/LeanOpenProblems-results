import FormalConjectures.Util.ProblemImports
#synth Field (ZMod 1)
#synth Lean.Grind.Field (ZMod 1)
example : False := by
  let ctx : Lean.Grind.CommRing.Context (ZMod 1) := Lean.RArray.leaf
  exact Lean.Grind.CommRing.one_eq_zero_unsat ctx (Lean.Grind.CommRing.Poly.num 1) (by rfl) (by simp)
