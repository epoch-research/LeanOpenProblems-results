import FormalConjectures.Util.ProblemImports
#check Sat.Fmla.refute
#check Sat.Clause.reify.prop
#check Sat.Literal.reify.prop
example : False := by
  refine Sat.Fmla.refute (p := False) (ps := []) [] ?_ ?_
  · intro v hv
    exact hv.prop [] (by simp)
  · intro v
    -- goal: (v.implies (Sat.Fmla.reify v [] False) [] 0)
    simp [Sat.Valuation.implies]
