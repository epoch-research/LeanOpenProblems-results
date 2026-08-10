import FormalConjectures.Util.ProblemImports
#check Lean.reduceBool
#eval Lean.reduceBool false
#eval Lean.reduceBool true
#check Lean.ofReduceBool false true
-- example : False := by
--   have h : false = true := Lean.ofReduceBool false true (by native_decide)
--   cases h
