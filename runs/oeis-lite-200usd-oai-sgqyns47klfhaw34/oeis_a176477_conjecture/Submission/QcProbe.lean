import FormalConjectures.Util.ProblemImports
#check qc
#check hqc
example : False := by
  have h : (qc : ℚ) = 0 := by nlinarith [hqc]
  -- if qc axiom arbitrary not nonzero, can't false
  exact False.elim (by contradiction)
