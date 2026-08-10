import FormalConjectures.Util.ProblemImports
#check Iir
#print axioms Iir
example : False := by
  have h := Iir (a:=0) (b:=1) (by norm_num)
  -- inspect type
  guard_hyp h : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (1 - 0))) = 1) -- maybe
  norm_num
