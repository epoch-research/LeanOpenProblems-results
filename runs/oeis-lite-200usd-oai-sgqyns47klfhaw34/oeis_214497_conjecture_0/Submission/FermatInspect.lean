import FormalConjectures.Util.ProblemImports

#print Fermat42
#print Fermat42.Minimal
#print Fermat42.not_minimal
#check Fermat42.not_minimal

example : False := by
  -- try simple automation
  apply Fermat42.not_minimal (a:=1) (b:=0) (c:=1)
  all_goals simp [Fermat42.Minimal]
