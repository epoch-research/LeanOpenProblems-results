import FormalConjectures.Util.ProblemImports
#print Fermat42
#print Fermat42.Minimal
#check Fermat42.not_minimal
#check not_fermat_42
example : False := by
  -- Try constructing an impossible Minimal counterexample by exact?/constructor.
  apply Fermat42.not_minimal (a:=1) (b:=1) (c:=1)
  · constructor <;> norm_num
  · norm_num
  · norm_num
