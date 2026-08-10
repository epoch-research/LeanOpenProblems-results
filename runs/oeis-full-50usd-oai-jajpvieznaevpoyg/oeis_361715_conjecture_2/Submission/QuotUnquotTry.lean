import FormalConjectures.Util.ProblemImports

def qfalse : Quot (fun (_ _ : False) => True) := by exact Quot.mk _ (by contradiction)
-- impossible construct above should fail
