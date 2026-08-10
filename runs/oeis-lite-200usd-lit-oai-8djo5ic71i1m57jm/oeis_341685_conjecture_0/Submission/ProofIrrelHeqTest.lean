import FormalConjectures.Util.ProblemImports
#check proof_irrel_heq
#check Eq.ndrec
#check HEq

example : HEq (True.intro) (False.elim (by contradiction) : False) := by
  apply proof_irrel_heq

example : False := by
  have hheq : HEq True.intro (False.elim (by contradiction) : False) := proof_irrel_heq _ _
  -- can we get False?
  apply?
