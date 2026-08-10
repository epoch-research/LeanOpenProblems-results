import FormalConjectures.Util.ProblemImports
partial def ssProp : Subsingleton Prop := ssProp
local instance : Subsingleton Prop := ssProp
theorem bad : False := by
  have h : (True:Prop) = False := Subsingleton.elim _ _
  exact Eq.mp h True.intro
#print axioms bad
