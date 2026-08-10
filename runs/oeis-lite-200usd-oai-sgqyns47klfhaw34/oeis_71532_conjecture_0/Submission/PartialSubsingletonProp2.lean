import FormalConjectures.Util.ProblemImports
partial def subProp (u : Unit) : Subsingleton Prop := subProp u
local instance : Subsingleton Prop := subProp ()
example : False := by
  have h : (True : Prop) = False := Subsingleton.elim _ _
  exact Eq.mp h True.intro
#print axioms subProp
#print axioms _example
