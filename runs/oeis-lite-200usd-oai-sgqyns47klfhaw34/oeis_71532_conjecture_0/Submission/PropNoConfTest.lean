import FormalConjectures.Util.ProblemImports

inductive OrP : Prop where
| left : OrP
| right : OrP

example : False := by
  have h : OrP.left = OrP.right := Subsingleton.elim _ _
  cases h

#print axioms OrP.noConfusion
