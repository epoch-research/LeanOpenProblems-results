import FormalConjectures.Util.ProblemImports
inductive Bad : Prop
#check (inferInstance : Inhabited Bad)
example : False := by
  have b : Bad := default
  cases b
#print axioms _example

inductive BadT : Type
#check (inferInstance : Inhabited BadT)
