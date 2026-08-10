import FormalConjectures.Util.ProblemImports
#check (inferInstance : Subsingleton Prop)
example (P : Prop) : P := by
  have h : True = P := Subsingleton.elim True P
  exact cast h True.intro
