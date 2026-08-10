import FormalConjectures.Util.ProblemImports
#check (inferInstance : Subsingleton Prop)
example (P : Prop) : True = P := Subsingleton.elim True P
example (P : Prop) : P := by
  exact cast (Subsingleton.elim True P) True.intro
