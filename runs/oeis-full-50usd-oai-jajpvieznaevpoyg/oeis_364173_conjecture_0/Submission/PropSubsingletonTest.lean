import FormalConjectures.Util.ProblemImports

#check propSubsingleton
#check Subsingleton.elim (α:=Prop)
example (P Q : Prop) : P = Q := Subsingleton.elim P Q
