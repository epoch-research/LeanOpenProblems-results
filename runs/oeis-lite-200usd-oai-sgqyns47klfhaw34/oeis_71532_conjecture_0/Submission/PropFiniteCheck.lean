import FormalConjectures.Util.ProblemImports
#check inferInstanceAs (Finite Prop)
#check inferInstanceAs (Fintype Prop)
#check inferInstanceAs (Infinite Prop)
example : False := Infinite.false (α:=Prop) (inferInstanceAs (Infinite Prop))
#print axioms _example
