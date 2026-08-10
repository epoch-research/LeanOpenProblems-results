import FormalConjectures.Util.ProblemImports
#check (Subsingleton.elim (False : Prop) (True : Prop))
example : False := by
  exact Eq.mp (Subsingleton.elim (True : Prop) (False : Prop)) True.intro
#print axioms _example
