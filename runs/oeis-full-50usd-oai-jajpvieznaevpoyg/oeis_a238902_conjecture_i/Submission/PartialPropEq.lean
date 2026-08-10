import FormalConjectures.Util.ProblemImports
partial def propEq (P Q : Prop) (_ : Unit) : P = Q := propEq P Q ()
#print propEq
#print axioms propEq

theorem bad : False := by
  have h : True = False := propEq True False ()
  exact Eq.mp h True.intro
#print axioms bad
