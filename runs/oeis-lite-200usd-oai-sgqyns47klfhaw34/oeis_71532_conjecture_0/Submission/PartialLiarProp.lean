import FormalConjectures.Util.ProblemImports

partial def Liar (_ : Unit) : Prop := ¬ Liar ()
#print Liar
#print axioms Liar

#check Mathlib.Tactic.CC.false_of_a_eq_not_a

example : False := by
  apply Mathlib.Tactic.CC.false_of_a_eq_not_a (a := Liar ())
  -- can we unfold Liar?
  unfold Liar
  rfl

#print axioms _example
