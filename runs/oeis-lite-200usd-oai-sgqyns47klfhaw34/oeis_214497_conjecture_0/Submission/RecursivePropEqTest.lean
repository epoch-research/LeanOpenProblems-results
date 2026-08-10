import FormalConjectures.Util.ProblemImports

partial def pLoop (_ : Unit) : Prop := ¬ pLoop ()
#print pLoop
#print axioms pLoop

example : pLoop () = ¬ pLoop () := by
  rfl

example : False := Mathlib.Tactic.CC.false_of_a_eq_not_a (show pLoop () = ¬ pLoop () from rfl)

-- normal recursive def should fail
def pRec (_ : Unit) : Prop := ¬ pRec ()
