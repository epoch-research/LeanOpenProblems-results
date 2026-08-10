import FormalConjectures.Util.ProblemImports
partial def loopProp (u : Unit) : Prop := ¬ loopProp u
#print loopProp
#print axioms loopProp
#check loopProp.eq_1
#print loopProp.eq_1
#print axioms loopProp.eq_1
example : False := by
  have hiff : loopProp () ↔ ¬ loopProp () := by
    -- try rw [loopProp.eq_1]
    exact propext.mp (loopProp.eq_1 ())
  exact Lean.Grind.false_of_not_eq_self (propext hiff).symm
#print axioms _example
