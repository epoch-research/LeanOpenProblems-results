import FormalConjectures.Util.ProblemImports

inductive E : Prop

#guard_msgs in
  deriving instance Nonempty for E

#check (inferInstance : Nonempty E)
theorem bad : False := by
  have e : E := Classical.choice (inferInstance : Nonempty E)
  cases e
#print axioms bad
