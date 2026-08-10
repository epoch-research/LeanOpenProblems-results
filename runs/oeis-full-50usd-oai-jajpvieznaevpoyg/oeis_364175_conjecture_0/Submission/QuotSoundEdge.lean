import FormalConjectures.Util.ProblemImports
-- Try to make a Setoid whose relation includes a chosen proposition.
def relP (P : Prop) : Unit → Unit → Prop := fun _ _ => P
-- Cannot make a Setoid without proving P for reflexivity:
example (P : Prop) : (Setoid Unit) := by
  refine { r := relP P, iseqv := ?_ }
  constructor
  · intro x
    -- stuck: need P
    guard_target = P
    exact ?_
  · intro x y h; exact h
  · intro x y z h1 h2; exact h1
