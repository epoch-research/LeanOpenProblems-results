import FormalConjectures.Util.ProblemImports

-- Test representative noConfusion eliminators: they need genuinely impossible equalities.
example (P : Sort*) : P := by
  exact Bool.noConfusion (show true = false from by decide) (motive := fun _ => P)

example (P : Sort*) : P := by
  exact Nat.noConfusion (show Nat.succ 0 = 0 from by decide) (motive := fun _ => P)

example (P : Sort*) : P := by
  exact Option.noConfusion (show (some () : Option Unit) = none from by decide) (motive := fun _ => P)

example (P : Sort*) : P := by
  exact Empty.elim (Classical.choice (inferInstance : Nonempty Empty))
