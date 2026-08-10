import FormalConjectures.Util.ProblemImports
#check Quot.sound
#check Quot.exact
#check Quotient.exact
example (P : Prop) : P := by
  let r : Unit → Unit → Prop := fun _ _ => P
  have hq : Quot.mk r () = Quot.mk r () := rfl
  -- exact Quot.exact hq
  fail_if_success exact Quot.exact hq
  exact False.elim (by contradiction)
