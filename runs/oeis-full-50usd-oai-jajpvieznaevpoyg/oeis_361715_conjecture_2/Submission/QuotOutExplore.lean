import FormalConjectures.Util.ProblemImports
#check Quot.out
#check Quot.out_eq
#check Quot.exists_rep
#check Quot.inductionOn
#check Quot.liftOn
#check Quot.hrecOn
#print Quot.out
#print Quot.out_eq

example (P : Prop) : P := by
  let r : Prop → Prop → Prop := fun x y => x → y
  have h : Quot.mk r P = Quot.mk r True := Quot.sound (by intro hp; trivial)
  have hout := congrArg Quot.out h
  -- trace_state
  fail_if_success exact hout.mp trivial
  fail_if_success exact Eq.mp hout trivial
  fail_if_success exact Eq.mpr hout trivial
  sorry
