import FormalConjectures.Util.ProblemImports

-- Try to exploit raw quotients over Prop. This should fail if Lean is sound.
example (P : Prop) : P := by
  let r : Prop → Prop → Prop := fun x y => x → y
  have hq : Quot.mk r P = Quot.mk r True := Quot.sound (by intro hp; trivial)
  have hout : (Quot.out (Quot.mk r P)) = (Quot.out (Quot.mk r True)) := congrArg Quot.out hq
  -- out_eq gives quotient equations for the chosen representatives, but not P = True.
  have ho1 : Quot.mk r (Quot.out (Quot.mk r P)) = Quot.mk r P := Quot.out_eq _
  have ho2 : Quot.mk r (Quot.out (Quot.mk r True)) = Quot.mk r True := Quot.out_eq _
  -- Try common transports.
  fail_if_success exact Eq.mp hout trivial
  fail_if_success exact Eq.mpr hout trivial
  fail_if_success exact cast hout trivial
  fail_if_success exact cast hout.mp trivial
  fail_if_success exact cast hout ▸ trivial
  -- trace_state
  sorry
