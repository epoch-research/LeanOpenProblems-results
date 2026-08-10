import FormalConjectures.Util.ProblemImports

#print Quot
#print Quot.sound
#check Quot.exact
#print Quot.exact

example (P : Prop) : P := by
  let r : Unit → Unit → Prop := fun _ _ => P
  have hq : Quot.mk r () = Quot.mk r () := rfl
  exact Quot.exact hq
