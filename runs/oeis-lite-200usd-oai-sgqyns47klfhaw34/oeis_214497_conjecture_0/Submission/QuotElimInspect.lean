import FormalConjectures.Util.ProblemImports

#check Quot.ind
#check Quot.inductionOn
#check Quot.lift
#check Quotient.ind
#check Quotient.inductionOn
#check Quotient.lift
#check Quot.rec
#check Quotient.rec

example : False := by
  let r : Bool → Bool → Prop := fun _ _ => True
  let qf : Quot r := Quot.mk r false
  let qt : Quot r := Quot.mk r true
  have hqt : qf = qt := Quot.sound trivial
  -- Try non-well-defined motive by induction: cannot define by quotient cases.
  exact?
