import FormalConjectures.Util.ProblemImports

#check Quot.out
#check Quot.out_eq
#check Quot.out_eq'

example : False := by
  let r : Bool → Bool → Prop := fun _ _ => True
  have hq : Quot.mk r true = Quot.mk r false := Quot.sound True.intro
  have hout := congrArg (@Quot.out Bool r) hq
  -- see whether this reduces to true = false
  change true = false at hout
  cases hout

#print axioms _example
