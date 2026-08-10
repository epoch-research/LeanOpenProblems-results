import FormalConjectures.Util.ProblemImports

#check Trunc
#check Trunc.mk
#check Trunc.rec

partial def truncP (P : Prop) : Trunc P := truncP P

theorem arbitrary (P : Prop) : P := by
  exact Trunc.rec (motive := fun _ => P) (fun hp => hp) (truncP P)

#print axioms arbitrary
