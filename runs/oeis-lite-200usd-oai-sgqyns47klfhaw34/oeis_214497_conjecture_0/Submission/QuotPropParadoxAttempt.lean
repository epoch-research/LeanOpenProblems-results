import FormalConjectures.Util.ProblemImports

#check Quot.rec
#check Quot.ind
#check Quot.sound
#check Quot.lift
#check Quotient.rec
#check Quotient.ind

universe u

def QP (P : Prop) := Quot (fun _ _ : Bool => True)

-- Try to define a Prop-valued function distinguishing representatives.
def mot (P : Prop) (q : QP P) : Prop := by
  -- exact Quot.rec (motive?)
  exact True

example (P : Prop) : P := by
  let q0 : QP P := Quot.mk _ false
  let q1 : QP P := Quot.mk _ true
  have hq : q0 = q1 := Quot.sound trivial
  -- If we could make a motive with motive q0=True, motive q1=P, transport True.
  fail_if_success
    exact Eq.mp (congrArg (fun q => q = q) hq) rfl
  guard_target = P
  sorry
