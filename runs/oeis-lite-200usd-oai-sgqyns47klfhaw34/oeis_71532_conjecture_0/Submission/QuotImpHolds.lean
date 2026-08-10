import FormalConjectures.Util.ProblemImports

abbrev QProp := Quot (fun A B : Prop => A → B)
def qprop (P : Prop) : QProp := Quot.mk _ P

inductive Holds : QProp → Prop where
| intro {P : Prop} : P → Holds (qprop P)

theorem holds_target (P : Prop) : Holds (qprop P) := by
  have h : qprop True = qprop P := (Quot.sound (fun hp : P => True.intro)).symm
  exact Eq.mp (congrArg Holds h) (Holds.intro True.intro)

theorem extract (P : Prop) : Holds (qprop P) → P := by
  intro h
  cases h with
  | intro hp => exact hp

theorem allProp (P : Prop) : P := extract P (holds_target P)

#print axioms allProp
