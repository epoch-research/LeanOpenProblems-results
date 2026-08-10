import FormalConjectures.Util.ProblemImports

def r (P Q : Prop) := P → Q

theorem exactImp {P Q : Prop} (h : Quot.mk r P = Quot.mk r Q) : P → Q := by
  cases h
  intro hp
  exact hp

theorem arbitrary (P : Prop) : P := by
  have hq : Quot.mk r True = Quot.mk r P := Eq.symm (Quot.sound (show P → True from fun _ => trivial))
  exact exactImp hq trivial

#print axioms exactImp
#print axioms arbitrary
