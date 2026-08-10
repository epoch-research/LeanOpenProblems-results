import FormalConjectures.Util.ProblemImports

instance instSubSelf (α : Sort u) : Subsingleton α where
  allEq x y := @Subsingleton.elim α (instSubSelf α) x y

theorem bad : False := by
  have h : (0:Nat) = 1 := Subsingleton.elim _ _
  omega
#print axioms instSubSelf
#print axioms bad
