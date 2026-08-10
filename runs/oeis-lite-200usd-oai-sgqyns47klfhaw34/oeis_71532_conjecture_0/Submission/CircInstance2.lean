import FormalConjectures.Util.ProblemImports

partial def fakeSub [Subsingleton Nat] : Subsingleton Nat := inferInstance
instance instFakeSub : Subsingleton Nat := fakeSub

theorem badFalse : False := by
  have h : (0:Nat) = 1 := Subsingleton.elim 0 1
  exact Nat.zero_ne_one h
#print axioms badFalse
