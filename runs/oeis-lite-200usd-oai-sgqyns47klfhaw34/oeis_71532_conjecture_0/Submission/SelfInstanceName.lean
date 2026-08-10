import FormalConjectures.Util.ProblemImports

partial def fakeSub (s : Subsingleton Nat) : Subsingleton Nat := s
instance instFakeSub : Subsingleton Nat := fakeSub instFakeSub

theorem badFalse : False := by
  have h : (0:Nat) = 1 := Subsingleton.elim 0 1
  exact Nat.zero_ne_one h
#print axioms badFalse
