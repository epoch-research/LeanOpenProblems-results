import FormalConjectures.Util.ProblemImports

partial def loopNat (n : Nat) : Nat := loopNat (n+1)
#print axioms loopNat
#check loopNat.eq_def
example : loopNat 0 = loopNat 1 := by rw [loopNat]
#print axioms loopNat.eq_def
