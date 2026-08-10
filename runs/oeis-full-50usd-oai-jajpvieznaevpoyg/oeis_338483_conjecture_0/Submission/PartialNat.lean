import FormalConjectures.Util.ProblemImports

partial def loopNat (_ : Unit) : Nat := loopNat () + 1

#check loopNat
#check loopNat.eq_def
example : loopNat () = loopNat () + 1 := by rfl

theorem false_of_loop : False := by
  have h : loopNat () = loopNat () + 1 := by rfl
  omega
#print axioms false_of_loop
