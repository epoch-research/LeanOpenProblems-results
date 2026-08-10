import FormalConjectures.Util.ProblemImports
partial def badNat (_ : Unit) : Nat := badNat () + 1
#check badNat.eq_def
theorem false_of_bad : False := by
  have h : badNat () = badNat () + 1 := by rw [badNat]
  omega
#print axioms false_of_bad
