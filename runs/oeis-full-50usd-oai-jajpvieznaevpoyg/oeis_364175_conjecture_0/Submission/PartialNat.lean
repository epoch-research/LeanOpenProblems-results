import FormalConjectures.Util.ProblemImports
partial def badNat : Nat := badNat + 1
#check badNat
#check badNat.eq_def
example : badNat = badNat + 1 := by
  rw [badNat]

theorem false_of_bad : False := by
  have h : badNat = badNat + 1 := by rw [badNat]
  omega
#print axioms false_of_bad
