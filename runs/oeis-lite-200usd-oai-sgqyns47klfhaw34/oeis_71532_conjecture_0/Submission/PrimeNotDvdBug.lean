import FormalConjectures.Util.ProblemImports
#check Nat.exists_prime_not_dvd
#print axioms Nat.exists_prime_not_dvd
example : False := by
  obtain ⟨p, hp, hnp⟩ := Nat.exists_prime_not_dvd 1 (by norm_num)
  exact hnp (by simp)
