import FormalConjectures.Util.ProblemImports

#check Finset.Coprime_pair_iff
#check Finset.Coprime

example : False := by
  have hiff := Finset.Coprime_pair_iff ({2} : Finset ℕ) 2 2 (by ext x; simp)
  have hcS : ({2} : Finset ℕ).Coprime := by
    simp [Finset.Coprime]
  have hc : Nat.Coprime 2 2 := hiff.mp hcS
  norm_num [Nat.Coprime] at hc

#print axioms Finset.Coprime_pair_iff
