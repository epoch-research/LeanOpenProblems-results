import FormalConjectures.Util.ProblemImports

#check int_eq_nat
#check extracted_1
example : False := by
  obtain ⟨n, hn⟩ := int_eq_nat (z := -1)
  omega
#print axioms int_eq_nat
#print axioms extracted_1
