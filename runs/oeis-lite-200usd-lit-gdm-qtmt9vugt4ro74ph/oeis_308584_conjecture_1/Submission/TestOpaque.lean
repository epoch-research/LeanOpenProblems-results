import FormalConjectures.Util.ProblemImports

opaque my_conjecture_proof (n : ℕ) : n > 0

theorem test_opaque (n : ℕ) : n > 0 :=
  my_conjecture_proof n

#print axioms test_opaque
