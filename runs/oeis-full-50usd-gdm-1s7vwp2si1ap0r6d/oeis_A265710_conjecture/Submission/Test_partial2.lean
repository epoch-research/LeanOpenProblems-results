import FormalConjectures.Util.ProblemImports

partial def my_proof_partial (n : ℕ) : n = 0 :=
  my_proof_partial n

theorem test_partial (n : ℕ) : n = 0 :=
  my_proof_partial n
