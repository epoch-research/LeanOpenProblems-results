import FormalConjectures.Util.ProblemImports
import Submission.Spec

opaque A273110_conjecture_opaque (n : ℕ) :
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m)

#print axioms A273110_conjecture_opaque
