import FormalConjectures.Util.ProblemImports
import Submission.Spec

mutual
  partial def impl_standard (n : ℕ) : (0 < n → 0 < A273110 n) ∧ (A273110 n = 1 ↔ ∃ k m, m ∈ A273110_set_M ∧ n = 4 ^ k * m) :=
    helper_standard n

  partial def helper_standard (n : ℕ) : (0 < n → 0 < A273110 n) ∧ (A273110 n = 1 ↔ ∃ k m, m ∈ A273110_set_M ∧ n = 4 ^ k * m) :=
    impl_standard n
end
