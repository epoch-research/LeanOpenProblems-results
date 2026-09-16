import Submission.Spec
import Aesop

theorem oeis_306477_conjecture_1_proof : ∀ n : ℕ, 0 < n → 0 < A306477 n := by
  aesop
