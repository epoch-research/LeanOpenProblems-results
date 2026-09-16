import Submission.Spec
open Nat

theorem oeis_3162_supercongruence_conjecture_proof :
    ∀ (n k p : ℕ),
      n > 0 → k > 0 → Nat.Prime p → p ≥ 5
      → (A003162.b (n * p ^ k) : ℤ) ≡ (A003162.b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)] := by
  intros n k p hn hk hp hp5
  unfold A003162.b A003162
  exact?
