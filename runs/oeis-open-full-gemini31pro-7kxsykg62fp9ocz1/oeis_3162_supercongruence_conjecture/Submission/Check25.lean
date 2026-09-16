import Submission.Spec
open Nat

theorem test : ∀ (n k p : ℕ),
      n > 0 → k > 0 → Nat.Prime p → p ≥ 5
      → (A003162.b (n * p ^ k) : ℤ) ≡ (A003162.b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)] := by
  exact fun n k p a a_1 a_2 a_3 => Int.ModEq.trans rfl rfl
