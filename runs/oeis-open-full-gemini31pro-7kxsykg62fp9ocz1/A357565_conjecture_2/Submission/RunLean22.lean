import Submission.Spec
open Finset Nat

theorem disproof_test : ¬ ∀ (p r : ℕ), Nat.Prime p → p ≥ 3 → r ≥ 2 →
    (A357565 (p ^ r)) ≡ (A357565 (p ^ (r - 1))) [MOD (p ^ (3 * r + 3))] := by
  sorry
