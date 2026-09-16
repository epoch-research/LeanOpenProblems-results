import Submission.Spec
open Nat

theorem a_test : ∀ (p : ℕ), Nat.Prime p → 5 ≤ p → (a p) ≡ (a 1) [MOD p^5] := by
  sorry
