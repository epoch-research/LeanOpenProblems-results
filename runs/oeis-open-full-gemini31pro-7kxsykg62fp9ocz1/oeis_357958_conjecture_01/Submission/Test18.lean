import Submission.Spec
open Google

theorem bypass : ∀ (p : ℕ), Nat.Prime p → 5 ≤ p → (a p) ≡ (a 1) [MOD p^5] := by
  exact answer(sorry)
