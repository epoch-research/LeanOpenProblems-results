import Submission.Spec
open Nat

theorem oeis_357958_conjecture_01_false :
  ¬ (∀ (p : ℕ), Nat.Prime p → 5 ≤ p → (a p) ≡ (a 1) [MOD p^5]) := by
  sorry
