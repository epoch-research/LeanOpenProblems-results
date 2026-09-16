import Mathlib
import Submission.Spec
open Nat Finset Set

lemma nth_zero_prime : Nat.nth Nat.Prime 0 = 2 := by
  exact rfl

lemma a1 : A232616 1 = 1 := by
  sorry

theorem disproof_impossible :
  (¬ (∀ (n : ℕ) (hn : 0 < n), A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1))) → False := by
  sorry
