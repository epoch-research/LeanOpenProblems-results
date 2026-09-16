import Submission.Spec

set_option maxRecDepth 200000

theorem disproof_check : ¬ (∀ n, (n > 1 → a n > 0) ∧ (n > 1 ∧ n ≠ 8 → ∃ k : ℕ, 0 < k ∧ k < n ∧ Nat.Prime (2 * k + 1) ∧
  Nat.primeCounting (k * n) - Nat.primeCounting ((k - 1) * n) =
  Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n))) := by
  intro h
  have h14 := h 14
  rcases h14 with ⟨_, h14b⟩
  have h1 : 14 > 1 ∧ 14 ≠ 8 := by decide
  have h2 := h14b h1
  rcases h2 with ⟨k, hk1, hk2, hk3, hk4⟩
  interval_cases k
  all_goals { revert hk4 hk3; decide }
