import Submission.Spec
open Nat Set

theorem try_disproof : ¬ (
  (∀ n : ℕ, 0 < n →
    ({ m : ℕ | 0 < m ∧ (m + n) ∣ (Nat.nth Nat.Prime (m - 1) + Nat.nth Nat.Prime (n - 1)) }).Nonempty)
  ∧
  (∀ n : ℕ, 2 < n → a n < n * (n - 1))
) := by
  intro h
  have h1 := h.1
  have h2 := h.2
  -- let's evaluate for n = 3
  sorry
