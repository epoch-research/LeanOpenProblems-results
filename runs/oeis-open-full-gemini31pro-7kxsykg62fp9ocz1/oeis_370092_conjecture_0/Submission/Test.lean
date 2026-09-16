import Submission.Spec
import Mathlib

theorem test (k : ℕ) (hk : 2 < k) :
    ∃ P : ℕ, P ∣ Nat.totient k ∧ eventually_periodic (a_mod_k k) P := by
  sorry
