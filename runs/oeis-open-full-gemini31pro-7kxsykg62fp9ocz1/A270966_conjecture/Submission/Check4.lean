import Submission.Spec
import Mathlib.Tactic.Aesop

theorem try_proof : (∀ n : ℕ, n > 0 → A270966 n > 0) ∧ (∀ n : ℕ, A270966 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) := by
  aesop
