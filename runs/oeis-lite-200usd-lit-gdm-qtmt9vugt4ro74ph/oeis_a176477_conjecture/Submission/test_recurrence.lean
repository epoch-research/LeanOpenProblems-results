import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat

lemma a_Q_recurrence (k : ℕ) :
  a_Q (k + 2) * (2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3 = 32 * ((k + 2 : ℕ) : ℚ) ^ 3 * a_Q (k + 1) + (21 * ((k + 2 : ℕ) : ℚ) ^ 3 + 22 * ((k + 2 : ℕ) : ℚ) ^ 2 + 8 * ((k + 2 : ℕ) : ℚ) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) ^ 4 := by
  have h_sub : k + 2 - 1 = k + 1 := by omega
  generalize h_prev : a_Q (k + 1) = prev
  -- now unfold only the LHS
  unfold a_Q
  dsimp only
  rw [h_sub, h_prev]
  have h_den_ne : (2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3 ≠ 0 := by
    have : (2 * ((k + 2 : ℕ) : ℚ) + 1) > 0 := by positivity
    positivity
  rw [div_mul_cancel₀ _ h_den_ne]
