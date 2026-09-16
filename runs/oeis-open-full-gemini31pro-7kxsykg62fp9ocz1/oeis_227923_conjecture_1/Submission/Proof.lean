import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat Finset

lemma factorial_gt_two_mul {N : ℕ} (h : 7 ≤ N) : (N + 1)! > 2 * N := by
  induction' h with k hk ih
  · exact by decide
  · have h1 : (k + 1 + 1)! = (k + 2) * (k + 1)! := rfl
    rw [h1]
    have h2 : 2 * (k + 1)! ≤ (k + 2) * (k + 1)! := Nat.mul_le_mul_right _ (by omega)
    have h3 : 2 * (2 * k) < 2 * (k + 1)! := Nat.mul_lt_mul_of_pos_left ih (by decide)
    have h_hk : 7 ≤ k := hk
    have h4 : 2 * (k + 1) < 2 * (2 * k) := by omega
    exact lt_of_lt_of_le (lt_trans h4 h3) h2

theorem oeis_227923_conjecture_1_proof :
  (∀ (n : ℕ), 1 < n → A227923 n > 0) →
  (Set.Infinite SophieGermainPrimes ∧ Set.Infinite TwinPrimes) := by
  sorry
