import Submission.Spec
import Mathlib

open Real Finset Filter Topology Nat

lemma harm_nonneg (n : ℕ) : (0 : ℝ) ≤ harmonic n := by
  induction' n with n ih
  · simp
  · rw [harmonic_succ]
    push_cast
    positivity

lemma a206911_S_n_eq_harmonic (n : ℕ) : (range n).sum (fun k => 1 / ((k : ℝ) + 1)) = harmonic n := by
  induction' n with n ih
  · simp
  · rw [sum_range_succ, ih, harmonic_succ]
    push_cast
    rw [one_div]

lemma A206911_eq (n : ℕ) : A206911 n = n + ⌊exp (harmonic n) - 1⌋₊ := by
  change n + ⌊rexp _ - 1⌋₊ = _
  rw [a206911_S_n_eq_harmonic]

lemma A206911_diff_eq (n : ℕ) : A206911_diff n = 1 + ⌊exp (harmonic (n + 1)) - 1⌋₊ - ⌊exp (harmonic n) - 1⌋₊ := by
  dsimp [A206911_diff]
  rw [A206911_eq, A206911_eq]
  omega

