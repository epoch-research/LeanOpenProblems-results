import Mathlib
import Submission.TestExpBound2

open Real Finset

lemma c_mono (n : ℕ) (hn : 1 ≤ n) : exp (harmonic n) * (exp (1 / (n + 1 : ℝ)) - 1) < exp (harmonic (n + 1)) * (exp (1 / (n + 2 : ℝ)) - 1) := by
  have H := c_ratio (1 / (n + 1 : ℝ)) (by positivity) (bound_add (1 / (n + 1 : ℝ)) (by positivity) (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (2 : ℝ) ≤ n + 1 := by linarith
    exact one_div_le_one_div_of_le (by norm_num) this
  ))
  have h_eq : (1 / (n + 1 : ℝ)) / (1 + 1 / (n + 1 : ℝ)) = 1 / (n + 2 : ℝ) := by
    have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
    have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
    rw [div_add_one_eq_mul_div hn1, div_div_div_cancel_right₀ _ hn1]
    ring
  rw [h_eq] at H
  have h_harm : harmonic (n + 1) = harmonic n + 1 / (n + 1 : ℝ) := by
    rw [harmonic_succ]; push_cast; rfl
  rw [h_harm, exp_add]
  calc
    exp (harmonic n) * (exp (1 / (n + 1 : ℝ)) - 1) < exp (harmonic n) * (exp (1 / (n + 1 : ℝ)) * (exp (1 / (n + 2 : ℝ)) - 1)) := by
      apply mul_lt_mul_of_pos_left H (exp_pos _)
    _ = exp (harmonic n) * exp (1 / (n + 1 : ℝ)) * (exp (1 / (n + 2 : ℝ)) - 1) := by ring

