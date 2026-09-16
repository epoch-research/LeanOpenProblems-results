import Mathlib
import Submission.Spec
import Submission.Helper2

open Nat Real intervalIntegral Polynomial Filter Topology Set

lemma I_k_nonneg (k : ℕ) : 0 ≤ I_k k := by
  dsimp [I_k]
  apply intervalIntegral.integral_nonneg
  · norm_num
  · intro x hx
    dsimp [P_poly]
    simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]
    have h1 : 0 ≤ x := hx.1
    have h2 : x ≤ 1 := hx.2
    have h3 : 0 ≤ 1 - x := by linarith
    have hp1 : 0 ≤ x * (1 - x) := by positivity
    have hp2 : 0 ≤ (x * (1 - x)) ^ k := pow_nonneg hp1 k
    have h_exp : 0 ≤ exp (1 - x) := exp_pos (1 - x) |>.le
    have h_fact : 0 ≤ ((k.factorial : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg k.factorial)
    positivity

lemma I_k_le (k : ℕ) : I_k k ≤ exp 1 * ((k.factorial : ℝ)⁻¹) := by
  have H : I_k k ≤ ∫ x in (0:ℝ)..1, exp 1 * ((k.factorial : ℝ)⁻¹) := by
    dsimp [I_k]
    apply intervalIntegral.integral_mono_on
    · norm_num
    · exact (P_poly_cont k).intervalIntegrable 0 1
    · exact continuous_const.intervalIntegrable 0 1
    · intro x hx
      dsimp [P_poly]
      simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]
      have h1 : 0 ≤ x := hx.1
      have h2 : x ≤ 1 := hx.2
      have h3 : 0 ≤ 1 - x := by linarith
      have hp1 : 0 ≤ x * (1 - x) := by positivity
      have hp2 : x * (1 - x) ≤ 1 := by
        calc
          x * (1 - x) = x - x^2 := by ring
          _ ≤ x := by
            have : 0 ≤ x^2 := by positivity
            linarith
          _ ≤ 1 := h2
      have hp3 : (x * (1 - x)) ^ k ≤ 1 ^ k := by
        gcongr
      simp at hp3
      have h_exp : exp (1 - x) ≤ exp 1 := by
        apply exp_le_exp.mpr
        linarith
      have h_fact : 0 ≤ ((k.factorial : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg k.factorial)
      have : ((x * (1 - x)) ^ k * (k.factorial : ℝ)⁻¹) * exp (1 - x) ≤ (1 * (k.factorial : ℝ)⁻¹) * exp 1 := by
        gcongr
      calc
        ((x * (1 - x)) ^ k * (k.factorial : ℝ)⁻¹) * exp (1 - x)
          ≤ (1 * (k.factorial : ℝ)⁻¹) * exp 1 := this
        _ = exp 1 * (k.factorial : ℝ)⁻¹ := by ring
  have h_int : ∫ x in (0:ℝ)..1, exp 1 * ((k.factorial : ℝ)⁻¹) = exp 1 * ((k.factorial : ℝ)⁻¹) := by
    simp
  rw [h_int] at H
  exact H
