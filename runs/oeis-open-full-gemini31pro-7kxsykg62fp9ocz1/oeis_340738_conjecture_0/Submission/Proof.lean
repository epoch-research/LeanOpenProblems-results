import Mathlib
import Submission.Spec
import Submission.Helper_mono
import Submission.Helper14

open Nat Real Filter Topology Set Metric

lemma a_pos (n : ℕ) (hn : 1 ≤ n) : (1 : ℝ) ≤ (A340738 n : ℝ) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk2 : n = 2 * k := by omega
    have hk_pos : 1 ≤ k := by omega
    have h_mono := a_mono_pair k hk_pos
    have h1 : 1 ≤ A340738 (2 * k - 1) := h_mono.1
    have h3 : 1 ≤ A340738 (2 * k) := by omega
    rw [hk2]
    exact_mod_cast h3
  · have hk2 : n = 2 * k + 1 := by omega
    obtain rfl | hk_pos2 := Nat.eq_zero_or_pos k
    · have eq1 : n = 1 := by omega
      rw [eq1]
      have : A340738 1 = 1 := rfl
      rw [this]
      norm_num
    · have h_mono := a_mono_pair (k + 1) (by omega)
      have h1 : 1 ≤ A340738 (2 * (k + 1) - 1) := h_mono.1
      have eq2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [eq2] at h1
      rw [hk2]
      exact_mod_cast h1

lemma sequence_of_fractions_converges :
  Tendsto sequence_of_fractions atTop (nhds (Real.exp 1)) := by
  have H_eq : (fun n : ℕ => sequence_of_fractions n - exp 1) =ᶠ[atTop] (fun n : ℕ => J n * ((A340738 n : ℝ)⁻¹)) := by
    apply eventually_atTop.mpr
    use 1
    intro n hn
    dsimp [sequence_of_fractions, J]
    have ha := a_pos n hn
    have ha_ne : (A340738 n : ℝ) ≠ 0 := by linarith
    calc
      (A340737 n : ℝ) / (A340738 n : ℝ) - exp 1
        = (A340737 n : ℝ) * (A340738 n : ℝ)⁻¹ - exp 1 * (A340738 n : ℝ) * (A340738 n : ℝ)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ ha_ne, mul_one]
          ring
      _ = ((A340737 n : ℝ) - (A340738 n : ℝ) * exp 1) * (A340738 n : ℝ)⁻¹ := by ring
  have H_zero : Tendsto (fun n : ℕ => J n * ((A340738 n : ℝ)⁻¹)) atTop (nhds 0) := by
    have h_j := J_tendsto_zero
    apply squeeze_zero_norm (a := fun n => ‖J n‖)
    · intro n
      have h_norm_inv : ‖((A340738 n : ℝ)⁻¹)‖ ≤ 1 := by
        by_cases hn : 1 ≤ n
        · have ha := a_pos n hn
          have ha_pos : 0 < (A340738 n : ℝ) := by linarith
          have H_inv : ((A340738 n : ℝ)⁻¹) ≤ 1 := (inv_le_one₀ ha_pos).mpr ha
          have H_pos : 0 ≤ ((A340738 n : ℝ)⁻¹) := inv_nonneg.mpr (by linarith)
          rw [norm_of_nonneg H_pos]
          exact H_inv
        · have h0 : n = 0 := by omega
          rw [h0]
          have : A340738 0 = 0 := rfl
          rw [this]
          norm_num
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) h_norm_inv
    · exact tendsto_zero_iff_norm_tendsto_zero.mp h_j
  have H_final : Tendsto (fun n : ℕ => sequence_of_fractions n - exp 1) atTop (nhds 0) := Tendsto.congr' H_eq.symm H_zero
  have H_add := Tendsto.add_const (exp 1) H_final
  simp at H_add
  exact H_add
