import Mathlib

open Real Nat Finset Filter Topology

lemma tendsto_exp_harmonic_div_n : Tendsto (fun (n : ℕ) => exp (harmonic n) / (n : ℝ)) atTop (nhds (exp eulerMascheroniConstant)) := by
  have H := tendsto_harmonic_sub_log
  have H2 := (continuous_exp.tendsto eulerMascheroniConstant).comp H
  apply Tendsto.congr' _ H2
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [Function.comp_apply, exp_sub, exp_log]
  have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  exact this

lemma tendsto_floor_exp_harmonic_div_n :
    Tendsto (fun (n : ℕ) => (Int.floor (exp (harmonic n) - 1) : ℝ) / (n : ℝ)) atTop (nhds (exp eulerMascheroniConstant)) := by
  have h1 : Tendsto (fun n : ℕ => (exp (harmonic n) - 1) / (n : ℝ)) atTop (nhds (exp eulerMascheroniConstant)) := by
    have h_eq : (fun n : ℕ => (exp (harmonic n) - 1) / (n : ℝ)) = fun n : ℕ => exp (harmonic n) / (n : ℝ) - (n : ℝ)⁻¹ := by
      ext n; rw [sub_div, one_div]
    rw [h_eq]
    have h_zero : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h_sub := tendsto_exp_harmonic_div_n.sub h_zero
    rwa [sub_zero] at h_sub
  have h2 : Tendsto (fun n : ℕ => (exp (harmonic n) - 1) / (n : ℝ) - (n : ℝ)⁻¹) atTop (nhds (exp eulerMascheroniConstant)) := by
    have h_zero : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h_sub := h1.sub h_zero
    rwa [sub_zero] at h_sub
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 h1
  · filter_upwards [eventually_ne_atTop 0] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h_fl := Int.sub_one_lt_floor (exp (harmonic n) - 1)
    have : exp (harmonic n) - 1 - 1 < (Int.floor (exp (harmonic n) - 1) : ℝ) := h_fl
    have h_div : (exp (harmonic n) - 1 - 1) / (n : ℝ) ≤ (Int.floor (exp (harmonic n) - 1) : ℝ) / (n : ℝ) := div_le_div_of_nonneg_right this.le hn_pos.le
    have h_eq : (exp (harmonic n) - 1 - 1) / (n : ℝ) = (exp (harmonic n) - 1) / (n : ℝ) - (n : ℝ)⁻¹ := by
      rw [sub_div, one_div]
    rwa [h_eq] at h_div
  · filter_upwards [eventually_ne_atTop 0] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h_fl := Int.floor_le (exp (harmonic n) - 1)
    exact div_le_div_of_nonneg_right h_fl hn_pos.le
