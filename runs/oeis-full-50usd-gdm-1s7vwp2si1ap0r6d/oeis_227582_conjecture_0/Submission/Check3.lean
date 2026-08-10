import FormalConjectures.Util.ProblemImports

open BigOperators Real Filter Topology

lemma h_ineq_fun : (fun n : ℕ ↦ (n : ℝ)) ≤ (fun n : ℕ ↦ (n : ℝ) * (n : ℝ)) := by
  intro n
  rcases n with _ | n
  · simp
  · push_cast
    nlinarith

lemma h_index_fun : Tendsto (fun n : ℕ ↦ (n : ℝ) * (n : ℝ)) atTop atTop :=
  tendsto_atTop_mono h_ineq_fun tendsto_natCast_atTop_atTop

lemma tendsto_LB_limit_eq : (fun n : ℕ ↦ 2 * log n - log (n * n + n - 1 : ℝ)) =ᶠ[atTop]
              (fun n : ℕ ↦ - log ( (n * n + n - 1 : ℝ) / ((n : ℝ) * (n : ℝ)) )) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_real : (n : ℝ) ≥ 1 := by exact_mod_cast hn
  have hn_pos : (n : ℝ) > 0 := by linarith
  have hnn : (n : ℝ) * (n : ℝ) > 0 := by nlinarith
  have h_idx : (n * n + n - 1 : ℝ) > 0 := by
    push_cast
    nlinarith
  have h_div : log (((n * n + n - 1 : ℝ)) / ((n : ℝ) * (n : ℝ))) =
               log (n * n + n - 1 : ℝ) - log ((n : ℝ) * (n : ℝ)) := by
    exact log_div (by linarith) (by linarith)
  have h_mul : log ((n : ℝ) * (n : ℝ)) = 2 * log n := by
    rw [log_mul (by linarith) (by linarith)]
    ring
  rw [h_div, h_mul]
  ring

lemma tendsto_LB_limit_div_eq : (fun n : ℕ ↦ ((n * n + n - 1 : ℝ) / ((n : ℝ) * (n : ℝ)))) =ᶠ[atTop]
                (fun n : ℕ ↦ 1 + 1 / (n : ℝ) - 1 / ((n : ℝ) * (n : ℝ))) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_real : (n : ℝ) ≥ 1 := by exact_mod_cast hn
  have : (n : ℝ) ≠ 0 := by linarith
  field_simp

lemma tendsto_LB_limit_lim : Tendsto (fun n : ℕ ↦ ( (n * n + n - 1 : ℝ) / ((n : ℝ) * (n : ℝ)) )) atTop (nhds 1) := by
  have h1 : Tendsto (fun n : ℕ ↦ (1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have h2 : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h3 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) * (n : ℝ))) atTop (nhds 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp h_index_fun
  have h_sum := Tendsto.add h1 h2
  have h_sub := Tendsto.sub h_sum h3
  rw [add_zero, sub_zero] at h_sub
  rw [tendsto_congr' tendsto_LB_limit_div_eq]
  simp only [one_div] at h_sub ⊢
  exact h_sub

lemma tendsto_LB_limit : Tendsto (fun n : ℕ ↦ 2 * log n - log (n * n + n - 1 : ℝ)) atTop (nhds 0) := by
  rw [tendsto_congr' tendsto_LB_limit_eq]
  have h_log : ContinuousAt log 1 := continuousAt_log (by norm_num)
  have h_comp := h_log.tendsto.comp tendsto_LB_limit_lim
  rw [Real.log_one] at h_comp
  have h_neg := h_comp.neg
  rwa [neg_zero] at h_neg

lemma tendsto_UB_limit : Tendsto (fun n : ℕ ↦ 2 * log (n + 1 : ℝ) - log (n * n + n : ℝ)) atTop (nhds 0) := by
  have h_eq : (fun n : ℕ ↦ 2 * log (n + 1 : ℝ) - log (n * n + n : ℝ)) =ᶠ[atTop]
              (fun n : ℕ ↦ log (1 + 1 / (n : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_real : (n : ℝ) ≥ 1 := by exact_mod_cast hn
    have hn_pos : (n : ℝ) > 0 := by linarith
    have hn1 : (n + 1 : ℝ) > 0 := by linarith
    have h_factor : (n : ℝ) * n + n = (n : ℝ) * (n + 1) := by ring
    have h_div : 1 + 1 / (n : ℝ) = (n + 1 : ℝ) / (n : ℝ) := by
      have : (n : ℝ) ≠ 0 := by linarith
      field_simp
    have h_log_div : log (1 + 1 / (n : ℝ)) = log (n + 1 : ℝ) - log n := by
      rw [h_div]
      exact log_div (by linarith) (by linarith)
    push_cast
    rw [h_factor]
    rw [log_mul (by linarith) (by linarith)]
    rw [h_log_div]
    ring
  rw [tendsto_congr' h_eq]
  have h_add : Tendsto (fun n : ℕ ↦ 1 + 1 / (n : ℝ)) atTop (nhds 1) := by
    have h1 : Tendsto (fun n : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have h2 : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
    have h_sum := Tendsto.add h1 h2
    rw [add_zero] at h_sum
    exact h_sum
  have h_log : ContinuousAt log 1 := continuousAt_log (by norm_num)
  have h_comp := h_log.tendsto.comp h_add
  rw [Real.log_one] at h_comp
  exact h_comp
