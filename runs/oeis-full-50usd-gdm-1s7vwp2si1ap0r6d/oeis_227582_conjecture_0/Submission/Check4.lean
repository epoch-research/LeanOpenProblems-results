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
  rw [h_div, h_mul]

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

noncomputable def D_seq (n : ℕ) : ℝ :=
  2 * (harmonic n : ℝ) - (harmonic (n * n + n - 1) : ℝ) - eulerMascheroniConstant

lemma harmonic_diff_eq_sum (a : ℕ) (k : ℕ) :
    (harmonic (a + k) : ℝ) - (harmonic a : ℝ) = ∑ i ∈ Finset.range k, (1 / (a + 1 + i : ℝ)) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    rw [Nat.add_succ, harmonic_succ]
    push_cast
    rw [inv_eq_one_div]
    rw [h_denom]
    linarith

lemma sum_inv_gt_log_sub (n : ℕ) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (1 / (n + 1 + i : ℝ))) > log (n + k + 2) - log (n + 1) := by
  induction k with
  | zero =>
    have h_sum : (∑ i ∈ Finset.range (0 + 1), (1 / (n + 1 + i : ℝ))) = 1 / (n + 1 : ℝ) := by
      simp
    rw [h_sum]
    push_cast
    rw [h_rhs]
    have h1 : 0 < 1 + 1 / (n + 1 : ℝ) := by positivity
    have h2 : 1 + 1 / (n + 1 : ℝ) ≠ 1 := by
      intro h
      have h_ne : 1 / (n + 1 : ℝ) ≠ 0 := by positivity
      have : 1 / (n + 1 : ℝ) = 0 := by linarith
      exact h_ne this
    have h3 := Real.log_lt_sub_one_of_pos h1 h2
    rw [h4] at h3
    have h_div : 1 + 1 / (n + 1 : ℝ) = (n + 2) / (n + 1) := by
      have : (n + 1 : ℝ) ≠ 0 := by positivity
    rw [h_div] at h3
    rw [log_div] at h3
    · linarith
    · positivity
    · positivity
  | succ k ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have h_log : log (1 + 1 / (n + k + 2 : ℝ)) < 1 / (n + k + 2 : ℝ) := by
      have h1 : 0 < 1 + 1 / (n + k + 2 : ℝ) := by positivity
      have h2 : 1 + 1 / (n + k + 2 : ℝ) ≠ 1 := by
        intro h
        have h_ne : 1 / (n + k + 2 : ℝ) ≠ 0 := by positivity
        have : 1 / (n + k + 2 : ℝ) = 0 := by linarith
        exact h_ne this
      have h3 := Real.log_lt_sub_one_of_pos h1 h2
      rwa [h4] at h3
    have h_log_rw : log (1 + 1 / (n + k + 2 : ℝ)) = log (n + k + 3) - log (n + k + 2) := by
      have h_div : 1 + 1 / (n + k + 2 : ℝ) = (n + k + 3) / (n + k + 2) := by
        have : (n + k + 2 : ℝ) ≠ 0 := by positivity
      rw [h_div]
      rw [log_div]
      · positivity
      · positivity
    rw [h_log_rw] at h_log
    have ih' := ih
    push_cast at ih'
    rw [h_eq, h_goal_rhs]
    linarith

lemma sum_inv_lt_log_sub (n : ℕ) (hn : 0 < n) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (1 / (n + 1 + i : ℝ))) < log (n + k + 1) - log n := by
  induction k with
  | zero =>
    have h_sum : (∑ i ∈ Finset.range (0 + 1), (1 / (n + 1 + i : ℝ))) = 1 / (n + 1 : ℝ) := by
      simp
    rw [h_sum]
    push_cast
    rw [h_rhs]
    have h1 : 0 < 1 - 1 / (n + 1 : ℝ) := by
      have : (n : ℝ) > 0 := by positivity
      have : (n + 1 : ℝ) > 0 := by positivity
      have : 1 / (n + 1 : ℝ) < 1 := by
        rw [one_div_lt]
        · linarith
        · positivity
        · linarith
      linarith
    have h2 : 1 - 1 / (n + 1 : ℝ) ≠ 1 := by
      intro h
      have h_ne : 1 / (n + 1 : ℝ) ≠ 0 := by positivity
      have : 1 / (n + 1 : ℝ) = 0 := by linarith
      exact h_ne this
    have h3 := Real.log_lt_sub_one_of_pos h1 h2
    rw [h4] at h3
    have h_div : 1 - 1 / (n + 1 : ℝ) = n / (n + 1) := by
      have : (n + 1 : ℝ) ≠ 0 := by positivity
    rw [h_div] at h3
    rw [log_div] at h3
    · linarith
    · positivity
    · positivity
  | succ k ih =>
    rw [Finset.sum_range_succ]
    generalize hS : (∑ i ∈ Finset.range (k + 1), (1 / (n + 1 + i : ℝ))) = S at ih ⊢
    push_cast
    have h_log : log (1 - 1 / (n + k + 2 : ℝ)) < -(1 / (n + k + 2 : ℝ)) := by
      have h1 : 0 < 1 - 1 / (n + k + 2 : ℝ) := by
        have : (n + k + 1 : ℝ) > 0 := by positivity
        have : (n + k + 2 : ℝ) > 0 := by positivity
        have : 1 / (n + k + 2 : ℝ) < 1 := by
          rw [one_div_lt]
          · linarith
          · positivity
          · linarith
        linarith
      have h2 : 1 - 1 / (n + k + 2 : ℝ) ≠ 1 := by
        intro h
        have h_ne : 1 / (n + k + 2 : ℝ) ≠ 0 := by positivity
        have : 1 / (n + k + 2 : ℝ) = 0 := by linarith
        exact h_ne this
      have h3 := Real.log_lt_sub_one_of_pos h1 h2
      rwa [h4] at h3
    have h_log_rw : log (1 - 1 / (n + k + 2 : ℝ)) = log (n + k + 1) - log (n + k + 2) := by
      have h_div : 1 - 1 / (n + k + 2 : ℝ) = (n + k + 1) / (n + k + 2) := by
        have : (n + k + 2 : ℝ) ≠ 0 := by positivity
      rw [h_div]
      rw [log_div]
      · positivity
      · positivity
    rw [h_log_rw] at h_log
    have ih' := ih
    push_cast at ih'
    rw [h_eq, h_goal_rhs]
    linarith

lemma h_LB (n : ℕ) (hn : 2 ≤ n) : 2 * log n - log (n * n + n - 1 : ℝ) < D_seq n := by
  unfold D_seq
  have h_gamma := eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have h_seq' : eulerMascheroniSeq' n = (harmonic n : ℝ) - log n := by
    unfold eulerMascheroniSeq'
    have : n ≠ 0 := by omega
    simp [this]
  rw [h_seq'] at h_gamma
  have h_sum_diff := harmonic_diff_eq_sum n (n * n + n - 1 - n)
  have h_le : n ≤ n * n + n - 1 := by
    rcases n with _ | n
    · contradiction
    · have h_eq : (n + 1) * (n + 1) + (n + 1) - 1 = (n + 1) * (n + 1) + n := rfl
      rw [h_eq]
      have h1 : n + 1 ≤ (n + 1) * (n + 1) := (n + 1).le_mul_self
      omega
  have h_sub_eq : n + (n * n + n - 1 - n) = n * n + n - 1 := Nat.add_sub_cancel' h_le
  rw [h_sub_eq] at h_sum_diff
  have h_range_eq : (n * n + n - 1 - n) = (n * n - 1) := by
    have h_n2 : n * n ≥ 4 := by nlinarith
    omega
  rw [h_range_eq] at h_sum_diff
  have h_lt := sum_inv_lt_log_sub n (by omega) (n * n - 2)
  have h_range_eq2 : (n * n - 2 + 1) = (n * n - 1) := by
    have h_n2 : n * n ≥ 4 := by nlinarith
    omega
  rw [h_range_eq2] at h_lt
  rw [← h_sum_diff] at h_lt
  have h_lt_cast : (n : ℝ) + (n * n - 2 : ℕ) + 1 = (n * n + n - 1 : ℝ) := by
    have h_n2 : n * n ≥ 2 := by nlinarith
    push_cast [h_n2]
  rw [h_lt_cast] at h_lt
  linarith

lemma h_UB (n : ℕ) (hn : 2 ≤ n) : D_seq n < 2 * log (n + 1) - log (n * n + n : ℝ) := by
  unfold D_seq
  have h_gamma := eulerMascheroniSeq_lt_eulerMascheroniConstant n
  unfold eulerMascheroniSeq at h_gamma
  have h_sum_diff := harmonic_diff_eq_sum n (n * n + n - 1 - n)
  have h_le : n ≤ n * n + n - 1 := by
    rcases n with _ | n
    · contradiction
    · have h_eq : (n + 1) * (n + 1) + (n + 1) - 1 = (n + 1) * (n + 1) + n := rfl
      rw [h_eq]
      have h1 : n + 1 ≤ (n + 1) * (n + 1) := (n + 1).le_mul_self
      omega
  have h_sub_eq : n + (n * n + n - 1 - n) = n * n + n - 1 := Nat.add_sub_cancel' h_le
  rw [h_sub_eq] at h_sum_diff
  have h_range_eq : (n * n + n - 1 - n) = (n * n - 1) := by
    have h_n2 : n * n ≥ 4 := by nlinarith
    omega
  rw [h_range_eq] at h_sum_diff
  have h_gt := sum_inv_gt_log_sub n (n * n - 2)
  have h_range_eq2 : (n * n - 2 + 1) = (n * n - 1) := by
    have h_n2 : n * n ≥ 4 := by nlinarith
    omega
  rw [h_range_eq2] at h_gt
  rw [← h_sum_diff] at h_gt
  have h_gt_cast : (n : ℝ) + (n * n - 2 : ℕ) + 2 = (n * n + n : ℝ) := by
    have h_n2 : n * n ≥ 2 := by nlinarith
    push_cast [h_n2]
  rw [h_gt_cast] at h_gt
  linarith

lemma tendsto_D_atTop : Tendsto D_seq atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_LB_limit tendsto_UB_limit
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact le_of_lt (h_LB n hn)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact le_of_lt (h_UB n hn)





noncomputable def L_seq (n : ℕ) : ℝ := 5 / (6 * (n : ℝ)^2 + 6 * (n : ℝ) + 4)

lemma L_diff_eq (n : ℕ) (hn : 2 ≤ n) : L_seq n - L_seq (n + 1) =
    5 * (12 * (n : ℝ) + 12) / ((6 * (n : ℝ)^2 + 6 * (n : ℝ) + 4) * (6 * ((n : ℝ) + 1)^2 + 6 * ((n : ℝ) + 1) + 4)) := by
  unfold L_seq
  have hn_real : (n : ℝ) ≥ 2 := by exact_mod_cast hn
  have h_pos1 : 6 * (n : ℝ) ^ 2 + 6 * (n : ℝ) + 4 > 0 := by positivity
  have h_ne1 : 6 * (n : ℝ) ^ 2 + 6 * (n : ℝ) + 4 ≠ 0 := by linarith
  have h_pos2 : 6 * ((n : ℝ) + 1) ^ 2 + 6 * ((n : ℝ) + 1) + 4 > 0 := by positivity
  have h_ne2 : 6 * ((n : ℝ) + 1) ^ 2 + 6 * ((n : ℝ) + 1) + 4 ≠ 0 := by linarith
  push_cast
  field_simp

lemma refined_bound_gt_L_diff (n : ℕ) (hn : 2 ≤ n) :
    (4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
    (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) - 2 / ((n : ℝ) + 1) >
    L_seq n - L_seq (n + 1) := by
  rw [L_diff_eq n hn]
  have hn_real : (n : ℝ) ≥ 2 := by exact_mod_cast hn
  have h_pos1 : 2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1 > 0 := by positivity
  have h_ne1 : 2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1 ≠ 0 := by linarith
  have h_pos2 : 3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) > 0 := by positivity
  have h_ne2 : 3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) ≠ 0 := by linarith
  have h_pos3 : (n : ℝ) + 1 > 0 := by linarith
  have h_ne3 : (n : ℝ) + 1 ≠ 0 := by linarith
  have h_pos4 : 6 * (n : ℝ) ^ 2 + 6 * (n : ℝ) + 4 > 0 := by positivity
  have h_ne4 : 6 * (n : ℝ) ^ 2 + 6 * (n : ℝ) + 4 ≠ 0 := by linarith
  have h_pos5 : 6 * ((n : ℝ) + 1) ^ 2 + 6 * ((n : ℝ) + 1) + 4 > 0 := by positivity
  have h_ne5 : 6 * ((n : ℝ) + 1) ^ 2 + 6 * ((n : ℝ) + 1) + 4 ≠ 0 := by linarith
  have h_eq : ((4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
              (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) - 2 / ((n : ℝ) + 1)) -
              5 * (12 * (n : ℝ) + 12) / ((6 * (n : ℝ)^2 + 6 * (n : ℝ) + 4) * (6 * ((n : ℝ) + 1)^2 + 6 * ((n : ℝ) + 1) + 4)) =
              (264 * (n : ℝ)^5 + 1320 * (n : ℝ)^4 + 2788 * (n : ℝ)^3 + 3084 * (n : ℝ)^2 + 1748 * (n : ℝ) + 396) /
              (3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) * (6 * (n : ℝ)^2 + 6 * (n : ℝ) + 4) * (6 * ((n : ℝ) + 1)^2 + 6 * ((n : ℝ) + 1) + 4)) := by
  rw [gt_iff_lt, ← sub_pos, h_eq]
  have h_num_pos : 264 * (n : ℝ)^5 + 1320 * (n : ℝ)^4 + 2788 * (n : ℝ)^3 + 3084 * (n : ℝ)^2 + 1748 * (n : ℝ) + 396 > 0 := by positivity
  have h_den_pos : 3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) * (6 * (n : ℝ)^2 + 6 * (n : ℝ) + 4) * (6 * ((n : ℝ) + 1)^2 + 6 * ((n : ℝ) + 1) + 4) > 0 := by positivity
  exact div_pos h_num_pos h_den_pos

  ∑ i ∈ Finset.range (n + 1), (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2


  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    push_cast
    have h_shift : (fun i : ℕ ↦ (2 * ((n : ℝ) + 1) + 1 - 2 * ((i : ℝ) + 1))^2) =
    rw [h_shift]
    rw [ih]
