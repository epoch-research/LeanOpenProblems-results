import FormalConjectures.Util.ProblemImports

open BigOperators LinearRecurrence Real Filter Topology

set_option linter.style.namespace false
set_option linter.unusedVariables false
set_option linter.style.copyright.formalConjectures false

lemma decreasing_limit_zero_pos (y : ℕ → ℝ) (h_dec : ∀ n, y (n + 1) < y n) (h_lim : Tendsto y atTop (nhds 0)) (n : ℕ) : y n > 0 := by
  by_cases h_ge : y (n + 1) ≥ 0
  · have : y n > y (n + 1) := h_dec n
    linarith
  · push_neg at h_ge -- now h_ge : y (n + 1) < 0
    have h_eps : (0 : ℝ) < - y (n + 1) := by linarith
    have h_lim' := h_lim
    rw [Metric.tendsto_atTop] at h_lim'
    rcases h_lim' (- y (n + 1)) h_eps with ⟨N, h_N⟩
    have h_mono : ∀ m, y (n + 1 + m + 1) < y (n + 1) := by
      intro m
      induction m with
      | zero => exact h_dec (n + 1)
      | succ m ih =>
        have h_step := h_dec (n + 1 + m + 1)
        have h_eq : n + 1 + (m + 1) + 1 = n + 1 + m + 1 + 1 := by ring
        rw [h_eq]
        exact lt_trans h_step ih
    let m := N
    have h_ge_N : n + 1 + m + 1 ≥ N := by omega
    have h_bnd := h_N (n + 1 + m + 1) h_ge_N
    have h_lt_y := h_mono m
    rw [Real.dist_0_eq_abs] at h_bnd
    have h_ym_neg : y (n + 1 + m + 1) < 0 := by linarith
    have h_abs : |y (n + 1 + m + 1)| = - y (n + 1 + m + 1) := abs_of_neg h_ym_neg
    rw [h_abs] at h_bnd
    linarith

lemma sum_inv_gt_log_sub (n : ℕ) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (1 / (n + 1 + i : ℝ))) > log (n + k + 2) - log (n + 1) := by
  induction k with
  | zero =>
    have h_sum : (∑ i ∈ Finset.range (0 + 1), (1 / (n + 1 + i : ℝ))) = 1 / (n + 1 : ℝ) := by
      simp
    rw [h_sum]
    push_cast
    have h_rhs : (n + (0 : ℝ) + 2) = n + 2 := by ring
    rw [h_rhs]
    have h1 : 0 < 1 + 1 / (n + 1 : ℝ) := by positivity
    have h2 : 1 + 1 / (n + 1 : ℝ) ≠ 1 := by
      intro h
      have h_ne : 1 / (n + 1 : ℝ) ≠ 0 := by positivity
      have : 1 / (n + 1 : ℝ) = 0 := by linarith
      exact h_ne this
    have h3 := Real.log_lt_sub_one_of_pos h1 h2
    have h4 : 1 + 1 / (n + 1 : ℝ) - 1 = 1 / (n + 1 : ℝ) := by ring
    rw [h4] at h3
    have h_div : 1 + 1 / (n + 1 : ℝ) = (n + 2) / (n + 1) := by
      have : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp; ring
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
      have h4 : 1 + 1 / (n + k + 2 : ℝ) - 1 = 1 / (n + k + 2 : ℝ) := by ring
      rwa [h4] at h3
    have h_log_rw : log (1 + 1 / (n + k + 2 : ℝ)) = log (n + k + 3) - log (n + k + 2) := by
      have h_div : 1 + 1 / (n + k + 2 : ℝ) = (n + k + 3) / (n + k + 2) := by
        have : (n + k + 2 : ℝ) ≠ 0 := by positivity
        field_simp; ring
      rw [h_div]
      rw [log_div]
      · positivity
      · positivity
    rw [h_log_rw] at h_log
    have ih' := ih
    push_cast at ih'
    have h_eq : (n + 1 + (k + 1 : ℝ)) = (n + k + 2 : ℝ) := by ring
    have h_goal_rhs : (n + (k + 1) + 2 : ℝ) = (n + k + 3 : ℝ) := by ring
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
    have h_rhs : (n + (0 : ℝ) + 1) = n + 1 := by ring
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
    have h4 : 1 - 1 / (n + 1 : ℝ) - 1 = -1 / (n + 1 : ℝ) := by ring
    rw [h4] at h3
    have h_div : 1 - 1 / (n + 1 : ℝ) = n / (n + 1) := by
      have : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp; ring
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
      have h4 : 1 - 1 / (n + k + 2 : ℝ) - 1 = -(1 / (n + k + 2 : ℝ)) := by ring
      rwa [h4] at h3
    have h_log_rw : log (1 - 1 / (n + k + 2 : ℝ)) = log (n + k + 1) - log (n + k + 2) := by
      have h_div : 1 - 1 / (n + k + 2 : ℝ) = (n + k + 1) / (n + k + 2) := by
        have : (n + k + 2 : ℝ) ≠ 0 := by positivity
        field_simp; ring
      rw [h_div]
      rw [log_div]
      · positivity
      · positivity
    rw [h_log_rw] at h_log
    have ih' := ih
    push_cast at ih'
    have h_eq : (n + 1 + (k + 1 : ℝ)) = (n + k + 2 : ℝ) := by ring
    have h_goal_rhs : (n + (k + 1) + 1 : ℝ) = (n + k + 2 : ℝ) := by ring
    rw [h_eq, h_goal_rhs]
    linarith

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
    have h_denom : (a + k + 1 : ℝ) = a + 1 + k := by ring
    rw [h_denom]
    linarith

lemma tendsto_index_atTop : Tendsto (fun n : ℕ ↦ n * n + n - 1) atTop atTop := by
  have h_ineq : id ≤ᶠ[atTop] (fun n : ℕ ↦ n * n + n - 1) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [id_eq]
    omega
  exact tendsto_atTop_mono h_ineq tendsto_id

lemma tendsto_index_real_atTop : Tendsto (fun n : ℕ ↦ (n * n + n - 1 : ℝ)) atTop atTop := by
  have h_ineq : (fun n : ℕ ↦ (n : ℝ)) ≤ᶠ[atTop] (fun n : ℕ ↦ (n * n + n - 1 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    push_cast
    have : (n : ℝ) ≥ 1 := by exact Nat.cast_le.mpr hn
    nlinarith
  exact tendsto_atTop_mono h_ineq tendsto_natCast_atTop_atTop

lemma tendsto_harmonic_sub_log_comp :
    Tendsto (fun n : ℕ ↦ (harmonic (n * n + n - 1) : ℝ) - log (n * n + n - 1)) atTop (nhds eulerMascheroniConstant) := by
  have h_comp := tendsto_harmonic_sub_log.comp tendsto_index_atTop
  exact h_comp

lemma tendsto_log_term : Tendsto (fun n : ℕ ↦ log (1 + 1 / (n * n + n - 1 : ℝ))) atTop (nhds 0) := by
  have h_div : Tendsto (fun n : ℕ ↦ 1 / (n * n + n - 1 : ℝ)) atTop (nhds 0) := by
    have h_inv : (fun n : ℕ ↦ 1 / (n * n + n - 1 : ℝ)) = (fun x ↦ x⁻¹) ∘ (fun n : ℕ ↦ (n * n + n - 1 : ℝ)) := by
      ext n; simp [one_div]
    rw [h_inv]
    exact tendsto_inv_atTop_zero.comp tendsto_index_real_atTop
  have h_add : Tendsto (fun n : ℕ ↦ 1 + 1 / (n * n + n - 1 : ℝ)) atTop (nhds 1) := by
    have h_one : Tendsto (fun n : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have h_sum := Tendsto.add h_one h_div
    rw [add_zero] at h_sum
    exact h_sum
  have h_log : ContinuousAt log 1 := continuousAt_log (by norm_num)
  have h_comp := h_log.tendsto.comp h_add
  rw [Real.log_one] at h_comp
  exact h_comp

noncomputable def D_seq (n : ℕ) : ℝ :=
  2 * (harmonic n : ℝ) - (harmonic (n * n + n - 1) : ℝ) - eulerMascheroniConstant

lemma h_LB (n : ℕ) (hn : 1 ≤ n) : 2 * log n - log (n * n + n - 1 : ℝ) < D_seq n := by
  unfold D_seq
  have h_gamma := eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have h_seq' : eulerMascheroniSeq' n = (harmonic n : ℝ) - log n := by
    unfold eulerMascheroniSeq'
    have : n ≠ 0 := by omega
    simp [this]
  rw [h_seq'] at h_gamma
  have h_sum_diff := harmonic_diff_eq_sum n (n * n + n - 1 - n)
  have h_sub_eq : n + (n * n + n - 1 - n) = n * n + n - 1 := by
    rcases n with _ | n
    · contradiction
    · omega
  rw [h_sub_eq] at h_sum_diff
  have h_range_eq : (n * n + n - 1 - n) = (n * n - 1) := by
    rcases n with _ | n
    · contradiction
    · omega
  rw [h_range_eq] at h_sum_diff
  have h_lt := sum_inv_lt_log_sub n (by omega) (n * n - 2)
  have h_range_eq2 : (n * n - 2 + 1) = (n * n - 1) := by
    rcases n with _ | n
    · contradiction
    · omega
  rw [h_range_eq2] at h_lt
  rw [← h_sum_diff] at h_lt
  have h_lt_cast : ((n + (n * n - 2) + 1 : ℕ) : ℝ) = ((n * n + n - 1 : ℕ) : ℝ) := by
    congr 1
    rcases n with _ | n
    · contradiction
    · omega
  rw [h_lt_cast] at h_lt
  linarith

lemma h_UB (n : ℕ) (hn : 1 ≤ n) : D_seq n < 2 * log (n + 1) - log (n * n + n : ℝ) := by
  unfold D_seq
  have h_gamma := eulerMascheroniSeq_lt_eulerMascheroniConstant n
  unfold eulerMascheroniSeq at h_gamma
  have h_sum_diff := harmonic_diff_eq_sum n (n * n + n - 1 - n)
  have h_sub_eq : n + (n * n + n - 1 - n) = n * n + n - 1 := by
    rcases n with _ | n
    · contradiction
    · omega
  rw [h_sub_eq] at h_sum_diff
  have h_range_eq : (n * n + n - 1 - n) = (n * n - 1) := by
    rcases n with _ | n
    · contradiction
    · omega
  rw [h_range_eq] at h_sum_diff
  have h_gt := sum_inv_gt_log_sub n (n * n - 2)
  have h_range_eq2 : (n * n - 2 + 1) = (n * n - 1) := by
    rcases n with _ | n
    · contradiction
    · omega
  rw [h_range_eq2] at h_gt
  rw [← h_sum_diff] at h_gt
  have h_gt_cast : ((n + (n * n - 2) + 2 : ℕ) : ℝ) = ((n * n + n : ℕ) : ℝ) := by
    congr 1
    rcases n with _ | n
    · contradiction
    · omega
  rw [h_gt_cast] at h_gt
  linarith
