import FormalConjectures.Util.ProblemImports

open BigOperators LinearRecurrence Real Filter Topology

set_option linter.style.namespace false
set_option linter.unusedVariables false
set_option linter.style.copyright.formalConjectures false

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

lemma index_le_index (n : ℕ) : n ≤ n * n + n - 1 := by
  rcases n with _ | n
  · simp
  · have h_eq : (n + 1) * (n + 1) + (n + 1) - 1 = (n + 1) * (n + 1) + n := rfl
    rw [h_eq]
    have h1 : n + 1 ≤ (n + 1) * (n + 1) := (n + 1).le_mul_self
    omega

lemma tendsto_index_atTop : Tendsto (fun n : ℕ ↦ n * n + n - 1) atTop atTop := by
  exact tendsto_atTop_mono index_le_index tendsto_id

lemma tendsto_index_real_atTop : Tendsto (fun n : ℕ ↦ (n * n + n - 1 : ℝ)) atTop atTop := by
  have h_ineq : (fun n : ℕ ↦ (n : ℝ)) ≤ᶠ[atTop] (fun n : ℕ ↦ (n * n + n - 1 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    push_cast
    have : (n : ℝ) ≥ 1 := by exact Nat.cast_le.mpr hn
    nlinarith
  exact tendsto_atTop_mono' atTop h_ineq tendsto_natCast_atTop_atTop

lemma tendsto_harmonic_sub_log_comp :
    Tendsto (fun n : ℕ ↦ (harmonic (n * n + n - 1) : ℝ) - log (n * n + n - 1)) atTop (nhds eulerMascheroniConstant) := by
  have h1 : Tendsto (fun n : ℕ ↦ (harmonic n : ℝ) - log n) atTop (nhds eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
  have h2 : Tendsto (fun n : ℕ ↦ n * n + n - 1) atTop atTop := tendsto_index_atTop
  have h_comp : Tendsto (fun n ↦ (harmonic (n * n + n - 1) : ℝ) - log ↑(n * n + n - 1)) atTop (nhds eulerMascheroniConstant) := h1.comp h2
  have h_eq : (fun n ↦ (harmonic (n * n + n - 1) : ℝ) - log ↑(n * n + n - 1)) =ᶠ[atTop]
              (fun n ↦ (harmonic (n * n + n - 1) : ℝ) - log (n * n + n - 1)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    congr 2
    rcases n with _ | n
    · contradiction
    · have h_idx_eq : (n + 1) * (n + 1) + (n + 1) - 1 = (n + 1) * (n + 1) + n := rfl
      rw [h_idx_eq]
      push_cast
      ring
  exact h_comp.congr' h_eq

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
    ring
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
    ring
  rw [h_gt_cast] at h_gt
  linarith
