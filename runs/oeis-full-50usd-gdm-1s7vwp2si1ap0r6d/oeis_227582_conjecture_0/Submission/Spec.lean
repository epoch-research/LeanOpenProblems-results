/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports

open BigOperators Real Filter Topology LinearRecurrence

set_option linter.style.namespace false
set_option linter.unusedVariables false
set_option linter.style.copyright.formalConjectures false

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

def A227582_base (n : ℕ) : ℤ :=
  let order := 7
  let coeffs : Fin order → ℤ := ![1, -2, 1, 0, 0, -1, 2]
  let init : Fin order → ℤ := ![2, 7, 14, 23, 35, 50, 67]
  let E : LinearRecurrence ℤ := { order := order, coeffs := coeffs }
  E.mkSol init n

noncomputable def a (n : ℕ) : ℕ :=
  if h : 0 < n then
    (A227582_base (n - 1)).toNat
  else
    0

noncomputable def D_seq (n : ℕ) : ℝ :=
  2 * (harmonic n : ℝ) - (harmonic (n * n + n - 1) : ℝ) - eulerMascheroniConstant

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

lemma increasing_limit_zero_neg (y : ℕ → ℝ) (h_inc : ∀ n, y n < y (n + 1)) (h_lim : Tendsto y atTop (nhds 0)) (n : ℕ) : y n < 0 := by
  have h_dec : ∀ n, - y (n + 1) < - y n := by
    intro k
    have := h_inc k
    linarith
  have h_lim_neg : Tendsto (fun k ↦ - y k) atTop (nhds 0) := by
    have h_neg := h_lim.neg
    rwa [neg_zero] at h_neg
  have h_pos := decreasing_limit_zero_pos (fun k ↦ - y k) h_dec h_lim_neg n
  linarith

lemma tendsto_index_atTop : Tendsto (fun n : ℕ ↦ n * n + n - 1) atTop atTop := by
  have h_ineq : ∀ n, n ≤ n * n + n - 1 := by
    intro n
    rcases n with _ | n
    · simp
    · dsimp
      have h_eq2 : (n + 1) * (n + 1) = (n + 1) * n + (n + 1) := by ring
      rw [h_eq2]
      omega
  exact tendsto_atTop_mono h_ineq tendsto_id

lemma tendsto_index_real_atTop : Tendsto (fun n : ℕ ↦ ((n * n + n - 1 : ℕ) : ℝ)) atTop atTop := by
  have h_ineq : ∀ n : ℕ, (n : ℝ) ≤ ((n * n + n - 1 : ℕ) : ℝ) := by
    intro n
    rcases n with _ | n
    · simp
    · have h_eq_rw : (((n + 1) * (n + 1) + (n + 1) - 1 : ℕ) : ℝ) = (((n + 1) * (n + 1) + n : ℕ) : ℝ) := by rfl
      rw [h_eq_rw]
      push_cast
      have : (n : ℝ) ≥ 0 := by positivity
      nlinarith
  exact tendsto_atTop_mono h_ineq tendsto_natCast_atTop_atTop

lemma tendsto_harmonic_sub_log_comp :
    Tendsto (fun n : ℕ ↦ (harmonic (n * n + n - 1) : ℝ) - log ((n * n + n - 1 : ℕ) : ℝ)) atTop (nhds eulerMascheroniConstant) := by
  have h_comp := tendsto_harmonic_sub_log.comp tendsto_index_atTop
  exact h_comp

lemma tendsto_log_term : Tendsto (fun n : ℕ ↦ log (1 + 1 / ((n * n + n - 1 : ℕ) : ℝ))) atTop (nhds 0) := by
  have h_div : Tendsto (fun n : ℕ ↦ 1 / ((n * n + n - 1 : ℕ) : ℝ)) atTop (nhds 0) := by
    have h_inv : (fun n : ℕ ↦ 1 / ((n * n + n - 1 : ℕ) : ℝ)) = (fun x ↦ x⁻¹) ∘ (fun n : ℕ ↦ ((n * n + n - 1 : ℕ) : ℝ)) := by
      ext n; simp [one_div]
    rw [h_inv]
    exact tendsto_inv_atTop_zero.comp tendsto_index_real_atTop
  have h_add : Tendsto (fun n : ℕ ↦ 1 + 1 / ((n * n + n - 1 : ℕ) : ℝ)) atTop (nhds 1) := by
    have h_one : Tendsto (fun n : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have h_sum := Tendsto.add h_one h_div
    rw [add_zero] at h_sum
    exact h_sum
  have h_log : ContinuousAt log 1 := continuousAt_log (by norm_num)
  have h_comp := h_log.tendsto.comp h_add
  rw [Real.log_one] at h_comp
  exact h_comp

lemma h_LB (n : ℕ) (hn : 2 ≤ n) : 2 * log n - log (n * n + n - 1 : ℝ) < D_seq n := by
  unfold D_seq
  have h_gamma := eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have h_seq' : eulerMascheroniSeq' n = (harmonic n : ℝ) - log n := by
    unfold eulerMascheroniSeq'
    have : n ≠ 0 := by omega
    simp [this]
  rw [h_seq'] at h_gamma
  have h_sum_diff := harmonic_diff_eq_sum n (n * n + n - 1 - n)
  have h_sub_eq : n + (n * n + n - 1 - n) = n * n + n - 1 := by
    clear h_gamma h_seq' h_sum_diff
    rcases n with _ | _ | n
    · contradiction
    · contradiction
    · have h_mul_ge4 : (n + 1 + 1) * (n + 1 + 1) ≥ 4 := by
        have h_ring : (n + 1 + 1) * (n + 1 + 1) = (n + 1 + 1) * n + (n + 1 + 1) * 2 := by ring
        rw [h_ring]
        omega
      omega
  rw [h_sub_eq] at h_sum_diff
  have h_range_eq : (n * n + n - 1 - n) = (n * n - 1) := by
    clear h_gamma h_seq' h_sum_diff
    rcases n with _ | _ | n
    · contradiction
    · contradiction
    · have h_mul_ge4 : (n + 1 + 1) * (n + 1 + 1) ≥ 4 := by
        have h_ring : (n + 1 + 1) * (n + 1 + 1) = (n + 1 + 1) * n + (n + 1 + 1) * 2 := by ring
        rw [h_ring]
        omega
      omega
  rw [h_range_eq] at h_sum_diff
  have h_lt := sum_inv_lt_log_sub n (by omega) (n * n - 2)
  have h_range_eq2 : (n * n - 2 + 1) = (n * n - 1) := by
    clear h_gamma h_seq' h_sum_diff h_lt
    rcases n with _ | _ | n
    · contradiction
    · contradiction
    · have h_mul_ge4 : (n + 1 + 1) * (n + 1 + 1) ≥ 4 := by
        have h_ring : (n + 1 + 1) * (n + 1 + 1) = (n + 1 + 1) * n + (n + 1 + 1) * 2 := by ring
        rw [h_ring]
        omega
      omega
  rw [h_range_eq2] at h_lt
  rw [← h_sum_diff] at h_lt
  have h_lt_cast : (n : ℝ) + ((n * n - 2 : ℕ) : ℝ) + 1 = ((n * n + n - 1 : ℕ) : ℝ) := by
    rcases n with _ | _ | n
    · contradiction
    · contradiction
    · have h1 : (n + 2) * (n + 2) - 2 = n * n + 4 * n + 2 := by
        have h_ring : (n + 2) * (n + 2) = n * n + 4 * n + 4 := by ring
        rw [h_ring]
        omega
      have h2 : (n + 2) * (n + 2) + (n + 2) - 1 = n * n + 5 * n + 5 := by
        have h_ring : (n + 2) * (n + 2) = n * n + 4 * n + 4 := by ring
        rw [h_ring]
        omega
      rw [h1, h2]
      push_cast
      ring
  rw [h_lt_cast] at h_lt
  have h_cast_eq : ((n * n + n - 1 : ℕ) : ℝ) = (n : ℝ) * (n : ℝ) + (n : ℝ) - 1 := by
    rcases n with _ | _ | n
    · contradiction
    · contradiction
    · have h_ring : (n + 2) * (n + 2) = n * n + 4 * n + 4 := by ring
      have h2 : (n + 2) * (n + 2) + (n + 2) - 1 = n * n + 5 * n + 5 := by
        rw [h_ring]
        omega
      rw [h2]
      push_cast
      ring
  rw [h_cast_eq] at h_lt
  linarith

lemma h_UB (n : ℕ) (hn : 2 ≤ n) : D_seq n < 2 * log (n + 1) - log (n * n + n : ℝ) := by
  unfold D_seq
  have h_gamma := eulerMascheroniSeq_lt_eulerMascheroniConstant n
  unfold eulerMascheroniSeq at h_gamma
  have h_sum_diff := harmonic_diff_eq_sum n (n * n + n - 1 - n)
  have h_sub_eq : n + (n * n + n - 1 - n) = n * n + n - 1 := by
    clear h_gamma h_sum_diff
    rcases n with _ | _ | n
    · contradiction
    · contradiction
    · have h_mul_ge4 : (n + 1 + 1) * (n + 1 + 1) ≥ 4 := by
        have h_ring : (n + 1 + 1) * (n + 1 + 1) = (n + 1 + 1) * n + (n + 1 + 1) * 2 := by ring
        rw [h_ring]
        omega
      omega
  rw [h_sub_eq] at h_sum_diff
  have h_range_eq : (n * n + n - 1 - n) = (n * n - 1) := by
    clear h_gamma h_sum_diff
    rcases n with _ | _ | n
    · contradiction
    · contradiction
    · have h_mul_ge4 : (n + 1 + 1) * (n + 1 + 1) ≥ 4 := by
        have h_ring : (n + 1 + 1) * (n + 1 + 1) = (n + 1 + 1) * n + (n + 1 + 1) * 2 := by ring
        rw [h_ring]
        omega
      omega
  rw [h_range_eq] at h_sum_diff
  have h_gt := sum_inv_gt_log_sub n (n * n - 2)
  have h_range_eq2 : (n * n - 2 + 1) = (n * n - 1) := by
    clear h_gamma h_sum_diff h_gt
    rcases n with _ | _ | n
    · contradiction
    · contradiction
    · have h_mul_ge4 : (n + 1 + 1) * (n + 1 + 1) ≥ 4 := by
        have h_ring : (n + 1 + 1) * (n + 1 + 1) = (n + 1 + 1) * n + (n + 1 + 1) * 2 := by ring
        rw [h_ring]
        omega
      omega
  rw [h_range_eq2] at h_gt
  rw [← h_sum_diff] at h_gt
  have h_gt_cast : (n : ℝ) + ((n * n - 2 : ℕ) : ℝ) + 2 = ((n * n + n : ℕ) : ℝ) := by
    rcases n with _ | _ | n
    · contradiction
    · contradiction
    · have h1 : (n + 2) * (n + 2) - 2 = n * n + 4 * n + 2 := by
        have h_ring : (n + 2) * (n + 2) = n * n + 4 * n + 4 := by ring
        rw [h_ring]
        omega
      have h2 : (n + 2) * (n + 2) + (n + 2) = n * n + 5 * n + 6 := by
        have h_ring : (n + 2) * (n + 2) = n * n + 4 * n + 4 := by ring
        rw [h_ring]
        omega
      rw [h1, h2]
      push_cast
      ring
  rw [h_gt_cast] at h_gt
  have h_cast_eq_ub : ((n * n + n : ℕ) : ℝ) = (n : ℝ) * (n : ℝ) + (n : ℝ) := by push_cast; ring
  rw [h_cast_eq_ub] at h_gt
  linarith

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

lemma tendsto_LB_limit : Tendsto (fun n : ℕ ↦ 2 * log n - log (n * n + n - 1 : ℝ)) atTop (nhds 0) := by
  rw [tendsto_congr' tendsto_LB_limit_eq]
  have h_lim : Tendsto (fun n : ℕ ↦ ( (n * n + n - 1 : ℝ) / ((n : ℝ) * (n : ℝ)) )) atTop (nhds 1) := by
    rw [tendsto_congr' tendsto_LB_limit_div_eq]
    have h1 : Tendsto (fun n : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have h2 : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
    have h3 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) * (n : ℝ))) atTop (nhds 0) := by
      have h_index : Tendsto (fun n : ℕ ↦ (n : ℝ) * (n : ℝ)) atTop atTop := by
        exact tendsto_atTop_mono (f := fun n : ℕ ↦ (n : ℝ)) (by intro n; rcases n with _ | n <;> [simp; { have : (n : ℝ) ≥ 0 := by positivity; nlinarith }]) tendsto_natCast_atTop_atTop
      have h_eq : (fun n : ℕ ↦ 1 / ((n : ℝ) * (n : ℝ))) = (fun n : ℕ ↦ ((n : ℝ) * (n : ℝ))⁻¹) := by
        ext n; simp [one_div]
      rw [h_eq]
      exact tendsto_inv_atTop_zero.comp h_index
    have h_sum := Tendsto.add h1 h2
    have h_sub := Tendsto.sub h_sum h3
    have h_sub_eq : (1 : ℝ) + 0 - 0 = 1 := by ring
    rw [h_sub_eq] at h_sub
    exact h_sub
  have h_log : ContinuousAt log 1 := continuousAt_log (by norm_num)
  have h_comp := h_log.tendsto.comp h_lim
  rw [Real.log_one] at h_comp
  have h_neg := h_comp.neg
  rw [neg_zero] at h_neg
  exact h_neg

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

lemma tendsto_D_atTop : Tendsto D_seq atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_LB_limit tendsto_UB_limit
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact le_of_lt (h_LB n hn)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact le_of_lt (h_UB n hn)

noncomputable def L_seq (n : ℕ) : ℝ := 5 / (6 * (n : ℝ)^2 + 6 * (n : ℝ))

lemma L_diff_eq (n : ℕ) (hn : 2 ≤ n) : L_seq n - L_seq (n + 1) =
    5 / (3 * (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  unfold L_seq
  have : (n : ℝ) > 0 := by positivity
  field_simp
  push_cast
  ring

noncomputable def U_seq (n : ℕ) : ℝ := 5 / (6 * (n : ℝ)^2 + 6 * (n : ℝ) - 1)

def pairing_sum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2

lemma pairing_sum_eq (n : ℕ) : pairing_sum n = ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) / 3 := by
  induction n with
  | zero =>
    unfold pairing_sum
    simp
  | succ n ih =>
    unfold pairing_sum at ih ⊢
    rw [Finset.sum_range_succ']
    push_cast
    have h_shift : (fun i : ℕ ↦ (2 * ((n : ℝ) + 1) + 1 - 2 * ((i : ℝ) + 1))^2) =
                   (fun i : ℕ ↦ (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2) := by
      ext i
      ring
    rw [h_shift]
    rw [ih]
    ring

lemma sum_pairing (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) + 1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ))) =
    ∑ k ∈ Finset.Ico (n^2 + n : ℕ) (n^2 + 3 * n + 2 : ℕ), (1 / (k : ℝ)) := by
  have h_split : ∑ k ∈ Finset.Ico (n^2 + n : ℕ) (n^2 + 3 * n + 2 : ℕ), (1 / (k : ℝ)) =
                 ∑ k ∈ Finset.Ico (n^2 + n : ℕ) (n^2 + 2 * n + 1 : ℕ), (1 / (k : ℝ)) +
                 ∑ k ∈ Finset.Ico (n^2 + 2 * n + 1 : ℕ) (n^2 + 3 * n + 2 : ℕ), (1 / (k : ℝ)) := by
    rw [Finset.sum_Ico_consecutive]
    · omega
    · omega
  rw [h_split]
  have h1 : ∑ k ∈ Finset.Ico (n^2 + n : ℕ) (n^2 + 2 * n + 1 : ℕ), (1 / (k : ℝ)) =
            ∑ i ∈ Finset.range (n + 1), (1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ))) := by
    have h_ico : n^2 + 2 * n + 1 = (n^2 + n) + (n + 1) := by omega
    rw [h_ico]
    rw [Finset.sum_Ico_eq_sum_range]
    have h_range_eq : n^2 + n + (n + 1) - (n^2 + n) = n + 1 := by omega
    rw [h_range_eq]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    rfl
  have h2 : ∑ k ∈ Finset.Ico (n^2 + 2 * n + 1 : ℕ) (n^2 + 3 * n + 2 : ℕ), (1 / (k : ℝ)) =
            ∑ i ∈ Finset.range (n + 1), (1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ))) := by
    have h_ico : n^2 + 3 * n + 2 = (n^2 + 2 * n + 1) + (n + 1) := by omega
    rw [h_ico]
    rw [Finset.sum_Ico_eq_sum_range]
    have h_range_eq2 : n^2 + 2 * n + 1 + (n + 1) - (n^2 + 2 * n + 1) = n + 1 := by omega
    rw [h_range_eq2]
    have h_congr : ∑ i ∈ Finset.range (n + 1), (1 / (((n^2 + 2 * n + 1) + i : ℕ) : ℝ)) =
                    ∑ i ∈ Finset.range (n + 1), (1 / ((n : ℝ)^2 + 2 * (n : ℝ) + 1 + (i : ℝ))) := by
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      rfl
    rw [h_congr]
    have h_reflect := Finset.sum_range_reflect (fun i : ℕ ↦ 1 / ((n : ℝ)^2 + 2 * (n : ℝ) + 1 + (i : ℝ))) (n + 1)
    rw [← h_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    have hi_lt : i < n + 1 := Finset.mem_range.mp hi
    have h_sub : n + 1 - 1 - i = n - i := by omega
    rw [h_sub]
    have h_cast_sub : ((n - i : ℕ) : ℝ) = (n : ℝ) - (i : ℝ) := by
      have : i ≤ n := by omega
      exact Nat.cast_sub this
    rw [h_cast_sub]
    congr 1
    ring
  rw [h1, h2, ← Finset.sum_add_distrib]

lemma summand_le (n i : ℕ) (hn : 1 ≤ n) (hi : i < n + 1) :
    1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) + 1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) ≥
    4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) := by
  have h_XY : ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) ≤ ((n : ℝ) + 1)^4 := by
    have h_eq : ((n : ℝ) + 1)^4 - ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) =
                ((n : ℝ) + 1)^2 - 1/4 + ((i : ℝ) - (n : ℝ) - 1/2)^2 := by ring
    rw [← sub_nonneg]
    rw [h_eq]
    have h_sq : ((i : ℝ) - (n : ℝ) - 1/2)^2 ≥ 0 := by positivity
    have : (n : ℝ) ≥ 1 := by exact_mod_cast hn
    nlinarith

  have h_posX : (n : ℝ)^2 + (n : ℝ) + (i : ℝ) > 0 := by positivity
  have h_posY : (n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ) > 0 := by
    have h_le : i ≤ n := by omega
    have : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast h_le
    have : (n : ℝ) ≥ 1 := by exact_mod_cast hn
    nlinarith
  have h_posSum : 2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1 > 0 := by positivity
  have h_posDen : ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) > 0 := by positivity
  have h_eq2 : 1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) + 1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) -
              (4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) =
              ((2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 * (((n : ℝ) + 1)^4 - ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)))) /
              (((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) * (((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) := by
    field_simp [ne_of_gt h_posX, ne_of_gt h_posY, ne_of_gt h_posSum, ne_of_gt h_posDen]; ring
  rw [ge_iff_le, ← sub_nonneg, h_eq2]
  have h_num_nonneg : (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 * (((n : ℝ) + 1)^4 - ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ))) ≥ 0 := by
    have h1 : (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 ≥ 0 := by positivity
    have h2 : ((n : ℝ) + 1)^4 - ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) ≥ 0 := by linarith
    exact mul_nonneg h1 h2
  have h_den_pos : ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) * (((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) > 0 := by
    positivity
  exact div_nonneg h_num_nonneg (le_of_lt h_den_pos)

lemma summand_ge (n i : ℕ) (hn : 1 ≤ n) (hi : i < n + 1) :
    1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) + 1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) ≤
    4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) := by
  have h_XY_ge : ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) ≤ ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) := by
    have h_eq : ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) - ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) =
                (i : ℝ) * (2 * (n : ℝ) + 1 - (i : ℝ)) := by ring
    rw [← sub_nonneg]
    rw [h_eq]
    have : (i : ℝ) ≥ 0 := by positivity
    have h_le : i ≤ n := by omega
    have : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast h_le
    have : (n : ℝ) ≥ 1 := by exact_mod_cast hn
    nlinarith

  have h_posX : (n : ℝ)^2 + (n : ℝ) + (i : ℝ) > 0 := by positivity
  have h_posY : (n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ) > 0 := by
    have h_le : i ≤ n := by omega
    have : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast h_le
    have : (n : ℝ) ≥ 1 := by exact_mod_cast hn
    nlinarith
  have h_posSum : 2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1 > 0 := by positivity
  have h_posDen : ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) > 0 := by positivity
  have h_eq2 : 1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) + 1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) -
              (4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) =
              -(((2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 * (((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) - ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1))) /
              (((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) * (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)))) := by
    field_simp [ne_of_gt h_posX, ne_of_gt h_posY, ne_of_gt h_posSum, ne_of_gt h_posDen]; ring
  rw [← sub_nonpos, h_eq2]
  have h_num_nonneg : (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 * (((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) - ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1)) ≥ 0 := by
    have h1 : (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 ≥ 0 := by positivity
    have h2 : ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) - ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) ≥ 0 := by linarith
    exact mul_nonneg h1 h2
  have h_den_pos : ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) * (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) > 0 := by
    positivity
  have h_div_nonneg : ((2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 * (((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) - ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1))) /
                     (((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) * (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) ≥ 0 := by
    exact div_nonneg h_num_nonneg (le_of_lt h_den_pos)
  linarith

lemma pairing_sum_bound (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Ico (n^2 + n) (n^2 + 3 * n + 2), (1 / (k : ℝ)) ≥
    (4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
    (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) := by
  rw [← sum_pairing n]
  have h_le : ∑ i ∈ Finset.range (n + 1), (1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) + 1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ))) ≥
              ∑ i ∈ Finset.range (n + 1), (4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi_lt : i < n + 1 := Finset.mem_range.mp hi
    exact summand_le n i hn hi_lt
  have h_sum_eq : ∑ i ∈ Finset.range (n + 1), (4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) =
                  (4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
                  pairing_sum n / (((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · simp
      ring
    · rw [← Finset.sum_div]
      congr 1
  rw [h_sum_eq]
  rw [pairing_sum_eq n]
  rfl

lemma refined_bound_gt_L_diff (n : ℕ) (hn : 2 ≤ n) :
    (4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
    (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) - 2 / ((n : ℝ) + 1) >
    L_seq n - L_seq (n + 1) := by
  rw [L_diff_eq n hn]
  have : (n : ℝ) ≥ 2 := by qify; exact hn
  have h_num_pos : 66*(n:ℝ)^4 + 264*(n:ℝ)^3 + 433*(n:ℝ)^2 + 338*(n:ℝ) + 99 > 0 := by positivity
  have h_den_pos : 3 * (18 * (n : ℝ)^9 + 162 * (n : ℝ)^8 + 645 * (n : ℝ)^7 + 1491 * (n : ℝ)^6 + 2210 * (n : ℝ)^5 + 2188 * (n : ℝ)^4 + 1453 * (n : ℝ)^3 + 623 * (n : ℝ)^2 + 154 * (n : ℝ) + 16) > 0 := by positivity
  have h_eq : ((4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
              (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) - 2 / ((n : ℝ) + 1)) -
              5 / (3 * (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) =
              (66*(n:ℝ)^4 + 264*(n:ℝ)^3 + 433*(n:ℝ)^2 + 338*(n:ℝ) + 99) /
              (3 * (18 * (n : ℝ)^9 + 162 * (n : ℝ)^8 + 645 * (n : ℝ)^7 + 1491 * (n : ℝ)^6 + 2210 * (n : ℝ)^5 + 2188 * (n : ℝ)^4 + 1453 * (n : ℝ)^3 + 623 * (n : ℝ)^2 + 154 * (n : ℝ) + 16)) := by
    field_simp; ring
  rw [← sub_pos, h_eq]
  exact div_pos h_num_pos h_den_pos

lemma D_sub_L_decreasing (n : ℕ) (hn : 2 ≤ n) : D_seq (n + 1) - L_seq (n + 1) < D_seq n - L_seq n := by
  have h_harm_n : (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) := by
    have : n + 1 = n + 1 := rfl
    rw [harmonic_succ]
    push_cast
    rfl
  have h_harm_idx : (n + 1) * (n + 1) + (n + 1) - 1 = (n * n + n - 1) + (2 * n + 2) := by omega
  have h_harm_diff := harmonic_diff_eq_sum (n * n + n - 1) (2 * n + 2)
  rw [← h_harm_idx] at h_harm_diff
  have h_Ico_range : ∑ k ∈ Finset.Ico (n^2 + n) (n^2 + 3 * n + 2), (1 / (k : ℝ)) =
                     ∑ i ∈ Finset.range (2 * n + 2), (1 / ((n * n + n - 1 : ℝ) + 1 + (i : ℝ))) := by
    have h_ico_eq : n^2 + 3 * n + 2 = (n^2 + n) + (2 * n + 2) := by omega
    rw [h_ico_eq]
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  rw [← h_Ico_range] at h_harm_diff
  unfold D_seq
  rw [h_harm_n]
  have h_bound1 := pairing_sum_bound n (by omega)
  have h_bound2 := refined_bound_gt_L_diff n hn
  linarith [h_harm_diff, h_bound1, h_bound2]

lemma pairing_sum_bound_upper (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Ico (n^2 + n) (n^2 + 3 * n + 2), (1 / (k : ℝ)) ≤
    (4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
    (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) := by
  rw [← sum_pairing n]
  have h_le : ∑ i ∈ Finset.range (n + 1), (1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) + 1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ))) ≤
              ∑ i ∈ Finset.range (n + 1), (4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi_lt : i < n + 1 := Finset.mem_range.mp hi
    exact summand_ge n i hn hi_lt
  apply le_trans h_le _
  have h_sum_eq : ∑ i ∈ Finset.range (n + 1), (4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) =
                  (4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
                  pairing_sum n / (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · simp
      ring
    · rw [← Finset.sum_div]
      congr 1
  rw [h_sum_eq]
  rw [pairing_sum_eq n]
  rfl

lemma refined_bound_lt_U_diff (n : ℕ) (hn : 2 ≤ n) :
    (4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
    (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) - 2 / ((n : ℝ) + 1) <
    U_seq n - U_seq (n + 1) := by
  have hn_real : (n : ℝ) ≥ 2 := by exact_mod_cast hn
  have h_den1 : -1 + (n : ℝ) * 6 + (n : ℝ)^2 * 6 ≠ 0 := by
    have : 6 * (n : ℝ)^2 + 6 * (n : ℝ) - 1 > 0 := by nlinarith
    linarith
  have h_den2 : -1 + ((1 + n : ℕ) : ℝ) * 6 + ((1 + n : ℕ) : ℝ)^2 * 6 ≠ 0 := by
    have : 6 * (n + 1 : ℝ)^2 + 6 * (n + 1 : ℝ) - 1 > 0 := by nlinarith
    linarith
  have h_den3 : 3 * (n : ℝ) * (72 * (n : ℝ)^9 + 720 * (n : ℝ)^8 + 2964 * (n : ℝ)^7 + 6504 * (n : ℝ)^6 + 8210 * (n : ℝ)^5 + 5952 * (n : ℝ)^4 + 2269 * (n : ℝ)^3 + 310 * (n : ℝ)^2 - 40 * (n : ℝ) - 11) ≠ 0 := by
    linarith
  have h_den4 : 2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1 ≠ 0 := by
    have : 2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1 > 0 := by positivity
    linarith
  have h_den5 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h_den6 : (n : ℝ)^2 + (n : ℝ) ≠ 0 := by positivity
  have h_den7 : (n : ℝ)^2 + 3 * (n : ℝ) + 1 ≠ 0 := by positivity
  have h_den8 : (n : ℝ) ≠ 0 := by positivity
  have h_num_pos : 48*(n:ℝ)^5 + 384*(n:ℝ)^4 + 782*(n:ℝ)^3 + 630*(n:ℝ)^2 + 223*(n:ℝ) + 33 > 0 := by positivity
  have h_den_pos : 3 * (n : ℝ) * (72 * (n : ℝ)^9 + 720 * (n : ℝ)^8 + 2964 * (n : ℝ)^7 + 6504 * (n : ℝ)^6 + 8210 * (n : ℝ)^5 + 5952 * (n : ℝ)^4 + 2269 * (n : ℝ)^3 + 310 * (n : ℝ)^2 - 40 * (n : ℝ) - 11) > 0 := by
    have : 310 * (n : ℝ)^2 - 40 * (n : ℝ) - 11 = 310 * (n : ℝ) * ((n : ℝ) - 2) + 580 * (n : ℝ) - 11 := by ring
    nlinarith
  have h_eq : (U_seq n - U_seq (n + 1)) -
              ((4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
              (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) - 2 / ((n : ℝ) + 1)) =
              (48*(n:ℝ)^5 + 384*(n:ℝ)^4 + 782*(n:ℝ)^3 + 630*(n:ℝ)^2 + 223*(n:ℝ) + 33) /
              (3 * (n : ℝ) * (72 * (n : ℝ)^9 + 720 * (n : ℝ)^8 + 2964 * (n : ℝ)^7 + 6504 * (n : ℝ)^6 + 8210 * (n : ℝ)^5 + 5952 * (n : ℝ)^4 + 2269 * (n : ℝ)^3 + 310 * (n : ℝ)^2 - 40 * (n : ℝ) - 11)) := by
    unfold U_seq
    field_simp [h_den1, h_den2, h_den3, h_den4, h_den5, h_den6, h_den7, h_den8]
    ring
  rw [← sub_pos, h_eq]
  exact div_pos h_num_pos h_den_pos

lemma U_sub_D_decreasing (n : ℕ) (hn : 2 ≤ n) : U_seq (n + 1) - D_seq (n + 1) < U_seq n - D_seq n := by
  have h_harm_n : (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) := by
    rw [harmonic_succ]
    push_cast
    rw [inv_eq_one_div]
  have h_harm_idx : (n + 1) * (n + 1) + (n + 1) - 1 = (n * n + n - 1) + (2 * n + 2) := by
    rcases n with _ | _ | n
    · contradiction
    · contradiction
    · have h1 : (n + 3) * (n + 3) = n * n + 6 * n + 9 := by ring
      have h2 : (n + 2) * (n + 2) = n * n + 4 * n + 4 := by ring
      rw [h1, h2]
      omega
  have h_harm_diff := harmonic_diff_eq_sum (n * n + n - 1) (2 * n + 2)
  rw [← h_harm_idx] at h_harm_diff
  have h_Ico_range : ∑ k ∈ Finset.Ico (n^2 + n : ℕ) (n^2 + 3 * n + 2 : ℕ), (1 / (k : ℝ)) =
                     ∑ i ∈ Finset.range (2 * n + 2), (1 / (((n * n + n - 1 : ℕ) : ℝ) + 1 + (i : ℝ))) := by
    have h_ico_eq : n^2 + 3 * n + 2 = (n^2 + n) + (2 * n + 2) := by omega
    rw [h_ico_eq]
    rw [Finset.sum_Ico_eq_sum_range]
    have h_range_eq : n^2 + n + (2 * n + 2) - (n^2 + n) = 2 * n + 2 := by omega
    rw [h_range_eq]
    apply Finset.sum_congr rfl
    intro i _
    have h_sub_add : n * n + n - 1 + 1 = n * n + n := by omega
    have h_cast : (((n * n + n - 1 : ℕ) : ℝ) + 1) = ((n * n + n : ℕ) : ℝ) := by
      exact_mod_cast h_sub_add
    rw [h_cast]
    push_cast
    ring
  rw [← h_Ico_range] at h_harm_diff
  unfold D_seq
  rw [h_harm_n]
  have h_bound1 := pairing_sum_bound_upper n (by omega)
  have h_bound2 := refined_bound_lt_U_diff n hn
  linarith [h_harm_diff, h_bound1, h_bound2]

lemma tendsto_L_seq_zero : Tendsto L_seq atTop (nhds 0) := by
  have h_eq : L_seq = (fun n : ℕ ↦ 5 * (6 * (n : ℝ)^2 + 6 * (n : ℝ))⁻¹) := by
    ext n; unfold L_seq; ring
  rw [h_eq]
  have h_index : Tendsto (fun n : ℕ ↦ (6 * (n : ℝ)^2 + 6 * (n : ℝ))) atTop atTop := by
    apply tendsto_atTop_mono (f := fun n : ℕ ↦ (n : ℝ))
    · intro n
      rcases n with _ | n
      · simp
      · push_cast; nlinarith
    · exact tendsto_natCast_atTop_atTop
  have h_inv : Tendsto (fun n : ℕ ↦ (6 * (n : ℝ)^2 + 6 * (n : ℝ))⁻¹) atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp h_index
  have h_mul := Tendsto.const_mul (5 : ℝ) h_inv
  rw [mul_zero] at h_mul
  exact h_mul

lemma tendsto_U_seq_zero : Tendsto U_seq atTop (nhds 0) := by
  have h_eq : U_seq = (fun n : ℕ ↦ 5 * (6 * (n : ℝ)^2 + 6 * (n : ℝ) - 1)⁻¹) := by
    ext n; unfold U_seq; ring
  rw [h_eq]
  have h_index : Tendsto (fun n : ℕ ↦ (6 * (n : ℝ)^2 + 6 * (n : ℝ) - 1)) atTop atTop := by
    have h_ineq : (fun n : ℕ ↦ (n : ℝ)) ≤ᶠ[atTop] (fun n : ℕ ↦ (6 * (n : ℝ)^2 + 6 * (n : ℝ) - 1)) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn_real : (n : ℝ) ≥ 1 := by exact_mod_cast hn
      nlinarith
    exact tendsto_atTop_mono' atTop h_ineq tendsto_natCast_atTop_atTop
  have h_inv : Tendsto (fun n : ℕ ↦ (6 * (n : ℝ)^2 + 6 * (n : ℝ) - 1)⁻¹) atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp h_index
  have h_mul := Tendsto.const_mul (5 : ℝ) h_inv
  rw [mul_zero] at h_mul
  exact h_mul

lemma D_seq_gt_L_seq (n : ℕ) (hn : 2 ≤ n) : D_seq n > L_seq n := by
  have h_dec : ∀ k, D_seq (k + 1 + 2) - L_seq (k + 1 + 2) < D_seq (k + 2) - L_seq (k + 2) := by
    intro k
    have h_ineq : 2 ≤ k + 2 := by omega
    have h_step := D_sub_L_decreasing (k + 2) h_ineq
    have h_eq : k + 2 + 1 = k + 1 + 2 := by ring
    rw [h_eq] at h_step
    exact h_step
  have h_lim : Tendsto (fun k ↦ D_seq (k + 2) - L_seq (k + 2)) atTop (nhds 0) := by
    have h1 := tendsto_D_atTop.comp (tendsto_add_atTop_nat 2)
    have h2 := tendsto_L_seq_zero.comp (tendsto_add_atTop_nat 2)
    have h_sub := Tendsto.sub h1 h2
    rw [sub_zero] at h_sub
    exact h_sub
  have h_pos := decreasing_limit_zero_pos (fun k ↦ D_seq (k + 2) - L_seq (k + 2)) h_dec h_lim (n - 2)
  have h_sub_eq : n - 2 + 2 = n := by omega
  rw [h_sub_eq] at h_pos
  linarith

lemma D_seq_lt_U_seq (n : ℕ) (hn : 2 ≤ n) : D_seq n < U_seq n := by
  have h_dec : ∀ k, U_seq (k + 1 + 2) - D_seq (k + 1 + 2) < U_seq (k + 2) - D_seq (k + 2) := by
    intro k
    have h_ineq : 2 ≤ k + 2 := by omega
    have h_step := U_sub_D_decreasing (k + 2) h_ineq
    have h_eq : k + 2 + 1 = k + 1 + 2 := by ring
    rw [h_eq] at h_step
    exact h_step
  have h_lim : Tendsto (fun k ↦ U_seq (k + 2) - D_seq (k + 2)) atTop (nhds 0) := by
    have h1 := tendsto_U_seq_zero.comp (tendsto_add_atTop_nat 2)
    have h2 := tendsto_D_atTop.comp (tendsto_add_atTop_nat 2)
    have h_sub := Tendsto.sub h1 h2
    rw [sub_zero] at h_sub
    exact h_sub
  have h_pos := decreasing_limit_zero_pos (fun k ↦ U_seq (k + 2) - D_seq (k + 2)) h_dec h_lim (n - 2)
  have h_sub_eq : n - 2 + 2 = n := by omega
  rw [h_sub_eq] at h_pos
  linarith

def u_formula (n : ℕ) : ℤ :=
  (6 * (n : ℤ)^2 + 18 * (n : ℤ) + 11) / 5

def E_recurrence : LinearRecurrence ℤ :=
  { order := 7, coeffs := ![1, -2, 1, 0, 0, -1, 2] }

lemma recurrence_formula_add (k : ℕ) :
    (6 * ((k+7 : ℕ) : ℤ)^2 + 18 * ((k+7 : ℕ) : ℤ) + 11) / 5 +
    2 * ((6 * ((k+1 : ℕ) : ℤ)^2 + 18 * ((k+1 : ℕ) : ℤ) + 11) / 5) +
    ((6 * ((k+5 : ℕ) : ℤ)^2 + 18 * ((k+5 : ℕ) : ℤ) + 11) / 5) =
    (6 * ((k : ℕ) : ℤ)^2 + 18 * ((k : ℕ) : ℤ) + 11) / 5 +
    2 * ((6 * ((k+6 : ℕ) : ℤ)^2 + 18 * ((k+6 : ℕ) : ℤ) + 11) / 5) +
    ((6 * ((k+2 : ℕ) : ℤ)^2 + 18 * ((k+2 : ℕ) : ℤ) + 11) / 5) := by
  have h_mod : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  rcases h_mod with h | h | h | h | h
  · have : k = 5 * (k / 5) := by omega
    generalize hq : k / 5 = q
    rw [hq] at this
    subst k
    push_cast
    have h_0_0 : 6 * (5 * (q:ℤ))^2 + 18 * (5 * (q:ℤ)) + 11 = 5 * (30 * (q:ℤ)^2 + 18 * (q:ℤ) + 2) + 1 := by ring
    rw [h_0_0]
    have h_0_1 : 6 * (5 * (q:ℤ) + 1)^2 + 18 * (5 * (q:ℤ) + 1) + 11 = 5 * (30 * (q:ℤ)^2 + 30 * (q:ℤ) + 7) + 0 := by ring
    rw [h_0_1]
    have h_0_2 : 6 * (5 * (q:ℤ) + 2)^2 + 18 * (5 * (q:ℤ) + 2) + 11 = 5 * (30 * (q:ℤ)^2 + 42 * (q:ℤ) + 14) + 1 := by ring
    rw [h_0_2]
    have h_0_5 : 6 * (5 * (q:ℤ) + 5)^2 + 18 * (5 * (q:ℤ) + 5) + 11 = 5 * (30 * (q:ℤ)^2 + 78 * (q:ℤ) + 50) + 1 := by ring
    rw [h_0_5]
    have h_0_6 : 6 * (5 * (q:ℤ) + 6)^2 + 18 * (5 * (q:ℤ) + 6) + 11 = 5 * (30 * (q:ℤ)^2 + 90 * (q:ℤ) + 67) + 0 := by ring
    rw [h_0_6]
    have h_0_7 : 6 * (5 * (q:ℤ) + 7)^2 + 18 * (5 * (q:ℤ) + 7) + 11 = 5 * (30 * (q:ℤ)^2 + 102 * (q:ℤ) + 86) + 1 := by ring
    rw [h_0_7]
    omega
  · have : k = 5 * (k / 5) + 1 := by omega
    generalize hq : k / 5 = q
    rw [hq] at this
    subst k
    push_cast
    have h_1_0 : 6 * (5 * (q:ℤ) + 1)^2 + 18 * (5 * (q:ℤ) + 1) + 11 = 5 * (30 * (q:ℤ)^2 + 30 * (q:ℤ) + 7) + 0 := by ring
    rw [h_1_0]
    have h_1_1 : 6 * (5 * (q:ℤ) + 1 + 1)^2 + 18 * (5 * (q:ℤ) + 1 + 1) + 11 = 5 * (30 * (q:ℤ)^2 + 42 * (q:ℤ) + 14) + 1 := by ring
    rw [h_1_1]
    have h_1_2 : 6 * (5 * (q:ℤ) + 1 + 2)^2 + 18 * (5 * (q:ℤ) + 1 + 2) + 11 = 5 * (30 * (q:ℤ)^2 + 54 * (q:ℤ) + 23) + 4 := by ring
    rw [h_1_2]
    have h_1_5 : 6 * (5 * (q:ℤ) + 1 + 5)^2 + 18 * (5 * (q:ℤ) + 1 + 5) + 11 = 5 * (30 * (q:ℤ)^2 + 90 * (q:ℤ) + 67) + 0 := by ring
    rw [h_1_5]
    have h_1_6 : 6 * (5 * (q:ℤ) + 1 + 6)^2 + 18 * (5 * (q:ℤ) + 1 + 6) + 11 = 5 * (30 * (q:ℤ)^2 + 102 * (q:ℤ) + 86) + 1 := by ring
    rw [h_1_6]
    have h_1_7 : 6 * (5 * (q:ℤ) + 1 + 7)^2 + 18 * (5 * (q:ℤ) + 1 + 7) + 11 = 5 * (30 * (q:ℤ)^2 + 114 * (q:ℤ) + 107) + 4 := by ring
    rw [h_1_7]
    omega
  · have : k = 5 * (k / 5) + 2 := by omega
    generalize hq : k / 5 = q
    rw [hq] at this
    subst k
    push_cast
    have h_2_0 : 6 * (5 * (q:ℤ) + 2)^2 + 18 * (5 * (q:ℤ) + 2) + 11 = 5 * (30 * (q:ℤ)^2 + 42 * (q:ℤ) + 14) + 1 := by ring
    rw [h_2_0]
    have h_2_1 : 6 * (5 * (q:ℤ) + 2 + 1)^2 + 18 * (5 * (q:ℤ) + 2 + 1) + 11 = 5 * (30 * (q:ℤ)^2 + 54 * (q:ℤ) + 23) + 4 := by ring
    rw [h_2_1]
    have h_2_2 : 6 * (5 * (q:ℤ) + 2 + 2)^2 + 18 * (5 * (q:ℤ) + 2 + 2) + 11 = 5 * (30 * (q:ℤ)^2 + 66 * (q:ℤ) + 35) + 4 := by ring
    rw [h_2_2]
    have h_2_5 : 6 * (5 * (q:ℤ) + 2 + 5)^2 + 18 * (5 * (q:ℤ) + 2 + 5) + 11 = 5 * (30 * (q:ℤ)^2 + 102 * (q:ℤ) + 86) + 1 := by ring
    rw [h_2_5]
    have h_2_6 : 6 * (5 * (q:ℤ) + 2 + 6)^2 + 18 * (5 * (q:ℤ) + 2 + 6) + 11 = 5 * (30 * (q:ℤ)^2 + 114 * (q:ℤ) + 107) + 4 := by ring
    rw [h_2_6]
    have h_2_7 : 6 * (5 * (q:ℤ) + 2 + 7)^2 + 18 * (5 * (q:ℤ) + 2 + 7) + 11 = 5 * (30 * (q:ℤ)^2 + 126 * (q:ℤ) + 131) + 4 := by ring
    rw [h_2_7]
    omega
  · have : k = 5 * (k / 5) + 3 := by omega
    generalize hq : k / 5 = q
    rw [hq] at this
    subst k
    push_cast
    have h_3_0 : 6 * (5 * (q:ℤ) + 3)^2 + 18 * (5 * (q:ℤ) + 3) + 11 = 5 * (30 * (q:ℤ)^2 + 54 * (q:ℤ) + 23) + 4 := by ring
    rw [h_3_0]
    have h_3_1 : 6 * (5 * (q:ℤ) + 3 + 1)^2 + 18 * (5 * (q:ℤ) + 3 + 1) + 11 = 5 * (30 * (q:ℤ)^2 + 66 * (q:ℤ) + 35) + 4 := by ring
    rw [h_3_1]
    have h_3_2 : 6 * (5 * (q:ℤ) + 3 + 2)^2 + 18 * (5 * (q:ℤ) + 3 + 2) + 11 = 5 * (30 * (q:ℤ)^2 + 78 * (q:ℤ) + 50) + 1 := by ring
    rw [h_3_2]
    have h_3_5 : 6 * (5 * (q:ℤ) + 3 + 5)^2 + 18 * (5 * (q:ℤ) + 3 + 5) + 11 = 5 * (30 * (q:ℤ)^2 + 114 * (q:ℤ) + 107) + 4 := by ring
    rw [h_3_5]
    have h_3_6 : 6 * (5 * (q:ℤ) + 3 + 6)^2 + 18 * (5 * (q:ℤ) + 3 + 6) + 11 = 5 * (30 * (q:ℤ)^2 + 126 * (q:ℤ) + 131) + 4 := by ring
    rw [h_3_6]
    have h_3_7 : 6 * (5 * (q:ℤ) + 3 + 7)^2 + 18 * (5 * (q:ℤ) + 3 + 7) + 11 = 5 * (30 * (q:ℤ)^2 + 138 * (q:ℤ) + 158) + 1 := by ring
    rw [h_3_7]
    omega
  · have : k = 5 * (k / 5) + 4 := by omega
    generalize hq : k / 5 = q
    rw [hq] at this
    subst k
    push_cast
    have h_4_0 : 6 * (5 * (q:ℤ) + 4)^2 + 18 * (5 * (q:ℤ) + 4) + 11 = 5 * (30 * (q:ℤ)^2 + 66 * (q:ℤ) + 35) + 4 := by ring
    rw [h_4_0]
    have h_4_1 : 6 * (5 * (q:ℤ) + 4 + 1)^2 + 18 * (5 * (q:ℤ) + 4 + 1) + 11 = 5 * (30 * (q:ℤ)^2 + 78 * (q:ℤ) + 50) + 1 := by ring
    rw [h_4_1]
    have h_4_2 : 6 * (5 * (q:ℤ) + 4 + 2)^2 + 18 * (5 * (q:ℤ) + 4 + 2) + 11 = 5 * (30 * (q:ℤ)^2 + 90 * (q:ℤ) + 67) + 0 := by ring
    rw [h_4_2]
    have h_4_5 : 6 * (5 * (q:ℤ) + 4 + 5)^2 + 18 * (5 * (q:ℤ) + 4 + 5) + 11 = 5 * (30 * (q:ℤ)^2 + 126 * (q:ℤ) + 131) + 4 := by ring
    rw [h_4_5]
    have h_4_6 : 6 * (5 * (q:ℤ) + 4 + 6)^2 + 18 * (5 * (q:ℤ) + 4 + 6) + 11 = 5 * (30 * (q:ℤ)^2 + 138 * (q:ℤ) + 158) + 1 := by ring
    rw [h_4_6]
    have h_4_7 : 6 * (5 * (q:ℤ) + 4 + 7)^2 + 18 * (5 * (q:ℤ) + 4 + 7) + 11 = 5 * (30 * (q:ℤ)^2 + 150 * (q:ℤ) + 187) + 0 := by ring
    rw [h_4_7]
    omega

lemma u_is_solution : E_recurrence.IsSolution u_formula := by
  intro n
  dsimp [u_formula, E_recurrence]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  simp only [Nat.reduceAdd]
  linarith [recurrence_formula_add n]

lemma u_formula_init (n : Fin 7) : u_formula n = (![2, 7, 14, 23, 35, 50, 67] : Fin 7 → ℤ) n := by
  fin_cases n <;> rfl

lemma A227582_base_eq_u_formula (k : ℕ) : A227582_base k = u_formula k := by
  have h : A227582_base k = E_recurrence.mkSol ![2, 7, 14, 23, 35, 50, 67] k := rfl
  rw [h]
  have h_eq : u_formula = E_recurrence.mkSol ![2, 7, 14, 23, 35, 50, 67] := by
    apply LinearRecurrence.eq_mk_of_is_sol_of_eq_init'
    · exact u_is_solution
    · exact u_formula_init
  rw [← h_eq]

lemma int_div_le_real_div (A : ℤ) (B : ℤ) (hB : B > 0) :
    ((A / B : ℤ) : ℝ) ≤ (A : ℝ) / (B : ℝ) := by
  have h_eq : A = B * (A / B) + A % B := by
    exact (Int.ediv_add_emod A B).symm
  have h_mod_ge : A % B ≥ 0 := Int.emod_nonneg A (by linarith)
  have h_le : B * (A / B) ≤ A := by linarith
  have h_cast : ((B * (A / B) : ℤ) : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast h_le
  push_cast at h_cast
  have hB_real : (B : ℝ) > 0 := by positivity
  rw [le_div_iff₀ hB_real]
  linarith

lemma real_div_add_one_fifth_lt_int_div_add_one (M : ℤ) :
    (M : ℝ) / 5 + 1 / 5 ≤ ((M / 5 : ℤ) : ℝ) + 1 := by
  have h_eq : M = 5 * (M / 5) + M % 5 := by
    exact (Int.ediv_add_emod M 5).symm
  have h_mod_ge : M % 5 ≥ 0 := Int.emod_nonneg M (by norm_num)
  have h_mod_lt : M % 5 < 5 := Int.emod_lt M (by norm_num)
  have h_mod_le4 : M % 5 ≤ 4 := by omega
  have h_le' : M + 1 ≤ 5 * (M / 5 + 1) := by linarith
  have h_cast : ((M + 1 : ℤ) : ℝ) ≤ ((5 * (M / 5 + 1) : ℤ) : ℝ) := by
    exact_mod_cast h_le'
  push_cast at h_cast
  linarith

theorem oeis_227582_conjecture_0 (n : ℕ) (hn : 0 < n) :
    a n = (Int.floor
      (1 / (2 * (↑(harmonic n) : ℝ) -
            (↑(harmonic (n * n + n - 1)) : ℝ) -
            Real.eulerMascheroniConstant))).toNat := by
  rcases n with _ | n
  · contradiction
  rcases n with _ | n
  · have h_lhs : a 1 = 2 := by
      dsimp [a, A227582_base]
      rw [LinearRecurrence.mkSol]
      simp
    rw [h_lhs]
    have h_harm1 : (harmonic 1 : ℝ) = 1 := by
      simp [harmonic]
    have h_idx1 : 1 * 1 + 1 - 1 = 1 := by rfl
    rw [h_idx1]
    rw [h_harm1]
    have h_denom : 2 * (1 : ℝ) - 1 - Real.eulerMascheroniConstant = 1 - Real.eulerMascheroniConstant := by ring
    rw [h_denom]
    have h_floor : Int.floor (1 / (1 - Real.eulerMascheroniConstant)) = 2 := by
      rw [Int.floor_eq_iff]
      simp
      have h_gamma_ub := Real.eulerMascheroniConstant_lt_two_thirds
      have h_gamma_lb := Real.one_half_lt_eulerMascheroniConstant
      constructor
      · have h_pos : 0 < 1 - Real.eulerMascheroniConstant := by linarith
        rw [inv_eq_one_div]
        rw [le_div_iff₀ h_pos]
        linarith
      · have h_pos : 0 < 1 - Real.eulerMascheroniConstant := by linarith
        rw [inv_eq_one_div]
        rw [div_lt_iff₀ h_pos]
        linarith
    rw [h_floor]
    rfl
  · have hn_ge : 2 ≤ n + 2 := by omega
    have h_D_pos : D_seq (n + 2) > 0 := by
      have : D_seq (n + 2) > L_seq (n + 2) := D_seq_gt_L_seq (n + 2) hn_ge
      have : L_seq (n + 2) > 0 := by
        unfold L_seq
        positivity
      linarith
    have h_U_pos : U_seq (n + 2) > 0 := by
      unfold U_seq
      have hn_real : ((n + 2 : ℕ) : ℝ) ≥ 2 := by exact_mod_cast hn_ge
      have h_denom_pos : 6 * ((n + 2 : ℕ) : ℝ)^2 + 6 * ((n + 2 : ℕ) : ℝ) - 1 > 0 := by nlinarith
      exact div_pos (by norm_num) h_denom_pos
    have h_lt : D_seq (n + 2) < U_seq (n + 2) := D_seq_lt_U_seq (n + 2) hn_ge
    have h_gt : D_seq (n + 2) > L_seq (n + 2) := D_seq_gt_L_seq (n + 2) hn_ge

    have h_rec_lt : 1 / D_seq (n + 2) < 1 / L_seq (n + 2) := by
      have hL : L_seq (n + 2) > 0 := by unfold L_seq; positivity
      rw [one_div, one_div, inv_lt_inv₀ h_D_pos hL]
      exact h_gt
    have h_rec_gt : 1 / D_seq (n + 2) > 1 / U_seq (n + 2) := by
      have hU : U_seq (n + 2) > 0 := by
        unfold U_seq
        have hn_real : ((n + 2 : ℕ) : ℝ) ≥ 2 := by exact_mod_cast hn_ge
        have h_denom_pos : 6 * ((n + 2 : ℕ) : ℝ)^2 + 6 * ((n + 2 : ℕ) : ℝ) - 1 > 0 := by nlinarith
        exact div_pos (by norm_num) h_denom_pos
      rw [gt_iff_lt, one_div, one_div, inv_lt_inv₀ hU h_D_pos]
      exact h_lt

    have h_one_div_L : 1 / L_seq (n + 2) = (6 * (n + 2 : ℝ)^2 + 6 * (n + 2 : ℝ)) / 5 := by
      unfold L_seq
      have : 6 * (n + 2 : ℝ)^2 + 6 * (n + 2 : ℝ) > 0 := by positivity
      have : 6 * (n + 2 : ℝ)^2 + 6 * (n + 2 : ℝ) ≠ 0 := by linarith
      field_simp
      push_cast
      ring
    have h_one_div_U : 1 / U_seq (n + 2) = (6 * (n + 2 : ℝ)^2 + 6 * (n + 2 : ℝ) - 1) / 5 := by
      unfold U_seq
      have hn_real : (n + 2 : ℝ) ≥ 2 := by exact_mod_cast hn_ge
      have : 6 * (n + 2 : ℝ)^2 + 6 * (n + 2 : ℝ) - 1 > 0 := by nlinarith
      have : 6 * (n + 2 : ℝ)^2 + 6 * (n + 2 : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      push_cast
      ring

    rw [h_one_div_L] at h_rec_lt
    rw [h_one_div_U] at h_rec_gt

    generalize hM : (6 * (n + 2 : ℤ)^2 + 6 * (n + 2 : ℤ) - 1) = M
    have hM_real : (6 * (n + 2 : ℝ)^2 + 6 * (n + 2 : ℝ) - 1) = (M : ℝ) := by
      push_cast [← hM]
      ring
    have hM_plus1_real : (6 * (n + 2 : ℝ)^2 + 6 * (n + 2 : ℝ)) = (M : ℝ) + 1 := by
      push_cast [← hM]
      ring

    rw [hM_real] at h_rec_gt
    rw [hM_plus1_real] at h_rec_lt

    have h_div_L : ((M : ℝ) + 1) / 5 = (M : ℝ) / 5 + 1 / 5 := by ring
    rw [h_div_L] at h_rec_lt

    have h_floor_gt : 1 / D_seq (n + 2) > ((M / 5 : ℤ) : ℝ) := by
      have h_int_le := int_div_le_real_div M 5 (by norm_num)
      linarith
    have h_floor_lt : 1 / D_seq (n + 2) < ((M / 5 : ℤ) : ℝ) + 1 := by
      have h_int_gt := real_div_add_one_fifth_lt_int_div_add_one M
      linarith

    have h_floor_eq : Int.floor (1 / D_seq (n + 2)) = M / 5 := by
      rw [Int.floor_eq_iff]
      constructor
      · linarith
      · linarith

    have h_formula_eq : u_formula (n + 1) = M / 5 := by
      unfold u_formula
      have h_algebra : 6 * ((n + 1 : ℕ) : ℤ)^2 + 18 * ((n + 1 : ℕ) : ℤ) + 11 = 6 * (n + 2 : ℤ)^2 + 6 * (n + 2 : ℤ) - 1 := by
        push_cast; ring
      rw [h_algebra, hM]

    have h_a_eq : a (n + 2) = (u_formula (n + 1)).toNat := by
      unfold a
      have h_cond : 0 < n + 2 := by omega
      rw [dif_pos h_cond]
      have h_sub : n + 2 - 1 = n + 1 := by omega
      rw [h_sub]
      rw [A227582_base_eq_u_formula]

    unfold D_seq at h_floor_eq
    rw [h_a_eq]
    rw [h_floor_eq]
    rw [h_formula_eq]
