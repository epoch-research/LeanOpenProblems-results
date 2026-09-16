import Submission.Spec
import Submission.A206911_eq

open Real Nat Finset Filter Topology

lemma tendsto_A206911_1_div_N : Tendsto (fun N : ℕ => (A206911 1 : ℝ) / N) atTop (nhds 0) := by
  have : (fun N : ℕ => (A206911 1 : ℝ) / N) = fun N : ℕ => (A206911 1 : ℝ) * (N : ℝ)⁻¹ := by
    ext N
    rw [div_eq_mul_inv]
  rw [this]
  have hz := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := hz.const_mul (A206911 1 : ℝ)
  rwa [mul_zero] at h

lemma tendsto_sum_div_N (h_mono : Monotone A206911) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    Tendsto (fun N : ℕ => ((range N).sum (fun n => A206911_diff (n + 1)) : ℝ) / N) atTop (nhds (1 + exp eulerMascheroniConstant)) := by
  have H := tendsto_A206911_succ_div_N.sub tendsto_A206911_1_div_N
  rw [sub_zero] at H
  apply Tendsto.congr' _ H
  filter_upwards [] with N
  rw [sum_diff_eq N h_mono]
  push_cast
  rw [sub_div]

lemma tendsto_c3_div_N (h_mono : Monotone A206911) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / N) atTop (nhds (exp eulerMascheroniConstant - 1)) := by
  have H := (tendsto_sum_div_N h_mono h23).sub_const 2
  have eq : 1 + exp eulerMascheroniConstant - 2 = exp eulerMascheroniConstant - 1 := by ring
  rw [eq] at H
  apply Tendsto.congr' _ H
  filter_upwards [eventually_ne_atTop 0] with N hn
  rw [count_3s_eq N h_mono h23]
  push_cast
  rw [sum_diff_eq N h_mono]
  push_cast
  rw [sub_div, sub_div, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hn)]

lemma tendsto_c2_div_N (h_mono : Monotone A206911) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    Tendsto (fun N : ℕ => (A206911_count_2s N : ℝ) / N) atTop (nhds (2 - exp eulerMascheroniConstant)) := by
  have H := (tendsto_const_nhds (a := (3 : ℝ))).sub (tendsto_sum_div_N h_mono h23)
  have eq : 3 - (1 + exp eulerMascheroniConstant) = 2 - exp eulerMascheroniConstant := by ring
  rw [eq] at H
  apply Tendsto.congr' _ H
  filter_upwards [eventually_ne_atTop 0] with N hn
  rw [count_2s_eq N h_mono h23]
  push_cast
  rw [sum_diff_eq N h_mono]
  push_cast
  rw [sub_div, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hn)]

