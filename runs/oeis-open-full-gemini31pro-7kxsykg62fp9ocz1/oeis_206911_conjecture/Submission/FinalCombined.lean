import Submission.Spec
import Mathlib
open Real Finset Filter Topology Nat


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



-- 1. Helper lemmas from TestExpBound2
lemma bound_add_helper (x y : ℝ) (hy : y * (1 + x) = x) :
    let A_minus_1 := y + y^2/2 + y^3/6 + y^4/24
    let B := 1 + x + x^2/2 + x^3/6 + 5/96 * x^4
    (A_minus_1 * B + 1 - B) * (2304 * (1+x)^4) = 85*x^8 + 292*x^7 + 580*x^6 + 504*x^5 + 168*x^4 := by
  intro A_minus_1 B
  have hy2 : y^2 * (1+x)^2 = x^2 := by
    calc y^2 * (1+x)^2 = (y * (1+x)) * (y * (1+x)) := by ring
    _ = x * x := by rw [hy]
    _ = x^2 := by ring
  have hy3 : y^3 * (1+x)^3 = x^3 := by
    calc y^3 * (1+x)^3 = (y * (1+x)) * (y * (1+x)) * (y * (1+x)) := by ring
    _ = x * x * x := by rw [hy]
    _ = x^3 := by ring
  have hy4 : y^4 * (1+x)^4 = x^4 := by
    calc y^4 * (1+x)^4 = (y * (1+x)) * (y * (1+x)) * (y * (1+x)) * (y * (1+x)) := by ring
    _ = x * x * x * x := by rw [hy]
    _ = x^4 := by ring
  have h_A : A_minus_1 * 24 * (1+x)^4 = 24 * x * (1+x)^3 + 12 * x^2 * (1+x)^2 + 4 * x^3 * (1+x) + x^4 := by
    calc
      A_minus_1 * 24 * (1+x)^4 = 24 * (y * (1+x) * (1+x)^3) + 12 * (y^2 * (1+x)^2 * (1+x)^2) + 4 * (y^3 * (1+x)^3 * (1+x)) + (y^4 * (1+x)^4) := by
        dsimp [A_minus_1]
        ring
      _ = 24 * (x * (1+x)^3) + 12 * (x^2 * (1+x)^2) + 4 * (x^3 * (1+x)) + x^4 := by rw [hy, hy2, hy3, hy4]
      _ = 24 * x * (1+x)^3 + 12 * x^2 * (1+x)^2 + 4 * x^3 * (1+x) + x^4 := by ring
  have h_full : (A_minus_1 * B + 1 - B) * (2304 * (1+x)^4) = (A_minus_1 * 24 * (1+x)^4) * (96 * B) + 2304 * (1+x)^4 * (1 - B) := by ring
  rw [h_full, h_A]
  dsimp [B]
  ring

lemma exp_lower_bound (x : ℝ) (hx : 0 ≤ x) :
    1 + x/(1+x) + (x/(1+x))^2/2 + (x/(1+x))^3/6 + (x/(1+x))^4/24 ≤ exp (x / (1 + x)) := by
  have H := sum_le_exp_of_nonneg (x := x / (1 + x)) (by positivity) 5
  have h_eq : ∑ i ∈ range 5, (x / (1 + x)) ^ i / (Nat.factorial i : ℝ) = 1 + x/(1+x) + (x/(1+x))^2/2 + (x/(1+x))^3/6 + (x/(1+x))^4/24 := by
    simp [sum_range_succ]
    ring
  rwa [h_eq] at H

lemma exp_upper_bound (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    exp x ≤ 1 + x + x^2/2 + x^3/6 + 5/96 * x^4 := by
  have H := exp_bound (x := x) (by exact (abs_le.mpr ⟨by linarith, hx1⟩)) (n := 4) (by decide)
  have h_eq : ∑ m ∈ range 4, x ^ m / (Nat.factorial m : ℝ) = 1 + x + x^2/2 + x^3/6 := by
    simp [sum_range_succ]
    ring
  rw [h_eq] at H
  have : (4 : ℕ).succ = 5 := rfl
  rw [this] at H
  have : ((4 : ℕ).factorial : ℝ) = 24 := rfl
  rw [this] at H
  have h_abs : |x| = x := abs_of_nonneg hx0
  rw [h_abs] at H
  have H_le := (le_abs_self _).trans H
  linarith

lemma exp_neg_lower_bound (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + x + x^2/2 + x^3/6 + 5/96 * x^4)⁻¹ ≤ exp (-x) := by
  have := exp_upper_bound x hx0 hx1
  have hB_pos : 0 < 1 + x + x^2/2 + x^3/6 + 5/96 * x^4 := by
    have hexp := exp_pos x
    linarith
  rw [exp_neg]
  exact (inv_le_inv₀ hB_pos (exp_pos x)).mpr this

lemma bound_add (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1/2) :
    2 < exp (x / (1 + x)) + exp (-x) := by
  let A := 1 + x/(1+x) + (x/(1+x))^2/2 + (x/(1+x))^3/6 + (x/(1+x))^4/24
  let B := 1 + x + x^2/2 + x^3/6 + 5/96 * x^4
  have H1 : A ≤ exp (x / (1 + x)) := exp_lower_bound x hx0.le
  have H2 : B⁻¹ ≤ exp (-x) := exp_neg_lower_bound x hx0.le (by linarith)
  have H_le : A + B⁻¹ ≤ exp (x / (1 + x)) + exp (-x) := add_le_add H1 H2
  have h_pos : 0 < B := by
    dsimp [B]; positivity
  have h_alg : ((A - 1) * B + 1 - B) * (2304 * (1+x)^4) = 85*x^8 + 292*x^7 + 580*x^6 + 504*x^5 + 168*x^4 := by
    have hy : (x / (1+x)) * (1+x) = x := div_mul_cancel₀ x (by positivity)
    have H_helper := bound_add_helper x (x / (1+x)) hy
    dsimp at H_helper
    have h_eq : A - 1 = x / (1 + x) + (x / (1 + x)) ^ 2 / 2 + (x / (1 + x)) ^ 3 / 6 + (x / (1 + x)) ^ 4 / 24 := by
      dsimp [A]
      ring
    rw [h_eq]
    exact H_helper
  have h_alg_pos : 0 < ((A - 1) * B + 1 - B) * (2304 * (1+x)^4) := by
    rw [h_alg]
    positivity
  have h_pos2 : 0 < 2304 * (1+x)^4 := by positivity
  have h_A_B : 0 < (A - 1) * B + 1 - B := pos_of_mul_pos_left h_alg_pos h_pos2.le
  have h_A_B2 : B - 1 < (A - 1) * B := by linarith
  have h_A_B3 : (B - 1) / B < A - 1 := by
    rwa [div_lt_iff₀ h_pos]
  have H_gt : 2 < A + B⁻¹ := by
    have : (B - 1) / B = 1 - B⁻¹ := by
      rw [sub_div, div_self h_pos.ne.symm, one_div]
    rw [this] at h_A_B3
    linarith
  exact H_gt.trans_le H_le

lemma c_ratio (x : ℝ) (h_bound : 2 < exp (x / (1 + x)) + exp (-x)) :
    exp x - 1 < exp x * (exp (x / (1 + x)) - 1) := by
  have H1 : exp x * (2 - exp (-x)) < exp x * exp (x / (1 + x)) := by
    apply mul_lt_mul_of_pos_left
    · linarith
    · exact exp_pos x
  have h_eq : exp x * (2 - exp (-x)) = 2 * exp x - 1 := by
    rw [mul_sub, ← exp_add]
    have : x + -x = 0 := add_neg_cancel x
    rw [this, exp_zero]
    ring
  rw [h_eq] at H1
  linarith

lemma c_mono (n : ℕ) (hn : 1 ≤ n) : exp (harmonic n) * (exp (1 / (n + 1 : ℝ)) - 1) < exp (harmonic (n + 1)) * (exp (1 / (n + 2 : ℝ)) - 1) := by
  have H := c_ratio (1 / (n + 1 : ℝ)) (bound_add (1 / (n + 1 : ℝ)) (by positivity) (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (2 : ℝ) ≤ n + 1 := by linarith
    exact one_div_le_one_div_of_le (by norm_num) this
  ))
  have h_eq : (1 / (n + 1 : ℝ)) / (1 + 1 / (n + 1 : ℝ)) = 1 / (n + 2 : ℝ) := by
    have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
    have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
    have hn3 : 1 + 1 / (n + 1 : ℝ) ≠ 0 := by positivity
    apply mul_right_cancel₀ hn3
    rw [div_mul_cancel₀ _ hn3]
    apply mul_left_cancel₀ hn2
    rw [← mul_assoc, mul_div_cancel₀ 1 hn2, one_mul]
    have : (n + 2 : ℝ) = (n + 1 : ℝ) + 1 := by ring
    rw [this, add_mul, mul_one_div_cancel hn1]
    ring
  rw [h_eq] at H
  have h_harm : (harmonic (n + 1) : ℝ) = harmonic n + 1 / (n + 1 : ℝ) := by
    rw [harmonic_succ]; push_cast; rw [one_div]
  rw [h_harm, exp_add]
  calc
    exp (harmonic n) * (exp (1 / (n + 1 : ℝ)) - 1) < exp (harmonic n) * (exp (1 / (n + 1 : ℝ)) * (exp (1 / (n + 2 : ℝ)) - 1)) := by
      apply mul_lt_mul_of_pos_left H (exp_pos _)
    _ = exp (harmonic n) * exp (1 / (n + 1 : ℝ)) * (exp (1 / (n + 2 : ℝ)) - 1) := by ring



lemma limit_bounds (E : ℝ) (hE1 : 16/9 < E) (hE2 : E < 41/23) :
    35/10 < (E - 1) / (2 - E) ∧ (E - 1) / (2 - E) < 36/10 := by
  have : 2 - E > 0 := by linarith
  constructor
  · rw [lt_div_iff₀ this]
    linarith
  · rw [div_lt_iff₀ this]
    linarith
