import FormalConjecturesUtil

/-! An exact diagnostic for a generating-function proof strategy. This does
not prove or disprove Erdős 972. -/
namespace Erdos972GeneratingCoefficientGap

open Polynomial Filter
open scoped Topology

noncomputable section

def model (k : ℕ) : ℝ[X] := (1 + X) ^ k * X ^ 2

def trimmed (k : ℕ) : ℝ[X] := model k - X ^ 2

lemma model_coeff_two (k : ℕ) : (model k).coeff 2 = 1 := by
  simp [model, coeff_mul_X_pow', coeff_one_add_X_pow]

lemma trimmed_coeff_two (k : ℕ) : (trimmed k).coeff 2 = 0 := by
  simp [trimmed, model_coeff_two]

lemma model_coeff_nonneg (k n : ℕ) : 0 ≤ (model k).coeff n := by
  simp only [model, coeff_mul_X_pow']
  split_ifs
  · rw [coeff_one_add_X_pow]
    positivity
  · exact le_rfl

lemma trimmed_coeff_nonneg (k n : ℕ) : 0 ≤ (trimmed k).coeff n := by
  by_cases h : n = 2
  · subst n
    rw [trimmed_coeff_two]
  · simpa [trimmed, coeff_X_pow, h, Ne.symm h] using model_coeff_nonneg k n

lemma eval_ratio (k : ℕ) {t : ℝ} (ht : 0 < t) :
    (trimmed k).eval t / (model k).eval t = 1 - ((1 + t)⁻¹) ^ k := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hp0 : 1 + t ≠ 0 := ne_of_gt (by linarith)
  simp only [trimmed, model, eval_sub, eval_mul, eval_pow, eval_add, eval_one, eval_X]
  rw [inv_pow]
  field_simp

/-- The ratio tends to one at every fixed positive parameter, even though
the degree-two coefficient has been completely removed. -/
theorem fixed_positive_asymptotic {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k : ℕ => (trimmed k).eval t / (model k).eval t)
      atTop (𝓝 1) := by
  have hpos : 0 < 1 + t := by linarith
  have hsmall : (1 + t)⁻¹ < (1 : ℝ) := by
    apply (inv_lt_one₀ hpos).mpr
    linarith
  have hzero := tendsto_pow_atTop_nhds_zero_of_lt_one
    (inv_nonneg.mpr hpos.le) hsmall
  have hlim : Tendsto (fun k : ℕ => (1 : ℝ) - ((1 + t)⁻¹) ^ k)
      atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hzero
  simpa only [sub_zero] using
    hlim.congr (fun k => (eval_ratio k ht).symm)

lemma ratio_bounds (k : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ (trimmed k).eval t / (model k).eval t ∧
    (trimmed k).eval t / (model k).eval t ≤ (k : ℝ) * t := by
  rw [eval_ratio k ht]
  have hpos : 0 < 1 + t := by linarith
  have hr0 : 0 ≤ (1 + t)⁻¹ := inv_nonneg.mpr hpos.le
  have hr1 : (1 + t)⁻¹ ≤ (1 : ℝ) := (inv_le_one₀ hpos).mpr (by linarith)
  have hpow : ((1 + t)⁻¹) ^ k ≤ 1 := pow_le_one₀ hr0 hr1
  have hbern := one_add_mul_le_pow
    (a := (1 + t)⁻¹ - 1) (by linarith : -2 ≤ (1 + t)⁻¹ - 1) k
  simp only [add_sub_cancel] at hbern
  have hid : 1 - (1 + t)⁻¹ = t / (1 + t) := by
    field_simp
    ring
  have hd : 1 - (1 + t)⁻¹ ≤ t := by
    rw [hid]
    apply (div_le_iff₀ hpos).mpr
    nlinarith [sq_nonneg t]
  refine ⟨sub_nonneg.mpr hpow, le_trans ?_ (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg k))⟩
  nlinarith

/-- A positive parameter tending to zero can instead make the ratio tend
to zero. Thus the preceding fixed-parameter limit is not uniform near zero. -/
theorem shrinking_parameter_asymptotic :
    Tendsto (fun k : ℕ =>
      (trimmed k).eval (1 / ((k : ℝ) + 1) ^ 2) /
        (model k).eval (1 / ((k : ℝ) + 1) ^ 2)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  apply squeeze_zero (fun k => (ratio_bounds k (by positivity)).1) ?_ hupper
  intro k
  refine (ratio_bounds k (by positivity)).2.trans ?_
  have hk : 0 < (k : ℝ) + 1 := by positivity
  apply (le_div_iff₀ hk).mpr
  have hid : (k : ℝ) * (1 / ((k : ℝ) + 1) ^ 2) * ((k : ℝ) + 1) =
      (k : ℝ) / ((k : ℝ) + 1) := by
    field_simp
  rw [hid]
  apply (div_le_one hk).mpr
  linarith

#print axioms trimmed_coeff_nonneg
#print axioms fixed_positive_asymptotic
#print axioms shrinking_parameter_asymptotic

end

end Erdos972GeneratingCoefficientGap
