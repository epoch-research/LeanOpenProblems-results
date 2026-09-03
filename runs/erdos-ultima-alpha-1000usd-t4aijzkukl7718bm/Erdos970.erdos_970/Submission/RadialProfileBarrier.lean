import Submission.ProfileTriangleIntegral

/-! A barrier for the continuous common radial-profile functional. It does
not apply to every sieve kernel, nor does it disprove the quadratic Jacobsthal
conjecture. The original inverse-shift energy must be integrable; otherwise
Lean's totalized integral cannot be used as that energy. -/
namespace Erdos970.RadialProfile
open MeasureTheory Set Real

noncomputable def profileNorm (f : ℝ → ℝ) : ℝ := ∫ u in (0 : ℝ)..1, f u ^ 2

noncomputable def shiftNumerator (f : ℝ → ℝ) (v : ℝ) : ℝ :=
  (∫ u in v..1, (f u - f (u - v)) ^ 2) + ∫ u in 0..v, f u ^ 2

noncomputable def profileEnergy (f : ℝ → ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, shiftNumerator f v / v

private lemma quadratic_nonneg (w x z G : ℝ) (hw : 0 < w) (hG : 1 ≤ w * G) :
    0 ≤ w * x ^ 2 - 2 * z * x + z ^ 2 * G := by
  have h1 := sq_nonneg (w * x - z)
  have h2 := mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hG)
  have he : w * (w * x ^ 2 - 2 * z * x + z ^ 2 * G) =
      (w * x - z) ^ 2 + z ^ 2 * (w * G - 1) := by ring
  have hprod : 0 ≤ w * (w * x ^ 2 - 2 * z * x + z ^ 2 * G) := by
    rw [he]
    exact add_nonneg h1 h2
  exact nonneg_of_mul_nonneg_right hprod hw

private noncomputable def reciprocalMajorant (u : ℝ) : ℝ :=
  3 / 5 + (9 / 25) * u + (27 / 50) * u ^ 2

private lemma majorant_product (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    1 ≤ (5 / 3 - u) * reciprocalMajorant u := by
  have he : (5 / 3 - u) * reciprocalMajorant u - 1 =
      (27 / 50) * u ^ 2 * (1 - u) := by unfold reciprocalMajorant; ring
  have hnn : 0 ≤ (27 / 50 : ℝ) * u ^ 2 * (1 - u) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg u)) (by linarith [hu.2])
  linarith

private lemma majorant_integral :
    (∫ u in (0 : ℝ)..1, reciprocalMajorant u) = 24 / 25 := by
  unfold reciprocalMajorant
  simp (discharger := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_pow, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul (9 / 25) (fun u : ℝ => u), integral_id]
  norm_num

/-- A rational weighted-square inequality. It is deliberately not optimized. -/
lemma profile_weighted_mean_square_le (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ u in (0 : ℝ)..1, f u) ^ 2 ≤
      ∫ u in (0 : ℝ)..1, (5 / 3 - u) * f u ^ 2 := by
  let M : ℝ := ∫ u in (0 : ℝ)..1, f u
  have hpoint (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      0 ≤ (5 / 3 - u) * f u ^ 2 - (2 * M) * f u + M ^ 2 * reciprocalMajorant u := by
    exact quadratic_nonneg (5 / 3 - u) (f u) M (reciprocalMajorant u)
      (by linarith [hu.2]) (majorant_product u hu)
  have h := intervalIntegral.integral_nonneg (μ := volume) (by norm_num : (0 : ℝ) ≤ 1) hpoint
  have hc1 : Continuous (fun u : ℝ => (5 / 3 - u) * f u ^ 2) := by fun_prop
  have hc2 : Continuous (fun u : ℝ => (2 * M) * f u) := by fun_prop
  have hc3 : Continuous (fun u : ℝ => M ^ 2 * reciprocalMajorant u) := by
    unfold reciprocalMajorant; fun_prop
  rw [intervalIntegral.integral_add ((hc1.sub hc2).intervalIntegrable 0 1)
    (hc3.intervalIntegrable 0 1), intervalIntegral.integral_sub
      (hc1.intervalIntegrable 0 1) (hc2.intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    majorant_integral] at h
  change M ^ 2 ≤ _
  change 0 ≤ (∫ u in (0 : ℝ)..1, (5 / 3 - u) * f u ^ 2) - (2 * M) * M + M ^ 2 * (24 / 25) at h
  nlinarith only [h, sq_nonneg M]

/-- The coarse, unweighted energy already exceeds one third of the norm. -/
theorem unweighted_profile_lower (f : ℝ → ℝ) (hf : Continuous f) :
    (1 / 3 : ℝ) * profileNorm f ≤ ∫ v in (0 : ℝ)..1, shiftNumerator f v := by
  have h := profile_weighted_mean_square_le f hf
  have he (u : ℝ) : (5 / 3 - u) * f u ^ 2 = (2 / 3) * f u ^ 2 + (1 - u) * f u ^ 2 := by ring
  simp_rw [he] at h
  rw [intervalIntegral.integral_add
    ((show Continuous (fun u => (2 / 3 : ℝ) * f u ^ 2) by fun_prop).intervalIntegrable 0 1)
    ((show Continuous (fun u => (1 - u) * f u ^ 2) by fun_prop).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul] at h
  change _ ≤ ∫ v in (0 : ℝ)..1,
    (∫ u in v..1, (f u - f (u - v)) ^ 2) + ∫ u in 0..v, f u ^ 2
  rw [unweighted_split_shift_integral f hf]
  unfold profileNorm
  linarith

lemma shiftNumerator_continuous (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (shiftNumerator f) :=
  (shift_inner_continuous f hf).add (primitive_continuous (fun u => f u ^ 2) (hf.pow 2))

lemma shiftNumerator_nonneg (f : ℝ → ℝ) (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 ≤ shiftNumerator f v := by
  apply add_nonneg
  · exact intervalIntegral.integral_nonneg hv.2 (fun _ _ => sq_nonneg _)
  · exact intervalIntegral.integral_nonneg hv.1 (fun _ _ => sq_nonneg _)

/-- The inverse-shift weight can only increase the energy on 0<v<=1.
The value at the single endpoint v=0 is handled exactly. -/
theorem profileEnergy_lower (f : ℝ → ℝ) (hf : Continuous f)
    (hint : IntervalIntegrable (fun v => shiftNumerator f v / v) volume 0 1) :
    (1 / 3 : ℝ) * profileNorm f ≤ profileEnergy f := by
  apply (unweighted_profile_lower f hf).trans
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((shiftNumerator_continuous f hf).intervalIntegrable 0 1) hint
  intro v hv
  by_cases hv0 : v = 0
  · simp [hv0, shiftNumerator]
  · have hvpos : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hv0)
    apply (le_div_iff₀ hvpos).mpr
    exact mul_le_of_le_one_right (shiftNumerator_nonneg f v hv) hv.2

/-- No continuous, finite-energy radial profile reaches the quadratic tail
threshold in this common-profile scheme. This is not a universal sieve barrier. -/
theorem no_quadratic_radial_profile (f : ℝ → ℝ) (hf : Continuous f)
    (hint : IntervalIntegrable (fun v => shiftNumerator f v / v) volume 0 1)
    (hn : 0 < profileNorm f) :
    ¬profileEnergy f / profileNorm f < 1 - log (2 : ℝ) := by
  intro hbad
  have hu := (div_lt_iff₀ hn).mp hbad
  have hl := profileEnergy_lower f hf hint
  have hlog : 1 - log (2 : ℝ) < (1 / 3 : ℝ) := by linarith only [log_two_gt_d9]
  have hgap := mul_lt_mul_of_pos_right hlog hn
  linarith

/-- At a reciprocal-tail budget of at least log 2, the continuous common
radial-profile leading margin is strictly negative for any nonzero profile. -/
theorem radial_margin_negative (f : ℝ → ℝ) (hf : Continuous f)
    (hint : IntervalIntegrable (fun v => shiftNumerator f v / v) volume 0 1)
    (hn : 0 < profileNorm f) (T : ℝ) (hT : log 2 ≤ T) :
    (1 - T) * profileNorm f - profileEnergy f < 0 := by
  have hl := profileEnergy_lower f hf hint
  have hlog : 1 - T < (1 / 3 : ℝ) := by linarith only [hT, log_two_gt_d9]
  have hgap := mul_lt_mul_of_pos_right hlog hn
  linarith

#print axioms unweighted_profile_lower
#print axioms profileEnergy_lower
#print axioms no_quadratic_radial_profile
#print axioms radial_margin_negative
end Erdos970.RadialProfile
