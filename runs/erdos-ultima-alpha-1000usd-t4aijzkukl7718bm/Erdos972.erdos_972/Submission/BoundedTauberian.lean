import Submission.TauberianDesmoothing

/-! A bounded Laplace-Tauberian theorem, including the de-smoothing step. -/
namespace Erdos972BoundedTauberian

open MeasureTheory Set Filter
open scoped Topology FourierTransform SchwartzMap
open Erdos972LaplaceSmoothing Erdos972TauberianDesmoothing

noncomputable def positiveStep : ℝ → ℝ := (Ioi 0).indicator (fun _ => 1)

lemma measurable_positiveStep : Measurable positiveStep :=
  measurable_const.indicator measurableSet_Ioi

lemma positiveStep_nonneg (t : ℝ) : 0 ≤ positiveStep t := by
  by_cases ht : 0 < t <;> simp [positiveStep, ht]

lemma positiveStep_le_one (t : ℝ) : positiveStep t ≤ 1 := by
  by_cases ht : 0 < t <;> simp [positiveStep, ht]

lemma positiveStep_norm_le_one (t : ℝ) : ‖positiveStep t‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (positiveStep_nonneg t)] using positiveStep_le_one t

lemma integral_translate (f k : ℝ → ℂ) (x : ℝ) :
    (∫ t, f t * k (t - x)) = ∫ u, f (x + u) * k u := by
  rw [← integral_add_left_eq_self (fun t => f t * k (t - x)) x]
  simp only [add_sub_cancel_left]

lemma step_average_tendsto {k : ℝ → ℝ} (hk : Integrable k) :
    Tendsto (fun x => ∫ u, positiveStep (x + u) * k u) atTop (𝓝 (∫ u, k u)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun u => ‖k u‖)
  · exact Eventually.of_forall fun x =>
      ((measurable_positiveStep.comp (measurable_const.add measurable_id)).aestronglyMeasurable.mul
        hk.aestronglyMeasurable)
  · exact Eventually.of_forall fun x => ae_of_all _ (fun u => by
      simp only [Pi.mul_apply, Function.comp_def, id_eq, norm_mul]
      exact (mul_le_mul_of_nonneg_right (positiveStep_norm_le_one (x + u)) (norm_nonneg _)).trans_eq (one_mul _))
  · exact hk.norm
  · filter_upwards with u
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (-u)] with x hx
    have hxu : 0 < x + u := by linarith
    simp [positiveStep, hxu]

noncomputable def remainder (f : ℝ → ℝ) (t : ℝ) : ℂ := (f t - positiveStep t : ℝ)

lemma measurable_remainder {f : ℝ → ℝ} (hf : Measurable f) : Measurable (remainder f) :=
  Complex.continuous_ofReal.measurable.comp (hf.sub measurable_positiveStep)

lemma remainder_norm_le {f : ℝ → ℝ} (M : ℝ) (hpos : ∀ t, 0 ≤ f t)
    (hM : ∀ t, f t ≤ M) (t : ℝ) : ‖remainder f t‖ ≤ M + 1 := by
  simp only [remainder, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  have hf0 := hpos t
  have hfM := hM t
  have hstep0 := positiveStep_nonneg t
  have hstep1 := positiveStep_le_one t
  constructor <;> linarith

lemma averages_of_remainder_smoothing {f : ℝ → ℝ} (hf : Measurable f)
    (hpos : ∀ t, 0 ≤ f t) (M : ℝ) (hM : ∀ t, f t ≤ M)
    (hSmooth : ∀ φ : 𝓢(ℝ, ℂ), HasCompactSupport (φ : ℝ → ℂ) →
      Tendsto (fun x => ∫ t, remainder f t * 𝓕 φ (t - x)) atTop (𝓝 0))
    (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ)) :
    Tendsto (fun x => ∫ u, f (x + u) * (𝓕 φ u).re) atTop
      (𝓝 (∫ u, (𝓕 φ u).re)) := by
  have hbound (t : ℝ) : ‖f t‖ ≤ M := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos t)] using hM t
  have hrem (x : ℝ) : Integrable (fun u => remainder f (x + u) * 𝓕 φ u) := by
    have hki : Integrable (fun u : ℝ => 𝓕 φ u) := (𝓕 φ).integrable
    apply (hki.norm.const_mul (M + 1)).mono'
      (((measurable_remainder hf).comp (measurable_const.add measurable_id)).aestronglyMeasurable.mul
        (𝓕 φ).continuous.aestronglyMeasurable)
    filter_upwards with u
    simp only [Pi.mul_apply, Function.comp_def, id_eq, norm_mul]
    exact mul_le_mul_of_nonneg_right (remainder_norm_le M hpos hM _) (norm_nonneg _)
  have hre (x : ℝ) : (∫ t, remainder f t * 𝓕 φ (t - x)).re =
      (∫ u, f (x + u) * (𝓕 φ u).re) - (∫ u, positiveStep (x + u) * (𝓕 φ u).re) := by
    rw [integral_translate]
    have hi := integral_re (hrem x)
    simp only [RCLike.re_eq_complex_re] at hi
    rw [← hi]
    simp only [remainder, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, sub_mul]
    exact integral_sub (integrable_average hf (𝓕 φ).integrable.re M hbound x)
      (integrable_average measurable_positiveStep (𝓕 φ).integrable.re 1 positiveStep_norm_le_one x)
  have hlim := (Complex.continuous_re.tendsto 0).comp (hSmooth φ hφ)
  change Tendsto (fun x => (∫ t, remainder f t * 𝓕 φ (t - x)).re) atTop (𝓝 0) at hlim
  simp_rw [hre] at hlim
  have hsum := hlim.add (step_average_tendsto (𝓕 φ).integrable.re)
  simpa only [RCLike.re_eq_complex_re, sub_add_cancel, zero_add] using hsum

/-- Continuous boundary values of the Laplace transform of `f - 1` on the
positive half-line, together with monotonicity of `exp t * f t`, force `f → 1`.
No Tauberian theorem is assumed here: the smoothing and de-smoothing steps are
proved in the imported auxiliary files. -/
theorem bounded_laplace_tauberian {f : ℝ → ℝ} (hf : Measurable f)
    (hpos : ∀ t, 0 ≤ f t) (hzero : ∀ t ≤ 0, f t = 0)
    (M : ℝ) (hM0 : 0 < M) (hM : ∀ t, f t ≤ M)
    (hm : Monotone (fun t => Real.exp t * f t))
    (F : ℝ × ℝ → ℂ) (hF : ContinuousOn F {z | 0 ≤ z.1 ∧ z.1 ≤ 1})
    (hLap : ∀ ε ξ : ℝ, 0 < ε → ε ≤ 1 →
      (∫ t in Ioi (0 : ℝ), Complex.exp (-((ε : ℂ) +
        (2 * Real.pi * ξ : ℝ) * Complex.I) * t) * (f t - 1 : ℝ)) = F (ε, ξ)) :
    Tendsto f atTop (𝓝 1) := by
  apply tendsto_of_schwartz_averages hf hpos M hM0 hM hm
  apply averages_of_remainder_smoothing hf hpos M hM
  intro φ hφ
  apply laplace_smoothing_tendsto (measurable_remainder hf).aestronglyMeasurable
    (fun t ht => by simp [remainder, positiveStep, hzero t ht, not_lt.mpr ht])
    (M + 1) (remainder_norm_le M hpos hM) F hF _ φ hφ
  intro ε ξ hε hε1
  rw [← hLap ε ξ hε hε1]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp [remainder, positiveStep, ht]

#print axioms bounded_laplace_tauberian

end Erdos972BoundedTauberian
