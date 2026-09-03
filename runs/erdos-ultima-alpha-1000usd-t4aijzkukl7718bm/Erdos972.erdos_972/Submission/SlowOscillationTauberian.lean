import Submission.BoundedTauberian

/-! A signed bounded Laplace-Tauberian theorem with eventual slow oscillation.
This variant does not require monotonicity or nonnegative values. -/
namespace Erdos972SlowOscillationTauberian

open MeasureTheory Filter Set
open scoped Topology FourierTransform SchwartzMap
open Erdos972LaplaceSmoothing Erdos972TauberianDesmoothing Erdos972BoundedTauberian

/-- A local oscillation estimate survives averaging with a positive kernel;
the mass outside the local interval is paid for with the uniform bound. -/
lemma average_error_bound {f k : ℝ → ℝ} (hf : Measurable f) {M ε δ x : ℝ}
    (hM : ∀ t, ‖f t‖ ≤ M) (hε : 0 ≤ ε)
    (hk : Integrable k) (hk0 : ∀ t, 0 ≤ k t) (hkmass : (∫ t, k t) = 1)
    (hlocal : ∀ u ∈ Ioo (-δ) δ, |f (x+u)-f x| ≤ ε) :
    |(∫ u, f (x+u)*k u)-f x| ≤ ε+2*M*(∫ u in (Ioo (-δ) δ)ᶜ, k u) := by
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  have hi := integrable_average hf hk M hM x
  have hconst := hk.const_mul (f x)
  have hdiff : Integrable (fun u => (f (x+u)-f x)*k u) := by
    simpa only [sub_mul] using hi.sub hconst
  have he : (∫ u, f (x+u)*k u)-f x = ∫ u, (f (x+u)-f x)*k u := by
    simp only [sub_mul]
    rw [integral_sub hi hconst, integral_const_mul, hkmass, mul_one]
  have htail : Integrable ((Ioo (-δ) δ)ᶜ.indicator k) := hk.indicator measurableSet_Ioo.compl
  have hpoint (u : ℝ) : ‖(f (x+u)-f x)*k u‖ ≤
      ε*k u+2*M*((Ioo (-δ) δ)ᶜ.indicator k) u := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 u)]
    by_cases hu : u ∈ Ioo (-δ) δ
    · rw [indicator_of_notMem (show u ∉ (Ioo (-δ) δ)ᶜ by simpa using hu), mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right (hlocal u hu) (hk0 u)
    · rw [indicator_of_mem hu]
      have hh : |f (x+u)-f x| ≤ 2*M := by
        have ht := abs_sub (f (x+u)) (f x)
        have ha := hM (x+u)
        have hb := hM x
        simp only [Real.norm_eq_abs] at ha hb
        linarith only [ht, ha, hb]
      have hm := mul_le_mul_of_nonneg_right hh (hk0 u)
      linarith only [hm, mul_nonneg hε (hk0 u)]
  rw [he, ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  have hh := integral_mono hdiff.norm ((hk.const_mul ε).add (htail.const_mul (2*M))) hpoint
  simpa only [Pi.add_apply, integral_add (hk.const_mul ε) (htail.const_mul (2*M)), integral_const_mul,
    integral_indicator measurableSet_Ioo.compl, hkmass, mul_one] using hh

/-- Pointwise recovery from band-limited averages for a bounded signed
function with arbitrarily small eventual local oscillation. -/
theorem tendsto_zero_of_schwartz_averages {f : ℝ → ℝ} (hf : Measurable f)
    (M : ℝ) (hM : ∀ t, ‖f t‖ ≤ M)
    (hslow : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ x : ℝ in atTop, ∀ u ∈ Ioo (-δ) δ, |f (x+u)-f x| ≤ ε)
    (hAvg : ∀ φ : 𝓢(ℝ, ℂ), HasCompactSupport (φ : ℝ → ℂ) →
      Tendsto (fun x => ∫ u, f (x+u)*(𝓕 φ u).re) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hlocal⟩ := hslow (ε/4) (by positivity)
  let η := ε/(8*(M+1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨φ, hφ, hk0, _, hmass, htail⟩ :=
    Erdos972PositiveBandKernel.exists_concentrated_positive_kernel hδ hη
  have ha := (Metric.tendsto_nhds.mp (hAvg φ hφ)) (ε/4) (by positivity)
  filter_upwards [hlocal, ha] with x hloc hx
  have hh := average_error_bound hf hM (by positivity : 0 ≤ ε/4) (𝓕 φ).integrable.re hk0 hmass hloc
  have htail' : 2*M*(∫ u in (Ioo (-δ) δ)ᶜ, (𝓕 φ u).re) ≤ ε/4 := by
    calc
      _ ≤ 2*M*η := mul_le_mul_of_nonneg_left htail.le (by positivity)
      _ ≤ 2*(M+1)*η := by nlinarith only [hη]
      _ = ε/4 := by dsimp [η]; field_simp; ring
  simp only [Real.dist_eq, sub_zero] at hx ⊢
  have ht := abs_sub_le (f x) (∫ u, f (x+u)*(𝓕 φ u).re) 0
  simp only [sub_zero] at ht
  rw [abs_sub_comm (f x)] at ht
  linarith only [ht, hx, hh, htail', hε]

/-- Continuous boundary values of the Laplace transform force a bounded
slowly oscillating signed function to tend to zero. -/
theorem bounded_slow_laplace_tauberian {f : ℝ → ℝ} (hf : Measurable f)
    (hzero : ∀ t ≤ 0, f t = 0) (M : ℝ) (hM : ∀ t, ‖f t‖ ≤ M)
    (hslow : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ x : ℝ in atTop, ∀ u ∈ Ioo (-δ) δ, |f (x+u)-f x| ≤ ε)
    (F : ℝ × ℝ → ℂ) (hF : ContinuousOn F {z | 0 ≤ z.1 ∧ z.1 ≤ 1})
    (hLap : ∀ ε ξ : ℝ, 0 < ε → ε ≤ 1 →
      (∫ t in Ioi (0 : ℝ), Complex.exp (-((ε : ℂ)+
        (2*Real.pi*ξ : ℝ)*Complex.I)*t)*(f t : ℂ)) = F (ε, ξ)) :
    Tendsto f atTop (𝓝 0) := by
  apply tendsto_zero_of_schwartz_averages hf M hM hslow
  intro φ hφ
  have hh := laplace_smoothing_tendsto (Complex.continuous_ofReal.measurable.comp hf).aestronglyMeasurable
    (fun t ht => by simp only [Function.comp_apply, hzero t ht, Complex.ofReal_zero]) M (fun t => by simpa only [Function.comp_apply, Complex.norm_real] using hM t)
    F hF hLap φ hφ
  have he (x : ℝ) : (∫ t, (f t : ℂ)*𝓕 φ (t-x)).re = ∫ u, f (x+u)*(𝓕 φ u).re := by
    rw [integral_translate]
    have hi : Integrable (fun u => (f (x+u) : ℂ)*𝓕 φ u) := by
      have hki : Integrable (fun u : ℝ => 𝓕 φ u) := (𝓕 φ).integrable
      apply (hki.norm.const_mul M).mono'
        ((Complex.continuous_ofReal.measurable.comp (hf.comp (measurable_const.add measurable_id))).aestronglyMeasurable.mul
          (𝓕 φ).continuous.aestronglyMeasurable)
      filter_upwards with u
      simpa only [Pi.mul_apply, Function.comp_apply, id_eq, norm_mul, Complex.norm_real] using
        mul_le_mul_of_nonneg_right (hM (x+u)) (norm_nonneg (𝓕 φ u))
    have hr := integral_re hi
    simp only [RCLike.re_eq_complex_re] at hr
    rw [← hr]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hr := (Complex.continuous_re.tendsto 0).comp hh
  simpa only [Function.comp_def, Complex.zero_re, he] using hr

#print axioms bounded_slow_laplace_tauberian

end Erdos972SlowOscillationTauberian
