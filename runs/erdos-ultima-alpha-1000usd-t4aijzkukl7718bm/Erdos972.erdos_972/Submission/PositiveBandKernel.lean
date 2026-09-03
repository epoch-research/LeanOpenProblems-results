import Submission.LaplaceSmoothing

/-! A nonnegative, normalized Schwartz kernel with compact Fourier support. -/
namespace Erdos972PositiveBandKernel

open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology Convolution

lemma fourier_real_of_even {h : ℝ → ℝ} (he : ∀ t, h (-t) = h t) (x : ℝ) :
    (starRingEnd ℂ) (𝓕 (fun t => (h t : ℂ)) x) =
      𝓕 (fun t => (h t : ℂ)) x := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
  simp only [smul_eq_mul]
  rw [← integral_neg_eq_self (fun t : ℝ =>
    Complex.exp ((-2 * Real.pi * t * x : ℝ) * Complex.I) * (h t : ℂ)) volume]
  apply integral_congr_ae
  filter_upwards with t
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I, he]
  congr 2
  push_cast
  ring

noncomputable def bump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

noncomputable def bumpSchwartz : 𝓢(ℝ, ℂ) :=
  (bump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).toSchwartzMap
    (by exact Complex.ofRealCLM.contDiff.comp bump.contDiff)

lemma bumpSchwartz_apply (t : ℝ) : bumpSchwartz t = (bump t : ℂ) := rfl

lemma bumpSchwartz_compact : HasCompactSupport (bumpSchwartz : ℝ → ℂ) :=
  bump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

noncomputable def spectralSquare : 𝓢(ℝ, ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) bumpSchwartz bumpSchwartz

lemma spectralSquare_compact : HasCompactSupport (spectralSquare : ℝ → ℂ) := by
  have he : (spectralSquare : ℝ → ℂ) =
      (bumpSchwartz ⋆[ContinuousLinearMap.mul ℂ ℂ] bumpSchwartz) := by
    ext t
    exact SchwartzMap.convolution_apply _ _ _ _
  rw [he]
  exact bumpSchwartz_compact.convolution _ bumpSchwartz_compact

lemma spectralSquare_fourier (t : ℝ) :
    𝓕 spectralSquare t = (‖𝓕 bumpSchwartz t‖ ^ 2 : ℝ) := by
  rw [spectralSquare, SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply]
  change 𝓕 bumpSchwartz t * 𝓕 bumpSchwartz t = _
  have hr : (starRingEnd ℂ) (𝓕 bumpSchwartz t) = 𝓕 bumpSchwartz t :=
    fourier_real_of_even (fun x => bump.neg x) t
  conv_lhs => rhs; rw [← hr]
  simpa using Complex.mul_conj' (𝓕 bumpSchwartz t)

lemma spectralSquare_fourier_re (t : ℝ) :
    (𝓕 spectralSquare t).re = ‖𝓕 bumpSchwartz t‖ ^ 2 := by
  rw [spectralSquare_fourier]
  rfl

lemma spectralSquare_fourier_re_nonneg (t : ℝ) : 0 ≤ (𝓕 spectralSquare t).re := by
  rw [spectralSquare_fourier_re]
  positivity

lemma bumpSchwartz_fourier_zero : 𝓕 bumpSchwartz 0 = (∫ t, bump t : ℝ) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul,
    bumpSchwartz_apply]
  exact integral_complex_ofReal (f := fun t : ℝ => bump t)

lemma spectralSquare_mass_pos : 0 < ∫ t, (𝓕 spectralSquare t).re := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (x := (0 : ℝ)) (Complex.continuous_re.comp (𝓕 spectralSquare).continuous) (𝓕 spectralSquare).integrable.re
    spectralSquare_fourier_re_nonneg
  change (𝓕 spectralSquare 0).re ≠ 0
  rw [spectralSquare_fourier_re, bumpSchwartz_fourier_zero]
  have hb : (0 : ℝ) < ∫ t, bump t := bump.integral_pos
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    pow_ne_zero 2 (abs_ne_zero.mpr hb.ne')

/-- The frequency-space test function has a real, nonnegative inverse kernel,
normalized to mass one. -/
theorem exists_positive_kernel :
    ∃ φ : 𝓢(ℝ, ℂ), HasCompactSupport (φ : ℝ → ℂ) ∧
      (∀ t, 0 ≤ (𝓕 φ t).re) ∧
      (∀ t, (𝓕 φ t).im = 0) ∧
      (∫ t, (𝓕 φ t).re) = 1 := by
  let M : ℝ := ∫ t, (𝓕 spectralSquare t).re
  have hM : 0 < M := spectralSquare_mass_pos
  let φ : 𝓢(ℝ, ℂ) := ((M⁻¹ : ℝ) : ℂ) • spectralSquare
  have hφ (t : ℝ) : 𝓕 φ t = ((M⁻¹ * (𝓕 spectralSquare t).re : ℝ) : ℂ) := by
    simp only [φ, FourierTransform.fourier_smul, SchwartzMap.smul_apply, smul_eq_mul]
    rw [spectralSquare_fourier_re, spectralSquare_fourier, Complex.ofReal_mul]
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · exact spectralSquare_compact.smul_left
  · intro t
    rw [hφ]
    exact mul_nonneg (inv_nonneg.mpr hM.le) (spectralSquare_fourier_re_nonneg t)
  · intro t
    rw [hφ]
    simp
  · simp_rw [hφ, Complex.ofReal_re]
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hM.ne'

lemma fourier_rescale (φ : ℝ → ℂ) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    𝓕 (fun ξ => φ (R⁻¹ * ξ)) t = (R : ℂ) * 𝓕 φ (R * t) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  have he : (fun ξ : ℝ =>
      Complex.exp ((-2 * Real.pi * ξ * t : ℝ) * Complex.I) * φ (R⁻¹ * ξ)) =
    (fun ξ : ℝ => (fun u : ℝ =>
      Complex.exp ((-2 * Real.pi * u * (R * t) : ℝ) * Complex.I) * φ u) (R⁻¹ * ξ)) := by
    funext ξ
    congr 3
    field_simp
  rw [he, Measure.integral_comp_mul_left
    (fun u : ℝ => Complex.exp ((-2 * Real.pi * u * (R * t) : ℝ) * Complex.I) * φ u) R⁻¹,
    inv_inv, abs_of_pos hR]
  rfl

noncomputable def rescaleTest (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ))
    (R : ℝ) (hR : 0 < R) : 𝓢(ℝ, ℂ) :=
  (hφ.comp_homeomorph (Homeomorph.mulLeft₀ R⁻¹ (inv_ne_zero hR.ne'))).toSchwartzMap
    (φ.smooth ⊤ |>.comp (contDiff_const.mul contDiff_id))

lemma rescaleTest_compact (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ))
    (R : ℝ) (hR : 0 < R) : HasCompactSupport (rescaleTest φ hφ R hR : ℝ → ℂ) :=
  hφ.comp_homeomorph (Homeomorph.mulLeft₀ R⁻¹ (inv_ne_zero hR.ne'))

lemma rescaleTest_fourier (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ))
    (R : ℝ) (hR : 0 < R) (t : ℝ) :
    𝓕 (rescaleTest φ hφ R hR) t = (R : ℂ) * 𝓕 φ (R * t) :=
  fourier_rescale φ hR t

lemma integral_rescale (k : ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ t, R * k (R * t)) = ∫ u, k u := by
  rw [integral_const_mul, Measure.integral_comp_mul_left, smul_eq_mul,
    abs_of_pos (inv_pos.mpr hR), ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]

lemma tail_rescale (k : ℝ → ℝ) {R : ℝ} (hR : 0 < R) (δ : ℝ) :
    (∫ t in (Ioo (-δ) δ)ᶜ, R * k (R * t)) =
      ∫ u in (Ioo (-(R * δ)) (R * δ))ᶜ, k u := by
  rw [← integral_indicator measurableSet_Ioo.compl,
    ← integral_indicator measurableSet_Ioo.compl]
  have he : (fun t : ℝ => (Ioo (-δ) δ)ᶜ.indicator (fun t => R * k (R * t)) t) =
      (fun t : ℝ => R * (Ioo (-(R * δ)) (R * δ))ᶜ.indicator k (R * t)) := by
    funext t
    have ht : R * t ∈ Ioo (-(R * δ)) (R * δ) ↔ t ∈ Ioo (-δ) δ := by
      simp only [mem_Ioo, ← mul_neg, mul_lt_mul_iff_right₀ hR]
    by_cases hh : t ∈ Ioo (-δ) δ
    · simp [hh, ht.mpr hh]
    · have hn : R * t ∉ Ioo (-(R * δ)) (R * δ) := by simpa [ht] using hh
      simp [hh, hn]
  rw [he, integral_rescale _ hR]

lemma tail_integral_tendsto_zero {k : ℝ → ℝ} (hk : Integrable k) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun n : ℕ =>
      ∫ t in (Ioo (-(((n : ℝ) + 1) * δ)) (((n : ℝ) + 1) * δ))ᶜ, k t)
      Filter.atTop (𝓝 0) := by
  simp_rw [← integral_indicator measurableSet_Ioo.compl]
  have ht := tendsto_integral_of_dominated_convergence (fun t => ‖k t‖)
    (F := fun n : ℕ => (Ioo (-(((n : ℝ) + 1) * δ)) (((n : ℝ) + 1) * δ))ᶜ.indicator k)
    (f := fun _ : ℝ => 0)
    (fun _ => hk.aestronglyMeasurable.indicator measurableSet_Ioo.compl)
    hk.norm
    (fun _ => ae_of_all _ (fun t => norm_indicator_le_norm_self _ _)) ?_
  · simpa using ht
  filter_upwards with t
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := exists_nat_gt (|t| / δ)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hlarge : |t| < ((n : ℝ) + 1) * δ := by
    have hdiv := (div_lt_iff₀ hδ).mp hN
    have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
    nlinarith
  have hmem := abs_lt.mp hlarge
  simp only [Set.indicator_of_notMem (show t ∉ (Ioo (-(((n : ℝ) + 1) * δ))
    (((n : ℝ) + 1) * δ))ᶜ from by simpa using hmem)]

/-- Positive normalized band-limited kernels can have arbitrarily small mass
outside any prescribed neighborhood of the origin. -/
theorem exists_concentrated_positive_kernel {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ φ : 𝓢(ℝ, ℂ), HasCompactSupport (φ : ℝ → ℂ) ∧
      (∀ t, 0 ≤ (𝓕 φ t).re) ∧
      (∀ t, (𝓕 φ t).im = 0) ∧
      (∫ t, (𝓕 φ t).re) = 1 ∧
      (∫ t in (Ioo (-δ) δ)ᶜ, (𝓕 φ t).re) < η := by
  obtain ⟨φ, hφ, hpos, him, hmass⟩ := exists_positive_kernel
  have ht := tail_integral_tendsto_zero (𝓕 φ).integrable.re hδ
  obtain ⟨n, hn⟩ := ((tendsto_order.mp ht).2 η hη).exists
  let R : ℝ := (n : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨rescaleTest φ hφ R hR, rescaleTest_compact φ hφ R hR, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [rescaleTest_fourier]
    simpa using mul_nonneg hR.le (hpos (R * t))
  · intro t
    rw [rescaleTest_fourier]
    simp [him]
  · simp only [rescaleTest_fourier, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [integral_rescale (fun t => (𝓕 φ t).re) hR, hmass]
  · simp only [rescaleTest_fourier, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [tail_rescale (fun t => (𝓕 φ t).re) hR]
    exact hn

#print axioms exists_concentrated_positive_kernel

end Erdos972PositiveBandKernel
