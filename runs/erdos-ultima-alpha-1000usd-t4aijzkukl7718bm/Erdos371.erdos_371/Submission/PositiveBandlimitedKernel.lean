import Submission.LaplaceBoundaryConvolution

/-! Positive integrable band-limited kernels, constructed as Fourier
transforms of convolutions of a smooth even real bump with itself. -/
namespace Erdos371.FourierBoundary
open Filter MeasureTheory FourierTransform Convolution
open scoped Topology ContDiff SchwartzMap
set_option autoImplicit false

lemma fourier_conj_reflect (f : ℝ → ℂ) (t : ℝ) :
    𝓕 (fun ξ => (starRingEnd ℂ) (f (-ξ))) t = (starRingEnd ℂ) (𝓕 f t) := by
  rw [Real.fourier_real_eq,Real.fourier_real_eq,← integral_conj]
  calc
    (∫ ξ : ℝ, 𝐞 (-(ξ*t)) • (starRingEnd ℂ) (f (-ξ))) =
        ∫ ξ : ℝ, 𝐞 (-(-ξ*t)) • (starRingEnd ℂ) (f ξ) := by
      simpa only [neg_neg] using
        (integral_neg_eq_self (fun ξ : ℝ => 𝐞 (-(ξ*t)) • (starRingEnd ℂ) (f (-ξ))) volume).symm
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro ξ
      simp [Circle.smul_def,smul_eq_mul,Real.fourierChar_apply,← Complex.exp_conj,map_ofNat]

noncomputable def frequencyBump : ContDiffBump (0 : ℝ) := default

noncomputable def complexFrequencyBump (x : ℝ) : ℂ := frequencyBump x

lemma complexFrequencyBump_compact : HasCompactSupport complexFrequencyBump := by
  have hs : Function.support complexFrequencyBump = Function.support frequencyBump := by
    ext x
    simp [complexFrequencyBump,Function.mem_support]
  simpa only [HasCompactSupport,tsupport,hs] using frequencyBump.hasCompactSupport

lemma complexFrequencyBump_smooth : ContDiff ℝ ∞ complexFrequencyBump := by
  exact Complex.ofRealCLM.contDiff.comp frequencyBump.contDiff

noncomputable def schwartzFrequencyBump : 𝓢(ℝ, ℂ) :=
  complexFrequencyBump_compact.toSchwartzMap complexFrequencyBump_smooth

lemma schwartzFrequencyBump_apply (x : ℝ) : schwartzFrequencyBump x = complexFrequencyBump x := rfl

lemma fourierFrequencyBump_real (x : ℝ) :
    (starRingEnd ℂ) (𝓕 schwartzFrequencyBump x) = 𝓕 schwartzFrequencyBump x := by
  rw [SchwartzMap.fourier_coe,← fourier_conj_reflect]
  have he : (fun ξ => (starRingEnd ℂ) (schwartzFrequencyBump (-ξ))) =
      (schwartzFrequencyBump : ℝ → ℂ) := by
    funext ξ
    simp only [schwartzFrequencyBump_apply,complexFrequencyBump,ContDiffBump.neg,Complex.conj_ofReal]
  rw [he]

noncomputable def kernelFrequency : 𝓢(ℝ, ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) schwartzFrequencyBump schwartzFrequencyBump

lemma kernelFrequency_compact : HasCompactSupport kernelFrequency := by
  have he : (kernelFrequency : ℝ → ℂ) =
      (complexFrequencyBump ⋆[ContinuousLinearMap.mul ℂ ℂ] complexFrequencyBump) := by
    funext x
    exact SchwartzMap.convolution_apply _ _ _ x
  rw [he]
  exact HasCompactSupport.convolution (ContinuousLinearMap.mul ℂ ℂ) complexFrequencyBump_compact complexFrequencyBump_compact

lemma kernelFrequency_fourier (x : ℝ) :
    𝓕 kernelFrequency x = (‖𝓕 schwartzFrequencyBump x‖^2 : ℝ) := by
  rw [kernelFrequency,SchwartzMap.fourier_convolution,SchwartzMap.pairing_apply_apply]
  change 𝓕 schwartzFrequencyBump x * 𝓕 schwartzFrequencyBump x = _
  nth_rw 2 [← fourierFrequencyBump_real x]
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]

noncomputable def rawPositiveKernel (x : ℝ) : ℝ := ‖𝓕 schwartzFrequencyBump x‖^2

lemma rawPositiveKernel_nonneg (x : ℝ) : 0 ≤ rawPositiveKernel x := sq_nonneg _

lemma rawPositiveKernel_continuous : Continuous rawPositiveKernel := by
  exact (𝓕 schwartzFrequencyBump).continuous.norm.pow 2

lemma rawPositiveKernel_integrable : Integrable rawPositiveKernel := by
  have hi : Integrable (fun x => (𝓕 kernelFrequency x).re) := ((𝓕 kernelFrequency).integrable (μ := volume)).re
  convert hi using 1
  funext x
  rw [kernelFrequency_fourier]
  rfl

lemma frequencyBump_integral_pos : 0 < ∫ x : ℝ, frequencyBump x := by
  apply integral_pos_of_integrable_nonneg_nonzero frequencyBump.continuous
    (frequencyBump.continuous.integrable_of_hasCompactSupport frequencyBump.hasCompactSupport)
    (fun x => frequencyBump.nonneg)
  have he : frequencyBump 0 = 1 := frequencyBump.one_of_mem_closedBall
    (Metric.mem_closedBall_self frequencyBump.rIn_pos.le)
  exact he.trans_ne one_ne_zero

lemma rawPositiveKernel_zero_pos : 0 < rawPositiveKernel 0 := by
  have he : 𝓕 schwartzFrequencyBump 0 = (((∫ x : ℝ, frequencyBump x) : ℝ) : ℂ) := by
    rw [SchwartzMap.fourier_coe,Real.fourier_real_eq]
    simp only [mul_zero,neg_zero,AddChar.map_zero_eq_one,one_smul,schwartzFrequencyBump_apply,complexFrequencyBump]
    exact integral_complex_ofReal
  unfold rawPositiveKernel
  rw [he]
  apply sq_pos_of_pos
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos frequencyBump_integral_pos]
    using frequencyBump_integral_pos

lemma rawPositiveKernel_integral_pos : 0 < ∫ x : ℝ, rawPositiveKernel x :=
  integral_pos_of_integrable_nonneg_nonzero rawPositiveKernel_continuous
    rawPositiveKernel_integrable rawPositiveKernel_nonneg rawPositiveKernel_zero_pos.ne'

noncomputable def positiveKernel (x : ℝ) : ℝ :=
  rawPositiveKernel x / (∫ t : ℝ, rawPositiveKernel t)

lemma positiveKernel_nonneg (x : ℝ) : 0 ≤ positiveKernel x :=
  div_nonneg (rawPositiveKernel_nonneg x) rawPositiveKernel_integral_pos.le

lemma positiveKernel_integrable : Integrable positiveKernel :=
  rawPositiveKernel_integrable.div_const _

lemma positiveKernel_continuous : Continuous positiveKernel :=
  rawPositiveKernel_continuous.div_const _

lemma positiveKernel_integral : (∫ x : ℝ, positiveKernel x) = 1 := by
  simp only [positiveKernel,integral_div]
  exact div_self rawPositiveKernel_integral_pos.ne'

noncomputable def normalizedFrequency : 𝓢(ℝ, ℂ) :=
  (((∫ t : ℝ, rawPositiveKernel t)⁻¹ : ℝ) : ℂ) • kernelFrequency

lemma normalizedFrequency_compact : HasCompactSupport normalizedFrequency := by
  convert kernelFrequency_compact.smul_left
    (f := fun _ => (((∫ t : ℝ, rawPositiveKernel t)⁻¹ : ℝ) : ℂ)) using 1

lemma normalizedFrequency_fourier (x : ℝ) :
    𝓕 normalizedFrequency x = (positiveKernel x : ℂ) := by
  rw [normalizedFrequency,FourierTransform.fourier_smul,SchwartzMap.smul_apply,kernelFrequency_fourier]
  simp only [positiveKernel,rawPositiveKernel,Complex.ofReal_div,Complex.ofReal_inv,smul_eq_mul]
  ring

lemma fourier_comp_div (ψ : ℝ → ℂ) (R : ℝ) (hR : 0 < R) (t : ℝ) :
    𝓕 (fun ξ => ψ (ξ/R)) t = (R : ℂ)*𝓕 ψ (R*t) := by
  rw [Real.fourier_real_eq,Real.fourier_real_eq]
  have he (ξ : ℝ) : (ξ/R)*(R*t) = ξ*t := by field_simp
  have hi := Measure.integral_comp_div (fun ξ : ℝ => 𝐞 (-(ξ*(R*t))) • ψ ξ) R
  simp_rw [he] at hi
  simpa only [abs_of_pos hR,Complex.real_smul] using hi

/-- Every positive rescaling of the normalized positive kernel is the
Fourier transform of an integrable compactly supported test function. -/
theorem positiveKernel_scaled_bandlimited (R : ℝ) (hR : 0 < R) :
    ∃ ψ : ℝ → ℂ, HasCompactSupport ψ ∧ Integrable ψ ∧ Integrable (𝓕 ψ) ∧
      ∀ t, 𝓕 ψ t = (R*positiveKernel (R*t) : ℝ) := by
  let ψ := fun ξ : ℝ => normalizedFrequency (ξ/R)
  have he (t : ℝ) : 𝓕 ψ t = ((R*positiveKernel (R*t) : ℝ) : ℂ) := by
    rw [fourier_comp_div _ R hR]
    change (R : ℂ)*𝓕 normalizedFrequency (R*t) = _
    rw [normalizedFrequency_fourier,Complex.ofReal_mul]
  refine ⟨ψ,?_,?_,?_,he⟩
  · simpa only [Function.comp_def,div_eq_mul_inv] using
      normalizedFrequency_compact.comp_homeomorph (Homeomorph.mulRight₀ R⁻¹ (inv_ne_zero hR.ne'))
  · exact normalizedFrequency.integrable.comp_div hR.ne'
  · have hi : Integrable (fun t => ((R*positiveKernel (R*t) : ℝ) : ℂ)) :=
      ((positiveKernel_integrable.comp_mul_left' hR.ne').const_mul R).ofReal
    convert hi using 1
    funext t
    exact he t

#print axioms positiveKernel_scaled_bandlimited

end Erdos371.FourierBoundary
