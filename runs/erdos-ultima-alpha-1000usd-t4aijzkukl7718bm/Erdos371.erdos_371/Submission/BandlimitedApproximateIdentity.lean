import Submission.PositiveBandlimitedKernel

/-! Positive probability kernels with compact frequency support and an
arbitrarily small first absolute moment. These provide a quantitative form
of the approximate identities used in the Tauberian squeeze. -/
namespace Erdos371.FourierBoundary
open Filter MeasureTheory FourierTransform
open scoped Topology SchwartzMap
set_option autoImplicit false

lemma positiveKernel_firstMoment_integrable :
    Integrable (fun x : ℝ => |x| *positiveKernel x) := by
  have h := (𝓕 normalizedFrequency).integrable_pow_mul volume 1
  simpa only [pow_one,Real.norm_eq_abs,normalizedFrequency_fourier,Complex.norm_real,
    abs_of_nonneg (positiveKernel_nonneg _)] using h

noncomputable def kernelFirstMoment : ℝ := ∫ x : ℝ, |x| *positiveKernel x

lemma kernelFirstMoment_nonneg : 0 ≤ kernelFirstMoment :=
  integral_nonneg (fun x => mul_nonneg (abs_nonneg x) (positiveKernel_nonneg x))

noncomputable def scaledPositiveKernel (R x : ℝ) : ℝ := R*positiveKernel (R*x)

lemma scaledPositiveKernel_nonneg (R : ℝ) (hR : 0 ≤ R) (x : ℝ) :
    0 ≤ scaledPositiveKernel R x := mul_nonneg hR (positiveKernel_nonneg _)

lemma scaledPositiveKernel_integrable (R : ℝ) (hR : R ≠ 0) :
    Integrable (scaledPositiveKernel R) := (positiveKernel_integrable.comp_mul_left' hR).const_mul R

lemma scaledPositiveKernel_integral (R : ℝ) (hR : 0 < R) :
    (∫ x : ℝ, scaledPositiveKernel R x) = 1 := by
  simp only [scaledPositiveKernel,integral_const_mul,
    Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr hR),smul_eq_mul,positiveKernel_integral]
  field_simp

lemma scaledPositiveKernel_moment_identity (R : ℝ) (hR : 0 < R) (x : ℝ) :
    |x| *scaledPositiveKernel R x = |R*x| *positiveKernel (R*x) := by
  rw [scaledPositiveKernel,abs_mul,abs_of_pos hR]
  ring

lemma scaledPositiveKernel_firstMoment_integrable (R : ℝ) (hR : 0 < R) :
    Integrable (fun x : ℝ => |x| *scaledPositiveKernel R x) := by
  simp_rw [scaledPositiveKernel_moment_identity R hR]
  exact positiveKernel_firstMoment_integrable.comp_mul_left' hR.ne'

lemma scaledPositiveKernel_firstMoment (R : ℝ) (hR : 0 < R) :
    (∫ x : ℝ, |x| *scaledPositiveKernel R x) = kernelFirstMoment/R := by
  simp_rw [scaledPositiveKernel_moment_identity R hR]
  rw [Measure.integral_comp_mul_left (fun x : ℝ => |x| *positiveKernel x) R,abs_of_pos (inv_pos.mpr hR)]
  change R⁻¹*kernelFirstMoment = kernelFirstMoment/R
  ring

/-- The construction is nontrivial (total mass one), nonnegative, and has
finite first moment. Its frequency side is both compactly supported and
integrable. -/
theorem exists_positive_bandlimited_small_moment (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ → ℝ, ∃ ψ : ℝ → ℂ,
      Integrable K ∧ (∀ x, 0 ≤ K x) ∧ (∫ x : ℝ, K x) = 1 ∧
      Integrable (fun x => |x| *K x) ∧ (∫ x : ℝ, |x| *K x) ≤ η ∧
      HasCompactSupport ψ ∧ Integrable ψ ∧ Integrable (𝓕 ψ) ∧
      ∀ x, 𝓕 ψ x = (K x : ℂ) := by
  let R := (kernelFirstMoment+1)/η
  have hR : 0 < R := div_pos (by linarith [kernelFirstMoment_nonneg]) hη
  obtain ⟨ψ,hc,hψ,hF,he⟩ := positiveKernel_scaled_bandlimited R hR
  refine ⟨scaledPositiveKernel R,ψ,scaledPositiveKernel_integrable R hR.ne',
    scaledPositiveKernel_nonneg R hR.le,scaledPositiveKernel_integral R hR,
    scaledPositiveKernel_firstMoment_integrable R hR,?_,hc,hψ,hF,he⟩
  rw [scaledPositiveKernel_firstMoment R hR]
  apply (div_le_iff₀ hR).mpr
  dsimp only [R]
  rw [mul_div_cancel₀ _ hη.ne']
  linarith

#print axioms exists_positive_bandlimited_small_moment
end Erdos371.FourierBoundary
