import Submission.PositiveKernelTauberian

/-! A bounded real Tauberian theorem. A measurable function supported on the
nonnegative half-line tends to zero when it is slowly decreasing and its
Fourier--Laplace transform has a continuous extension to the closed strip.
The theorem is analytic only: no arithmetic transform identity is assumed
to hold without proof. -/
namespace Erdos371.FourierBoundary
open Filter MeasureTheory FourierTransform
open scoped Topology
set_option autoImplicit false

lemma real_kernelMean_decay
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f)
    (M : ℝ) (hM : ∀ t, |f t| ≤ M) (hsupp : ∀ t, t < 0 → f t = 0)
    (F : ℝ × ℝ → ℂ) (hF : ContinuousOn F ((Set.Icc 0 1) ×ˢ Set.univ))
    (hEq : ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ ξ,
      𝓕 (damped (fun t => (f t : ℂ)) σ) ξ = F (σ,ξ))
    (K : ℝ → ℝ) (ψ : ℝ → ℂ) (hc : HasCompactSupport ψ)
    (hψ : Integrable ψ) (hK : Integrable (𝓕 ψ))
    (hKF : ∀ x, 𝓕 ψ x = (K x : ℂ)) :
    Tendsto (kernelMean K f) atTop (𝓝 0) := by
  have hfc : AEStronglyMeasurable (fun t => (f t : ℂ)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hf
  obtain ⟨_,_,hlim⟩ := closed_strip_convolution_decay (fun t => (f t : ℂ)) hfc M
    (fun t => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hM t)
    (fun t ht => by simp only [hsupp t ht,Complex.ofReal_zero]) F hF hEq ψ hc hψ hK
  have he (x : ℝ) : (∫ t, (f t : ℂ)*𝓕 ψ (t-x)) = ((kernelMean K f x : ℝ) : ℂ) := by
    simp_rw [hKF,← Complex.ofReal_mul]
    rw [integral_complex_ofReal,kernelMean_translation]
  simp_rw [he] at hlim
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hlim
  simpa only [Function.comp_def,Complex.ofReal_re,Complex.zero_re] using hr

/-- A bounded Fourier--Laplace Tauberian theorem, with the right-half-plane
transform equality and the closed-boundary continuity both explicit. -/
theorem bounded_laplace_tauberian
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f)
    (M : ℝ) (hMpos : 0 < M) (hM : ∀ t, |f t| ≤ M)
    (hsupp : ∀ t, t < 0 → f t = 0) (hslow : SlowlyDecreasing f)
    (F : ℝ × ℝ → ℂ) (hF : ContinuousOn F ((Set.Icc 0 1) ×ˢ Set.univ))
    (hEq : ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ ξ,
      𝓕 (damped (fun t => (f t : ℂ)) σ) ξ = F (σ,ξ)) :
    Tendsto f atTop (𝓝 0) := by
  apply tendsto_zero_of_small_moment_kernel_means f hf M hMpos hM hslow
  intro η hη
  obtain ⟨K,ψ,hK,hpos,hmass,hmom,hsmall,hc,hψ,hFψ,hEqψ⟩ :=
    exists_positive_bandlimited_small_moment η hη
  refine ⟨K,hK,hpos,hmass,hmom,hsmall,?_⟩
  exact real_kernelMean_decay f hf M hM hsupp F hF hEq K ψ hc hψ hFψ hEqψ

#print axioms bounded_laplace_tauberian
end Erdos371.FourierBoundary
