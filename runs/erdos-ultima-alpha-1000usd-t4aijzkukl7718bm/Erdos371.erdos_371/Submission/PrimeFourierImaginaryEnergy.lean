import Submission.PrimeFourierSkewSpectrum

/-! Vanishing imaginary prime multiplier in L2, not only its signed integral.
This is for a fixed spectral measure with no infinite-order atoms. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex AbelPrimes
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

lemma primeFourier_im_square_le (N : ℕ) (x : UnitAddCircle) :
    ((primeFourierAverage N x).im)^2 ≤ ‖primeFourierAverage N x‖^2 := by
  have h := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr
    (Complex.abs_im_le_norm (primeFourierAverage N x))
  simpa only [sq_abs] using h

lemma primeFourier_im_square_le_one (N : ℕ) (x : UnitAddCircle) :
    ((primeFourierAverage N x).im)^2 ≤ 1 := by
  apply (primeFourier_im_square_le N x).trans
  simpa only [one_pow] using (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr
    (primeFourierAverage_norm_le N x)

lemma atomless_primeFourier_im_square_zero (μ : Measure UnitAddCircle)
    [IsFiniteMeasure μ] [NoAtoms μ] :
    Tendsto (fun N => ∫ x, ((primeFourierAverage N x).im)^2 ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun N => integral_nonneg (fun _ => sq_nonneg _)) _
    (atomless_primeFourierAverage_L2_zero μ)
  intro N
  apply integral_mono
  · exact ((Complex.continuous_im.comp (continuous_primeFourierAverage N)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact ((continuous_primeFourierAverage N).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact primeFourier_im_square_le N

lemma torsion_primeFourier_im_square_zero (μ : Measure UnitAddCircle) [IsFiniteMeasure μ] :
    Tendsto (fun N => ∫ x, ((primeFourierAverage N x).im)^2 ∂μ.restrict torsionCircle)
      atTop (𝓝 0) := by
  have hm (N : ℕ) : AEStronglyMeasurable (fun x => ((primeFourierAverage N x).im)^2)
      (μ.restrict torsionCircle) :=
    ((Complex.continuous_im.comp (continuous_primeFourierAverage N)).pow 2).aestronglyMeasurable
  have hb (N : ℕ) : ∀ᵐ x ∂μ.restrict torsionCircle,
      ‖((primeFourierAverage N x).im)^2‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ((primeFourierAverage N x).im))]
    exact primeFourier_im_square_le_one N x
  have ht : ∀ᵐ x ∂μ.restrict torsionCircle,
      Tendsto (fun N => ((primeFourierAverage N x).im)^2) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem torsionCircle_measurable] with x hx
    simpa only [zero_pow (by decide : 2 ≠ 0)] using (primeFourier_im_torsion_zero x hx).pow 2
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun _ => (1 : ℝ)) hm (integrable_const 1) hb ht

theorem primeFourier_im_square_zero_of_no_infinite_order_atoms
    (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (hno : ∀ x : UnitAddCircle, ¬IsOfFinAddOrder x → μ {x}=0) :
    Tendsto (fun N => ∫ x, ((primeFourierAverage N x).im)^2 ∂μ) atTop (𝓝 0) := by
  letI := noAtoms_restrict_torsion_compl μ hno
  have ht := (torsion_primeFourier_im_square_zero μ).add
    (atomless_primeFourier_im_square_zero (μ.restrict torsionCircleᶜ))
  simp only [add_zero] at ht
  apply ht.congr'
  apply Eventually.of_forall
  intro N
  exact integral_add_compl torsionCircle_measurable
    (((Complex.continuous_im.comp (continuous_primeFourierAverage N)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

#print axioms primeFourier_im_square_zero_of_no_infinite_order_atoms
end Erdos371.DilationSpectrum
