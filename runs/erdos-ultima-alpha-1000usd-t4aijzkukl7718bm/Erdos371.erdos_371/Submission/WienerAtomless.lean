import Submission.FourierAtomTests

/-! Wiener's mean-square Fourier-coefficient lemma for an atomless finite
measure on the unit circle. The proof uses bounded geometric means and DCT
on the product measure, not a spectral ergodic theorem. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

noncomputable def measureFourier (μ : Measure UnitAddCircle) (k : ℤ) : ℂ := ∫ x, fourier k x ∂μ

lemma measureFourier_neg (μ : Measure UnitAddCircle) (k : ℤ) :
    measureFourier μ (-k) = conj (measureFourier μ k) := by
  simp only [measureFourier,fourier_neg,integral_conj]

lemma fourier_difference_integral (μ : Measure UnitAddCircle) [IsFiniteMeasure μ] (k : ℤ) :
    (∫ z : UnitAddCircle × UnitAddCircle, fourier k (z.1-z.2) ∂μ.prod μ) =
      measureFourier μ k*conj (measureFourier μ k) := by
  have hc : Continuous (fun z : UnitAddCircle × UnitAddCircle => fourier k (z.1-z.2)) :=
    (fourier k).continuous.comp (continuous_fst.sub continuous_snd)
  rw [integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp only [fourier_sub_argument,integral_const_mul,integral_conj,integral_mul_const,measureFourier]

lemma fourierAverage_difference_integral (μ : Measure UnitAddCircle) [IsFiniteMeasure μ] (N : ℕ) :
    (∫ z : UnitAddCircle × UnitAddCircle, fourierAverage N (z.1-z.2) ∂μ.prod μ) =
      Complex.ofReal ((∑ k : Fin (N+1), ‖measureFourier μ (k : ℤ)‖^2)/(N+1 : ℝ)) := by
  unfold fourierAverage
  have hi (k : Fin (N+1)) : Integrable
      (fun z : UnitAddCircle × UnitAddCircle => fourier (k : ℤ) (z.1-z.2)) (μ.prod μ) :=
    ((fourier (k : ℤ)).continuous.comp (continuous_fst.sub continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_div,integral_finset_sum _ (fun k _ => hi k)]
  simp only [fourier_difference_integral,Complex.mul_conj,Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one]

lemma ae_product_ne_of_noAtoms (μ : Measure UnitAddCircle) [IsFiniteMeasure μ] [NoAtoms μ] :
    ∀ᵐ z : UnitAddCircle × UnitAddCircle ∂μ.prod μ, z.1 ≠ z.2 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun continuous_fst.measurable continuous_snd.measurable).compl).mpr
  filter_upwards [] with x
  filter_upwards [μ.ae_ne x] with y hy
  exact hy.symm

/-- Atomless finite measures have Fourier coefficients with vanishing
Cesàro mean square. No rate or Fourier pointwise decay is asserted. -/
theorem atomless_fourier_mean_square_zero (μ : Measure UnitAddCircle) [IsFiniteMeasure μ] [NoAtoms μ] :
    Tendsto (fun N : ℕ => (∑ k ∈ range N, ‖measureFourier μ (k : ℤ)‖^2)/(N : ℝ)) atTop (𝓝 0) := by
  have hm (N : ℕ) : AEStronglyMeasurable
      (fun z : UnitAddCircle × UnitAddCircle => fourierAverage N (z.1-z.2)) (μ.prod μ) :=
    ((continuous_fourierAverage N).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
  have hb (N : ℕ) : ∀ᵐ z : UnitAddCircle × UnitAddCircle ∂μ.prod μ,
      ‖fourierAverage N (z.1-z.2)‖ ≤ (1 : ℝ) :=
    Eventually.of_forall (fun z => fourierAverage_norm_le N (z.1-z.2))
  have ht : ∀ᵐ z : UnitAddCircle × UnitAddCircle ∂μ.prod μ,
      Tendsto (fun N => fourierAverage N (z.1-z.2)) atTop (𝓝 (0 : ℂ)) := by
    filter_upwards [ae_product_ne_of_noAtoms μ] with z hz
    exact fourierAverage_tendsto_zero (sub_ne_zero.mpr hz)
  have hd := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hm (integrable_const 1) hb ht
  simp only [integral_zero,fourierAverage_difference_integral] at hd
  have hr := Complex.continuous_re.tendsto 0 |>.comp hd
  simp only [Function.comp_def,Complex.ofReal_re,Complex.zero_re] at hr
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [← Finset.sum_range (fun k : ℕ => ‖measureFourier μ (k : ℤ)‖^2),Nat.cast_add,Nat.cast_one] using hr

#print axioms atomless_fourier_mean_square_zero
end Erdos371.DilationSpectrum
