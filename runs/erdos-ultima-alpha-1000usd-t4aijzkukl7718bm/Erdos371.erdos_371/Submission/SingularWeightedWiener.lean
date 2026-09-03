import Submission.FinitePrimeDifferenceEnergy

/-! The singular factor from the prime-difference sieve can be absorbed by
Cauchy--Schwarz and Wiener's lemma, without pointwise Fourier decay. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex FiniteSieve
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

lemma measureFourier_norm_le_mass (μ : Measure UnitAddCircle) [IsFiniteMeasure μ] (k : ℤ) :
    ‖measureFourier μ k‖ ≤ μ.real Set.univ := by
  apply (norm_integral_le_integral_norm _).trans_eq
  simp only [fourier_apply,Circle.norm_coe,integral_const,smul_eq_mul,mul_one]

lemma atomless_fourier_shifted_mean_square_zero (μ : Measure UnitAddCircle)
    [IsFiniteMeasure μ] [NoAtoms μ] :
    Tendsto (fun N : ℕ => (∑ k ∈ range N, ‖measureFourier μ (k+1 : ℕ)‖^2)/(N : ℝ)) atTop (𝓝 0) := by
  let F (k : ℕ) := ‖measureFourier μ (k : ℤ)‖^2
  let M := μ.real Set.univ
  have hF (k : ℕ) : F k ≤ M^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (measureFourier_norm_le_mass μ k) 2
  have hM : 0 ≤ M := measureReal_nonneg
  have hbound (N : ℕ) : (∑ k ∈ range N,F (k+1))/(N : ℝ) ≤
      (∑ k ∈ range N,F k)/(N : ℝ)+M^2/N := by
    have he := (sum_range_succ' F N).symm.trans (sum_range_succ F N)
    have hh : (∑ k ∈ range N,F (k+1)) ≤ (∑ k ∈ range N,F k)+M^2 := by
      have hf0 : 0 ≤ F 0 := sq_nonneg _
      linarith [hF N]
    simpa only [add_div] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) N)
  have ht := (atomless_fourier_mean_square_zero μ).add (tendsto_const_div_atTop_nhds_zero_nat (M^2))
  simp only [add_zero] at ht
  exact squeeze_zero (fun N => div_nonneg (sum_nonneg fun k _ => sq_nonneg _) (Nat.cast_nonneg N)) hbound ht

noncomputable def singularFourierMean (μ : Measure UnitAddCircle) (N : ℕ) : ℝ :=
  (∑ k ∈ range N, slopeSieveFactor (2*(k+1))*‖measureFourier μ (k+1 : ℕ)‖)/N

lemma singularFourierMean_nonneg (μ : Measure UnitAddCircle) (N : ℕ) : 0 ≤ singularFourierMean μ N := by
  unfold singularFourierMean
  apply div_nonneg _ (Nat.cast_nonneg N)
  exact sum_nonneg (fun k _ => mul_nonneg (zero_le_one.trans (slopeSieveFactor_one_le _)) (norm_nonneg _))

lemma singularFourierMean_le_sqrt (μ : Measure UnitAddCircle) (N : ℕ) :
    singularFourierMean μ N ≤ Real.sqrt (Real.exp 18*
      ((∑ k ∈ range N, ‖measureFourier μ (k+1 : ℕ)‖^2)/(N : ℝ))) := by
  by_cases hN : N=0
  · simp [singularFourierMean,hN]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hS := sum_mul_sq_le_sq_mul_sq (range N)
    (fun k => slopeSieveFactor (2*(k+1))) (fun k => ‖measureFourier μ (k+1 : ℕ)‖)
  have hh := mul_le_mul_of_nonneg_right (primeDifference_factor_second_moment N)
    (show (0 : ℝ) ≤ ∑ k ∈ range N, ‖measureFourier μ (k+1 : ℕ)‖^2 from sum_nonneg (fun k _ => sq_nonneg _))
  have hd := div_le_div_of_nonneg_right (hS.trans hh) (sq_nonneg (N : ℝ))
  apply Real.le_sqrt_of_sq_le
  unfold singularFourierMean
  convert hd using 1
  · ring
  · field_simp

/-- Singular-series weighted absolute Fourier coefficients have vanishing
natural mean whenever the underlying measure is atomless. -/
theorem atomless_singularFourierMean_zero (μ : Measure UnitAddCircle)
    [IsFiniteMeasure μ] [NoAtoms μ] :
    Tendsto (singularFourierMean μ) atTop (𝓝 0) := by
  have ht := Real.continuous_sqrt.tendsto (Real.exp 18*0) |>.comp
    ((atomless_fourier_shifted_mean_square_zero μ).const_mul (Real.exp 18))
  simp only [mul_zero,Real.sqrt_zero] at ht
  exact squeeze_zero (singularFourierMean_nonneg μ) (singularFourierMean_le_sqrt μ) ht

#print axioms atomless_singularFourierMean_zero
end Erdos371.DilationSpectrum
