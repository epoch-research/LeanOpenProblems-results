import Submission.HarmonicPrimeLabelSpectrum
import Submission.PrimeFourierSkewSpectrum

/-! Ordinary prime-gap skew cancellation for a fixed stationary finite
label law satisfying the proved harmonic dilation inequalities. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex FiniteInformation AbelPrimes
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

lemma primeFourier_im_integral_eq (σ : Measure UnitAddCircle) [IsFiniteMeasure σ] (N : ℕ) :
    (∫ x, (primeFourierAverage N x).im ∂σ) =
      (∑ p ∈ initialPrimes N, (measureFourier σ (p : ℤ)).im)/(initialPrimes N).card := by
  have hint : Integrable (primeFourierAverage N) σ :=
    (continuous_primeFourierAverage N).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (∫ x, (primeFourierAverage N x).im ∂σ) = (∫ x, primeFourierAverage N x ∂σ).im := integral_im hint
  rw [he]
  have hc : (∫ x, primeFourierAverage N x ∂σ) =
      (∑ p ∈ initialPrimes N, measureFourier σ (p : ℤ))/((initialPrimes N).card : ℂ) := by
    unfold primeFourierAverage
    rw [integral_div,integral_finset_sum (initialPrimes N) (fun p _ =>
      (fourier (p : ℤ)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    rfl
  rw [hc,Complex.div_natCast_im]
  congr 1
  exact map_sum Complex.imAddGroupHom _ _

variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A]

lemma stationary_prime_covariance_im_zero
    (μ : Measure (ℕ → A)) [IsFiniteMeasure μ] (hμ : MeasurePreserving wordShift μ μ)
    (hdom : ∀ p K : ℕ, 0 < p → ∀ F : (Fin K → A) → ℝ, (∀ x, 0 ≤ F x ∧ F x ≤ 1) →
      (∫ x, F (fun k => x k) ∂μ) ≤ p*∫ x, F (fun k => x (p*k)) ∂μ)
    (f : A → ℂ) :
    Tendsto (fun N => (∑ p ∈ initialPrimes N, (wordCovariance μ f (p : ℤ)).im)/(initialPrimes N).card)
      atTop (𝓝 0) := by
  obtain ⟨σ,hσ,hno⟩ := exists_word_spectral_measure_no_infinite_order_atoms μ hμ hdom f
  have ht := primeFourier_im_integral_zero_of_no_infinite_order_atoms (σ : Measure UnitAddCircle) hno
  simpa only [primeFourier_im_integral_eq,measureFourier,hσ] using ht

noncomputable def pairPhase (a b x : A) : ℂ := by
  classical
  exact ⟨if x=a then 1 else 0,if x=b then 1 else 0⟩

lemma pairPhase_im [DecidableEq A] (a b x y : A) :
    (pairPhase a b y*conj (pairPhase a b x)).im =
      (if x=a ∧ y=b then (1 : ℝ) else 0)-(if x=b ∧ y=a then 1 else 0) := by
  classical
  by_cases hxa : x=a <;> by_cases hxb : x=b <;> by_cases hya : y=a <;> by_cases hyb : y=b
  all_goals simp [pairPhase,Complex.mul_im,hxa,hxb,hya,hyb]
  all_goals simp only [ite_and]; ring

lemma antisymmetric_phase_expansion (C : A → A → ℝ) (hC : ∀ a b, C b a = -C a b) (x y : A) :
    2*C x y = ∑ a, ∑ b, C a b*(pairPhase a b y*conj (pairPhase a b x)).im := by
  classical
  simp_rw [pairPhase_im,mul_sub]
  have he (a b : A) : C a b*(if x=a ∧ y=b then (1 : ℝ) else 0) =
      if x=a ∧ y=b then C a b else 0 := by split_ifs <;> simp
  have he' (a b : A) : C a b*(if x=b ∧ y=a then (1 : ℝ) else 0) =
      if x=b ∧ y=a then C a b else 0 := by split_ifs <;> simp
  simp_rw [he,he',sum_sub_distrib]
  simp only [ite_and,sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_univ,if_true]
  rw [hC y x]
  ring

lemma wordCovariance_nat_im (μ : Measure (ℕ → A)) [IsFiniteMeasure μ] (f : A → ℂ) (p : ℕ) :
    (wordCovariance μ f (p : ℤ)).im = ∫ x, (f (x p)*conj (f (x 0))).im ∂μ := by
  have hh : Integrable (fun x : ℕ → A => f (x p)*conj (f (x 0))) μ :=
    (continuous_word_pair f p 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he := integral_im hh
  simpa only [wordCovariance,Int.toNat_natCast,Int.toNat_neg_natCast] using he.symm

lemma antisymmetric_word_integral_expansion (μ : Measure (ℕ → A)) [IsFiniteMeasure μ]
    (C : A → A → ℝ) (hC : ∀ a b, C b a = -C a b) (p : ℕ) :
    2*(∫ x, C (x 0) (x p) ∂μ) = ∑ a, ∑ b, C a b*(wordCovariance μ (pairPhase a b) (p : ℤ)).im := by
  have hint (a b : A) : Integrable (fun x : ℕ → A => C a b*(pairPhase a b (x p)*conj (pairPhase a b (x 0))).im) μ :=
    (continuous_const.mul (Complex.continuous_im.comp (continuous_word_pair (pairPhase a b) p 0))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_const_mul]
  simp_rw [antisymmetric_phase_expansion C hC]
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ => hint a b))]
  simp_rw [integral_finset_sum _ (fun b _ => hint _ b),integral_const_mul,← wordCovariance_nat_im]

lemma prime_word_skew_expansion (μ : Measure (ℕ → A)) [IsFiniteMeasure μ]
    (C : A → A → ℝ) (hC : ∀ a b, C b a = -C a b) (N : ℕ) :
    2*((∑ p ∈ initialPrimes N, ∫ x, C (x 0) (x p) ∂μ)/(initialPrimes N).card) =
      ∑ a, ∑ b, C a b*((∑ p ∈ initialPrimes N, (wordCovariance μ (pairPhase a b) (p : ℤ)).im)/
        (initialPrimes N).card) := by
  rw [← mul_div_assoc,mul_sum]
  simp_rw [antisymmetric_word_integral_expansion μ C hC]
  simp only [sum_div,mul_div_assoc,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  rw [sum_comm]

/-- Prime-gap averages of every fixed antisymmetric finite-label observable
vanish in a fixed stationary law with cylinder dilation domination. -/
theorem stationary_prime_skew_zero
    (μ : Measure (ℕ → A)) [IsFiniteMeasure μ] (hμ : MeasurePreserving wordShift μ μ)
    (hdom : ∀ p K : ℕ, 0 < p → ∀ F : (Fin K → A) → ℝ, (∀ x, 0 ≤ F x ∧ F x ≤ 1) →
      (∫ x, F (fun k => x k) ∂μ) ≤ p*∫ x, F (fun k => x (p*k)) ∂μ)
    (C : A → A → ℝ) (hC : ∀ a b, C b a = -C a b) :
    Tendsto (fun N => (∑ p ∈ initialPrimes N, ∫ x, C (x 0) (x p) ∂μ)/(initialPrimes N).card)
      atTop (𝓝 0) := by
  have ht := tendsto_finset_sum (univ : Finset A) (fun a _ =>
    tendsto_finset_sum (univ : Finset A) (fun b _ =>
      (stationary_prime_covariance_im_zero μ hμ hdom (pairPhase a b)).const_mul (C a b)))
  simp only [mul_zero,sum_const_zero,← prime_word_skew_expansion μ C hC] at ht
  have hh := ht.div_const 2
  simp only [zero_div] at hh
  convert hh using 1
  funext N
  ring

#print axioms stationary_prime_skew_zero
end Erdos371.DilationSpectrum
