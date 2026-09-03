import Submission.NaturalComplexSpectrum
import Submission.StationaryPrimeSkew

/-! Prime-gap skew cancellation in a natural empirical word law.
This is a prime-gap average after taking the natural limit law; it is not
cancellation of the adjacent skew at a prescribed endpoint. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex FiniteInformation AbelPrimes
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A]

lemma natural_prime_covariance_im_zero
    (L : ℕ → ℕ → A)
    (hd : ∀ p : ℕ, p.Prime → Tendsto (fun N =>
      (∑ m ∈ Icc 1 N, labelDilationDefect p (L N) m)/(N : ℝ)) atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : Tendsto D atTop atTop) (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => naturalWordEmpirical L (D j)) atTop (𝓝 μ))
    (f : A → ℂ) (hfr : ∀ a, |(f a).re| ≤ 1) (hfi : ∀ a, |(f a).im| ≤ 1) :
    Tendsto (fun H => (∑ p ∈ initialPrimes H,
      (wordCovariance (μ : Measure (ℕ → A)) f (p : ℤ)).im)/(initialPrimes H).card)
      atTop (𝓝 0) := by
  obtain ⟨σ,hσ,hno⟩ := natural_word_complex_spectral_measure_no_infinite_order_atoms
    L hd D hD μ hlim f hfr hfi
  have ht := primeFourier_im_integral_zero_of_no_infinite_order_atoms (σ : Measure UnitAddCircle) hno
  simpa only [primeFourier_im_integral_eq,measureFourier,hσ] using ht

/-- Antisymmetric finite-label observables cancel under prime-gap averaging
in any natural empirical limit of a fixed-prime-stable array. -/
theorem natural_prime_skew_zero
    (L : ℕ → ℕ → A)
    (hd : ∀ p : ℕ, p.Prime → Tendsto (fun N =>
      (∑ m ∈ Icc 1 N, labelDilationDefect p (L N) m)/(N : ℝ)) atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : Tendsto D atTop atTop) (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => naturalWordEmpirical L (D j)) atTop (𝓝 μ))
    (C : A → A → ℝ) (hC : ∀ a b, C b a = -C a b) :
    Tendsto (fun H => (∑ p ∈ initialPrimes H,
      ∫ x, C (x 0) (x p) ∂(μ : Measure (ℕ → A)))/(initialPrimes H).card)
      atTop (𝓝 0) := by
  have ht (a b : A) := natural_prime_covariance_im_zero L hd D hD μ hlim (pairPhase a b)
    (fun x => by
      classical
      unfold pairPhase
      split_ifs <;> norm_num)
    (fun x => by
      classical
      unfold pairPhase
      split_ifs <;> norm_num)
  have hh := tendsto_finset_sum (univ : Finset A) (fun a _ =>
    tendsto_finset_sum (univ : Finset A) (fun b _ => (ht a b).const_mul (C a b)))
  simp only [mul_zero,sum_const_zero,← prime_word_skew_expansion (μ : Measure (ℕ → A)) C hC] at hh
  have hz := hh.div_const 2
  simp only [zero_div] at hz
  convert hz using 1
  funext H
  ring

/-- At a fixed prime cutoff, the actual natural empirical prime-gap skew
converges to the skew in the common word law. -/
lemma natural_prime_skew_tendsto
    (L : ℕ → ℕ → A) (D : ℕ → ℕ) (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => naturalWordEmpirical L (D j)) atTop (𝓝 μ))
    (C : A → A → ℝ) (H : ℕ) :
    Tendsto (fun j => (∑ p ∈ initialPrimes H,
      (∑ n ∈ range (D j+1), C (L (D j+1) (n+1)) (L (D j+1) (n+1+p)))/(D j+1 : ℝ)) /
        (initialPrimes H).card) atTop
      (𝓝 ((∑ p ∈ initialPrimes H, ∫ x, C (x 0) (x p) ∂(μ : Measure (ℕ → A)))/
        (initialPrimes H).card)) := by
  apply Tendsto.div_const
  apply tendsto_finset_sum
  intro p _
  let F : C((ℕ → A),ℝ) :=
    ⟨fun x => C (x 0) (x p),by
      have hc : Continuous (fun y : A×A => C y.1 y.2) := continuous_of_discreteTopology
      have hp : Continuous (fun x : ℕ → A => (x 0,x p)) :=
        (continuous_apply 0).prodMk (continuous_apply p)
      exact hc.comp hp⟩
  simpa only [F,ContinuousMap.coe_mk,wordOrbit,Nat.add_zero] using
    natural_word_integral_tendsto L D μ hlim F

/-- Specialization to actual quantized largest-prime labels. -/
theorem primeQuantLabel_natural_prime_skew_zero
    (Q : ℕ) (D : ℕ → ℕ) (hD : Tendsto D atTop atTop)
    (μ : ProbabilityMeasure (ℕ → Fin (Q+1)))
    (hlim : Tendsto (fun j => naturalWordEmpirical (primeQuantLabel Q) (D j)) atTop (𝓝 μ))
    (C : Fin (Q+1) → Fin (Q+1) → ℝ) (hC : ∀ a b, C b a = -C a b) :
    Tendsto (fun H => (∑ p ∈ initialPrimes H,
      ∫ x, C (x 0) (x p) ∂(μ : Measure (ℕ → Fin (Q+1))))/(initialPrimes H).card)
      atTop (𝓝 0) :=
  natural_prime_skew_zero (primeQuantLabel Q)
    (fun p hp => primeQuantLabel_natural_dilation_zero Q p hp.pos) D hD μ hlim C hC

#print axioms natural_prime_skew_zero
#print axioms primeQuantLabel_natural_prime_skew_zero
end Erdos371.DilationSpectrum
