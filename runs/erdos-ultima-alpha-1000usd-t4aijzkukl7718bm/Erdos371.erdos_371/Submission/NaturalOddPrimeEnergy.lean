import Submission.NaturalWordSpectrum
import Submission.StationaryOddPrimeEnergy

/-! Odd-prime-shift energies vanish in natural empirical limit laws.
The order of limits is explicit: first take the natural subsequential word
law, then let the prime-gap cutoff grow. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex FiniteInformation AbelPrimes
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A]

/-- A spectral version of the odd-energy theorem, without any cylinder
dilation domination assumption. -/
theorem stationary_wordOddAverage_energy_zero_of_spectrum
    (μ : Measure (ℕ → A)) [IsFiniteMeasure μ] (hμ : MeasurePreserving wordShift μ μ)
    (f : A → ℝ) (σ : Measure UnitAddCircle) [IsFiniteMeasure σ]
    (hσ : ∀ k : ℤ, (∫ x, fourier k x ∂σ) = wordCovariance μ (fun a => (f a : ℂ)) k)
    (hno : ∀ x : UnitAddCircle, ¬IsOfFinAddOrder x → σ {x}=0)
    (R : ℕ → ℕ) (hR : ∀ H, H ≤ R H) :
    Tendsto (fun H => ∫ x, (wordOddAverage (R H) (initialPrimes H) f x)^2 ∂μ)
      atTop (𝓝 0) := by
  have ht := (primeFourier_im_square_zero_of_no_infinite_order_atoms σ hno).const_mul 4
  simp only [mul_zero] at ht
  apply ht.congr'
  apply Eventually.of_forall
  intro H
  symm
  exact wordOddAverage_spectral_energy μ hμ f σ hσ (R H) (initialPrimes H)
    (fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).2.trans (hR H))

/-- Every natural limit law of a fixed-prime-stable finite-label array has
vanishing odd-prime-shift energy for real unit-bounded observables. -/
theorem natural_wordOddAverage_prime_energy_zero
    (L : ℕ → ℕ → A)
    (hd : ∀ p : ℕ, p.Prime → Tendsto (fun N =>
      (∑ m ∈ Icc 1 N, labelDilationDefect p (L N) m)/(N : ℝ)) atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : Tendsto D atTop atTop) (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => naturalWordEmpirical L (D j)) atTop (𝓝 μ))
    (f : A → ℝ) (hf : ∀ a, |f a| ≤ 1) (R : ℕ → ℕ) (hR : ∀ H, H ≤ R H) :
    Tendsto (fun H => ∫ x, (wordOddAverage (R H) (initialPrimes H) f x)^2
      ∂(μ : Measure (ℕ → A))) atTop (𝓝 0) := by
  obtain ⟨σ,hσ,hno⟩ := natural_word_spectral_measure_no_infinite_order_atoms L hd D hD μ hlim f hf
  exact stationary_wordOddAverage_energy_zero_of_spectrum _
    (natural_word_limit_measurePreserving L D hD μ hlim) f (σ : Measure UnitAddCircle) hσ hno R hR

/-- Actual empirical energy converges to the stationary energy at each fixed
prime cutoff. This assertion does not exchange the two limits. -/
lemma natural_wordOddAverage_energy_tendsto
    (L : ℕ → ℕ → A) (D : ℕ → ℕ) (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => naturalWordEmpirical L (D j)) atTop (𝓝 μ))
    (f : A → ℝ) (R H : ℕ) :
    Tendsto (fun j => (∑ n ∈ range (D j+1),
      (wordOddAverage R (initialPrimes H) f (wordOrbit (L (D j+1)) (n+1)))^2)/(D j+1 : ℝ))
      atTop (𝓝 (∫ x, (wordOddAverage R (initialPrimes H) f x)^2 ∂(μ : Measure (ℕ → A)))) :=
  natural_word_integral_tendsto L D μ hlim
    ⟨fun x => (wordOddAverage R (initialPrimes H) f x)^2,
      (continuous_wordOddAverage R (initialPrimes H) f).pow 2⟩

/-- Actual quantized largest-prime labels satisfy this natural-law energy
conclusion. Adjacent order cancellation is not a consequence asserted here. -/
theorem primeQuantLabel_natural_wordOddAverage_prime_energy_zero
    (Q : ℕ) (D : ℕ → ℕ) (hD : Tendsto D atTop atTop)
    (μ : ProbabilityMeasure (ℕ → Fin (Q+1)))
    (hlim : Tendsto (fun j => naturalWordEmpirical (primeQuantLabel Q) (D j)) atTop (𝓝 μ))
    (f : Fin (Q+1) → ℝ) (hf : ∀ a, |f a| ≤ 1) (R : ℕ → ℕ) (hR : ∀ H, H ≤ R H) :
    Tendsto (fun H => ∫ x, (wordOddAverage (R H) (initialPrimes H) f x)^2
      ∂(μ : Measure (ℕ → Fin (Q+1)))) atTop (𝓝 0) :=
  natural_wordOddAverage_prime_energy_zero (primeQuantLabel Q)
    (fun p hp => primeQuantLabel_natural_dilation_zero Q p hp.pos) D hD μ hlim f hf R hR

#print axioms natural_wordOddAverage_prime_energy_zero
#print axioms primeQuantLabel_natural_wordOddAverage_prime_energy_zero
end Erdos371.DilationSpectrum
