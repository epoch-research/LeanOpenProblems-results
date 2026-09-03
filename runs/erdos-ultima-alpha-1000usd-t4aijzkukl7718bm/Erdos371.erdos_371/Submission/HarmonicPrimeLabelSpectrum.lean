import Submission.FourierAtomTests

/-! Irrational-atom exclusion for spectral measures of actual fixed local
prime labels in a common stationary harmonic limit. This is not a natural
density claim, nor yet a prime-averaged skew cancellation theorem. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex FiniteInformation
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A]

/-- Stationarity, finite-window dilation domination, and positivity exclude
all irrational atoms from every coordinate observable's spectral measure. -/
theorem exists_word_spectral_measure_no_infinite_order_atoms
    (μ : Measure (ℕ → A)) [IsFiniteMeasure μ] (hμ : MeasurePreserving wordShift μ μ)
    (hdom : ∀ p K : ℕ, 0 < p → ∀ F : (Fin K → A) → ℝ, (∀ x, 0 ≤ F x ∧ F x ≤ 1) →
      (∫ x, F (fun k => x k) ∂μ) ≤ p*∫ x, F (fun k => x (p*k)) ∂μ)
    (f : A → ℂ) :
    ∃ σ : FiniteMeasure UnitAddCircle,
      (∀ k : ℤ, (∫ x, fourier k x ∂(σ : Measure UnitAddCircle)) = wordCovariance μ f k) ∧
      ∀ x : UnitAddCircle, ¬IsOfFinAddOrder x → (σ : Measure UnitAddCircle) {x} = 0 := by
  obtain ⟨σ,hσ⟩ := exists_word_spectral_measure μ hμ f
  refine ⟨σ,hσ,?_⟩
  intro x hx
  apply singleton_zero_of_dilation_fiber_bound (σ : Measure UnitAddCircle) x hx
  · intro n
    exact (measurableSet_singleton x).preimage (continuous_id.nsmul n).measurable
  · intro p hp
    exact atom_fiber_bound_of_polynomial_energy (σ : Measure UnitAddCircle) p
      (fun K a => spectral_polynomial_dilation_bound μ hμ f (σ : Measure UnitAddCircle) hσ p K
        (hdom p K hp) a) x

theorem exists_word_spectral_measure_no_irrational_atoms
    (μ : Measure (ℕ → A)) [IsFiniteMeasure μ] (hμ : MeasurePreserving wordShift μ μ)
    (hdom : ∀ p K : ℕ, 0 < p → ∀ F : (Fin K → A) → ℝ, (∀ x, 0 ≤ F x ∧ F x ≤ 1) →
      (∫ x, F (fun k => x k) ∂μ) ≤ p*∫ x, F (fun k => x (p*k)) ∂μ)
    (f : A → ℂ) :
    ∃ σ : FiniteMeasure UnitAddCircle,
      (∀ k : ℤ, (∫ x, fourier k x ∂(σ : Measure UnitAddCircle)) = wordCovariance μ f k) ∧
      ∀ a : ℝ, Irrational a → (σ : Measure UnitAddCircle) {(a : UnitAddCircle)} = 0 := by
  obtain ⟨σ,hσ,hno⟩ := exists_word_spectral_measure_no_infinite_order_atoms μ hμ hdom f
  refine ⟨σ,hσ,fun a ha => hno _ ?_⟩
  simpa only [AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div,div_one] using ha

lemma localPrimeLabel_mean_dilation_defect_zero (Q p : ℕ) (hp : 0 < p) :
    Tendsto (fun N => prefixMean N (labelDilationDefect p (localPrimeLabel Q))) atTop (𝓝 0) := by
  convert localPrimeLabel_mul_mean_zero Q p hp using 1
  congr 1
  funext N
  congr 1
  funext n
  unfold labelDilationDefect
  split_ifs <;> rfl

/-- One common harmonic subsequential law for the actual fixed labels, with
stationarity and irrational-atom exclusion for every coordinate observable.
The law is chosen before the observable; no observable-dependent endpoint
subsequence is substituted into the entropy transfer. -/
theorem exists_localPrimeLabel_harmonic_spectral_limit
    (Q : ℕ) (D : ℕ → ℕ) (hD : Tendsto D atTop atTop) :
    ∃ μ : ProbabilityMeasure (ℕ → Fin (Q+1)), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => harmonicEmpirical (D (φ j)) (wordOrbit (localPrimeLabel Q))) atTop (𝓝 μ) ∧
      MeasurePreserving wordShift (μ : Measure (ℕ → Fin (Q+1))) (μ : Measure (ℕ → Fin (Q+1))) ∧
      ∀ f : Fin (Q+1) → ℂ, ∃ σ : FiniteMeasure UnitAddCircle,
        (∀ k : ℤ, (∫ x, fourier k x ∂(σ : Measure UnitAddCircle)) =
          wordCovariance (μ : Measure (ℕ → Fin (Q+1))) f k) ∧
        ∀ a : ℝ, Irrational a → (σ : Measure UnitAddCircle) {(a : UnitAddCircle)} = 0 := by
  obtain ⟨μ,φ,hφ,hlim,hμ,hdom⟩ := exists_stationary_harmonic_word_limit (localPrimeLabel Q)
    (localPrimeLabel_mean_dilation_defect_zero Q) D hD
  exact ⟨μ,φ,hφ,hlim,hμ,fun f => exists_word_spectral_measure_no_irrational_atoms _ hμ hdom f⟩

#print axioms exists_localPrimeLabel_harmonic_spectral_limit
end Erdos371.DilationSpectrum
