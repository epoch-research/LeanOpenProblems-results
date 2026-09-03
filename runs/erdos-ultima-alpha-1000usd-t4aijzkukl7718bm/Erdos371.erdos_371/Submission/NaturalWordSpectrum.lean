import Submission.NaturalWordLimit
import Submission.PrimeLogQuantization

/-! Actual natural empirical word limits have coordinate spectral measures
with no infinite-order atoms. This does not assert dilation domination for
all natural word cylinders, or symmetry of adjacent coordinates. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex FiniteInformation
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A]

omit [Fintype A] [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A] in
lemma real_wordCovariance_nat (μ : Measure (ℕ → A)) (f : A → ℝ) (h : ℕ) :
    wordCovariance μ (fun a => (f a : ℂ)) (h : ℤ) =
      ((∫ x, f (x 0)*f (x h) ∂μ : ℝ) : ℂ) := by
  simp only [wordCovariance,Int.toNat_natCast,Int.toNat_neg_natCast,
    Complex.conj_ofReal,← Complex.ofReal_mul,integral_complex_ofReal]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  ring

lemma natural_word_covariance_tendsto (L : ℕ → ℕ → A) (D : ℕ → ℕ)
    (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => naturalWordEmpirical L (D j)) atTop (𝓝 μ))
    (f : A → ℝ) (h : ℕ) :
    Tendsto (fun j => (((∑ n ∈ range (D j+1),
      f (L (D j+1) (n+1))*f (L (D j+1) (n+1+h)))/(D j+1 : ℝ) : ℝ) : ℂ))
      atTop (𝓝 (wordCovariance (μ : Measure (ℕ → A)) (fun a => (f a : ℂ)) (h : ℤ))) := by
  let F : C((ℕ → A),ℝ) :=
    ⟨fun x => f (x 0)*f (x h),
      (continuous_of_discreteTopology.comp (continuous_apply 0)).mul
        (continuous_of_discreteTopology.comp (continuous_apply h))⟩
  have ht := (Complex.continuous_ofReal.tendsto _).comp
    (natural_word_integral_tendsto L D μ hlim F)
  simpa only [Function.comp_def,F,ContinuousMap.coe_mk,wordOrbit,Nat.add_zero,
    real_wordCovariance_nat] using ht

omit [Fintype A] [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] in
lemma label_observable_dilation_error (L : ℕ → A) (p n : ℕ)
    (f : A → ℝ) (hf : ∀ a, |f a| ≤ 1) :
    |f (L (p*n))-f (L n)| ≤ 2*labelDilationDefect p L n := by
  classical
  unfold labelDilationDefect
  split_ifs with he
  · have hb := abs_sub (f (L (p*n))) (f (L n))
    linarith [hf (L (p*n)),hf (L n)]
  · simp [not_not.mp he]

omit [Fintype A] [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] in
lemma stable_label_observable_dilation_zero (L : ℕ → ℕ → A)
    (hd : ∀ p : ℕ, p.Prime → Tendsto (fun N =>
      (∑ m ∈ Icc 1 N, labelDilationDefect p (L N) m)/(N : ℝ)) atTop (𝓝 0))
    (f : A → ℝ) (hf : ∀ a, |f a| ≤ 1) (p : ℕ) (hp : p.Prime) :
    Tendsto (fun N => (∑ m ∈ Icc 1 N, |f (L N (p*m))-f (L N m)|)/(N : ℝ))
      atTop (𝓝 0) := by
  have ht := (hd p hp).const_mul 2
  simp only [mul_zero] at ht
  apply squeeze_zero (fun N => div_nonneg (sum_nonneg (fun _ _ => abs_nonneg _)) (Nat.cast_nonneg N)) _ ht
  intro N
  rw [← mul_div_assoc,mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact sum_le_sum (fun m _ => label_observable_dilation_error (L N) p m f hf)

/-- The same natural word law works for every real unit-bounded coordinate
observable. A separate subsequence for each observable is not needed. -/
theorem natural_word_spectral_measure_no_infinite_order_atoms
    (L : ℕ → ℕ → A)
    (hd : ∀ p : ℕ, p.Prime → Tendsto (fun N =>
      (∑ m ∈ Icc 1 N, labelDilationDefect p (L N) m)/(N : ℝ)) atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : Tendsto D atTop atTop) (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => naturalWordEmpirical L (D j)) atTop (𝓝 μ))
    (f : A → ℝ) (hf : ∀ a, |f a| ≤ 1) :
    ∃ σ : FiniteMeasure UnitAddCircle,
      (∀ k : ℤ, (∫ x, fourier k x ∂(σ : Measure UnitAddCircle)) =
        wordCovariance (μ : Measure (ℕ → A)) (fun a => (f a : ℂ)) k) ∧
      ∀ x : UnitAddCircle, ¬IsOfFinAddOrder x → (σ : Measure UnitAddCircle) {x}=0 := by
  obtain ⟨σ,hσ⟩ := exists_word_spectral_measure (μ : Measure (ℕ → A))
    (natural_word_limit_measurePreserving L D hD μ hlim) (fun a => (f a : ℂ))
  refine ⟨σ,hσ,?_⟩
  apply natural_covariance_spectral_no_infinite_order_atoms
    (fun N n => f (L N n)) (fun N n => hf (L N n))
    (stable_label_observable_dilation_zero L hd f hf) (fun j => D j+1)
    ((tendsto_add_atTop_nat 1).comp hD) (σ : Measure UnitAddCircle)
  intro h
  simpa only [Nat.cast_add,Nat.cast_one,hσ] using
    natural_word_covariance_tendsto L D μ hlim f h

lemma primeQuantLabel_natural_dilation_zero (Q p : ℕ) (hp : 0 < p) :
    Tendsto (fun N => (∑ m ∈ Icc 1 N,
      labelDilationDefect p (primeQuantLabel Q N) m)/(N : ℝ)) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [primeQuantLabel_eventually_mul Q p] with N hN
  have he (m : ℕ) : labelDilationDefect p (primeQuantLabel Q N) m=0 := by
    simp only [labelDilationDefect,hN p hp (le_refl p) m,ne_eq,not_true_eq_false,if_false]
  simp only [he,sum_const_zero,zero_div]

/-- An actual natural spectral limit for finite quantized largest-prime
labels, common to all real unit-bounded observables. -/
theorem exists_primeQuantLabel_natural_spectral_limit
    (Q : ℕ) (D : ℕ → ℕ) (hD : Tendsto D atTop atTop) :
    ∃ μ : ProbabilityMeasure (ℕ → Fin (Q+1)), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => naturalWordEmpirical (primeQuantLabel Q) (D (φ j))) atTop (𝓝 μ) ∧
      MeasurePreserving wordShift (μ : Measure (ℕ → Fin (Q+1))) (μ : Measure (ℕ → Fin (Q+1))) ∧
      ∀ f : Fin (Q+1) → ℝ, (∀ a, |f a| ≤ 1) → ∃ σ : FiniteMeasure UnitAddCircle,
        (∀ k : ℤ, (∫ x, fourier k x ∂(σ : Measure UnitAddCircle)) =
          wordCovariance (μ : Measure (ℕ → Fin (Q+1))) (fun a => (f a : ℂ)) k) ∧
        ∀ x : UnitAddCircle, ¬IsOfFinAddOrder x → (σ : Measure UnitAddCircle) {x}=0 := by
  obtain ⟨μ,φ,hφ,hlim,hμ⟩ := exists_stationary_natural_word_limit (primeQuantLabel Q) D hD
  refine ⟨μ,φ,hφ,hlim,hμ,fun f hf => ?_⟩
  exact natural_word_spectral_measure_no_infinite_order_atoms (primeQuantLabel Q)
    (fun p hp => primeQuantLabel_natural_dilation_zero Q p hp.pos)
    (D ∘ φ) (hD.comp hφ.tendsto_atTop) μ hlim f hf

#print axioms natural_word_spectral_measure_no_infinite_order_atoms
#print axioms exists_primeQuantLabel_natural_spectral_limit
end Erdos371.DilationSpectrum
