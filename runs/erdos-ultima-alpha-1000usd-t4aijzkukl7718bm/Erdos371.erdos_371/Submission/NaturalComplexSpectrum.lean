import Submission.NaturalWordSpectrum

/-! Passing natural coordinate atom exclusion from real to complex
observables by positive spectral energy domination. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex FiniteInformation
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A]

lemma complex_sum_re_im_energy_bound {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (v : ι → ℂ) :
    ‖∑ i, a i*v i‖^2 ≤
      2*(‖∑ i, a i*(v i).re‖^2+‖∑ i, a i*(v i).im‖^2) := by
  have he : (∑ i, a i*v i) =
      (∑ i, a i*(v i).re)+(∑ i, a i*(v i).im)*Complex.I := by
    rw [sum_mul,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [mul_assoc,← mul_add,Complex.re_add_im]
  have hn := norm_add_le (∑ i, a i*(v i).re) ((∑ i, a i*(v i).im)*Complex.I)
  simp only [norm_mul,Complex.norm_I,mul_one,← he] at hn
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  nlinarith [sq_nonneg (‖∑ i, a i*(v i).re‖-‖∑ i, a i*(v i).im‖)]

lemma word_spectral_re_im_energy_bound
    (μ : Measure (ℕ → A)) [IsFiniteMeasure μ] (hμ : MeasurePreserving wordShift μ μ)
    (f : A → ℂ) (σ σr σi : Measure UnitAddCircle)
    [IsFiniteMeasure σ] [IsFiniteMeasure σr] [IsFiniteMeasure σi]
    (hσ : ∀ k : ℤ, (∫ x, fourier k x ∂σ) = wordCovariance μ f k)
    (hr : ∀ k : ℤ, (∫ x, fourier k x ∂σr) = wordCovariance μ (fun a => ((f a).re : ℂ)) k)
    (hi : ∀ k : ℤ, (∫ x, fourier k x ∂σi) = wordCovariance μ (fun a => ((f a).im : ℂ)) k)
    (K : ℕ) (a : Fin K → ℂ) :
    (∫ x, ‖spectralPolynomial a (fun k => k) x‖^2 ∂σ) ≤
      2*((∫ x, ‖spectralPolynomial a (fun k => k) x‖^2 ∂σr)+
        (∫ x, ‖spectralPolynomial a (fun k => k) x‖^2 ∂σi)) := by
  rw [spectral_word_energy μ hμ f σ hσ a (fun k => k),
    spectral_word_energy μ hμ (fun b => ((f b).re : ℂ)) σr hr a (fun k => k),
    spectral_word_energy μ hμ (fun b => ((f b).im : ℂ)) σi hi a (fun k => k)]
  have hint (g : A → ℂ) : Integrable (fun x : ℕ → A => ‖∑ k : Fin K, a k*g (x k)‖^2) μ := by
    have hc : Continuous (fun x : ℕ → A => ∑ k : Fin K, a k*g (x k)) := by
      apply continuous_finset_sum
      intro k _
      exact continuous_const.mul (continuous_word_eval g k)
    exact (hc.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_add (hint (fun b => ((f b).re : ℂ))) (hint (fun b => ((f b).im : ℂ))),
    ← integral_const_mul]
  apply integral_mono (hint f)
    (((hint (fun b => ((f b).re : ℂ))).add (hint (fun b => ((f b).im : ℂ)))).const_mul 2)
  intro x
  exact complex_sum_re_im_energy_bound a (fun k => f (x k))

/-- The complex observable's atom is bounded by the two real observable
atoms. This uses positive measures and does not discard mixed covariances. -/
theorem word_spectral_re_im_atom_bound
    (μ : Measure (ℕ → A)) [IsFiniteMeasure μ] (hμ : MeasurePreserving wordShift μ μ)
    (f : A → ℂ) (σ σr σi : Measure UnitAddCircle)
    [IsFiniteMeasure σ] [IsFiniteMeasure σr] [IsFiniteMeasure σi]
    (hσ : ∀ k : ℤ, (∫ x, fourier k x ∂σ) = wordCovariance μ f k)
    (hr : ∀ k : ℤ, (∫ x, fourier k x ∂σr) = wordCovariance μ (fun a => ((f a).re : ℂ)) k)
    (hi : ∀ k : ℤ, (∫ x, fourier k x ∂σi) = wordCovariance μ (fun a => ((f a).im : ℂ)) k)
    (x : UnitAddCircle) : σ.real {x} ≤ 2*(σr.real {x}+σi.real {x}) := by
  have ht := fourierAverage_integral_atom σ (ContinuousMap.id _) x
  have htr := fourierAverage_integral_atom σr (ContinuousMap.id _) x
  have hti := fourierAverage_integral_atom σi (ContinuousMap.id _) x
  have hh := le_of_tendsto_of_tendsto' ht ((htr.add hti).const_mul 2) (fun N => ?_)
  · simpa only [ContinuousMap.id_apply,Set.setOf_eq_eq_singleton] using hh
  · simpa only [ContinuousMap.id_apply,fourierAverage_eq_spectralPolynomial] using
      word_spectral_re_im_energy_bound μ hμ f σ σr σi hσ hr hi (N+1)
        (fun k : Fin (N+1) => conj (fourier (k : ℤ) x)/(N+1 : ℂ))

/-- Complex coordinate spectra in an actual natural word law also have no
infinite-order atoms, provided each real component is unit bounded. -/
theorem natural_word_complex_spectral_measure_no_infinite_order_atoms
    (L : ℕ → ℕ → A)
    (hd : ∀ p : ℕ, p.Prime → Tendsto (fun N =>
      (∑ m ∈ Icc 1 N, labelDilationDefect p (L N) m)/(N : ℝ)) atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : Tendsto D atTop atTop) (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => naturalWordEmpirical L (D j)) atTop (𝓝 μ))
    (f : A → ℂ) (hfr : ∀ a, |(f a).re| ≤ 1) (hfi : ∀ a, |(f a).im| ≤ 1) :
    ∃ σ : FiniteMeasure UnitAddCircle,
      (∀ k : ℤ, (∫ x, fourier k x ∂(σ : Measure UnitAddCircle)) =
        wordCovariance (μ : Measure (ℕ → A)) f k) ∧
      ∀ x : UnitAddCircle, ¬IsOfFinAddOrder x → (σ : Measure UnitAddCircle) {x}=0 := by
  have hμ := natural_word_limit_measurePreserving L D hD μ hlim
  obtain ⟨σ,hσ⟩ := exists_word_spectral_measure (μ : Measure (ℕ → A)) hμ f
  obtain ⟨σr,hr,hnr⟩ := natural_word_spectral_measure_no_infinite_order_atoms L hd D hD μ hlim
    (fun a => (f a).re) hfr
  obtain ⟨σi,hi,hni⟩ := natural_word_spectral_measure_no_infinite_order_atoms L hd D hD μ hlim
    (fun a => (f a).im) hfi
  refine ⟨σ,hσ,fun x hx => ?_⟩
  have hb := word_spectral_re_im_atom_bound (μ : Measure (ℕ → A)) hμ f
    (σ : Measure UnitAddCircle) (σr : Measure UnitAddCircle) (σi : Measure UnitAddCircle) hσ hr hi x
  have hrzero : (σr : Measure UnitAddCircle).real {x}=0 := by simp [Measure.real,hnr x hx]
  have hizero : (σi : Measure UnitAddCircle).real {x}=0 := by simp [Measure.real,hni x hx]
  rw [hrzero,hizero,add_zero,mul_zero] at hb
  have he : (σ : Measure UnitAddCircle).real {x}=0 := le_antisymm hb measureReal_nonneg
  exact ((ENNReal.toReal_eq_zero_iff ((σ : Measure UnitAddCircle) {x})).mp he).resolve_right
    (measure_ne_top (σ : Measure UnitAddCircle) {x})

#print axioms word_spectral_re_im_atom_bound
#print axioms natural_word_complex_spectral_measure_no_infinite_order_atoms
end Erdos371.DilationSpectrum
