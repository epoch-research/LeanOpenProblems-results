import Submission.HarmonicWordLimit
import Submission.NaturalSpectralAtoms

/-! Natural empirical laws for endpoint-dependent finite-label arrays.
The empirical parameter N samples N+1 points and uses array row N+1.
Stationarity needs no multiplicative hypotheses. -/
namespace Erdos371.FiniteInformation
open Finset Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
set_option autoImplicit false

variable {X : Type*} [MeasurableSpace X]

noncomputable def naturalEmpiricalRaw (N : ℕ) (x : ℕ → X) : Measure X :=
  ∑ n ∈ range (N+1), ENNReal.ofReal (1/(N+1 : ℝ)) • Measure.dirac (x (n+1))

lemma naturalEmpiricalRaw_univ (N : ℕ) (x : ℕ → X) :
    naturalEmpiricalRaw N x Set.univ = 1 := by
  rw [naturalEmpiricalRaw,Measure.finset_sum_apply]
  simp only [Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  rw [mul_one_div_cancel (by positivity : (N+1 : ℝ) ≠ 0)]
  norm_num

noncomputable def naturalEmpirical (N : ℕ) (x : ℕ → X) : ProbabilityMeasure X :=
  ⟨naturalEmpiricalRaw N x,⟨naturalEmpiricalRaw_univ N x⟩⟩

lemma integral_naturalEmpirical [MeasurableSingletonClass X]
    (N : ℕ) (x : ℕ → X) (F : X → ℝ) :
    (∫ y, F y ∂(naturalEmpirical N x : Measure X)) =
      (∑ n ∈ range (N+1), F (x (n+1)))/(N+1 : ℝ) := by
  change (∫ y, F y ∂naturalEmpiricalRaw N x) = _
  rw [naturalEmpiricalRaw,integral_finset_sum_measure]
  · simp only [integral_smul_measure,integral_dirac,smul_eq_mul,
      ENNReal.toReal_ofReal (show 0 ≤ 1/(N+1 : ℝ) by positivity),sum_div]
    apply sum_congr rfl
    intro n _
    ring
  · intro n _
    exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

/-- Compactness chooses a single subsequence before the observable, even
when the sampled array changes with the endpoint. -/
theorem exists_naturalEmpirical_limit [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X] [T2Space X] [MetrizableSpace X] [SeparableSpace X]
    (x : ℕ → ℕ → X) (D : ℕ → ℕ) :
    ∃ μ : ProbabilityMeasure X, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => naturalEmpirical (D (φ j)) (x (D (φ j)+1))) atTop (𝓝 μ) := by
  obtain ⟨μ,_,φ,hφ,hlim⟩ := isCompact_univ.tendsto_subseq
    (x := fun j => naturalEmpirical (D j) (x (D j+1))) (fun j => Set.mem_univ _)
  exact ⟨μ,φ,hφ,hlim⟩

lemma natural_array_shift_difference_zero (F : ℕ → ℕ → ℝ)
    (B : ℝ) (hF : ∀ N n, |F N n| ≤ B) :
    Tendsto (fun N =>
      (∑ n ∈ range (N+1), F (N+1) (n+2))/(N+1 : ℝ) -
      (∑ n ∈ range (N+1), F (N+1) (n+1))/(N+1 : ℝ)) atTop (𝓝 0) := by
  have he (N : ℕ) :
      (∑ n ∈ range (N+1), F (N+1) (n+2))/(N+1 : ℝ) -
      (∑ n ∈ range (N+1), F (N+1) (n+1))/(N+1 : ℝ) =
      (F (N+1) (N+2)-F (N+1) 1)/(N+1 : ℝ) := by
    rw [← sub_div,← sum_sub_distrib]
    congr 1
    exact sum_range_sub (fun n => F (N+1) (n+1)) (N+1)
  simp_rw [he]
  have ht : Tendsto (fun N : ℕ => (2*B)/(N+1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (2*B)).comp (tendsto_add_atTop_nat 1)
  apply squeeze_zero_norm _ ht
  intro N
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (show 0 < (N+1 : ℝ) by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (abs_sub _ _).trans (by linarith [hF (N+1) (N+2),hF (N+1) 1])

variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A]

noncomputable def naturalWordEmpirical (L : ℕ → ℕ → A) (N : ℕ) :
    ProbabilityMeasure (ℕ → A) := naturalEmpirical N (wordOrbit (L (N+1)))

lemma natural_word_integral_tendsto (L : ℕ → ℕ → A) (D : ℕ → ℕ)
    (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => naturalWordEmpirical L (D j)) atTop (𝓝 μ))
    (F : C((ℕ → A),ℝ)) :
    Tendsto (fun j => (∑ n ∈ range (D j+1), F (wordOrbit (L (D j+1)) (n+1)))/(D j+1 : ℝ))
      atTop (𝓝 (∫ x, F x ∂(μ : Measure (ℕ → A)))) := by
  simpa only [Function.comp_def,naturalWordEmpirical,integral_naturalEmpirical] using
    (ProbabilityMeasure.continuous_integral_continuousMap F).tendsto μ |>.comp hlim

lemma natural_word_limit_shift_integral (L : ℕ → ℕ → A) (D : ℕ → ℕ)
    (hD : Tendsto D atTop atTop) (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => naturalWordEmpirical L (D j)) atTop (𝓝 μ))
    (F : C((ℕ → A),ℝ)) :
    (∫ x, F (wordShift x) ∂(μ : Measure (ℕ → A))) =
      ∫ x, F x ∂(μ : Measure (ℕ → A)) := by
  have ht₁ := natural_word_integral_tendsto L D μ hlim (F.comp wordShift)
  have ht₂ := natural_word_integral_tendsto L D μ hlim F
  have hb (N n : ℕ) : |F (wordOrbit (L N) n)| ≤ ‖F‖ := by
    simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (wordOrbit (L N) n)
  have he := (natural_array_shift_difference_zero
    (fun N n => F (wordOrbit (L N) n)) ‖F‖ hb).comp hD
  have hd := ht₁.sub ht₂
  simp only [ContinuousMap.comp_apply,wordShift_wordOrbit] at hd
  exact sub_eq_zero.mp (tendsto_nhds_unique hd he)

/-- Stationarity of every natural empirical subsequential law. -/
theorem natural_word_limit_measurePreserving (L : ℕ → ℕ → A) (D : ℕ → ℕ)
    (hD : Tendsto D atTop atTop) (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => naturalWordEmpirical L (D j)) atTop (𝓝 μ)) :
    MeasurePreserving wordShift (μ : Measure (ℕ → A)) (μ : Measure (ℕ → A)) := by
  refine ⟨wordShift.continuous.measurable,?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro F
  change (∫ x, F.toContinuousMap x ∂Measure.map wordShift (μ : Measure (ℕ → A))) = _
  rw [integral_map wordShift.continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable]
  exact natural_word_limit_shift_integral L D hD μ hlim F.toContinuousMap

/-- One stationary natural law captures all continuous tests simultaneously. -/
theorem exists_stationary_natural_word_limit (L : ℕ → ℕ → A) (D : ℕ → ℕ)
    (hD : Tendsto D atTop atTop) :
    ∃ μ : ProbabilityMeasure (ℕ → A), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => naturalWordEmpirical L (D (φ j))) atTop (𝓝 μ) ∧
      MeasurePreserving wordShift (μ : Measure (ℕ → A)) (μ : Measure (ℕ → A)) := by
  obtain ⟨μ,φ,hφ,hlim⟩ := exists_naturalEmpirical_limit (fun N => wordOrbit (L N)) D
  exact ⟨μ,φ,hφ,hlim,natural_word_limit_measurePreserving L (D ∘ φ)
    (hD.comp hφ.tendsto_atTop) μ hlim⟩

#print axioms exists_stationary_natural_word_limit
end Erdos371.FiniteInformation
