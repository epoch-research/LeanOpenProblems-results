import Submission.ShiftedHarmonicPrimeTransfer
import Submission.HarmonicWordLimit

/-! Genuine stationary word measures from translated harmonic intervals.
The interval endpoints may both vary; their harmonic mass must diverge. -/
namespace Erdos371.FiniteInformation
open Finset Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
set_option autoImplicit false

lemma shiftedHarmonicMean_shift_zero (F : ℕ → ℝ) (B : ℝ) (hB : 0 < B)
    (hF : ∀ n, |F n| ≤ B) (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j) (fun n => F (n+1))-
      shiftedHarmonicMean (A j) (M j) F) atTop (𝓝 0) := by
  let G := fun n => F n/B
  have hG : ∀ n, |G n| ≤ 1 := by
    intro n
    dsimp [G]
    rw [abs_div,abs_of_pos hB]
    exact (div_le_one hB).mpr (hF n)
  have ht : Tendsto (fun j => shiftedHarmonicMean (A j) (M j) (fun n => G (n+1))-
      shiftedHarmonicMean (A j) (M j) G) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ (tendsto_const_nhds.div_atTop hH :
      Tendsto (fun j => (4 : ℝ)/shiftedHarmonicMass (A j) (M j)) atTop (𝓝 0))
    intro j
    simpa only [Real.norm_eq_abs] using shiftedHarmonicMean_shift_bound (A j) (M j) G hG
  have hfg (n : ℕ) : B*G n=F n := by dsimp [G]; field_simp
  convert ht.const_mul B using 1
  · funext j
    rw [mul_sub,← shiftedHarmonicMean_const_mul,← shiftedHarmonicMean_const_mul]
    simp_rw [hfg]
  · simp

noncomputable def shiftedHarmonicWeight (A N n : ℕ) : ℝ :=
  (1/(A+n+1 : ℝ))/shiftedHarmonicMass A N

lemma shiftedHarmonicWeight_nonneg (A N n : ℕ) : 0 ≤ shiftedHarmonicWeight A N n := by
  unfold shiftedHarmonicWeight
  exact div_nonneg (by positivity) (shiftedHarmonicMass_pos A N).le

lemma shiftedHarmonicWeight_sum (A N : ℕ) :
    ∑ n ∈ range (N+1), shiftedHarmonicWeight A N n = 1 := by
  unfold shiftedHarmonicWeight
  rw [← sum_div]
  exact div_self (shiftedHarmonicMass_pos A N).ne'

variable {X : Type*} [MeasurableSpace X]

noncomputable def shiftedEmpiricalRaw (A N : ℕ) (x : ℕ → X) : Measure X :=
  ∑ n ∈ range (N+1), ENNReal.ofReal (shiftedHarmonicWeight A N n) • Measure.dirac (x (A+n+1))

lemma shiftedEmpiricalRaw_univ (A N : ℕ) (x : ℕ → X) : shiftedEmpiricalRaw A N x Set.univ = 1 := by
  rw [shiftedEmpiricalRaw,Measure.finset_sum_apply]
  simp only [Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => shiftedHarmonicWeight_nonneg A N n),shiftedHarmonicWeight_sum]
  norm_num

noncomputable def shiftedEmpirical (A N : ℕ) (x : ℕ → X) : ProbabilityMeasure X :=
  ⟨shiftedEmpiricalRaw A N x,⟨shiftedEmpiricalRaw_univ A N x⟩⟩

lemma integral_shiftedEmpirical [MeasurableSingletonClass X] (A N : ℕ) (x : ℕ → X) (F : X → ℝ) :
    (∫ y, F y ∂(shiftedEmpirical A N x : Measure X)) = shiftedHarmonicMean A N (fun n => F (x n)) := by
  change (∫ y, F y ∂shiftedEmpiricalRaw A N x) = _
  rw [shiftedEmpiricalRaw,integral_finset_sum_measure]
  · simp only [integral_smul_measure,integral_dirac,smul_eq_mul]
    rw [shiftedHarmonicMean,shiftedHarmonicRaw,sum_div]
    apply sum_congr rfl
    intro n _
    rw [ENNReal.toReal_ofReal (shiftedHarmonicWeight_nonneg A N n),shiftedHarmonicWeight]
    ring
  · intro n _
    exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

theorem exists_shiftedEmpirical_limit [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X] [T2Space X] [MetrizableSpace X] [SeparableSpace X]
    (x : ℕ → X) (A M : ℕ → ℕ) :
    ∃ μ : ProbabilityMeasure X, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => shiftedEmpirical (A (φ j)) (M (φ j)) x) atTop (𝓝 μ) := by
  obtain ⟨μ,_,φ,hφ,hlim⟩ := isCompact_univ.tendsto_subseq
    (x := fun j => shiftedEmpirical (A j) (M j) x) (fun j => Set.mem_univ _)
  exact ⟨μ,φ,hφ,hlim⟩

variable {B : Type*} [Fintype B] [TopologicalSpace B] [DiscreteTopology B]
    [MeasurableSpace B] [BorelSpace B]

lemma shifted_word_integral_tendsto (L : ℕ → B) (A M : ℕ → ℕ)
    (μ : ProbabilityMeasure (ℕ → B))
    (hlim : Tendsto (fun j => shiftedEmpirical (A j) (M j) (wordOrbit L)) atTop (𝓝 μ))
    (F : C((ℕ → B),ℝ)) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j) (fun n => F (wordOrbit L n))) atTop
      (𝓝 (∫ x, F x ∂(μ : Measure (ℕ → B)))) := by
  simpa only [Function.comp_def,integral_shiftedEmpirical] using
    (ProbabilityMeasure.continuous_integral_continuousMap F).tendsto μ |>.comp hlim

lemma shifted_word_limit_shift_integral (L : ℕ → B) (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop)
    (μ : ProbabilityMeasure (ℕ → B))
    (hlim : Tendsto (fun j => shiftedEmpirical (A j) (M j) (wordOrbit L)) atTop (𝓝 μ))
    (F : C((ℕ → B),ℝ)) :
    (∫ x, F (wordShift x) ∂(μ : Measure (ℕ → B))) = ∫ x, F x ∂(μ : Measure (ℕ → B)) := by
  have ht₁ := shifted_word_integral_tendsto L A M μ hlim (F.comp wordShift)
  have ht₂ := shifted_word_integral_tendsto L A M μ hlim F
  have hb (n : ℕ) : |F (wordOrbit L n)| ≤ ‖F‖+1 := by
    have hh := F.norm_coe_le_norm (wordOrbit L n)
    rw [Real.norm_eq_abs] at hh
    linarith
  have he := shiftedHarmonicMean_shift_zero (fun n => F (wordOrbit L n)) (‖F‖+1) (by positivity) hb A M hH
  have hd := ht₁.sub ht₂
  simp only [ContinuousMap.comp_apply,wordShift_wordOrbit] at hd
  exact sub_eq_zero.mp (tendsto_nhds_unique hd he)

theorem shifted_word_limit_measurePreserving (L : ℕ → B) (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop)
    (μ : ProbabilityMeasure (ℕ → B))
    (hlim : Tendsto (fun j => shiftedEmpirical (A j) (M j) (wordOrbit L)) atTop (𝓝 μ)) :
    MeasurePreserving wordShift (μ : Measure (ℕ → B)) (μ : Measure (ℕ → B)) := by
  refine ⟨wordShift.continuous.measurable,?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro F
  change (∫ x, F.toContinuousMap x ∂Measure.map wordShift (μ : Measure (ℕ → B))) = _
  rw [integral_map wordShift.continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable]
  exact shifted_word_limit_shift_integral L A M hH μ hlim F.toContinuousMap

theorem shifted_word_limit_dilation_cylinder (L : ℕ → B)
    (hL : ∀ p, 0 < p → Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (A M : ℕ → ℕ) (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop)
    (μ : ProbabilityMeasure (ℕ → B))
    (hlim : Tendsto (fun j => shiftedEmpirical (A j) (M j) (wordOrbit L)) atTop (𝓝 μ))
    (p K : ℕ) (hp : 0 < p) (F : (Fin K → B) → ℝ) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    (∫ x, F (fun k => x k) ∂(μ : Measure (ℕ → B))) ≤
      p*∫ x, F (fun k => x (p*k)) ∂(μ : Measure (ℕ → B)) := by
  have ha := shifted_word_integral_tendsto L A M μ hlim (wordCylinder F)
  have hb := shifted_word_integral_tendsto L A M μ hlim (wordDilationCylinder p F)
  have hh := le_of_tendsto_of_tendsto' ha
    ((hb.const_mul (p : ℝ)).add (shiftedWindowDilationBudget_zero p K L (hL p hp) A M hH))
    (fun j => shifted_harmonic_window_dilation_le (A j) (M j) p K hp L F hF)
  simpa only [add_zero] using hh

#print axioms exists_shiftedEmpirical_limit
#print axioms shifted_word_limit_measurePreserving
#print axioms shifted_word_limit_dilation_cylinder
end Erdos371.FiniteInformation
