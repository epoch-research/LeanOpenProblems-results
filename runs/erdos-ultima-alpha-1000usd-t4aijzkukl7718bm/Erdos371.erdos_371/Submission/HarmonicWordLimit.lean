import Submission.HarmonicEmpiricalMeasure

/-! Stationary harmonic limit measures of fixed finite label sequences.
All finite-window dilation inequalities hold in one common limit. -/
namespace Erdos371.FiniteInformation
open Finset Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
set_option autoImplicit false

variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A]

noncomputable def wordOrbit (L : ℕ → A) (n : ℕ) : ℕ → A := fun k => L (n+k)

def wordShift : C((ℕ → A), (ℕ → A)) where
  toFun x := fun k => x (k+1)
  continuous_toFun := continuous_pi (fun k => continuous_apply (k+1))

def wordCylinder {K : ℕ} (F : (Fin K → A) → ℝ) : C((ℕ → A),ℝ) where
  toFun x := F (fun k => x k)
  continuous_toFun := continuous_of_discreteTopology.comp (continuous_pi fun k => continuous_apply (k : ℕ))

def wordDilationCylinder {K : ℕ} (p : ℕ) (F : (Fin K → A) → ℝ) : C((ℕ → A),ℝ) where
  toFun x := F (fun k => x (p*k))
  continuous_toFun := continuous_of_discreteTopology.comp (continuous_pi fun k => continuous_apply (p*k))

lemma wordShift_wordOrbit (L : ℕ → A) (n : ℕ) : wordShift (wordOrbit L n) = wordOrbit L (n+1) := by
  funext k
  change L (n+(k+1)) = L (n+1+k)
  congr 1
  omega

lemma harmonic_word_integral_tendsto (L : ℕ → A) (D : ℕ → ℕ)
    (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => harmonicEmpirical (D j) (wordOrbit L)) atTop (𝓝 μ))
    (F : C((ℕ → A),ℝ)) :
    Tendsto (fun j => harmonicMean (D j+1) (fun n => F (wordOrbit L n))) atTop
      (𝓝 (∫ x, F x ∂(μ : Measure (ℕ → A)))) := by
  simpa only [Function.comp_def,integral_harmonicEmpirical] using
    (ProbabilityMeasure.continuous_integral_continuousMap F).tendsto μ |>.comp hlim

lemma harmonic_word_limit_shift_integral (L : ℕ → A) (D : ℕ → ℕ) (hD : Tendsto D atTop atTop)
    (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => harmonicEmpirical (D j) (wordOrbit L)) atTop (𝓝 μ))
    (F : C((ℕ → A),ℝ)) :
    (∫ x, F (wordShift x) ∂(μ : Measure (ℕ → A))) = ∫ x, F x ∂(μ : Measure (ℕ → A)) := by
  have ht₁ := harmonic_word_integral_tendsto L D μ hlim (F.comp wordShift)
  have ht₂ := harmonic_word_integral_tendsto L D μ hlim F
  have hb (n : ℕ) : |F (wordOrbit L n)| ≤ ‖F‖+1 := by
    have hh := F.norm_coe_le_norm (wordOrbit L n)
    rw [Real.norm_eq_abs] at hh
    linarith
  have he := (harmonicMean_succ_difference_zero (fun n => F (wordOrbit L n)) (‖F‖+1)
    (by positivity) hb).comp hD
  have hd := ht₁.sub ht₂
  simp only [ContinuousMap.comp_apply,wordShift_wordOrbit] at hd
  exact sub_eq_zero.mp (tendsto_nhds_unique hd he)

/-- Stationarity holds as equality of actual measures, not merely for a
finite list of cylinder tests. -/
theorem harmonic_word_limit_measurePreserving (L : ℕ → A) (D : ℕ → ℕ) (hD : Tendsto D atTop atTop)
    (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => harmonicEmpirical (D j) (wordOrbit L)) atTop (𝓝 μ)) :
    MeasurePreserving wordShift (μ : Measure (ℕ → A)) (μ : Measure (ℕ → A)) := by
  refine ⟨wordShift.continuous.measurable,?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro F
  change (∫ x, F.toContinuousMap x ∂Measure.map wordShift (μ : Measure (ℕ → A))) = _
  rw [integral_map wordShift.continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable]
  exact harmonic_word_limit_shift_integral L D hD μ hlim F.toContinuousMap

/-- Common-subsequence dilation domination for every fixed finite window. -/
theorem harmonic_word_limit_dilation_cylinder (L : ℕ → A)
    (hL : ∀ p, 0 < p → Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : Tendsto D atTop atTop) (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => harmonicEmpirical (D j) (wordOrbit L)) atTop (𝓝 μ))
    (p K : ℕ) (hp : 0 < p) (F : (Fin K → A) → ℝ) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    (∫ x, F (fun k => x k) ∂(μ : Measure (ℕ → A))) ≤
      p*∫ x, F (fun k => x (p*k)) ∂(μ : Measure (ℕ → A)) := by
  exact harmonic_window_dilation_limit_le p K hp L F hF (hL p hp) D hD _ _
    (harmonic_word_integral_tendsto L D μ hlim (wordCylinder F))
    (harmonic_word_integral_tendsto L D μ hlim (wordDilationCylinder p F))

/-- One harmonic subsequential measure has stationarity and all the fixed
window dilation inequalities simultaneously. The label sequence itself is
fixed, independent of the endpoint and of the extracted subsequence. -/
theorem exists_stationary_harmonic_word_limit (L : ℕ → A)
    (hL : ∀ p, 0 < p → Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : Tendsto D atTop atTop) :
    ∃ μ : ProbabilityMeasure (ℕ → A), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => harmonicEmpirical (D (φ j)) (wordOrbit L)) atTop (𝓝 μ) ∧
      MeasurePreserving wordShift (μ : Measure (ℕ → A)) (μ : Measure (ℕ → A)) ∧
      ∀ p K : ℕ, 0 < p → ∀ F : (Fin K → A) → ℝ, (∀ x, 0 ≤ F x ∧ F x ≤ 1) →
        (∫ x, F (fun k => x k) ∂(μ : Measure (ℕ → A))) ≤
          p*∫ x, F (fun k => x (p*k)) ∂(μ : Measure (ℕ → A)) := by
  obtain ⟨μ,φ,hφ,hlim⟩ := exists_harmonicEmpirical_limit (wordOrbit L) D
  have hE := hD.comp hφ.tendsto_atTop
  refine ⟨μ,φ,hφ,hlim,harmonic_word_limit_measurePreserving L (D ∘ φ) hE μ hlim,?_⟩
  exact fun p K hp F hF => harmonic_word_limit_dilation_cylinder L hL (D ∘ φ) hE μ hlim p K hp F hF

#print axioms exists_stationary_harmonic_word_limit
end Erdos371.FiniteInformation
