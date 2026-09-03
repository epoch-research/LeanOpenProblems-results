import Submission.StationaryPrimeSkew

/-! Harmonic reversal for fixed finite labels with negligible fixed-multiplier
defects. The common word law is chosen first; its prime cancellation then
chooses a starting scale for the common-scale entropy transfer. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex FiniteInformation AbelPrimes BlockPrimes EntropyScales
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A]

def wordPairTest (C : A → A → ℝ) (p : ℕ) : C((ℕ → A),ℝ) where
  toFun x := C (x 0) (x p)
  continuous_toFun := by
    have hf : Continuous (fun x : ℕ → A => (x 0,x p)) :=
      (continuous_apply 0).prodMk (continuous_apply p)
    exact (continuous_of_discreteTopology (f := fun y : A × A => C y.1 y.2)).comp hf

lemma harmonic_word_pair_tendsto (L : ℕ → A) (D : ℕ → ℕ) (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => harmonicEmpirical (D j) (wordOrbit L)) atTop (𝓝 μ))
    (C : A → A → ℝ) (p : ℕ) :
    Tendsto (fun j => harmonicMean (D j+1) (fun n => C (L n) (L (n+p)))) atTop
      (𝓝 (∫ x, C (x 0) (x p) ∂(μ : Measure (ℕ → A)))) := by
  simpa only [wordPairTest,ContinuousMap.coe_mk,wordOrbit,Nat.add_zero] using
    harmonic_word_integral_tendsto L D μ hlim (wordPairTest C p)

noncomputable def wordPrimeGapMean (μ : Measure (ℕ → A)) (C : A → A → ℝ) (H : ℕ) : ℝ :=
  (∑ p ∈ halfBlockPrimes H, ∫ x, C (x 0) (x p) ∂μ)/(halfBlockPrimes H).card

lemma stationary_halfBlock_skew_zero (μ : Measure (ℕ → A)) [IsFiniteMeasure μ]
    (hμ : MeasurePreserving wordShift μ μ)
    (hdom : ∀ p K : ℕ, 0 < p → ∀ F : (Fin K → A) → ℝ, (∀ x, 0 ≤ F x ∧ F x ≤ 1) →
      (∫ x, F (fun k => x k) ∂μ) ≤ p*∫ x, F (fun k => x (p*k)) ∂μ)
    (C : A → A → ℝ) (hC : ∀ a b, C b a = -C a b) :
    Tendsto (wordPrimeGapMean μ C) atTop (𝓝 0) := by
  have ht := (stationary_prime_skew_zero μ hμ hdom C hC).comp
    (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ)≠0))
  simpa only [Function.comp_def,initialPrimes_eq_primesBelow,halfBlockPrimes,wordPrimeGapMean] using ht

lemma harmonic_word_limit_adjacent_skew_zero (L : ℕ → A)
    (hL : ∀ p, 0 < p → Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : Tendsto D atTop atTop) (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => harmonicEmpirical (D j) (wordOrbit L)) atTop (𝓝 μ))
    (C : A → A → ℝ) (hC : ∀ a b, C b a = -C a b) (hCb : ∀ a b, |C a b| ≤ 1) :
    (∫ x, C (x 0) (x 1) ∂(μ : Measure (ℕ → A))) = 0 := by
  let a := ∫ x, C (x 0) (x 1) ∂(μ : Measure (ℕ → A))
  have ha := harmonic_word_pair_tendsto L D μ hlim C 1
  have hμ := harmonic_word_limit_measurePreserving L D hD μ hlim
  have hdom := harmonic_word_limit_dilation_cylinder L hL D hD μ hlim
  have hprime := stationary_halfBlock_skew_zero (μ : Measure (ℕ → A)) hμ hdom C hC
  have hsmall (ε : ℝ) (hε : 0 < ε) : |a| ≤ 3*ε := by
    have hp := (tendsto_order.mp hprime.abs).2 ε (by simpa using hε)
    obtain ⟨B,hB⟩ := eventually_atTop.mp hp
    let H₀ := max B 8
    have hH₀ : 8 ≤ H₀ := le_max_right _ _
    have hgap (n : ℕ) : |wordPrimeGapMean (μ : Measure (ℕ → A)) C (factorialScale H₀ n)| < ε :=
      hB _ ((le_max_left B 8).trans (factorialScale_ge H₀ n))
    obtain ⟨K,hK,htransfer⟩ := approximate_harmonic_prime_transfer (A := A) H₀ hH₀ ε hε
    have htrans := hD.eventually (htransfer L hL)
    let V (j n : ℕ) := (∑ p ∈ halfBlockPrimes (factorialScale H₀ n),
      harmonicMean (D j+1) (fun m => C (L m) (L (m+p))))/(halfBlockPrimes (factorialScale H₀ n)).card
    have hV (n : Fin K) : Tendsto (fun j => V j n) atTop
        (𝓝 (wordPrimeGapMean (μ : Measure (ℕ → A)) C (factorialScale H₀ n))) := by
      have ht := tendsto_finset_sum (halfBlockPrimes (factorialScale H₀ n))
        (fun p _ => harmonic_word_pair_tendsto L D μ hlim C p)
      exact ht.div_const _
    have hnear : ∀ᶠ j : ℕ in atTop, ∀ n : Fin K,
        |V j n-wordPrimeGapMean (μ : Measure (ℕ → A)) C (factorialScale H₀ n)| < ε := by
      apply eventually_all.mpr
      intro n
      simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp (hV n) ε hε)
    have hb : ∀ᶠ j : ℕ in atTop,
        |harmonicMean (D j+1) (fun m => C (L m) (L (m+1)))| ≤ 3*ε := by
      filter_upwards [htrans,hnear] with j htrans hnear
      obtain ⟨n,hn,hdis⟩ := htrans
      have hh := hdis C hCb
      have hne := hnear ⟨n,hn⟩
      have hpr := hgap n
      change |harmonicMean (D j+1) (fun m => C (L m) (L (m+1)))-V j n| < ε at hh
      have htri := abs_sub_le (harmonicMean (D j+1) (fun m => C (L m) (L (m+1)))) (V j n) 0
      have htri' := abs_sub_le (V j n) (wordPrimeGapMean (μ : Measure (ℕ → A)) C (factorialScale H₀ n)) 0
      simp only [sub_zero] at htri htri'
      change |V j n-wordPrimeGapMean (μ : Measure (ℕ → A)) C (factorialScale H₀ n)|<ε at hne
      linarith
    exact le_of_tendsto ha.abs hb
  by_contra h
  have hap : 0 < |a| := abs_pos.mpr h
  have hh := hsmall (|a|/4) (by positivity)
  linarith

/-- General harmonic skew cancellation for a fixed finite stable label
sequence. This theorem makes no assertion about natural averages. -/
theorem stable_finite_labels_harmonic_skew_zero (L : ℕ → A)
    (hL : ∀ p, 0 < p → Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (C : A → A → ℝ) (hC : ∀ a b, C b a = -C a b) (hCb : ∀ a b, |C a b| ≤ 1) :
    Tendsto (fun N => harmonicMean (N+1) (fun n => C (L n) (L (n+1)))) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro D hD
  obtain ⟨μ,φ,hφ,hlim⟩ := exists_harmonicEmpirical_limit (wordOrbit L) D
  have hE := hD.comp hφ.tendsto_atTop
  have hz := harmonic_word_limit_adjacent_skew_zero L hL (D ∘ φ) hE μ hlim C hC hCb
  refine ⟨φ,?_⟩
  simpa only [hz,Function.comp_def] using harmonic_word_pair_tendsto L (D ∘ φ) μ hlim C 1

#print axioms stable_finite_labels_harmonic_skew_zero
end Erdos371.DilationSpectrum
