import Submission.ShiftedHarmonicWordLimit
import Submission.HarmonicStableSkewZero

/-! Reversal of finite stable labels on every sequence of harmonic intervals
whose total harmonic mass diverges. Fixed-ratio intervals are not covered. -/
namespace Erdos371.FiniteInformation
open Finset Filter BlockPrimes EntropyScales
open scoped Topology
set_option autoImplicit false

lemma shifted_pair_dilation_error {X : Type*} (A N p : ℕ) (hp : 0 < p)
    (L : ℕ → X) (C : X → X → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    |shiftedHarmonicGapDiscrepancy A N p L C-
      (shiftedHarmonicMean A N (fun n => C (L n) (L (n+1)))-
        shiftedHarmonicMean A N (fun n => C (L n) (L (n+p))))| ≤
          shiftedWindowDilationBudget A N p 2 L := by
  have h := shifted_harmonic_window_dilation_error A N p 2 hp L
    (fun x => C (x 0) (x 1)) (fun x => hC _ _)
  simp only [Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.mul_one,Nat.add_zero] at h
  unfold shiftedHarmonicGapDiscrepancy translatedGapTest
  rw [shiftedHarmonicMean_sub,shiftedHarmonicMean_const_mul,sub_sub_sub_cancel_right]
  exact h

/-- Common-scale adjacent-to-prime-gap transfer on the same harmonic window.
Both endpoint losses are included in the vanishing dilation budget. -/
theorem shifted_approximate_harmonic_prime_transfer {X : Type*} [Fintype X]
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ L : ℕ → X,
      (∀ p, 0 < p → Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0)) →
      ∀ A M : ℕ → ℕ, Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop →
      ∀ᶠ j : ℕ in atTop, ∃ n < K,
        ∀ C : X → X → ℝ, (∀ a b, |C a b| ≤ 1) →
          |shiftedHarmonicMean (A j) (M j) (fun m => C (L m) (L (m+1)))-
            (∑ p ∈ halfBlockPrimes (factorialScale H₀ n),
              shiftedHarmonicMean (A j) (M j) (fun m => C (L m) (L (m+p)))) /
                (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  classical
  obtain ⟨K,hK,htrans⟩ := shifted_harmonic_prime_gap_transfer (X := X) H₀ hH₀ (ε/2) (by positivity)
  let B := (range K).sup (factorialScale H₀)
  refine ⟨K,hK,?_⟩
  intro L hL A M hH
  have he : ∀ᶠ j : ℕ in atTop, ∀ p : Icc 1 B,
      shiftedWindowDilationBudget (A j) (M j) p 2 L < ε/2 := by
    apply eventually_all.mpr
    intro p
    exact (shiftedWindowDilationBudget_zero p 2 L (hL p (mem_Icc.mp p.property).1) A M hH).eventually_lt_const
      (by positivity)
  filter_upwards [htrans A M hH,he] with j htrans he
  obtain ⟨n,hn,hscale⟩ := htrans L
  refine ⟨n,hn,?_⟩
  intro C hC
  let S := halfBlockPrimes (factorialScale H₀ n)
  have hHn : factorialScale H₀ n ≤ B := le_sup (mem_range.mpr hn)
  have hS : S.Nonempty := halfBlockPrimes_nonempty _
    (le_trans (by omega : 4 ≤ H₀) (factorialScale_ge H₀ n))
  let V (p : ℕ) := shiftedHarmonicMean (A j) (M j) (fun m => C (L m) (L (m+p)))
  have herr : |(∑ p ∈ S, (shiftedHarmonicGapDiscrepancy (A j) (M j) p L C-(V 1-V p)))/(S.card : ℝ)| ≤ ε/2 := by
    apply abs_finset_average_le S hS
    intro p hp
    obtain ⟨hpp,hpH⟩ := mem_halfBlockPrimes.mp hp
    have hpB : p ≤ B := by omega
    exact (shifted_pair_dilation_error (A j) (M j) p hpp.pos L C hC).trans
      (he ⟨p,mem_Icc.mpr ⟨hpp.pos,hpB⟩⟩).le
  have heq : (∑ p ∈ S, (V 1-V p))/(S.card : ℝ) = V 1-(∑ p ∈ S,V p)/(S.card : ℝ) := by
    rw [sum_sub_distrib,sub_div,sum_const,nsmul_eq_mul]
    have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hS).ne'
    field_simp
  rw [sum_sub_distrib,sub_div,heq,abs_sub_comm] at herr
  have hs := hscale C hC
  change |(∑ p ∈ S,shiftedHarmonicGapDiscrepancy (A j) (M j) p L C)/(S.card : ℝ)| < ε/2 at hs
  have htri := abs_sub_le (V 1-(∑ p ∈ S,V p)/(S.card : ℝ))
    ((∑ p ∈ S,shiftedHarmonicGapDiscrepancy (A j) (M j) p L C)/(S.card : ℝ)) 0
  simp only [sub_zero] at htri
  change |V 1-(∑ p ∈ S,V p)/(S.card : ℝ)| < ε
  linarith

end Erdos371.FiniteInformation
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory FiniteInformation BlockPrimes EntropyScales
open scoped Topology
set_option autoImplicit false

variable {X : Type*} [Fintype X] [TopologicalSpace X] [DiscreteTopology X]
    [MeasurableSpace X] [BorelSpace X]

lemma shifted_word_pair_tendsto (L : ℕ → X) (A M : ℕ → ℕ) (μ : ProbabilityMeasure (ℕ → X))
    (hlim : Tendsto (fun j => shiftedEmpirical (A j) (M j) (wordOrbit L)) atTop (𝓝 μ))
    (C : X → X → ℝ) (p : ℕ) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j) (fun n => C (L n) (L (n+p)))) atTop
      (𝓝 (∫ x, C (x 0) (x p) ∂(μ : Measure (ℕ → X)))) := by
  simpa only [wordPairTest,ContinuousMap.coe_mk,wordOrbit,Nat.add_zero] using
    shifted_word_integral_tendsto L A M μ hlim (wordPairTest C p)

lemma shifted_word_limit_adjacent_skew_zero (L : ℕ → X)
    (hL : ∀ p, 0 < p → Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (A M : ℕ → ℕ) (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop)
    (μ : ProbabilityMeasure (ℕ → X))
    (hlim : Tendsto (fun j => shiftedEmpirical (A j) (M j) (wordOrbit L)) atTop (𝓝 μ))
    (C : X → X → ℝ) (hC : ∀ a b, C b a = -C a b) (hCb : ∀ a b, |C a b| ≤ 1) :
    (∫ x, C (x 0) (x 1) ∂(μ : Measure (ℕ → X))) = 0 := by
  let a := ∫ x, C (x 0) (x 1) ∂(μ : Measure (ℕ → X))
  have ha := shifted_word_pair_tendsto L A M μ hlim C 1
  have hμ := shifted_word_limit_measurePreserving L A M hH μ hlim
  have hdom := shifted_word_limit_dilation_cylinder L hL A M hH μ hlim
  have hprime := stationary_halfBlock_skew_zero (μ : Measure (ℕ → X)) hμ hdom C hC
  have hsmall (ε : ℝ) (hε : 0 < ε) : |a| ≤ 3*ε := by
    have hp := (tendsto_order.mp hprime.abs).2 ε (by simpa using hε)
    obtain ⟨B,hB⟩ := eventually_atTop.mp hp
    let H₀ := max B 8
    have hH₀ : 8 ≤ H₀ := le_max_right _ _
    have hgap (n : ℕ) : |wordPrimeGapMean (μ : Measure (ℕ → X)) C (factorialScale H₀ n)| < ε :=
      hB _ ((le_max_left B 8).trans (factorialScale_ge H₀ n))
    obtain ⟨K,hK,htransfer⟩ := shifted_approximate_harmonic_prime_transfer (X := X) H₀ hH₀ ε hε
    let V (j n : ℕ) := (∑ p ∈ halfBlockPrimes (factorialScale H₀ n),
      shiftedHarmonicMean (A j) (M j) (fun m => C (L m) (L (m+p))))/(halfBlockPrimes (factorialScale H₀ n)).card
    have hV (n : Fin K) : Tendsto (fun j => V j n) atTop
        (𝓝 (wordPrimeGapMean (μ : Measure (ℕ → X)) C (factorialScale H₀ n))) := by
      have ht := tendsto_finset_sum (halfBlockPrimes (factorialScale H₀ n))
        (fun p _ => shifted_word_pair_tendsto L A M μ hlim C p)
      exact ht.div_const _
    have hnear : ∀ᶠ j : ℕ in atTop, ∀ n : Fin K,
        |V j n-wordPrimeGapMean (μ : Measure (ℕ → X)) C (factorialScale H₀ n)| < ε := by
      apply eventually_all.mpr
      intro n
      simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp (hV n) ε hε)
    have hb : ∀ᶠ j : ℕ in atTop,
        |shiftedHarmonicMean (A j) (M j) (fun m => C (L m) (L (m+1)))| ≤ 3*ε := by
      filter_upwards [htransfer L hL A M hH,hnear] with j htrans hnear
      obtain ⟨n,hn,hdis⟩ := htrans
      have hh := hdis C hCb
      have hne := hnear ⟨n,hn⟩
      have hpr := hgap n
      change |shiftedHarmonicMean (A j) (M j) (fun m => C (L m) (L (m+1)))-V j n| < ε at hh
      have htri := abs_sub_le (shiftedHarmonicMean (A j) (M j) (fun m => C (L m) (L (m+1)))) (V j n) 0
      have htri' := abs_sub_le (V j n) (wordPrimeGapMean (μ : Measure (ℕ → X)) C (factorialScale H₀ n)) 0
      simp only [sub_zero] at htri htri'
      change |V j n-wordPrimeGapMean (μ : Measure (ℕ → X)) C (factorialScale H₀ n)|<ε at hne
      linarith
    exact le_of_tendsto ha.abs hb
  by_contra h
  have hap : 0 < |a| := abs_pos.mpr h
  have hh := hsmall (|a|/4) (by positivity)
  linarith

/-- Uniform growing-log-window reversal for every fixed finite stable label
sequence. The harmonic mass is allowed to diverge arbitrarily slowly. -/
theorem stable_finite_labels_shifted_harmonic_skew_zero (L : ℕ → X)
    (hL : ∀ p, 0 < p → Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (C : X → X → ℝ) (hC : ∀ a b, C b a = -C a b) (hCb : ∀ a b, |C a b| ≤ 1)
    (A M : ℕ → ℕ) (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j) (fun n => C (L n) (L (n+1)))) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro D hD
  obtain ⟨μ,φ,hφ,hlim⟩ := exists_shiftedEmpirical_limit (wordOrbit L) (A ∘ D) (M ∘ D)
  have hE := (hH.comp hD).comp hφ.tendsto_atTop
  have hz := shifted_word_limit_adjacent_skew_zero L hL (A ∘ D ∘ φ) (M ∘ D ∘ φ) hE μ hlim C hC hCb
  refine ⟨φ,?_⟩
  simpa only [hz,Function.comp_def] using shifted_word_pair_tendsto L (A ∘ D ∘ φ) (M ∘ D ∘ φ) μ hlim C 1

#print axioms shifted_word_limit_adjacent_skew_zero
#print axioms stable_finite_labels_shifted_harmonic_skew_zero
end Erdos371.DilationSpectrum
