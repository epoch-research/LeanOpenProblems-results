import Submission.MetricFrequentLinear
import Submission.LogCorrelationCriterion
import Submission.LinearPrefixDivergence

/-!
Almost-everywhere divergence of the reciprocal-weighted genuine prime-pair
correlation. This strengthens the metric infinitude result, but retains its
almost-everywhere qualification and does not settle the universal conjecture.
-/
namespace Erdos972MetricLogDivergence

open Finset Filter MeasureTheory
open scoped Topology
open Erdos972ChebyshevLower Erdos972RichSlopes Erdos972WidePairWeights
open Erdos972MetricFrequentLinear Erdos972PrimePowerError
open Erdos972LogCorrelationCriterion Erdos972LinearPrefixDivergence

lemma primeTerm_prefix (α : ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, primeTerm α n) = primeCorrelation α N := by
  classical
  simp only [primeCorrelation, sum_filter, primeTerm]

lemma widePairs_le_primeCorrelation (A N : ℕ) (α : ℝ) :
    widePairs A N α ≤ primeCorrelation α N := by
  classical
  rw [← primeTerm_prefix]
  unfold widePairs
  calc
    _ ≤ ∑ p ∈ (Ioc 0 N).filter Nat.Prime, primeTerm α p := by
      apply sum_le_sum
      intro p hp
      have hpp := (mem_filter.mp hp).2
      let q₀ := ⌊α * p⌋₊
      let s := (Ioc p (A*p)).filter Nat.Prime
      change (∑ q ∈ s, pairBox p q α) ≤ _
      by_cases hmem : q₀ ∈ s
      · have hqp : q₀.Prime := (mem_filter.mp hmem).2
        rw [sum_eq_single q₀ (fun q _ hq => pairBox_eq_zero_of_ne_floor hpp.pos hq)
          (fun h => (h hmem).elim)]
        have hterm : primeTerm α p = Real.log p * Real.log q₀ := by
          simp only [primeTerm, floorMul, if_pos (show p.Prime ∧ (⌊α*p⌋₊).Prime from ⟨hpp, hqp⟩)]
          rfl
        rw [hterm]
        unfold pairBox
        simp only [Set.indicator]
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
      · have hz : (∑ q ∈ s, pairBox p q α) = 0 := by
          apply sum_eq_zero
          intro q hq
          apply pairBox_eq_zero_of_ne_floor hpp.pos
          intro he
          change q = q₀ at he
          exact hmem (he ▸ hq)
        rw [hz]
        exact primeTerm_nonneg α p
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun p _ _ => primeTerm_nonneg α p)

/-- The weighted mass here counts only prime input and prime output. -/
theorem ae_frequently_linear_primeCorrelation :
    ∀ᵐ α : ℝ, 1 < α → ∀ B : ℕ, ∃ N : ℕ,
      B < N ∧ (N : ℝ)/16 < primeCorrelation α N := by
  filter_upwards [ae_frequently_linear_widePairs] with α hα
  intro hα1 B
  obtain ⟨A, hA⟩ := exists_nat_gt α
  obtain ⟨N, hBN, hN⟩ := hα A hα1 hA B
  exact ⟨N, hBN, hN.trans_le (widePairs_le_primeCorrelation A N α)⟩

lemma not_summable_prime_of_frequently_linear {α : ℝ}
    (h : ∀ B : ℕ, ∃ N : ℕ, B < N ∧ (N : ℝ)/16 < primeCorrelation α N) :
    ¬ Summable (fun n : ℕ => primeTerm α n / ((n+1 : ℕ) : ℝ)) := by
  apply not_summable_div_succ_of_frequently_linear (primeTerm_nonneg α)
    (c := 1/16) (by norm_num)
  intro B
  obtain ⟨N, hBN, hN⟩ := h B
  refine ⟨N, hBN, ?_⟩
  rw [primeTerm_prefix]
  linarith

theorem ae_not_summable_prime :
    ∀ᵐ α : ℝ, 1 < α →
      ¬ Summable (fun n : ℕ => primeTerm α n / ((n+1 : ℕ) : ℝ)) := by
  filter_upwards [ae_frequently_linear_primeCorrelation] with α hα
  intro hα1
  exact not_summable_prime_of_frequently_linear (hα hα1)

lemma logPrimeCorrelation_tendsto_of_not_summable {α : ℝ}
    (h : ¬ Summable (fun n : ℕ => primeTerm α n / ((n+1 : ℕ) : ℝ))) :
    Tendsto (logPrimeCorrelation α) atTop atTop := by
  have hpos (n : ℕ) : 0 ≤ primeTerm α n / ((n+1 : ℕ) : ℝ) :=
    div_nonneg (primeTerm_nonneg α n) (by positivity)
  have hh := (not_summable_iff_tendsto_nat_atTop_of_nonneg hpos).mp h
  have hn : Tendsto (fun N : ℕ => N+1) atTop atTop := tendsto_add_atTop_nat 1
  have hh' := hh.comp hn
  have hzero : primeTerm α 0 / ((0+1 : ℕ) : ℝ) = 0 := by simp
  simpa only [Function.comp_def, sum_range_succ_eq_Ioc (a := fun n => primeTerm α n / ((n+1 : ℕ) : ℝ)) hzero, logPrimeCorrelation] using hh'

/-- A genuine divergence result for almost every slope, not a claimed
pointwise lower bound for all irrational slopes. -/
theorem ae_logPrimeCorrelation_tendsto :
    ∀ᵐ α : ℝ, 1 < α → Tendsto (logPrimeCorrelation α) atTop atTop := by
  filter_upwards [ae_not_summable_prime] with α hα
  exact fun hα1 => logPrimeCorrelation_tendsto_of_not_summable (hα hα1)

theorem ae_not_summable_mangoldt :
    ∀ᵐ α : ℝ, 1 < α →
      ¬ Summable (fun n : ℕ => mangoldtTerm α n / ((n+1 : ℕ) : ℝ)) := by
  filter_upwards [ae_not_summable_prime] with α hα
  intro hα1 hm
  exact hα hα1 ((summable_mangoldt_iff_prime hα1.le).mp hm)

lemma logPrimeCorrelation_le_logMangoldtCorrelation (α : ℝ) (N : ℕ) :
    logPrimeCorrelation α N ≤ logMangoldtCorrelation α N := by
  apply sum_le_sum
  intro n _
  exact div_le_div_of_nonneg_right (primeTerm_le α n) (by positivity)

theorem ae_logMangoldtCorrelation_tendsto :
    ∀ᵐ α : ℝ, 1 < α → Tendsto (logMangoldtCorrelation α) atTop atTop := by
  filter_upwards [ae_logPrimeCorrelation_tendsto] with α hα
  intro hα1
  exact tendsto_atTop_mono (logPrimeCorrelation_le_logMangoldtCorrelation α) (hα hα1)

#print axioms widePairs_le_primeCorrelation
#print axioms ae_frequently_linear_primeCorrelation
#print axioms ae_logPrimeCorrelation_tendsto
#print axioms ae_not_summable_mangoldt
#print axioms ae_logMangoldtCorrelation_tendsto

end Erdos972MetricLogDivergence
