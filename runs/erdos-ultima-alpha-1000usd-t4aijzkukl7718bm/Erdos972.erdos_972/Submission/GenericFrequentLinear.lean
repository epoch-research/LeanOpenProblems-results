import Submission.MetricFrequentLinear
import Submission.MetricLogDivergence

/-! A residual-set version of frequent linear growth for the actual weighted
prime-pair count. It does not assert the property at every irrational slope. -/
namespace Erdos972GenericFrequentLinear

open Set Filter MeasureTheory Finset
open scoped Topology
open Erdos972ChebyshevLower Erdos972WidePairWeights Erdos972RichSlopes
open Erdos972MetricFrequentLinear Erdos972AlmostEverywherePairs
open Erdos972MetricLogDivergence Erdos972PrimePowerError

lemma continuousAt_pairBox_irrational {α : ℝ} (hI : Irrational α) (p q : ℕ) :
    ContinuousAt (pairBox p q) α := by
  have hlo : α ≠ (q : ℝ) / p := by
    simpa only [Int.cast_natCast] using hI.ne_rational (q : ℤ) (p : ℤ)
  have hhi : α ≠ ((q : ℝ) + 1) / p := by
    simpa only [Int.cast_natCast, Int.cast_add, Int.cast_one] using
      hI.ne_rational ((q : ℤ) + 1) (p : ℤ)
  unfold pairBox
  by_cases hmem : α ∈ Set.Ico ((q : ℝ) / p) (((q : ℝ) + 1) / p)
  · have hinside : α ∈ Set.Ioo ((q : ℝ) / p) (((q : ℝ) + 1) / p) :=
      ⟨lt_of_le_of_ne hmem.1 (Ne.symm hlo), hmem.2⟩
    apply (continuousAt_const (y := Real.log p * Real.log q)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hinside] with β hβ
    exact Set.indicator_of_mem (s := Set.Ico ((q : ℝ) / p) (((q : ℝ) + 1) / p))
      ⟨hβ.1.le, hβ.2⟩ _
  · have hout : α < (q : ℝ) / p ∨ ((q : ℝ) + 1) / p < α := by
      simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at hmem
      exact hmem.imp id (fun h => lt_of_le_of_ne h (Ne.symm hhi))
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    rcases hout with hlo' | hhi'
    · filter_upwards [isOpen_Iio.mem_nhds hlo'] with β hβ
      exact Set.indicator_of_notMem (fun h => not_lt_of_ge h.1 hβ) _
    · filter_upwards [isOpen_Ioi.mem_nhds hhi'] with β hβ
      exact Set.indicator_of_notMem (fun h => not_lt_of_ge hβ.le h.2) _

lemma continuousAt_widePairs_irrational {α : ℝ} (hI : Irrational α) (A N : ℕ) :
    ContinuousAt (widePairs A N) α := by
  unfold widePairs ContinuousAt
  apply tendsto_finset_sum
  intro p hp
  exact tendsto_finset_sum _ fun q hq => continuousAt_pairBox_irrational hI p q

lemma irrational_richTail_mem_interior {α : ℝ} (hI : Irrational α) {A B : ℕ}
    (hα : α ∈ richTail A B) : α ∈ interior (richTail A B) := by
  obtain ⟨N, hBN, hN⟩ := hα
  rw [mem_interior_iff_mem_nhds]
  have h := (continuousAt_widePairs_irrational hI A N).preimage_mem_nhds
    (isOpen_Ioi.mem_nhds hN)
  exact Filter.mem_of_superset h fun β hβ => ⟨N, hBN, hβ⟩

noncomputable def augmentedRich (A B : ℕ) : Set ℝ :=
  Set.Iio 1 ∪ Set.Ioi (A : ℝ) ∪ interior (richTail A B)

lemma isOpen_augmentedRich (A B : ℕ) : IsOpen (augmentedRich A B) :=
  (isOpen_Iio.union isOpen_Ioi).union isOpen_interior

lemma ae_mem_augmentedRich (A B : ℕ) :
    ∀ᵐ α : ℝ, α ∈ augmentedRich A B := by
  by_cases hA : 1 ≤ A
  · filter_upwards [ae_mem_richTail A B hA, ae_irrational] with α hα hI
    by_cases hα1 : α < 1
    · exact Or.inl (Or.inl hα1)
    by_cases hαA : (A : ℝ) < α
    · exact Or.inl (Or.inr hαA)
    have h1 : 1 < α := lt_of_le_of_ne (le_of_not_gt hα1) (Ne.symm hI.ne_one)
    have hA' : α < (A : ℝ) := lt_of_le_of_ne (le_of_not_gt hαA) (hI.ne_nat A)
    exact Or.inr (irrational_richTail_mem_interior hI (hα h1 hA'))
  · have hA0 : A = 0 := by omega
    subst A
    apply Filter.Eventually.of_forall
    intro α
    by_cases hα : α < 1
    · exact Or.inl (Or.inl hα)
    · apply Or.inl
      apply Or.inr
      simp only [Set.mem_Ioi, Nat.cast_zero]
      linarith [le_of_not_gt hα]

lemma dense_augmentedRich (A B : ℕ) : Dense (augmentedRich A B) :=
  Measure.dense_of_ae (ae_mem_augmentedRich A B)

/-- Frequent linear growth holds on a residual set of irrational slopes.
The residual quantifier cannot be replaced by a universal one. -/
theorem eventually_residual_frequently_linear_widePairs :
    ∀ᶠ α : ℝ in residual ℝ, Irrational α ∧
      ∀ A : ℕ, 1 < α → α < A →
        ∀ B : ℕ, ∃ N : ℕ, B < N ∧ (N : ℝ) / 16 < widePairs A N α := by
  have h : ∀ᶠ α : ℝ in residual ℝ, ∀ A B : ℕ, α ∈ augmentedRich A B := by
    apply eventually_countable_forall.mpr
    intro A
    apply eventually_countable_forall.mpr
    intro B
    exact residual_of_dense_open (isOpen_augmentedRich A B) (dense_augmentedRich A B)
  filter_upwards [h, residual_of_dense_Gδ IsGδ.setOf_irrational dense_irrational] with α hα hI
  refine ⟨hI, fun A hα1 hαA B => ?_⟩
  rcases hα A B with (hlo | hhi) | hr
  · exact (not_lt_of_ge hα1.le hlo).elim
  · exact (not_lt_of_ge hαA.le hhi).elim
  · have hmem : α ∈ richTail A B := interior_subset hr
    exact hmem

/-- The unrestricted genuine-prime correlation inherits the same lower bound. -/
theorem eventually_residual_frequently_linear_primeCorrelation :
    ∀ᶠ α : ℝ in residual ℝ, Irrational α ∧
      (1 < α → ∀ B : ℕ, ∃ N : ℕ, B < N ∧
        (N : ℝ) / 16 < primeCorrelation α N) := by
  filter_upwards [eventually_residual_frequently_linear_widePairs] with α hα
  refine ⟨hα.1, fun hα1 B => ?_⟩
  obtain ⟨A, hA⟩ := exists_nat_gt α
  obtain ⟨N, hBN, hN⟩ := hα.2 A hα1 hA B
  exact ⟨N, hBN, hN.trans_le (widePairs_le_primeCorrelation A N α)⟩

open Erdos972LogCorrelationCriterion

/-- The reciprocal-weighted genuine-prime series diverges for a residual set
of slopes above one. This is still a residual, rather than pointwise, result. -/
theorem eventually_residual_not_summable_prime :
    ∀ᶠ α : ℝ in residual ℝ, Irrational α ∧
      (1 < α → ¬ Summable (fun n : ℕ =>
        primeTerm α n / ((n+1 : ℕ) : ℝ))) := by
  filter_upwards [eventually_residual_frequently_linear_primeCorrelation] with α hα
  exact ⟨hα.1, fun hα1 => not_summable_prime_of_frequently_linear (hα.2 hα1)⟩

theorem eventually_residual_logPrimeCorrelation_tendsto :
    ∀ᶠ α : ℝ in residual ℝ, Irrational α ∧
      (1 < α → Tendsto (logPrimeCorrelation α) atTop atTop) := by
  filter_upwards [eventually_residual_not_summable_prime] with α hα
  exact ⟨hα.1, fun hα1 => logPrimeCorrelation_tendsto_of_not_summable (hα.2 hα1)⟩

theorem eventually_residual_logMangoldtCorrelation_tendsto :
    ∀ᶠ α : ℝ in residual ℝ, Irrational α ∧
      (1 < α → Tendsto (logMangoldtCorrelation α) atTop atTop) := by
  filter_upwards [eventually_residual_logPrimeCorrelation_tendsto] with α hα
  exact ⟨hα.1, fun hα1 =>
    tendsto_atTop_mono (logPrimeCorrelation_le_logMangoldtCorrelation α) (hα.2 hα1)⟩

#print axioms continuousAt_widePairs_irrational
#print axioms eventually_residual_frequently_linear_widePairs
#print axioms eventually_residual_frequently_linear_primeCorrelation
#print axioms eventually_residual_not_summable_prime
#print axioms eventually_residual_logPrimeCorrelation_tendsto
#print axioms eventually_residual_logMangoldtCorrelation_tendsto
end Erdos972GenericFrequentLinear
