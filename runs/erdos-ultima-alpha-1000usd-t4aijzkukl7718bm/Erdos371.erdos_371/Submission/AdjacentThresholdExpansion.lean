import Submission.ActualPrimeComparisonTransfer
import Submission.FixedMaxMultiplicativeSymmetry

/-! An order comparison has a sparse expansion involving only neighboring
thresholds, rather than all pairs of label indicators. -/
namespace Erdos371
open Finset Filter FiniteInformation
open FixedPrimeAvoidance

noncomputable def thresholdStep (t a : ℕ) : ℝ := if a ≤ t then 1 else 0

noncomputable def adjacentThresholdSkew (t a b : ℕ) : ℝ :=
  thresholdStep t a*thresholdStep (t+1) b-thresholdStep t b*thresholdStep (t+1) a

lemma adjacentThresholdSkew_swap (t a b : ℕ) :
    adjacentThresholdSkew t b a = -adjacentThresholdSkew t a b := by
  unfold adjacentThresholdSkew
  ring

lemma adjacentThresholdSkew_of_lt (t a b : ℕ) (hab : a < b) :
    adjacentThresholdSkew t a b = thresholdStep (t+1) b-thresholdStep t b := by
  unfold adjacentThresholdSkew thresholdStep
  split_ifs <;> (first | omega | norm_num)

lemma adjacentThresholdSkew_sum_of_lt (Q a b : ℕ) (hab : a < b) (hb : b ≤ Q) :
    (∑ t ∈ range Q, adjacentThresholdSkew t a b) = 1 := by
  simp_rw [adjacentThresholdSkew_of_lt _ a b hab]
  rw [sum_range_sub (fun t => thresholdStep t b)]
  simp [thresholdStep,hb,show ¬b ≤ 0 by omega]

/-- Only consecutive thresholds occur in the exact expansion of order skew. -/
theorem orderSkew_eq_adjacent_threshold_sum (Q a b : ℕ) (ha : a ≤ Q) (hb : b ≤ Q) :
    orderSkew a b = ∑ t ∈ range Q, adjacentThresholdSkew t a b := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [adjacentThresholdSkew_sum_of_lt Q a b hab hb]
    simp [orderSkew,hab]
  · simp [orderSkew,adjacentThresholdSkew]
  · have he : (∑ t ∈ range Q, adjacentThresholdSkew t a b) =
        -(∑ t ∈ range Q, adjacentThresholdSkew t b a) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl (fun t _ => adjacentThresholdSkew_swap t b a)
    rw [he,adjacentThresholdSkew_sum_of_lt Q b a hba ha]
    simp [orderSkew,hba,hba.not_gt]

noncomputable def quantThreshold (Q N t n : ℕ) : ℝ :=
  thresholdStep t (primeQuantLabel Q N n).val

noncomputable def quantNeighborSkew (Q N t n : ℕ) : ℝ :=
  pairSkew (quantThreshold Q N t) (quantThreshold Q N (t+1)) n

lemma quantFactorSign_neighbor_expansion (Q N n : ℕ) :
    quantFactorSign Q N n = ∑ t ∈ range Q, quantNeighborSkew Q N t n := by
  have he := orderSkew_eq_adjacent_threshold_sum Q (primeQuantLabel Q N n).val
    (primeQuantLabel Q N (n+1)).val (Nat.le_of_lt_succ (primeQuantLabel Q N n).isLt)
    (Nat.le_of_lt_succ (primeQuantLabel Q N (n+1)).isLt)
  simpa only [quantFactorSign,orderSkew,Fin.lt_def,quantNeighborSkew,pairSkew,
    quantThreshold,adjacentThresholdSkew,mul_comm] using he

lemma quantFactorSign_neighbor_mean (Q N : ℕ) :
    prefixMean N (quantFactorSign Q N) = ∑ t ∈ range Q, prefixMean N (quantNeighborSkew Q N t) := by
  simp only [prefixMean,quantFactorSign_neighbor_expansion,← sum_div]
  rw [sum_comm]

lemma primeQuantLabel_mul_max (Q N a b : ℕ) (hN : 1 < N) (ha : 0 < a) (hb : 0 < b) :
    primeQuantLabel Q N (a*b) = max (primeQuantLabel Q N a) (primeQuantLabel Q N b) := by
  unfold primeQuantLabel
  rw [normalizedPrimeLog_mul_max N a b hN ha hb,unitQuantize_max]

lemma quantThreshold_mul (Q N t a b : ℕ) (hN : 1 < N) (ha : 0 < a) (hb : 0 < b) :
    quantThreshold Q N t (a*b) = quantThreshold Q N t a*quantThreshold Q N t b := by
  unfold quantThreshold thresholdStep
  rw [primeQuantLabel_mul_max Q N a b hN ha hb]
  change (if max (primeQuantLabel Q N a).val (primeQuantLabel Q N b).val ≤ t then (1 : ℝ) else 0) = _
  simp only [max_le_iff]
  split_ifs <;> simp_all

/-- Exact sparse form of the remaining quantized cancellation criterion.
The quantization must still be allowed to become arbitrarily fine. -/
theorem density_iff_arbitrarily_fine_neighbor_cancellation :
    {n | Nat.maxPrimeFac (n+1) > Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      ∀ ε : ℝ, 0 < ε → ∀ Q₀ : ℕ, ∃ Q ≥ Q₀, 0 < Q ∧
        ∀ᶠ N : ℕ in atTop, |∑ t ∈ range Q, prefixMean N (quantNeighborSkew Q N t)| ≤ ε := by
  rw [density_iff_arbitrarily_fine_quantized_cancellation]
  simp only [quantFactorSign_neighbor_mean]

#print axioms orderSkew_eq_adjacent_threshold_sum
#print axioms density_iff_arbitrarily_fine_neighbor_cancellation
end Erdos371
