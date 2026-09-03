import FormalConjecturesUtil
import Submission.TwoSidedPrimeDeletion

/-! The sum of the two normalized prime-deletion affine sums cancels
unconditionally. Cancellation of their difference, not their sum, is equivalent
to Erdős 371. No estimate of the difference is proved here. -/

namespace Erdos371PairedAffineCancellation

open Filter Erdos371PrimeDeletionVariance Erdos371TwoSidedPrimeDeletion
open scoped Topology

noncomputable def pairedSum (N : ℕ) : ℝ :=
  ((minusSum N + plusSum N) / N) / primeMass N

noncomputable def pairedDifference (N : ℕ) : ℝ :=
  ((minusSum N - plusSum N) / N) / primeMass N

lemma pairedSum_eq (N : ℕ) : pairedSum N = affineMean N + afterAffine N := by
  rw [pairedSum, affineMean_eq_minusSum, afterAffine_eq, add_div, add_div]

lemma pairedDifference_eq (N : ℕ) :
    pairedDifference N = affineMean N - afterAffine N := by
  rw [pairedDifference, affineMean_eq_minusSum, afterAffine_eq, sub_div, sub_div]

/-- This cancellation does not require the conjecture. -/
theorem pairedSum_tendsto_zero : Tendsto pairedSum atTop (𝓝 0) := by
  have hh := (signed_affine_error_tendsto_zero.add after_error_tendsto_zero).neg
  simp only [add_zero, neg_zero] at hh
  apply hh.congr
  intro N
  rw [pairedSum_eq]
  ring

/-- The remaining signed difference approximates twice the original
normalized discrepancy. -/
theorem pairedDifference_error_tendsto_zero :
    Tendsto (fun N : ℕ =>
      2 * ((Erdos371PrimeDiscrepancy.total N : ℝ) / N) - pairedDifference N)
      atTop (𝓝 0) := by
  have hh := signed_affine_error_tendsto_zero.sub after_error_tendsto_zero
  simp only [sub_zero] at hh
  apply hh.congr
  intro N
  rw [pairedDifference_eq]
  ring

/-- This is an exact criterion; its right-hand side remains unproved. -/
theorem density_half_iff_pairedDifference_zero :
    {n | Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)}.HasDensity (1/2) ↔
      Tendsto pairedDifference atTop (𝓝 0) := by
  rw [Erdos371PrimeDiscrepancy.density_half_iff_total_mean_zero]
  constructor
  · intro h
    have hh := (h.const_mul 2).sub pairedDifference_error_tendsto_zero
    simp only [mul_zero, sub_zero] at hh
    apply hh.congr
    intro N
    ring
  · intro h
    have hh := (pairedDifference_error_tendsto_zero.add h).div_const 2
    simp only [add_zero, zero_div] at hh
    apply hh.congr
    intro N
    ring

end Erdos371PairedAffineCancellation

#print axioms Erdos371PairedAffineCancellation.pairedSum_tendsto_zero
#print axioms Erdos371PairedAffineCancellation.pairedDifference_error_tendsto_zero
#print axioms Erdos371PairedAffineCancellation.density_half_iff_pairedDifference_zero
