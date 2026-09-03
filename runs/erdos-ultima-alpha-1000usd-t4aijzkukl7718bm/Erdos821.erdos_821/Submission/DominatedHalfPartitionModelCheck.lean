import Submission.DominatedHalfPartitionModel

/-! Type checks and axiom audit for the factor-two finite moment certificate.
This is not a proof or disproof of the arithmetic conjecture. -/

open Erdos821.DominatedHalfPartitionModel

example : meanQ (fun _ => 1) = 1 := meanQ_one

example (j : ℕ) (hj : 1 ≤ j) (hj' : j ≤ 12) :
    meanQ (fun p => (p.count j : ℚ)) = (j : ℚ)⁻¹ :=
  meanQ_count j hj hj'

example (a b c d e f : ℕ) (h : a+2*b+3*c+4*d+5*e+6*f ≤ 6) :
    meanQ (fun p => (moment a b c d e f p : ℚ)) =
      (momentDenominator a b c d e f : ℚ)⁻¹ :=
  meanQ_half_weight_moment a b c d e f h

example (f : List ℕ → ℚ) (hf : ∀ p ∈ referencePartitions, 0 ≤ f p) :
    meanQ f ≤ 2*referenceMeanQ f := all_nonnegative_tests_bounded f hf

example : meanQ (fun p => if ∀ j ∈ p, 4*j ≤ p.sum then 1 else 0) = 0 :=
  meanQ_fourth_root_smooth_zero

#print axioms support_properties
#print axioms half_weight_moments
#print axioms reference_properties
#print axioms support_sublist
#print axioms pointwise_reference_bound
#print axioms reference_normalized
#print axioms all_nonnegative_tests_bounded
#print axioms meanQ_nat
#print axioms meanQ_one
#print axioms meanQ_count
#print axioms meanQ_half_weight_moment
#print axioms meanQ_fourth_root_smooth_zero
