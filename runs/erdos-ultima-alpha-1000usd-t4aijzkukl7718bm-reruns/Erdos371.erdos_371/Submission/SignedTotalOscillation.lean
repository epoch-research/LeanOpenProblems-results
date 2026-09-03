import FormalConjecturesUtil
import Submission.PrimeDiscrepancy

/-! Finite signs of the actual cumulative comparison discrepancy.
This is not a disproof of the density conjecture. -/

namespace Erdos371SignedTotalOscillation

open Erdos371PrimeDiscrepancy

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 1000000 in
lemma total_negative_example : total 3895 = -1 := by
  decide +kernel

lemma total_positive_example : total 3 = 3 := by
  decide +kernel

theorem total_not_always_nonnegative : ¬ ∀ N, 0 ≤ total N := by
  intro h
  have hh := h 3895
  rw [total_negative_example] at hh
  norm_num at hh

end Erdos371SignedTotalOscillation

#print axioms Erdos371SignedTotalOscillation.total_negative_example
#print axioms Erdos371SignedTotalOscillation.total_not_always_nonnegative
