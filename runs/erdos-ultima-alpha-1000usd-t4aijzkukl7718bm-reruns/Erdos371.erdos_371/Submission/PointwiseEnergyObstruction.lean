import FormalConjecturesUtil
import Submission.CofactorDiscrepancy

/-! Finite obstructions to proposed pointwise square-root bounds.
These statements do not disprove the density conjecture. -/

namespace Erdos371PointwiseEnergyObstruction

open Erdos371PrimeDiscrepancy Erdos371CofactorDiscrepancy

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma group_5039 : group 5039 40312 = 7 := by
  rw [group_eq_cofactorDifference (by decide +kernel : Nat.Prime 5039)]
  decide +kernel

lemma pointwise_six_bound_fails :
    ¬ ∀ p N : ℕ, p.Prime →
      (group p N)^2 ≤ 6 * (N / p : ℕ) := by
  intro h
  have hb := h 5039 40312 (by decide +kernel)
  rw [group_5039] at hb
  norm_num at hb

end Erdos371PointwiseEnergyObstruction

#print axioms Erdos371PointwiseEnergyObstruction.group_5039
#print axioms Erdos371PointwiseEnergyObstruction.pointwise_six_bound_fails
