import FormalConjecturesUtil
import Submission.CofactorDiscrepancy

/-! Exact finite checks: the discrepancy of one winning prime can change sign.
These statements do not negate the density conjecture. -/

namespace Erdos371GroupOscillation

open Erdos371PrimeDiscrepancy Erdos371CofactorDiscrepancy

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

lemma group_seventeen_positive : group 17 595 = 3 := by
  rw [group_eq_cofactorDifference (by norm_num : Nat.Prime 17)]
  decide +kernel

lemma group_seventeen_negative : group 17 31213 = -3 := by
  rw [group_eq_cofactorDifference (by norm_num : Nat.Prime 17)]
  decide +kernel

lemma not_each_prime_group_has_constant_sign :
    ¬ ∀ p : ℕ, p.Prime →
      (∀ N, 0 ≤ group p N) ∨ (∀ N, group p N ≤ 0) := by
  intro h
  rcases h 17 (by norm_num) with hpos | hneg
  · have hh := hpos 31213
    rw [group_seventeen_negative] at hh
    norm_num at hh
  · have hh := hneg 595
    rw [group_seventeen_positive] at hh
    norm_num at hh

end Erdos371GroupOscillation

#print axioms Erdos371GroupOscillation.group_seventeen_positive
#print axioms Erdos371GroupOscillation.group_seventeen_negative
#print axioms Erdos371GroupOscillation.not_each_prime_group_has_constant_sign
