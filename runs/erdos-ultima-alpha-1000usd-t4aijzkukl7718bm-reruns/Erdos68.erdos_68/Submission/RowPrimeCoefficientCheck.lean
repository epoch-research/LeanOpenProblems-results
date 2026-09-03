import Submission.RowwiseFloors
import Submission.FactorialLambert

/-! Exact check that rowwise carrying does not preserve the prime unit coefficient.
This is an auxiliary obstruction, not a proof or disproof of Erdős 68. -/

namespace Erdos68Development

lemma rowFloor_seven : rowFloor 7 = 6317 := by
  norm_num [rowFloor, scaledRow, Finset.sum_range_succ, Nat.factorial]

lemma rowCoeff_seven : rowCoeff 7 = 3 := by
  change rowFloor 7 - 7 * rowFloor 6 = 3
  rw [rowFloor_seven, rowFloor_first_congruence_failure.2.1]
  norm_num

lemma rowwise_prime_coefficient_not_preserved :
    Nat.Prime 7 ∧ lambertCoeff 7 = 1 ∧ rowCoeff 7 ≠ 1 := by
  refine ⟨by norm_num, lambertCoeff_prime (by norm_num), ?_⟩
  rw [rowCoeff_seven]
  norm_num

#print axioms rowwise_prime_coefficient_not_preserved

end Erdos68Development
