import FormalConjecturesUtil
import Submission.PrimeDiscrepancy

/-! A finite obstruction to exact cancellation in each winning-prime fiber.
This does not assert that a full smooth-number fiber has been enumerated,
and is not a disproof of Erdős 371. -/

namespace Erdos371WinningFiberObstruction

open Erdos371PrimeDiscrepancy

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma eleven_ascents :
    (Finset.range 99).filter (fun n => P (n+1) = 11 ∧ P n < 11) =
      {10, 21, 32, 54, 98} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  by_cases hn : n < 99
  · interval_cases n <;> decide +kernel
  · omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma eleven_descents :
    (Finset.range 99).filter (fun n => P n = 11 ∧ P (n+1) < 11) =
      {11, 44, 55} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  by_cases hn : n < 99
  · interval_cases n <;> decide +kernel
  · omega

lemma eleven_group : group 11 99 = 2 := by
  rw [group_eq_counts, eleven_ascents, eleven_descents]
  norm_num

/-- Even a unit absolute bound for every finite fiber is false. -/
lemma not_unit_fiber_bound :
    ¬ ∀ p N : ℕ, p.Prime → |group p N| ≤ 1 := by
  intro h
  have hh := h 11 99 (by norm_num)
  rw [eleven_group] at hh
  norm_num at hh

end Erdos371WinningFiberObstruction

#print axioms Erdos371WinningFiberObstruction.eleven_group
#print axioms Erdos371WinningFiberObstruction.not_unit_fiber_bound
