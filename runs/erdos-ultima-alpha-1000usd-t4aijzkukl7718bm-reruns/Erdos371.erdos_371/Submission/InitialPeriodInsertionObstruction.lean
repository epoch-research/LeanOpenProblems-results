import FormalConjecturesUtil
import Submission.PeriodEnergyObstruction

/-! A finite obstruction to a simple energy induction on initial prime sets.
This does not disprove the original conjecture or a linear aggregate energy bound. -/

namespace Erdos371InitialPeriodInsertionObstruction

open Erdos371PeriodEnergyObstruction

set_option maxRecDepth 200000 in
set_option maxHeartbeats 12000000 in
lemma before_insertion : energy (Nat.primesBelow 41) 100 = 5 := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 12000000 in
lemma after_insertion : energy (Nat.primesBelow 42) 100 = 13 := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 12000000 in
lemma new_prime_group_zero : group (Nat.primesBelow 42) 41 100 = 0 := by
  decide +kernel

lemma prime_sets_differ_by_one :
    Nat.primesBelow 42 = insert 41 (Nat.primesBelow 41) := by
  decide +kernel

/-- The top group can vanish while the energy increases by more than twice
    the number of multiples of the inserted prime. -/
lemma increase_gt_twice_multiples :
    2 * (100 / 41 : ℕ) <
      energy (Nat.primesBelow 42) 100 - energy (Nat.primesBelow 41) 100 := by
  rw [before_insertion, after_insertion]
  norm_num

/-- In particular, the insertion cost is not always at most `2N/q`. -/
theorem not_uniform_two_insertion_bound :
    ¬ ∀ q N : ℕ, q.Prime →
      (energy (Nat.primesBelow (q + 1)) N - energy (Nat.primesBelow q) N : ℤ) * q
        ≤ 2 * N := by
  intro h
  have hh := h 41 100 (by decide +kernel)
  rw [before_insertion, after_insertion] at hh
  norm_num at hh

end Erdos371InitialPeriodInsertionObstruction

#print axioms Erdos371InitialPeriodInsertionObstruction.before_insertion
#print axioms Erdos371InitialPeriodInsertionObstruction.after_insertion
#print axioms Erdos371InitialPeriodInsertionObstruction.not_uniform_two_insertion_bound
