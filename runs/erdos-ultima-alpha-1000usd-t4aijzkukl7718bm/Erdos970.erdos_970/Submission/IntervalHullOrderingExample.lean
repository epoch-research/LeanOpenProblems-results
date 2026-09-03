import Submission.IntervalHullFinite
import Submission.IntervalHullWheelThirty

/-!
# Increasing-prime order need not dominate in the integer hull recurrence

The seed below is a sound compatible period-30 pair for 2,3,5. Processing
11 before 7 can improve either branch at particular lengths. This is not a
counterexample to Erdős 970, and gives no asymptotic gain from reordering.
-/
namespace Erdos970.IntervalRescaling.IntegerHull
namespace OrderingExample

def seed : (ℕ → ℤ) × (ℕ → ℤ) := (WheelThirty.lo, WheelThirty.hi)

def increasing : (ℕ → ℤ) × (ℕ → ℤ) := finiteStep 11 (finiteStep 7 seed)
def reversed : (ℕ → ℤ) × (ℕ → ℤ) := finiteStep 7 (finiteStep 11 seed)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem upper_values : increasing.2 483 = 105 ∧ reversed.2 483 = 104 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower_values : increasing.1 744 = 150 ∧ reversed.1 744 = 151 := by
  decide +kernel

lemma seed_compatible : Compatible (realPair seed).1 (realPair seed).2 := WheelThirty.compatible
lemma seed_lower_nonneg (n : ℕ) : 0 ≤ (realPair seed).1 n := by
  change 0 ≤ (WheelThirty.lo n : ℝ)
  exact_mod_cast (WheelThirty.nonneg n).1

theorem upper_order_failure :
    (closedStep 7 (closedStep 11 (realPair seed))).2 483 <
      (closedStep 11 (closedStep 7 (realPair seed))).2 483 := by
  rw [← cast_finiteStep_twice 11 7 (by omega) (by omega) seed seed_compatible seed_lower_nonneg,
    ← cast_finiteStep_twice 7 11 (by omega) (by omega) seed seed_compatible seed_lower_nonneg]
  change (reversed.2 483 : ℝ) < (increasing.2 483 : ℝ)
  rw [upper_values.1, upper_values.2]
  norm_num

theorem lower_order_failure :
    (closedStep 11 (closedStep 7 (realPair seed))).1 744 <
      (closedStep 7 (closedStep 11 (realPair seed))).1 744 := by
  rw [← cast_finiteStep_twice 7 11 (by omega) (by omega) seed seed_compatible seed_lower_nonneg,
    ← cast_finiteStep_twice 11 7 (by omega) (by omega) seed seed_compatible seed_lower_nonneg]
  change (increasing.1 744 : ℝ) < (reversed.1 744 : ℝ)
  rw [lower_values.1, lower_values.2]
  norm_num

#print axioms upper_order_failure
#print axioms lower_order_failure
end OrderingExample
end Erdos970.IntervalRescaling.IntegerHull
