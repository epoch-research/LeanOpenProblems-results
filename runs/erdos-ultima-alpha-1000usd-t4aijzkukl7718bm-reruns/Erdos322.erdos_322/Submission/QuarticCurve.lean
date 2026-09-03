import FormalConjecturesUtil

/-! An additional rational curve on the quartic level of norm two. -/

namespace Erdos322Research

/-- This identity produces quartic representations, but does not assert a
positive-power lower bound for their multiplicity. -/
theorem quartic_curve_identity (x y : ℤ) :
    (2 * x * y ^ 3) ^ 4 + (2 * x ^ 3 * y) ^ 4 +
      2 * (x ^ 4 - y ^ 4) ^ 4 = 2 * (x ^ 4 + y ^ 4) ^ 4 := by
  ring

theorem quartic_positive_seed :
    (4 : ℕ) ^ 4 + 15 ^ 4 + 15 ^ 4 + 16 ^ 4 = 2 * 17 ^ 4 := by
  norm_num

end Erdos322Research

#print axioms Erdos322Research.quartic_curve_identity
#print axioms Erdos322Research.quartic_positive_seed
