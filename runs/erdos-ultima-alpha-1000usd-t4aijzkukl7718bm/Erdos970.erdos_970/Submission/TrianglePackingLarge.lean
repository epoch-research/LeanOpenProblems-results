import Submission.TriangleMultipliers

/-! Kernel-checked examples of triangle incompatibility at length 25000.
These are positional packing bounds, not Jacobsthal bounds. -/
namespace Erdos970.PatternPacking.LargeExample

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The common core is 211; the three tails are 7,23,103. -/
def family211 : Finset (Finset ℕ) :=
  {{211, 7, 23}, {211, 7, 103}, {211, 23, 103}}

lemma prime_members211 : ∀ A ∈ family211, ∀ p ∈ A, p.Prime := by decide +kernel

lemma multiplier_check211 : ∀ A ∈ family211, ∀ B ∈ family211, ∀ C ∈ family211,
    ¬AdmitsMultiplierTriangle 25000 A B C := by decide +kernel

/-- At most two positions in an interval of length 25000 hit the core 211
and at least two of the tails 7,23,103. -/
theorem actual_card211_le_two (r : ℕ → ℕ) : patternCount 25000 family211 r ≤ 2 :=
  patternCount_le_two_of_multiplier_checks 25000 family211 prime_members211
    multiplier_check211 r

/-- A second cut, with common core 47 and tails 29,41,397. -/
def family47 : Finset (Finset ℕ) :=
  {{47, 29, 41}, {47, 29, 397}, {47, 41, 397}}

lemma prime_members47 : ∀ A ∈ family47, ∀ p ∈ A, p.Prime := by decide +kernel

lemma multiplier_check47 : ∀ A ∈ family47, ∀ B ∈ family47, ∀ C ∈ family47,
    ¬AdmitsMultiplierTriangle 25000 A B C := by decide +kernel

theorem actual_card47_le_two (r : ℕ → ℕ) : patternCount 25000 family47 r ≤ 2 :=
  patternCount_le_two_of_multiplier_checks 25000 family47 prime_members47
    multiplier_check47 r

#print axioms actual_card211_le_two
#print axioms actual_card47_le_two
end Erdos970.PatternPacking.LargeExample
