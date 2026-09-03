import Submission.DyadicHarmonicCancellation

/-!
Finite tests of the ordinary non-between discrepancy. Its prefixes do not
have a fixed sign. This rules out only an everywhere-nonnegative or
everywhere-nonpositive prefix argument, not an eventual or sublinear bound,
and is not a disproof of the density conjecture.
-/

namespace Erdos371
open Finset
set_option autoImplicit false

/-- Ordinary, rather than harmonic, signed non-between discrepancy on [1,N]. -/
def nonBetweenPrefixDiscrepancy (N : ℕ) : ℤ :=
  ∑ n ∈ Icc 1 N, if factorBetween n then 0 else
    if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then 1 else -1

lemma nonBetweenPrefixDiscrepancy_two : nonBetweenPrefixDiscrepancy 2 = 2 := by
  decide +kernel

lemma nonBetweenPrefixDiscrepancy_fifteen : nonBetweenPrefixDiscrepancy 15 = -1 := by
  decide +kernel

/-- The arithmetic discrepancy, not an auxiliary label model, has both signs. -/
theorem nonBetweenPrefixDiscrepancy_both_signs :
    (∃ N, nonBetweenPrefixDiscrepancy N < 0) ∧
      (∃ N, 0 < nonBetweenPrefixDiscrepancy N) := by
  constructor
  · exact ⟨15, by rw [nonBetweenPrefixDiscrepancy_fifteen]; norm_num⟩
  · exact ⟨2, by rw [nonBetweenPrefixDiscrepancy_two]; norm_num⟩

theorem nonBetweenPrefixDiscrepancy_not_nonnegative :
    ¬ ∀ N, 0 ≤ nonBetweenPrefixDiscrepancy N := by
  intro h
  have h15 := h 15
  rw [nonBetweenPrefixDiscrepancy_fifteen] at h15
  norm_num at h15

theorem nonBetweenPrefixDiscrepancy_not_nonpositive :
    ¬ ∀ N, nonBetweenPrefixDiscrepancy N ≤ 0 := by
  intro h
  have h2 := h 2
  rw [nonBetweenPrefixDiscrepancy_two] at h2
  norm_num at h2

#print axioms nonBetweenPrefixDiscrepancy_both_signs
#print axioms nonBetweenPrefixDiscrepancy_not_nonnegative
#print axioms nonBetweenPrefixDiscrepancy_not_nonpositive
end Erdos371
