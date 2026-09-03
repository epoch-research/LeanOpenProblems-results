import Submission.DivisorCycleBound

/-! A mixed-orientation cycle in the actual largest-prime-factor sequence.
The directed divisor-cycle size bound does not extend to mixed orientations:
the two endpoint products can agree exactly. This does not disprove Erdős 371. -/

namespace Erdos371

/-- Forward edges at 172 and 173 and the backward edge at 86 form the
largest-prime-label cycle 43 -> 173 -> 29 -> 43. -/
theorem actual_mixed_prime_cycle_labels :
    Nat.maxPrimeFac 172 = 43 ∧ Nat.maxPrimeFac 173 = 173 ∧
    Nat.maxPrimeFac 174 = 29 ∧ Nat.maxPrimeFac 87 = 29 ∧
    Nat.maxPrimeFac 86 = 43 := by
  decide +kernel

/-- Both endpoint products of this cycle agree. Hence their difference is
zero, rather than a positive integer bounding the product of its labels. -/
theorem actual_mixed_prime_cycle_product_equality :
    (172 : ℕ) * 173 * 87 = 173 * 174 * 86 := by
  norm_num

/-- The product of the three actual labels exceeds the bound for a directed
cycle of length three whose indices are at most 173. -/
theorem actual_mixed_prime_cycle_exceeds_directed_bound :
    3 * (173 + 1) ^ (3 - 1) <
      Nat.maxPrimeFac 172 * Nat.maxPrimeFac 173 * Nat.maxPrimeFac 174 := by
  obtain ⟨h172, h173, h174, _, _⟩ := actual_mixed_prime_cycle_labels
  rw [h172, h173, h174]
  norm_num

/-- This is an explicit obstruction to the mixed-orientation extension of
an auxiliary finite bound, not a counterexample to the density conjecture. -/
theorem mixed_prime_cycle_obstruction :
    (Nat.maxPrimeFac 172 = Nat.maxPrimeFac 86 ∧
      Nat.maxPrimeFac 174 = Nat.maxPrimeFac 87) ∧
    (172 : ℕ) * 173 * 87 = 173 * 174 * 86 ∧
    3 * (173 + 1) ^ (3 - 1) <
      Nat.maxPrimeFac 172 * Nat.maxPrimeFac 173 * Nat.maxPrimeFac 174 := by
  obtain ⟨h172, _, h174, h87, h86⟩ := actual_mixed_prime_cycle_labels
  exact ⟨⟨h172.trans h86.symm, h174.trans h87.symm⟩,
    actual_mixed_prime_cycle_product_equality,
    actual_mixed_prime_cycle_exceeds_directed_bound⟩

#print axioms mixed_prime_cycle_obstruction

/-- The same obstruction also occurs for an even cycle, relevant to fourth
moments: the three forward edges starting at 906, 907, 908 and the backward
edge starting at 302 have four distinct largest-prime labels. -/
theorem actual_mixed_four_cycle_labels :
    Nat.maxPrimeFac 906 = 151 ∧ Nat.maxPrimeFac 907 = 907 ∧
    Nat.maxPrimeFac 908 = 227 ∧ Nat.maxPrimeFac 909 = 101 ∧
    Nat.maxPrimeFac 303 = 101 ∧ Nat.maxPrimeFac 302 = 151 := by
  decide +kernel

/-- A degenerate mixed four-cycle can exceed the directed-cycle size bound.
Its label cycle is 151 -> 907 -> 227 -> 101 -> 151. -/
theorem mixed_prime_four_cycle_obstruction :
    (Nat.maxPrimeFac 906 = Nat.maxPrimeFac 302 ∧
      Nat.maxPrimeFac 909 = Nat.maxPrimeFac 303) ∧
    (906 : ℕ) * 907 * 908 * 303 = 907 * 908 * 909 * 302 ∧
    4 * (908 + 1) ^ (4 - 1) <
      Nat.maxPrimeFac 906 * Nat.maxPrimeFac 907 *
        Nat.maxPrimeFac 908 * Nat.maxPrimeFac 909 := by
  obtain ⟨h906, h907, h908, h909, h303, h302⟩ := actual_mixed_four_cycle_labels
  rw [h906, h907, h908, h909, h303, h302]
  norm_num

#print axioms mixed_prime_four_cycle_obstruction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A balanced mixed four-cycle, with two forward and two backward edges.
It is obtained from the prime values t, 6*t+1, 16*t+3, 8*t+1 at t=1811.
The label cycle is 1811 -> 10867 -> 28979 -> 14489 -> 1811. -/
theorem actual_balanced_four_cycle_labels :
    Nat.maxPrimeFac 10866 = 1811 ∧ Nat.maxPrimeFac 10867 = 10867 ∧
    Nat.maxPrimeFac 86936 = 10867 ∧ Nat.maxPrimeFac 86937 = 28979 ∧
    Nat.maxPrimeFac 28979 = 28979 ∧ Nat.maxPrimeFac 28978 = 14489 ∧
    Nat.maxPrimeFac 14489 = 14489 ∧ Nat.maxPrimeFac 14488 = 1811 := by
  decide +kernel

/-- Even with two edges in each orientation, exact product degeneracy need
not be backtracking, and does not imply the directed-cycle size bound.
Such a cycle has positive orientation product in an even-moment expansion. -/
theorem balanced_mixed_prime_four_cycle_obstruction :
    (Nat.maxPrimeFac 10867 = Nat.maxPrimeFac 86936 ∧
      Nat.maxPrimeFac 86937 = Nat.maxPrimeFac 28979 ∧
      Nat.maxPrimeFac 28978 = Nat.maxPrimeFac 14489 ∧
      Nat.maxPrimeFac 14488 = Nat.maxPrimeFac 10866) ∧
    (10866 : ℕ) * 86936 * 28979 * 14489 =
      10867 * 86937 * 28978 * 14488 ∧
    4 * (86936 + 1) ^ (4 - 1) <
      Nat.maxPrimeFac 10866 * Nat.maxPrimeFac 10867 *
        Nat.maxPrimeFac 28979 * Nat.maxPrimeFac 14489 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := actual_balanced_four_cycle_labels
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  norm_num

#print axioms balanced_mixed_prime_four_cycle_obstruction
/-- Balance of traversal orientations is different from balance of the
actual comparisons: all four edges in this cycle are rises. -/
theorem balanced_four_cycle_all_comparisons_rise :
    Nat.maxPrimeFac (10866+1) > Nat.maxPrimeFac 10866 ∧
    Nat.maxPrimeFac (86936+1) > Nat.maxPrimeFac 86936 ∧
    Nat.maxPrimeFac (28978+1) > Nat.maxPrimeFac 28978 ∧
    Nat.maxPrimeFac (14488+1) > Nat.maxPrimeFac 14488 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := actual_balanced_four_cycle_labels
  norm_num only at ⊢
  rw [h1,h2,h3,h4,h5,h6,h7,h8]
  norm_num

/-- Exact zero logarithmic circulation around the same mixed cycle.
Thus zero logarithmic circulation does not force comparison-sign balance. -/
theorem balanced_four_cycle_log_circulation_zero :
    Real.log ((10867 : ℝ)/10866)+Real.log ((86937 : ℝ)/86936)-
      Real.log ((28979 : ℝ)/28978)-Real.log ((14489 : ℝ)/14488)=0 := by
  have he : ((10867 : ℝ)/10866)*((86937 : ℝ)/86936)=
      ((28979 : ℝ)/28978)*((14489 : ℝ)/14488) := by norm_num
  have hl := congrArg Real.log he
  rw [Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)] at hl
  linarith

#print axioms balanced_four_cycle_all_comparisons_rise
#print axioms balanced_four_cycle_log_circulation_zero
end Erdos371
