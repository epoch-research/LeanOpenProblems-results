import Submission.GeometricClearingBarrier

/-!
# A mixed geometric truncation with a small reduced scaled error

This is an auxiliary counterexample to extending the termwise-clearing bound
to reduced denominators. It does not settle the irrationality conjecture.
-/

namespace MixedReducedCancellation

open Erdos68Development GeometricClearingBarrier

def orders (k : ℕ) : ℕ := if k = 0 then 2 else 1

def approximation : ℚ := 7057699 / 5630400

lemma approximation_eq_mixed :
    (approximation : ℝ) = mixedApprox 2 4 orders := by
  norm_num [approximation, mixedApprox, rowPrefix, orders, term, powerTerm,
    Finset.sum_range_succ, Nat.factorial]

lemma approximation_num_den :
    approximation.num = 7057699 ∧ approximation.den = 5630400 := by
  norm_num [approximation]

lemma sum_strict_upper :
    (∑' k : ℕ, term k) < (7057700 / 5630400 : ℝ) := by
  have he := (partial_sum_error 10).2
  have hfinite : (∑ k ∈ Finset.range 10, term k) + (3 / 2 : ℝ) * term 10 <
      (7057700 / 5630400 : ℝ) := by
    norm_num [Finset.sum_range_succ, term, Nat.factorial]
  linarith

/-- A single positive scaled error below 1; this is not a sequence tending to 0. -/
theorem reduced_scaled_error_small :
    0 < (approximation.den : ℝ) *
        ((∑' k : ℕ, term k) - (approximation : ℝ)) ∧
      (approximation.den : ℝ) *
        ((∑' k : ℕ, term k) - (approximation : ℝ)) < 1 := by
  have he := mixedApprox_error_lower 2 4 orders
  rw [← approximation_eq_mixed] at he
  have hpos : 0 < (∑' k : ℕ, term k) - (approximation : ℝ) := by
    have hfirst : (0 : ℝ) <
        1 / (((2 + 4).factorial : ℝ) ^ orders 0 * ((2 + 4).factorial - 1)) := by
      norm_num [orders, Nat.factorial]
    exact hfirst.trans he
  have hu := sum_strict_upper
  rw [approximation_num_den.2]
  constructor
  · exact mul_pos (by norm_num) hpos
  · norm_num [approximation] at hu ⊢
    linarith

/-- The prime 7 from 5!-1, as well as some factorial prime powers, is removed
by reduction of the entire mixed approximation. -/
lemma missing_termwise_factors :
    ¬denom 3 ∣ approximation.den ∧
      ¬(6 : ℕ).factorial ^ 2 ∣ approximation.den := by
  norm_num [approximation, denom, Nat.factorial]

/-- The earlier theorem's three divisibility hypotheses cannot be replaced by
merely clearing the final reduced rational approximation. -/
theorem reduced_denominator_does_not_obey_termwise_barrier :
    ¬(1 < (approximation.den : ℝ) *
      ((∑' k : ℕ, term k) - mixedApprox 2 4 orders)) := by
  rw [← approximation_eq_mixed]
  exact not_lt.mpr reduced_scaled_error_small.2.le

#print axioms reduced_scaled_error_small
#print axioms reduced_denominator_does_not_obey_termwise_barrier

end MixedReducedCancellation
