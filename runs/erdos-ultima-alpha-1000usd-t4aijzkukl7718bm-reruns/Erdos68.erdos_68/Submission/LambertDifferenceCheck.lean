import Submission.FactorialLambert
import Submission.LambertDifferenceOperators

/-! An exact check of the arithmetic cost of the first two row-annihilating
operators. This file does not settle the original conjecture. -/

namespace LambertDifferenceOperators

open Erdos68Development

def prefixQ (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), (lambertCoeff k : ℚ) / k.factorial

lemma first_two_shifts (x : ℝ) :
    12 * applyShifts [2, 3] (fun n => x - (prefixQ n : ℝ)) 0 =
      5 * x - 33 / 5 := by
  have hd₄ : Nat.divisors 4 = {1, 2, 4} := by decide
  have h₀ : prefixQ 0 = 0 := by norm_num [prefixQ, lambertCoeff, Finset.sum_range_succ, Nat.factorial]
  have h₂ : prefixQ 2 = 1 / 2 := by norm_num [prefixQ, lambertCoeff, Finset.sum_range_succ, Nat.factorial]
  have h₃ : prefixQ 3 = 2 / 3 := by norm_num [prefixQ, lambertCoeff, Finset.sum_range_succ, Nat.factorial]
  have h₅ : prefixQ 5 = 29 / 30 := by
    norm_num [prefixQ, lambertCoeff, Finset.sum_range_succ, Nat.factorial, hd₄]
  norm_num [applyShifts, rowShift, h₀, h₂, h₃, h₅]
  ring

lemma first_two_cleared_shifts (x : ℝ) :
    60 * applyShifts [2, 3] (fun n => x - (prefixQ n : ℝ)) 0 =
      25 * x - 33 := by
  have h := first_two_shifts x
  linarith

/-- The integer constant in the reduced cleared form is 33, not 33/5.
The resulting absolute error is already greater than one. -/
lemma first_two_cleared_error_large :
    1 < |25 * (∑' k : ℕ, term k) - 33| := by
  have hu := sum_bounds.2
  have hn : 25 * (∑' k : ℕ, term k) - 33 < 0 := by linarith
  rw [abs_of_neg hn]
  linarith

end LambertDifferenceOperators

#print axioms LambertDifferenceOperators.first_two_shifts
#print axioms LambertDifferenceOperators.first_two_cleared_error_large
