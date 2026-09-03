import Mathlib

/-!
# An algebraic obstruction for the joint-factor-pattern investigation

This file does not import `Submission.Spec`, assert a prime-gap theorem, or
assume a number-theoretic asymptotic. It checks that even exact row/column
marginals together with divisor-weighted row/column moments can admit a
nonnegative completion whose prime--prime cell is zero.

The three indices represent squarefree factor counts 1, 2, 3; their divisor
counts are 2, 4, 8. Rows/columns with larger factor counts can be left unchanged.
-/

open scoped BigOperators

namespace JointPatternAudit

def benchmark (a b : ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![1, a, b], ![a, a * a, a * b], ![b, a * b, b * b]]

noncomputable def completion (a b : ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![0, a + 3 / 2, b - 1 / 2],
    ![a + 3 / 2, a * a - 9 / 4, a * b + 3 / 4],
    ![b - 1 / 2, a * b + 3 / 4, b * b - 1 / 4]]

def divisorCount : Fin 3 → ℝ := ![2, 4, 8]

theorem same_row_marginals (a b : ℝ) (i : Fin 3) :
    ∑ j, completion a b i j = ∑ j, benchmark a b i j := by
  fin_cases i <;> norm_num [completion, benchmark, Fin.sum_univ_succ] <;> ring

theorem same_column_marginals (a b : ℝ) (j : Fin 3) :
    ∑ i, completion a b i j = ∑ i, benchmark a b i j := by
  fin_cases j <;> norm_num [completion, benchmark, Fin.sum_univ_succ] <;> ring

theorem same_row_divisor_moments (a b : ℝ) (i : Fin 3) :
    ∑ j, divisorCount j * completion a b i j =
      ∑ j, divisorCount j * benchmark a b i j := by
  fin_cases i <;>
    norm_num [completion, benchmark, divisorCount, Fin.sum_univ_succ] <;> ring

theorem same_column_divisor_moments (a b : ℝ) (j : Fin 3) :
    ∑ i, divisorCount i * completion a b i j =
      ∑ i, divisorCount i * benchmark a b i j := by
  fin_cases j <;>
    norm_num [completion, benchmark, divisorCount, Fin.sum_univ_succ] <;> ring

theorem completion_nonnegative (a b : ℝ)
    (ha : 3 / 2 ≤ a) (hb : 1 / 2 ≤ b) :
    ∀ i j, 0 ≤ completion a b i j := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hab : 0 ≤ a * b := mul_nonneg ha0 hb0
  have ha2 : (9 : ℝ) / 4 ≤ a * a := by
    nlinarith [sq_nonneg (a - 3 / 2)]
  have hb2 : (1 : ℝ) / 4 ≤ b * b := by
    nlinarith [sq_nonneg (b - 1 / 2)]
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [completion] <;> nlinarith

theorem prime_pair_cells_differ (a b : ℝ) :
    completion a b 0 0 = 0 ∧ benchmark a b 0 0 = 1 := by
  norm_num [completion, benchmark]

#print axioms same_row_marginals
#print axioms same_column_marginals
#print axioms same_row_divisor_moments
#print axioms same_column_divisor_moments
#print axioms completion_nonnegative
#print axioms prime_pair_cells_differ

end JointPatternAudit
