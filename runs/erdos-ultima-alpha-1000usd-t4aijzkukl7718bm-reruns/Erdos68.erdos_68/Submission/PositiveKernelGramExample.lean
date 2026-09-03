import Submission.RationalKernelForms

/-!
A rational sum-of-squares construction with A=B=1. It bypasses the
single-square mod-four obstruction, but its sum is merely alpha-1.
It supplies no sequence of small forms and does not settle Spec.lean.
-/

namespace PositiveKernelGramExample

open Polynomial RationalKernelForms

noncomputable def lower : Polynomial ℚ :=
  C (1 / 66584) *
    (-C 89 * X^7 + C 1130 * X^6 - C 6040 * X^5 + C 16603 * X^4 -
      C 29917 * X^3 + C 52885 * X^2 - C 94608 * X + C 93340)

noncomputable def middle : Polynomial ℚ :=
  C (4160 / 66584) * (X^2 - C 7 * X + C 14)

noncomputable def family (j : ℕ) : Polynomial ℚ :=
  if j = 0 then lower else if j = 1 then middle else 0

noncomputable def c (x : ℝ) : ℝ := -x^4 + 9*x^3 - 21*x^2 - 7*x + 30
noncomputable def w (x : ℝ) : ℝ := x^4 - 14*x^3 + 65*x^2 - 116*x + 65

lemma boundary_eq_one : boundary family 3 = 1 := by
  norm_num [boundary, Finset.sum_range_succ, family, lower, middle]

/-- Exact algebraic identity. No numerical approximations enter this certificate. -/
theorem kernel_identity (n : ℕ) (t : ℝ) :
    kernel 1 family 3 n t =
      (66560*t^3 + (1-t)*(65*(c (n+2) + 32*t)^2 + 24*(w (n+2))^2) + 24) / 66584 := by
  norm_num [kernel, rowCoeff, Finset.sum_range_succ, family, lower, middle, c, w]
  ring

lemma kernel_pos_on_unit_interval (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < kernel 1 family 3 n t := by
  rw [kernel_identity]
  apply div_pos _ (by norm_num)
  have h1 : 0 ≤ 66560*t^3 := by positivity
  have h2 : 0 ≤ (1-t)*(65*(c (n+2)+32*t)^2 + 24*(w (n+2))^2) := by
    apply mul_nonneg (by linarith)
    positivity
  linarith

/-- Integral endpoint data and strict positivity are simultaneously possible
with rational polynomial coefficients once more than one square is allowed. -/
theorem integral_boundary_and_positive_rows :
    boundary family 3 = 1 ∧ ∀ n : ℕ,
      0 < kernel 1 family 3 n (1 / ((n+2).factorial : ℝ)) := by
  refine ⟨boundary_eq_one, fun n => ?_⟩
  exact kernel_pos_on_unit_interval n _ (by positivity)
    (Erdos68Development.reciprocal_factorial_lt_one n).le

/-- The certificate yields the fixed form alpha-1, not a vanishing sequence. -/
theorem sum_kernel :
    (∑' n : ℕ, kernel 1 family 3 n (1 / ((n+2).factorial : ℝ)) /
      (((n+2).factorial : ℝ)-1)) =
        (∑' n : ℕ, Erdos68Development.term n) - 1 := by
  simpa only [boundary_eq_one, Rat.cast_one, one_mul] using
    (hasSum_kernel 1 family 3).tsum_eq

end PositiveKernelGramExample

#print axioms PositiveKernelGramExample.kernel_identity
#print axioms PositiveKernelGramExample.integral_boundary_and_positive_rows
#print axioms PositiveKernelGramExample.sum_kernel
