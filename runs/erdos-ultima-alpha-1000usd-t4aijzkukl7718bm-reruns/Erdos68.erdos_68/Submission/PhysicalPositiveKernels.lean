import Submission.RationalKernelForms
import Submission.PositiveKernelBoundary

/-! A quadratic kernel positive on the physical index domain. Unlike the
older A*t^J+(1-t)*SOS ansatz, it has no fixed omitted-column baseline. -/
namespace PhysicalPositiveKernels

open Polynomial RationalKernelForms PositiveKernelBoundary Erdos68Development

/-- The positivity condition is required only at the actual row indices,
not at the auxiliary polynomial endpoints zero and one. -/
theorem quadratic_kernel_identity (a : ℚ) (H : ℕ → Polynomial ℚ)
    (R S : ℕ → ℝ)
    (h₁ : ∀ n, (rowCoeff (H 0) 1 n : ℝ) = -2 * (a : ℝ) * R n - S n)
    (h₂ : ∀ n, (rowCoeff (H 1) 2 n : ℝ) = S n) (n : ℕ) (t : ℝ) :
    kernel (a^2) H 2 n t =
      ((a : ℝ) + (1-t)*R n)^2 + (1-t)^2 * (S n - (R n)^2) := by
  norm_num only [kernel, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, pow_zero, pow_one, Nat.reduceAdd, Rat.cast_pow]
  rw [h₁, h₂]
  ring

theorem quadratic_kernel_nonneg (a : ℚ) (H : ℕ → Polynomial ℚ)
    (R S : ℕ → ℝ)
    (h₁ : ∀ n, (rowCoeff (H 0) 1 n : ℝ) = -2 * (a : ℝ) * R n - S n)
    (h₂ : ∀ n, (rowCoeff (H 1) 2 n : ℝ) = S n)
    (hvariance : ∀ n, (R n)^2 ≤ S n) (n : ℕ) (t : ℝ) :
    0 ≤ kernel (a^2) H 2 n t := by
  rw [quadratic_kernel_identity a H R S h₁ h₂]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
    (sub_nonneg.mpr (hvariance n)))

/-- With a polynomial cross term, only its two endpoint values determine
the rational boundary. -/
theorem quadratic_boundary (a : ℚ) (H : ℕ → Polynomial ℚ) (R S : Polynomial ℚ)
    (h₁ : columnOperator (H 0) 0 = -C (2*a)*R-S)
    (h₂ : columnOperator (H 1) 1 = S) :
    boundary H 2 = 2*a*(R.eval 0 + R.eval 1) := by
  rw [boundary_from_endpoints]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd]
  rw [h₁, h₂]
  simp only [eval_add, eval_sub, eval_neg, eval_mul, eval_C]
  ring

/-- Exact variational error decomposition. The variance can be zero, so a
strictly positive row must still be supplied when using it for nonvanishing. -/
theorem hasSum_quadratic_error (a : ℚ) (H : ℕ → Polynomial ℚ)
    (R S : ℕ → ℝ)
    (h₁ : ∀ n, (rowCoeff (H 0) 1 n : ℝ) = -2 * (a : ℝ) * R n - S n)
    (h₂ : ∀ n, (rowCoeff (H 1) 2 n : ℝ) = S n) :
    HasSum (fun n : ℕ =>
      (((a : ℝ) + (1 - 1 / ((n+2).factorial : ℝ))*R n)^2 +
        (1 - 1 / ((n+2).factorial : ℝ))^2 * (S n - (R n)^2)) /
          (((n+2).factorial : ℝ)-1))
      ((a : ℝ)^2 * (∑' n : ℕ, term n) - (boundary H 2 : ℝ)) := by
  convert hasSum_kernel (a^2) H 2 using 1
  · funext n
    rw [quadratic_kernel_identity a H R S h₁ h₂]
  · simp only [Rat.cast_pow]

end PhysicalPositiveKernels

#print axioms PhysicalPositiveKernels.quadratic_kernel_nonneg
#print axioms PhysicalPositiveKernels.quadratic_boundary
#print axioms PhysicalPositiveKernels.hasSum_quadratic_error
