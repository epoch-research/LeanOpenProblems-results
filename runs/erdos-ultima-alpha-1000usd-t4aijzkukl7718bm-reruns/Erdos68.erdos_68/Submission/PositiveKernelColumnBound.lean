import Submission.RationalKernelForms
import Submission.TailPowerExpansion

/-!
The full omitted-column barrier for positive polynomial kernels.
This is auxiliary work and does not settle Erdős 68.
-/

namespace PositiveKernelColumnBound

open Erdos68Development RationalKernelForms TailPowerExpansion

noncomputable def truncated (J : ℕ) : ℝ :=
  ∑ r ∈ Finset.range J, ∑' n : ℕ, powerTerm r n

lemma sum_split (J : ℕ) :
    (∑' n : ℕ, term n) = truncated J + tailError J 0 := by
  simpa only [truncated, columnTail, Nat.add_zero] using finite_tail_expansion J 0

/-- The non-baseline part of the kernel approximates the finite column sum,
not the full original sum. This identity requires no sign assumption. -/
theorem hasSum_residual (A : ℚ) (H : ℕ → Polynomial ℚ) (J : ℕ)
    (R : ℕ → ℝ)
    (hK : ∀ n : ℕ,
      kernel A H J n (1 / ((n + 2).factorial : ℝ)) =
        (A : ℝ) * (1 / ((n + 2).factorial : ℝ)) ^ J +
          (1 - 1 / ((n + 2).factorial : ℝ)) * R n) :
    HasSum (fun n : ℕ => R n / ((n + 2).factorial : ℝ))
      ((A : ℝ) * truncated J - (boundary H J : ℝ)) := by
  have hs := (hasSum_kernel A H J).sub
    ((summable_rowError J).hasSum.mul_left (A : ℝ))
  convert hs using 1
  · ext n
    rw [hK n]
    have hf : ((n + 2).factorial : ℝ) ≠ 0 := by positivity
    have hd := (denom_pos n).ne'
    simp only [rowError, div_pow, one_pow]
    field_simp
    ring
  · have he := sum_split J
    have ht : (∑' n : ℕ, rowError J n) = tailError J 0 := by
      simp only [tailError, Nat.add_zero]
    rw [ht, he]
    ring

/-- This includes arbitrary finite sums of squares and positive-semidefinite
Gram kernels: only nonnegativity at the actual factorial nodes is needed. -/
theorem boundary_le_truncated (A : ℚ) (H : ℕ → Polynomial ℚ) (J : ℕ)
    (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n)
    (hK : ∀ n : ℕ,
      kernel A H J n (1 / ((n + 2).factorial : ℝ)) =
        (A : ℝ) * (1 / ((n + 2).factorial : ℝ)) ^ J +
          (1 - 1 / ((n + 2).factorial : ℝ)) * R n) :
    (boundary H J : ℝ) ≤ (A : ℝ) * truncated J := by
  have hs := hasSum_residual A H J R hK
  have hh : 0 ≤ ∑' n : ℕ, R n / ((n + 2).factorial : ℝ) :=
    tsum_nonneg (fun n => div_nonneg (hR n) (by positivity))
  rw [hs.tsum_eq] at hh
  linarith

/-- The complete omitted-column tail is an unavoidable positive baseline. -/
theorem full_remainder_lower_bound (A : ℚ) (H : ℕ → Polynomial ℚ) (J : ℕ)
    (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n)
    (hK : ∀ n : ℕ,
      kernel A H J n (1 / ((n + 2).factorial : ℝ)) =
        (A : ℝ) * (1 / ((n + 2).factorial : ℝ)) ^ J +
          (1 - 1 / ((n + 2).factorial : ℝ)) * R n) :
    (A : ℝ) * tailError J 0 ≤
      (A : ℝ) * (∑' n : ℕ, term n) - (boundary H J : ℝ) := by
  have hh := boundary_le_truncated A H J R hR hK
  rw [sum_split J]
  nlinarith

#print axioms hasSum_residual
#print axioms boundary_le_truncated
#print axioms full_remainder_lower_bound

end PositiveKernelColumnBound
