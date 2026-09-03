import Submission.RationalKernelForms

/-!
An endpoint formula for the boundary of a polynomial positive-kernel ansatz.
This does not construct small integer forms and does not settle Spec.lean.
-/

namespace PositiveKernelBoundary

open Polynomial

/-- The unshifted telescoping operator for the column of exponent `j + 1`. -/
noncomputable def columnOperator (H : Polynomial ℚ) (j : ℕ) : Polynomial ℚ :=
  X ^ (j + 1) * H.comp (X - C 1) - H

lemma columnOperator_zero (H : Polynomial ℚ) (j : ℕ) :
    (columnOperator H j).eval 0 = -H.eval 0 := by
  simp [columnOperator]

lemma columnOperator_one (H : Polynomial ℚ) (j : ℕ) :
    (columnOperator H j).eval 1 = H.eval 0 - H.eval 1 := by
  simp [columnOperator]

lemma columnOperator_eval_row (H : Polynomial ℚ) (j n : ℕ) :
    (columnOperator H j).eval ((n + 2 : ℕ) : ℚ) =
      RationalKernelForms.rowCoeff H (j + 1) n := by
  have h : ((n + 2 : ℕ) : ℚ) - 1 = ((n + 1 : ℕ) : ℚ) := by
    push_cast
    ring
  simp only [columnOperator, eval_sub, eval_mul, eval_pow, eval_X,
    eval_comp, eval_C, RationalKernelForms.rowCoeff, h]

/-- Summing all column operators and evaluating at zero and one recovers
exactly the boundary used in the infinite telescoping identity. -/
theorem boundary_from_endpoints (H : ℕ → Polynomial ℚ) (J : ℕ) :
    RationalKernelForms.boundary H J =
      -(∑ j ∈ Finset.range J, columnOperator (H j) j).eval 0 -
        (∑ j ∈ Finset.range J, columnOperator (H j) j).eval 1 := by
  simp only [eval_finset_sum, columnOperator_zero, columnOperator_one,
    Finset.sum_neg_distrib, Finset.sum_sub_distrib, RationalKernelForms.boundary]
  ring

/-- For the square-kernel ansatz, `R` is the polynomial `R(n,1)`.
Only the two endpoint values are needed to compute the rational boundary. -/
theorem square_boundary (A : ℚ) (H : ℕ → Polynomial ℚ) (J : ℕ)
    (R : Polynomial ℚ)
    (h : (∑ j ∈ Finset.range J, columnOperator (H j) j) =
      C ((J : ℚ) * A) - R ^ 2) :
    RationalKernelForms.boundary H J =
      (R.eval 0)^2 + (R.eval 1)^2 - 2 * (J : ℚ) * A := by
  rw [boundary_from_endpoints, h]
  simp only [eval_sub, eval_C, eval_pow]
  ring

/-- The same identity holds for an arbitrary finite sum of squares. -/
theorem sum_squares_boundary {ι : Type*} (s : Finset ι) (R : ι → Polynomial ℚ)
    (A : ℚ) (H : ℕ → Polynomial ℚ) (J : ℕ)
    (h : (∑ j ∈ Finset.range J, columnOperator (H j) j) =
      C ((J : ℚ) * A) - ∑ i ∈ s, (R i)^2) :
    RationalKernelForms.boundary H J =
      (∑ i ∈ s, ((R i).eval 0)^2) +
      (∑ i ∈ s, ((R i).eval 1)^2) - 2 * (J : ℚ) * A := by
  rw [boundary_from_endpoints, h]
  simp only [eval_sub, eval_C, eval_finset_sum, eval_pow]
  ring

end PositiveKernelBoundary

#print axioms PositiveKernelBoundary.square_boundary
#print axioms PositiveKernelBoundary.sum_squares_boundary
