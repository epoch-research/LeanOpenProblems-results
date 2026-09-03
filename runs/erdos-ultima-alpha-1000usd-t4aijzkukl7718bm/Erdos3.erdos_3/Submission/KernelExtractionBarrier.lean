import Submission.ThinningCheck
import Submission.FiniteKernelCase

/-! A verified obstruction to an auxiliary reduction. This does NOT disprove
Erdős Problem 3. The original conjecture in `Spec.lean` remains unsettled. -/

namespace Erdos3KernelExtractionBarrier

open Erdos3FiniteKernelCase

lemma finite_shift_of_affine_thin {A : Set ℕ}
    (hA : Erdos3ThinningCheck.AffineThin A) : FiniteShiftIntersections A := by
  intro d hd
  apply (hA 1 d 1 0 (by omega) (by omega) (Or.inr (by omega))).subset
  rintro x ⟨hx, hy⟩
  exact ⟨hx, x + d, hy, by omega⟩

/-- Every divergent set contains a divergent subset on which the proposed
finite-kernel extraction route cannot work. -/
theorem divergent_subset_without_finite_kernel_subsets {A : Set ℕ}
    (hA : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) :
    ∃ B ⊆ A, (¬ Summable (fun b : B ↦ 1 / (b : ℝ))) ∧
      ∀ C ⊆ B, (dyadicKernel C).Finite → Summable (fun c : C ↦ 1 / (c : ℝ)) := by
  obtain ⟨B, hBA, hB, hthin⟩ := Erdos3ThinningCheck.divergent_affine_thin_subset hA
  refine ⟨B, hBA, hB, fun C hCB hK ↦ ?_⟩
  exact finite_kernel_subset_summable (finite_shift_of_affine_thin hthin) hCB hK

/-- Negation of a tempting auxiliary reduction, not negation of the conjecture. -/
theorem no_divergent_finite_kernel_extraction :
    ¬ (∀ A : Set ℕ, (¬ Summable (fun a : A ↦ 1 / (a : ℝ))) →
      ∃ B ⊆ A, (¬ Summable (fun b : B ↦ 1 / (b : ℝ))) ∧ (dyadicKernel B).Finite) := by
  intro h
  obtain ⟨A, hA, hthin⟩ := Erdos3ThinningCheck.exists_divergent_affine_thin
  obtain ⟨B, hBA, hB, hK⟩ := h A hA
  exact hB (finite_kernel_subset_summable (finite_shift_of_affine_thin hthin) hBA hK)

#print axioms divergent_subset_without_finite_kernel_subsets
#print axioms no_divergent_finite_kernel_extraction

end Erdos3KernelExtractionBarrier
