import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3560 : ∀ i : Fin 200, Compatible (712000 + i.val) →
    (table.lookup (712000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3560 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 712000 712200 :=
  FiniteIntervals.of_fin 712000 200 complete_chunk3560

lemma complete_chunk3561 : ∀ i : Fin 200, Compatible (712200 + i.val) →
    (table.lookup (712200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3561 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 712200 712400 :=
  FiniteIntervals.of_fin 712200 200 complete_chunk3561

lemma complete_chunk3562 : ∀ i : Fin 200, Compatible (712400 + i.val) →
    (table.lookup (712400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3562 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 712400 712600 :=
  FiniteIntervals.of_fin 712400 200 complete_chunk3562

lemma complete_chunk3563 : ∀ i : Fin 200, Compatible (712600 + i.val) →
    (table.lookup (712600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3563 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 712600 712800 :=
  FiniteIntervals.of_fin 712600 200 complete_chunk3563

lemma complete_chunk3564 : ∀ i : Fin 200, Compatible (712800 + i.val) →
    (table.lookup (712800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3564 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 712800 713000 :=
  FiniteIntervals.of_fin 712800 200 complete_chunk3564

lemma complete_chunk3565 : ∀ i : Fin 200, Compatible (713000 + i.val) →
    (table.lookup (713000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3565 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 713000 713200 :=
  FiniteIntervals.of_fin 713000 200 complete_chunk3565

lemma complete_chunk3566 : ∀ i : Fin 200, Compatible (713200 + i.val) →
    (table.lookup (713200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3566 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 713200 713400 :=
  FiniteIntervals.of_fin 713200 200 complete_chunk3566

lemma complete_chunk3567 : ∀ i : Fin 200, Compatible (713400 + i.val) →
    (table.lookup (713400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3567 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 713400 713600 :=
  FiniteIntervals.of_fin 713400 200 complete_chunk3567

lemma complete_chunk3568 : ∀ i : Fin 200, Compatible (713600 + i.val) →
    (table.lookup (713600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3568 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 713600 713800 :=
  FiniteIntervals.of_fin 713600 200 complete_chunk3568

lemma complete_chunk3569 : ∀ i : Fin 200, Compatible (713800 + i.val) →
    (table.lookup (713800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3569 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 713800 714000 :=
  FiniteIntervals.of_fin 713800 200 complete_chunk3569

#print axioms interval_chunk3560
end Erdos184Work.PureFiveFilter4
