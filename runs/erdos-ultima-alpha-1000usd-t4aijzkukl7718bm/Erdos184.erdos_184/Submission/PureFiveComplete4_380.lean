import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3800 : ∀ i : Fin 200, Compatible (760000 + i.val) →
    (table.lookup (760000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3800 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 760000 760200 :=
  FiniteIntervals.of_fin 760000 200 complete_chunk3800

lemma complete_chunk3801 : ∀ i : Fin 200, Compatible (760200 + i.val) →
    (table.lookup (760200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3801 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 760200 760400 :=
  FiniteIntervals.of_fin 760200 200 complete_chunk3801

lemma complete_chunk3802 : ∀ i : Fin 200, Compatible (760400 + i.val) →
    (table.lookup (760400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3802 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 760400 760600 :=
  FiniteIntervals.of_fin 760400 200 complete_chunk3802

lemma complete_chunk3803 : ∀ i : Fin 200, Compatible (760600 + i.val) →
    (table.lookup (760600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3803 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 760600 760800 :=
  FiniteIntervals.of_fin 760600 200 complete_chunk3803

lemma complete_chunk3804 : ∀ i : Fin 200, Compatible (760800 + i.val) →
    (table.lookup (760800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3804 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 760800 761000 :=
  FiniteIntervals.of_fin 760800 200 complete_chunk3804

lemma complete_chunk3805 : ∀ i : Fin 200, Compatible (761000 + i.val) →
    (table.lookup (761000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3805 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 761000 761200 :=
  FiniteIntervals.of_fin 761000 200 complete_chunk3805

lemma complete_chunk3806 : ∀ i : Fin 200, Compatible (761200 + i.val) →
    (table.lookup (761200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3806 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 761200 761400 :=
  FiniteIntervals.of_fin 761200 200 complete_chunk3806

lemma complete_chunk3807 : ∀ i : Fin 200, Compatible (761400 + i.val) →
    (table.lookup (761400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3807 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 761400 761600 :=
  FiniteIntervals.of_fin 761400 200 complete_chunk3807

lemma complete_chunk3808 : ∀ i : Fin 200, Compatible (761600 + i.val) →
    (table.lookup (761600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3808 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 761600 761800 :=
  FiniteIntervals.of_fin 761600 200 complete_chunk3808

lemma complete_chunk3809 : ∀ i : Fin 200, Compatible (761800 + i.val) →
    (table.lookup (761800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3809 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 761800 762000 :=
  FiniteIntervals.of_fin 761800 200 complete_chunk3809

#print axioms interval_chunk3800
end Erdos184Work.PureFiveFilter4
