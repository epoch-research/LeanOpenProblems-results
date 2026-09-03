import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3750 : ∀ i : Fin 200, Compatible (750000 + i.val) →
    (table.lookup (750000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3750 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 750000 750200 :=
  FiniteIntervals.of_fin 750000 200 complete_chunk3750

lemma complete_chunk3751 : ∀ i : Fin 200, Compatible (750200 + i.val) →
    (table.lookup (750200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3751 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 750200 750400 :=
  FiniteIntervals.of_fin 750200 200 complete_chunk3751

lemma complete_chunk3752 : ∀ i : Fin 200, Compatible (750400 + i.val) →
    (table.lookup (750400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3752 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 750400 750600 :=
  FiniteIntervals.of_fin 750400 200 complete_chunk3752

lemma complete_chunk3753 : ∀ i : Fin 200, Compatible (750600 + i.val) →
    (table.lookup (750600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3753 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 750600 750800 :=
  FiniteIntervals.of_fin 750600 200 complete_chunk3753

lemma complete_chunk3754 : ∀ i : Fin 200, Compatible (750800 + i.val) →
    (table.lookup (750800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3754 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 750800 751000 :=
  FiniteIntervals.of_fin 750800 200 complete_chunk3754

lemma complete_chunk3755 : ∀ i : Fin 200, Compatible (751000 + i.val) →
    (table.lookup (751000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3755 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 751000 751200 :=
  FiniteIntervals.of_fin 751000 200 complete_chunk3755

lemma complete_chunk3756 : ∀ i : Fin 200, Compatible (751200 + i.val) →
    (table.lookup (751200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3756 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 751200 751400 :=
  FiniteIntervals.of_fin 751200 200 complete_chunk3756

lemma complete_chunk3757 : ∀ i : Fin 200, Compatible (751400 + i.val) →
    (table.lookup (751400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3757 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 751400 751600 :=
  FiniteIntervals.of_fin 751400 200 complete_chunk3757

lemma complete_chunk3758 : ∀ i : Fin 200, Compatible (751600 + i.val) →
    (table.lookup (751600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3758 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 751600 751800 :=
  FiniteIntervals.of_fin 751600 200 complete_chunk3758

lemma complete_chunk3759 : ∀ i : Fin 200, Compatible (751800 + i.val) →
    (table.lookup (751800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3759 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 751800 752000 :=
  FiniteIntervals.of_fin 751800 200 complete_chunk3759

#print axioms interval_chunk3750
end Erdos184Work.PureFiveFilter4
