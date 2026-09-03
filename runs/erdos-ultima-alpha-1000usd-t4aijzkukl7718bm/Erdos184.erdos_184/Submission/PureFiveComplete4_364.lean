import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3640 : ∀ i : Fin 200, Compatible (728000 + i.val) →
    (table.lookup (728000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3640 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 728000 728200 :=
  FiniteIntervals.of_fin 728000 200 complete_chunk3640

lemma complete_chunk3641 : ∀ i : Fin 200, Compatible (728200 + i.val) →
    (table.lookup (728200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3641 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 728200 728400 :=
  FiniteIntervals.of_fin 728200 200 complete_chunk3641

lemma complete_chunk3642 : ∀ i : Fin 200, Compatible (728400 + i.val) →
    (table.lookup (728400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3642 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 728400 728600 :=
  FiniteIntervals.of_fin 728400 200 complete_chunk3642

lemma complete_chunk3643 : ∀ i : Fin 200, Compatible (728600 + i.val) →
    (table.lookup (728600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3643 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 728600 728800 :=
  FiniteIntervals.of_fin 728600 200 complete_chunk3643

lemma complete_chunk3644 : ∀ i : Fin 200, Compatible (728800 + i.val) →
    (table.lookup (728800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3644 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 728800 729000 :=
  FiniteIntervals.of_fin 728800 200 complete_chunk3644

lemma complete_chunk3645 : ∀ i : Fin 200, Compatible (729000 + i.val) →
    (table.lookup (729000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3645 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 729000 729200 :=
  FiniteIntervals.of_fin 729000 200 complete_chunk3645

lemma complete_chunk3646 : ∀ i : Fin 200, Compatible (729200 + i.val) →
    (table.lookup (729200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3646 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 729200 729400 :=
  FiniteIntervals.of_fin 729200 200 complete_chunk3646

lemma complete_chunk3647 : ∀ i : Fin 200, Compatible (729400 + i.val) →
    (table.lookup (729400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3647 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 729400 729600 :=
  FiniteIntervals.of_fin 729400 200 complete_chunk3647

lemma complete_chunk3648 : ∀ i : Fin 200, Compatible (729600 + i.val) →
    (table.lookup (729600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3648 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 729600 729800 :=
  FiniteIntervals.of_fin 729600 200 complete_chunk3648

lemma complete_chunk3649 : ∀ i : Fin 200, Compatible (729800 + i.val) →
    (table.lookup (729800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3649 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 729800 730000 :=
  FiniteIntervals.of_fin 729800 200 complete_chunk3649

#print axioms interval_chunk3640
end Erdos184Work.PureFiveFilter4
