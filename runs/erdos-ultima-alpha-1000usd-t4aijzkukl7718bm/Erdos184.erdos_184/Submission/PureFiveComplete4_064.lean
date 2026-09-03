import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk640 : ∀ i : Fin 200, Compatible (128000 + i.val) →
    (table.lookup (128000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk640 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 128000 128200 :=
  FiniteIntervals.of_fin 128000 200 complete_chunk640

lemma complete_chunk641 : ∀ i : Fin 200, Compatible (128200 + i.val) →
    (table.lookup (128200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk641 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 128200 128400 :=
  FiniteIntervals.of_fin 128200 200 complete_chunk641

lemma complete_chunk642 : ∀ i : Fin 200, Compatible (128400 + i.val) →
    (table.lookup (128400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk642 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 128400 128600 :=
  FiniteIntervals.of_fin 128400 200 complete_chunk642

lemma complete_chunk643 : ∀ i : Fin 200, Compatible (128600 + i.val) →
    (table.lookup (128600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk643 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 128600 128800 :=
  FiniteIntervals.of_fin 128600 200 complete_chunk643

lemma complete_chunk644 : ∀ i : Fin 200, Compatible (128800 + i.val) →
    (table.lookup (128800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk644 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 128800 129000 :=
  FiniteIntervals.of_fin 128800 200 complete_chunk644

lemma complete_chunk645 : ∀ i : Fin 200, Compatible (129000 + i.val) →
    (table.lookup (129000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk645 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 129000 129200 :=
  FiniteIntervals.of_fin 129000 200 complete_chunk645

lemma complete_chunk646 : ∀ i : Fin 200, Compatible (129200 + i.val) →
    (table.lookup (129200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk646 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 129200 129400 :=
  FiniteIntervals.of_fin 129200 200 complete_chunk646

lemma complete_chunk647 : ∀ i : Fin 200, Compatible (129400 + i.val) →
    (table.lookup (129400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk647 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 129400 129600 :=
  FiniteIntervals.of_fin 129400 200 complete_chunk647

lemma complete_chunk648 : ∀ i : Fin 200, Compatible (129600 + i.val) →
    (table.lookup (129600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk648 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 129600 129800 :=
  FiniteIntervals.of_fin 129600 200 complete_chunk648

lemma complete_chunk649 : ∀ i : Fin 200, Compatible (129800 + i.val) →
    (table.lookup (129800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk649 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 129800 130000 :=
  FiniteIntervals.of_fin 129800 200 complete_chunk649

#print axioms interval_chunk640
end Erdos184Work.PureFiveFilter4
