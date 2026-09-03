import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5640 : ∀ i : Fin 200, Compatible (1128000 + i.val) →
    (table.lookup (1128000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5640 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1128000 1128200 :=
  FiniteIntervals.of_fin 1128000 200 complete_chunk5640

lemma complete_chunk5641 : ∀ i : Fin 200, Compatible (1128200 + i.val) →
    (table.lookup (1128200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5641 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1128200 1128400 :=
  FiniteIntervals.of_fin 1128200 200 complete_chunk5641

lemma complete_chunk5642 : ∀ i : Fin 200, Compatible (1128400 + i.val) →
    (table.lookup (1128400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5642 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1128400 1128600 :=
  FiniteIntervals.of_fin 1128400 200 complete_chunk5642

lemma complete_chunk5643 : ∀ i : Fin 200, Compatible (1128600 + i.val) →
    (table.lookup (1128600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5643 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1128600 1128800 :=
  FiniteIntervals.of_fin 1128600 200 complete_chunk5643

lemma complete_chunk5644 : ∀ i : Fin 200, Compatible (1128800 + i.val) →
    (table.lookup (1128800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5644 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1128800 1129000 :=
  FiniteIntervals.of_fin 1128800 200 complete_chunk5644

lemma complete_chunk5645 : ∀ i : Fin 200, Compatible (1129000 + i.val) →
    (table.lookup (1129000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5645 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1129000 1129200 :=
  FiniteIntervals.of_fin 1129000 200 complete_chunk5645

lemma complete_chunk5646 : ∀ i : Fin 200, Compatible (1129200 + i.val) →
    (table.lookup (1129200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5646 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1129200 1129400 :=
  FiniteIntervals.of_fin 1129200 200 complete_chunk5646

lemma complete_chunk5647 : ∀ i : Fin 200, Compatible (1129400 + i.val) →
    (table.lookup (1129400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5647 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1129400 1129600 :=
  FiniteIntervals.of_fin 1129400 200 complete_chunk5647

lemma complete_chunk5648 : ∀ i : Fin 200, Compatible (1129600 + i.val) →
    (table.lookup (1129600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5648 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1129600 1129800 :=
  FiniteIntervals.of_fin 1129600 200 complete_chunk5648

lemma complete_chunk5649 : ∀ i : Fin 200, Compatible (1129800 + i.val) →
    (table.lookup (1129800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5649 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1129800 1130000 :=
  FiniteIntervals.of_fin 1129800 200 complete_chunk5649

#print axioms interval_chunk5640
end Erdos184Work.PureFiveFilter4
