import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5650 : ∀ i : Fin 200, Compatible (1130000 + i.val) →
    (table.lookup (1130000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5650 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1130000 1130200 :=
  FiniteIntervals.of_fin 1130000 200 complete_chunk5650

lemma complete_chunk5651 : ∀ i : Fin 200, Compatible (1130200 + i.val) →
    (table.lookup (1130200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5651 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1130200 1130400 :=
  FiniteIntervals.of_fin 1130200 200 complete_chunk5651

lemma complete_chunk5652 : ∀ i : Fin 200, Compatible (1130400 + i.val) →
    (table.lookup (1130400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5652 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1130400 1130600 :=
  FiniteIntervals.of_fin 1130400 200 complete_chunk5652

lemma complete_chunk5653 : ∀ i : Fin 200, Compatible (1130600 + i.val) →
    (table.lookup (1130600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5653 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1130600 1130800 :=
  FiniteIntervals.of_fin 1130600 200 complete_chunk5653

lemma complete_chunk5654 : ∀ i : Fin 200, Compatible (1130800 + i.val) →
    (table.lookup (1130800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5654 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1130800 1131000 :=
  FiniteIntervals.of_fin 1130800 200 complete_chunk5654

lemma complete_chunk5655 : ∀ i : Fin 200, Compatible (1131000 + i.val) →
    (table.lookup (1131000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5655 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1131000 1131200 :=
  FiniteIntervals.of_fin 1131000 200 complete_chunk5655

lemma complete_chunk5656 : ∀ i : Fin 200, Compatible (1131200 + i.val) →
    (table.lookup (1131200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5656 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1131200 1131400 :=
  FiniteIntervals.of_fin 1131200 200 complete_chunk5656

lemma complete_chunk5657 : ∀ i : Fin 200, Compatible (1131400 + i.val) →
    (table.lookup (1131400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5657 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1131400 1131600 :=
  FiniteIntervals.of_fin 1131400 200 complete_chunk5657

lemma complete_chunk5658 : ∀ i : Fin 200, Compatible (1131600 + i.val) →
    (table.lookup (1131600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5658 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1131600 1131800 :=
  FiniteIntervals.of_fin 1131600 200 complete_chunk5658

lemma complete_chunk5659 : ∀ i : Fin 200, Compatible (1131800 + i.val) →
    (table.lookup (1131800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5659 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1131800 1132000 :=
  FiniteIntervals.of_fin 1131800 200 complete_chunk5659

#print axioms interval_chunk5650
end Erdos184Work.PureFiveFilter4
