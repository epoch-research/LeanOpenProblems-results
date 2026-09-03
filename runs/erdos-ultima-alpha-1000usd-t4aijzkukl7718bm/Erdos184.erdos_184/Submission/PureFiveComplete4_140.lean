import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1400 : ∀ i : Fin 200, Compatible (280000 + i.val) →
    (table.lookup (280000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1400 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 280000 280200 :=
  FiniteIntervals.of_fin 280000 200 complete_chunk1400

lemma complete_chunk1401 : ∀ i : Fin 200, Compatible (280200 + i.val) →
    (table.lookup (280200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1401 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 280200 280400 :=
  FiniteIntervals.of_fin 280200 200 complete_chunk1401

lemma complete_chunk1402 : ∀ i : Fin 200, Compatible (280400 + i.val) →
    (table.lookup (280400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1402 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 280400 280600 :=
  FiniteIntervals.of_fin 280400 200 complete_chunk1402

lemma complete_chunk1403 : ∀ i : Fin 200, Compatible (280600 + i.val) →
    (table.lookup (280600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1403 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 280600 280800 :=
  FiniteIntervals.of_fin 280600 200 complete_chunk1403

lemma complete_chunk1404 : ∀ i : Fin 200, Compatible (280800 + i.val) →
    (table.lookup (280800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1404 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 280800 281000 :=
  FiniteIntervals.of_fin 280800 200 complete_chunk1404

lemma complete_chunk1405 : ∀ i : Fin 200, Compatible (281000 + i.val) →
    (table.lookup (281000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1405 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 281000 281200 :=
  FiniteIntervals.of_fin 281000 200 complete_chunk1405

lemma complete_chunk1406 : ∀ i : Fin 200, Compatible (281200 + i.val) →
    (table.lookup (281200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1406 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 281200 281400 :=
  FiniteIntervals.of_fin 281200 200 complete_chunk1406

lemma complete_chunk1407 : ∀ i : Fin 200, Compatible (281400 + i.val) →
    (table.lookup (281400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1407 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 281400 281600 :=
  FiniteIntervals.of_fin 281400 200 complete_chunk1407

lemma complete_chunk1408 : ∀ i : Fin 200, Compatible (281600 + i.val) →
    (table.lookup (281600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1408 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 281600 281800 :=
  FiniteIntervals.of_fin 281600 200 complete_chunk1408

lemma complete_chunk1409 : ∀ i : Fin 200, Compatible (281800 + i.val) →
    (table.lookup (281800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1409 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 281800 282000 :=
  FiniteIntervals.of_fin 281800 200 complete_chunk1409

#print axioms interval_chunk1400
end Erdos184Work.PureFiveFilter4
