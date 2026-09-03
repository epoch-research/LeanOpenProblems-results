import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2470 : ∀ i : Fin 200, Compatible (494000 + i.val) →
    (table.lookup (494000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2470 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 494000 494200 :=
  FiniteIntervals.of_fin 494000 200 complete_chunk2470

lemma complete_chunk2471 : ∀ i : Fin 200, Compatible (494200 + i.val) →
    (table.lookup (494200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2471 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 494200 494400 :=
  FiniteIntervals.of_fin 494200 200 complete_chunk2471

lemma complete_chunk2472 : ∀ i : Fin 200, Compatible (494400 + i.val) →
    (table.lookup (494400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2472 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 494400 494600 :=
  FiniteIntervals.of_fin 494400 200 complete_chunk2472

lemma complete_chunk2473 : ∀ i : Fin 200, Compatible (494600 + i.val) →
    (table.lookup (494600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2473 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 494600 494800 :=
  FiniteIntervals.of_fin 494600 200 complete_chunk2473

lemma complete_chunk2474 : ∀ i : Fin 200, Compatible (494800 + i.val) →
    (table.lookup (494800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2474 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 494800 495000 :=
  FiniteIntervals.of_fin 494800 200 complete_chunk2474

lemma complete_chunk2475 : ∀ i : Fin 200, Compatible (495000 + i.val) →
    (table.lookup (495000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2475 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 495000 495200 :=
  FiniteIntervals.of_fin 495000 200 complete_chunk2475

lemma complete_chunk2476 : ∀ i : Fin 200, Compatible (495200 + i.val) →
    (table.lookup (495200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2476 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 495200 495400 :=
  FiniteIntervals.of_fin 495200 200 complete_chunk2476

lemma complete_chunk2477 : ∀ i : Fin 200, Compatible (495400 + i.val) →
    (table.lookup (495400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2477 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 495400 495600 :=
  FiniteIntervals.of_fin 495400 200 complete_chunk2477

lemma complete_chunk2478 : ∀ i : Fin 200, Compatible (495600 + i.val) →
    (table.lookup (495600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2478 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 495600 495800 :=
  FiniteIntervals.of_fin 495600 200 complete_chunk2478

lemma complete_chunk2479 : ∀ i : Fin 200, Compatible (495800 + i.val) →
    (table.lookup (495800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2479 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 495800 496000 :=
  FiniteIntervals.of_fin 495800 200 complete_chunk2479

#print axioms interval_chunk2470
end Erdos184Work.PureFiveFilter4
