import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1390 : ∀ i : Fin 200, Compatible (278000 + i.val) →
    (table.lookup (278000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1390 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 278000 278200 :=
  FiniteIntervals.of_fin 278000 200 complete_chunk1390

lemma complete_chunk1391 : ∀ i : Fin 200, Compatible (278200 + i.val) →
    (table.lookup (278200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1391 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 278200 278400 :=
  FiniteIntervals.of_fin 278200 200 complete_chunk1391

lemma complete_chunk1392 : ∀ i : Fin 200, Compatible (278400 + i.val) →
    (table.lookup (278400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1392 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 278400 278600 :=
  FiniteIntervals.of_fin 278400 200 complete_chunk1392

lemma complete_chunk1393 : ∀ i : Fin 200, Compatible (278600 + i.val) →
    (table.lookup (278600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1393 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 278600 278800 :=
  FiniteIntervals.of_fin 278600 200 complete_chunk1393

lemma complete_chunk1394 : ∀ i : Fin 200, Compatible (278800 + i.val) →
    (table.lookup (278800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1394 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 278800 279000 :=
  FiniteIntervals.of_fin 278800 200 complete_chunk1394

lemma complete_chunk1395 : ∀ i : Fin 200, Compatible (279000 + i.val) →
    (table.lookup (279000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1395 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 279000 279200 :=
  FiniteIntervals.of_fin 279000 200 complete_chunk1395

lemma complete_chunk1396 : ∀ i : Fin 200, Compatible (279200 + i.val) →
    (table.lookup (279200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1396 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 279200 279400 :=
  FiniteIntervals.of_fin 279200 200 complete_chunk1396

lemma complete_chunk1397 : ∀ i : Fin 200, Compatible (279400 + i.val) →
    (table.lookup (279400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1397 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 279400 279600 :=
  FiniteIntervals.of_fin 279400 200 complete_chunk1397

lemma complete_chunk1398 : ∀ i : Fin 200, Compatible (279600 + i.val) →
    (table.lookup (279600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1398 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 279600 279800 :=
  FiniteIntervals.of_fin 279600 200 complete_chunk1398

lemma complete_chunk1399 : ∀ i : Fin 200, Compatible (279800 + i.val) →
    (table.lookup (279800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1399 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 279800 280000 :=
  FiniteIntervals.of_fin 279800 200 complete_chunk1399

#print axioms interval_chunk1390
end Erdos184Work.PureFiveFilter4
