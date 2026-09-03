import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1480 : ∀ i : Fin 200, Compatible (296000 + i.val) →
    (table.lookup (296000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1480 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 296000 296200 :=
  FiniteIntervals.of_fin 296000 200 complete_chunk1480

lemma complete_chunk1481 : ∀ i : Fin 200, Compatible (296200 + i.val) →
    (table.lookup (296200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1481 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 296200 296400 :=
  FiniteIntervals.of_fin 296200 200 complete_chunk1481

lemma complete_chunk1482 : ∀ i : Fin 200, Compatible (296400 + i.val) →
    (table.lookup (296400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1482 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 296400 296600 :=
  FiniteIntervals.of_fin 296400 200 complete_chunk1482

lemma complete_chunk1483 : ∀ i : Fin 200, Compatible (296600 + i.val) →
    (table.lookup (296600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1483 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 296600 296800 :=
  FiniteIntervals.of_fin 296600 200 complete_chunk1483

lemma complete_chunk1484 : ∀ i : Fin 200, Compatible (296800 + i.val) →
    (table.lookup (296800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1484 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 296800 297000 :=
  FiniteIntervals.of_fin 296800 200 complete_chunk1484

lemma complete_chunk1485 : ∀ i : Fin 200, Compatible (297000 + i.val) →
    (table.lookup (297000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1485 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 297000 297200 :=
  FiniteIntervals.of_fin 297000 200 complete_chunk1485

lemma complete_chunk1486 : ∀ i : Fin 200, Compatible (297200 + i.val) →
    (table.lookup (297200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1486 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 297200 297400 :=
  FiniteIntervals.of_fin 297200 200 complete_chunk1486

lemma complete_chunk1487 : ∀ i : Fin 200, Compatible (297400 + i.val) →
    (table.lookup (297400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1487 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 297400 297600 :=
  FiniteIntervals.of_fin 297400 200 complete_chunk1487

lemma complete_chunk1488 : ∀ i : Fin 200, Compatible (297600 + i.val) →
    (table.lookup (297600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1488 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 297600 297800 :=
  FiniteIntervals.of_fin 297600 200 complete_chunk1488

lemma complete_chunk1489 : ∀ i : Fin 200, Compatible (297800 + i.val) →
    (table.lookup (297800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1489 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 297800 298000 :=
  FiniteIntervals.of_fin 297800 200 complete_chunk1489

#print axioms interval_chunk1480
end Erdos184Work.PureFiveFilter4
