import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1550 : ∀ i : Fin 200, Compatible (310000 + i.val) →
    (table.lookup (310000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1550 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 310000 310200 :=
  FiniteIntervals.of_fin 310000 200 complete_chunk1550

lemma complete_chunk1551 : ∀ i : Fin 200, Compatible (310200 + i.val) →
    (table.lookup (310200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1551 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 310200 310400 :=
  FiniteIntervals.of_fin 310200 200 complete_chunk1551

lemma complete_chunk1552 : ∀ i : Fin 200, Compatible (310400 + i.val) →
    (table.lookup (310400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1552 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 310400 310600 :=
  FiniteIntervals.of_fin 310400 200 complete_chunk1552

lemma complete_chunk1553 : ∀ i : Fin 200, Compatible (310600 + i.val) →
    (table.lookup (310600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1553 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 310600 310800 :=
  FiniteIntervals.of_fin 310600 200 complete_chunk1553

lemma complete_chunk1554 : ∀ i : Fin 200, Compatible (310800 + i.val) →
    (table.lookup (310800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1554 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 310800 311000 :=
  FiniteIntervals.of_fin 310800 200 complete_chunk1554

lemma complete_chunk1555 : ∀ i : Fin 200, Compatible (311000 + i.val) →
    (table.lookup (311000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1555 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 311000 311200 :=
  FiniteIntervals.of_fin 311000 200 complete_chunk1555

lemma complete_chunk1556 : ∀ i : Fin 200, Compatible (311200 + i.val) →
    (table.lookup (311200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1556 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 311200 311400 :=
  FiniteIntervals.of_fin 311200 200 complete_chunk1556

lemma complete_chunk1557 : ∀ i : Fin 200, Compatible (311400 + i.val) →
    (table.lookup (311400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1557 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 311400 311600 :=
  FiniteIntervals.of_fin 311400 200 complete_chunk1557

lemma complete_chunk1558 : ∀ i : Fin 200, Compatible (311600 + i.val) →
    (table.lookup (311600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1558 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 311600 311800 :=
  FiniteIntervals.of_fin 311600 200 complete_chunk1558

lemma complete_chunk1559 : ∀ i : Fin 200, Compatible (311800 + i.val) →
    (table.lookup (311800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1559 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 311800 312000 :=
  FiniteIntervals.of_fin 311800 200 complete_chunk1559

#print axioms interval_chunk1550
end Erdos184Work.PureFiveFilter4
