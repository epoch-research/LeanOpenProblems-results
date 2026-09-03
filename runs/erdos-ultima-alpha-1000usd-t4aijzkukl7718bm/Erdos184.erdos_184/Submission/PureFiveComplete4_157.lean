import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1570 : ∀ i : Fin 200, Compatible (314000 + i.val) →
    (table.lookup (314000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1570 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 314000 314200 :=
  FiniteIntervals.of_fin 314000 200 complete_chunk1570

lemma complete_chunk1571 : ∀ i : Fin 200, Compatible (314200 + i.val) →
    (table.lookup (314200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1571 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 314200 314400 :=
  FiniteIntervals.of_fin 314200 200 complete_chunk1571

lemma complete_chunk1572 : ∀ i : Fin 200, Compatible (314400 + i.val) →
    (table.lookup (314400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1572 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 314400 314600 :=
  FiniteIntervals.of_fin 314400 200 complete_chunk1572

lemma complete_chunk1573 : ∀ i : Fin 200, Compatible (314600 + i.val) →
    (table.lookup (314600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1573 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 314600 314800 :=
  FiniteIntervals.of_fin 314600 200 complete_chunk1573

lemma complete_chunk1574 : ∀ i : Fin 200, Compatible (314800 + i.val) →
    (table.lookup (314800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1574 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 314800 315000 :=
  FiniteIntervals.of_fin 314800 200 complete_chunk1574

lemma complete_chunk1575 : ∀ i : Fin 200, Compatible (315000 + i.val) →
    (table.lookup (315000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1575 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 315000 315200 :=
  FiniteIntervals.of_fin 315000 200 complete_chunk1575

lemma complete_chunk1576 : ∀ i : Fin 200, Compatible (315200 + i.val) →
    (table.lookup (315200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1576 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 315200 315400 :=
  FiniteIntervals.of_fin 315200 200 complete_chunk1576

lemma complete_chunk1577 : ∀ i : Fin 200, Compatible (315400 + i.val) →
    (table.lookup (315400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1577 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 315400 315600 :=
  FiniteIntervals.of_fin 315400 200 complete_chunk1577

lemma complete_chunk1578 : ∀ i : Fin 200, Compatible (315600 + i.val) →
    (table.lookup (315600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1578 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 315600 315800 :=
  FiniteIntervals.of_fin 315600 200 complete_chunk1578

lemma complete_chunk1579 : ∀ i : Fin 200, Compatible (315800 + i.val) →
    (table.lookup (315800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1579 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 315800 316000 :=
  FiniteIntervals.of_fin 315800 200 complete_chunk1579

#print axioms interval_chunk1570
end Erdos184Work.PureFiveFilter4
