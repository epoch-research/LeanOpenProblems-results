import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1490 : ∀ i : Fin 200, Compatible (298000 + i.val) →
    (table.lookup (298000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1490 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 298000 298200 :=
  FiniteIntervals.of_fin 298000 200 complete_chunk1490

lemma complete_chunk1491 : ∀ i : Fin 200, Compatible (298200 + i.val) →
    (table.lookup (298200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1491 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 298200 298400 :=
  FiniteIntervals.of_fin 298200 200 complete_chunk1491

lemma complete_chunk1492 : ∀ i : Fin 200, Compatible (298400 + i.val) →
    (table.lookup (298400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1492 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 298400 298600 :=
  FiniteIntervals.of_fin 298400 200 complete_chunk1492

lemma complete_chunk1493 : ∀ i : Fin 200, Compatible (298600 + i.val) →
    (table.lookup (298600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1493 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 298600 298800 :=
  FiniteIntervals.of_fin 298600 200 complete_chunk1493

lemma complete_chunk1494 : ∀ i : Fin 200, Compatible (298800 + i.val) →
    (table.lookup (298800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1494 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 298800 299000 :=
  FiniteIntervals.of_fin 298800 200 complete_chunk1494

lemma complete_chunk1495 : ∀ i : Fin 200, Compatible (299000 + i.val) →
    (table.lookup (299000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1495 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 299000 299200 :=
  FiniteIntervals.of_fin 299000 200 complete_chunk1495

lemma complete_chunk1496 : ∀ i : Fin 200, Compatible (299200 + i.val) →
    (table.lookup (299200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1496 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 299200 299400 :=
  FiniteIntervals.of_fin 299200 200 complete_chunk1496

lemma complete_chunk1497 : ∀ i : Fin 200, Compatible (299400 + i.val) →
    (table.lookup (299400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1497 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 299400 299600 :=
  FiniteIntervals.of_fin 299400 200 complete_chunk1497

lemma complete_chunk1498 : ∀ i : Fin 200, Compatible (299600 + i.val) →
    (table.lookup (299600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1498 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 299600 299800 :=
  FiniteIntervals.of_fin 299600 200 complete_chunk1498

lemma complete_chunk1499 : ∀ i : Fin 200, Compatible (299800 + i.val) →
    (table.lookup (299800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1499 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 299800 300000 :=
  FiniteIntervals.of_fin 299800 200 complete_chunk1499

#print axioms interval_chunk1490
end Erdos184Work.PureFiveFilter4
