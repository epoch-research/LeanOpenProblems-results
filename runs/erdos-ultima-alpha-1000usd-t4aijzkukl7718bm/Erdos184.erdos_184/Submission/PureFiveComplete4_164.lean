import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1640 : ∀ i : Fin 200, Compatible (328000 + i.val) →
    (table.lookup (328000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1640 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 328000 328200 :=
  FiniteIntervals.of_fin 328000 200 complete_chunk1640

lemma complete_chunk1641 : ∀ i : Fin 200, Compatible (328200 + i.val) →
    (table.lookup (328200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1641 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 328200 328400 :=
  FiniteIntervals.of_fin 328200 200 complete_chunk1641

lemma complete_chunk1642 : ∀ i : Fin 200, Compatible (328400 + i.val) →
    (table.lookup (328400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1642 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 328400 328600 :=
  FiniteIntervals.of_fin 328400 200 complete_chunk1642

lemma complete_chunk1643 : ∀ i : Fin 200, Compatible (328600 + i.val) →
    (table.lookup (328600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1643 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 328600 328800 :=
  FiniteIntervals.of_fin 328600 200 complete_chunk1643

lemma complete_chunk1644 : ∀ i : Fin 200, Compatible (328800 + i.val) →
    (table.lookup (328800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1644 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 328800 329000 :=
  FiniteIntervals.of_fin 328800 200 complete_chunk1644

lemma complete_chunk1645 : ∀ i : Fin 200, Compatible (329000 + i.val) →
    (table.lookup (329000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1645 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 329000 329200 :=
  FiniteIntervals.of_fin 329000 200 complete_chunk1645

lemma complete_chunk1646 : ∀ i : Fin 200, Compatible (329200 + i.val) →
    (table.lookup (329200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1646 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 329200 329400 :=
  FiniteIntervals.of_fin 329200 200 complete_chunk1646

lemma complete_chunk1647 : ∀ i : Fin 200, Compatible (329400 + i.val) →
    (table.lookup (329400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1647 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 329400 329600 :=
  FiniteIntervals.of_fin 329400 200 complete_chunk1647

lemma complete_chunk1648 : ∀ i : Fin 200, Compatible (329600 + i.val) →
    (table.lookup (329600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1648 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 329600 329800 :=
  FiniteIntervals.of_fin 329600 200 complete_chunk1648

lemma complete_chunk1649 : ∀ i : Fin 200, Compatible (329800 + i.val) →
    (table.lookup (329800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1649 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 329800 330000 :=
  FiniteIntervals.of_fin 329800 200 complete_chunk1649

#print axioms interval_chunk1640
end Erdos184Work.PureFiveFilter4
