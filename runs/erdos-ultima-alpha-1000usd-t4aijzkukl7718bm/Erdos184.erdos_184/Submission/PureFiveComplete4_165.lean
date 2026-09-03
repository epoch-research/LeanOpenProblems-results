import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1650 : ∀ i : Fin 200, Compatible (330000 + i.val) →
    (table.lookup (330000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1650 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 330000 330200 :=
  FiniteIntervals.of_fin 330000 200 complete_chunk1650

lemma complete_chunk1651 : ∀ i : Fin 200, Compatible (330200 + i.val) →
    (table.lookup (330200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1651 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 330200 330400 :=
  FiniteIntervals.of_fin 330200 200 complete_chunk1651

lemma complete_chunk1652 : ∀ i : Fin 200, Compatible (330400 + i.val) →
    (table.lookup (330400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1652 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 330400 330600 :=
  FiniteIntervals.of_fin 330400 200 complete_chunk1652

lemma complete_chunk1653 : ∀ i : Fin 200, Compatible (330600 + i.val) →
    (table.lookup (330600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1653 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 330600 330800 :=
  FiniteIntervals.of_fin 330600 200 complete_chunk1653

lemma complete_chunk1654 : ∀ i : Fin 200, Compatible (330800 + i.val) →
    (table.lookup (330800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1654 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 330800 331000 :=
  FiniteIntervals.of_fin 330800 200 complete_chunk1654

lemma complete_chunk1655 : ∀ i : Fin 200, Compatible (331000 + i.val) →
    (table.lookup (331000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1655 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 331000 331200 :=
  FiniteIntervals.of_fin 331000 200 complete_chunk1655

lemma complete_chunk1656 : ∀ i : Fin 200, Compatible (331200 + i.val) →
    (table.lookup (331200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1656 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 331200 331400 :=
  FiniteIntervals.of_fin 331200 200 complete_chunk1656

lemma complete_chunk1657 : ∀ i : Fin 200, Compatible (331400 + i.val) →
    (table.lookup (331400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1657 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 331400 331600 :=
  FiniteIntervals.of_fin 331400 200 complete_chunk1657

lemma complete_chunk1658 : ∀ i : Fin 200, Compatible (331600 + i.val) →
    (table.lookup (331600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1658 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 331600 331800 :=
  FiniteIntervals.of_fin 331600 200 complete_chunk1658

lemma complete_chunk1659 : ∀ i : Fin 200, Compatible (331800 + i.val) →
    (table.lookup (331800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1659 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 331800 332000 :=
  FiniteIntervals.of_fin 331800 200 complete_chunk1659

#print axioms interval_chunk1650
end Erdos184Work.PureFiveFilter4
