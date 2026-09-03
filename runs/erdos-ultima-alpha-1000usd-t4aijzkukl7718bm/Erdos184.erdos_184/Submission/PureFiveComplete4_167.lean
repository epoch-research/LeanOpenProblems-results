import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1670 : ∀ i : Fin 200, Compatible (334000 + i.val) →
    (table.lookup (334000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1670 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 334000 334200 :=
  FiniteIntervals.of_fin 334000 200 complete_chunk1670

lemma complete_chunk1671 : ∀ i : Fin 200, Compatible (334200 + i.val) →
    (table.lookup (334200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1671 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 334200 334400 :=
  FiniteIntervals.of_fin 334200 200 complete_chunk1671

lemma complete_chunk1672 : ∀ i : Fin 200, Compatible (334400 + i.val) →
    (table.lookup (334400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1672 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 334400 334600 :=
  FiniteIntervals.of_fin 334400 200 complete_chunk1672

lemma complete_chunk1673 : ∀ i : Fin 200, Compatible (334600 + i.val) →
    (table.lookup (334600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1673 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 334600 334800 :=
  FiniteIntervals.of_fin 334600 200 complete_chunk1673

lemma complete_chunk1674 : ∀ i : Fin 200, Compatible (334800 + i.val) →
    (table.lookup (334800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1674 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 334800 335000 :=
  FiniteIntervals.of_fin 334800 200 complete_chunk1674

lemma complete_chunk1675 : ∀ i : Fin 200, Compatible (335000 + i.val) →
    (table.lookup (335000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1675 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 335000 335200 :=
  FiniteIntervals.of_fin 335000 200 complete_chunk1675

lemma complete_chunk1676 : ∀ i : Fin 200, Compatible (335200 + i.val) →
    (table.lookup (335200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1676 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 335200 335400 :=
  FiniteIntervals.of_fin 335200 200 complete_chunk1676

lemma complete_chunk1677 : ∀ i : Fin 200, Compatible (335400 + i.val) →
    (table.lookup (335400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1677 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 335400 335600 :=
  FiniteIntervals.of_fin 335400 200 complete_chunk1677

lemma complete_chunk1678 : ∀ i : Fin 200, Compatible (335600 + i.val) →
    (table.lookup (335600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1678 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 335600 335800 :=
  FiniteIntervals.of_fin 335600 200 complete_chunk1678

lemma complete_chunk1679 : ∀ i : Fin 200, Compatible (335800 + i.val) →
    (table.lookup (335800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1679 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 335800 336000 :=
  FiniteIntervals.of_fin 335800 200 complete_chunk1679

#print axioms interval_chunk1670
end Erdos184Work.PureFiveFilter4
