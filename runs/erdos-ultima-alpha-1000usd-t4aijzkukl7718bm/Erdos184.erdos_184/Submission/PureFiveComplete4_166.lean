import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1660 : ∀ i : Fin 200, Compatible (332000 + i.val) →
    (table.lookup (332000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1660 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 332000 332200 :=
  FiniteIntervals.of_fin 332000 200 complete_chunk1660

lemma complete_chunk1661 : ∀ i : Fin 200, Compatible (332200 + i.val) →
    (table.lookup (332200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1661 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 332200 332400 :=
  FiniteIntervals.of_fin 332200 200 complete_chunk1661

lemma complete_chunk1662 : ∀ i : Fin 200, Compatible (332400 + i.val) →
    (table.lookup (332400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1662 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 332400 332600 :=
  FiniteIntervals.of_fin 332400 200 complete_chunk1662

lemma complete_chunk1663 : ∀ i : Fin 200, Compatible (332600 + i.val) →
    (table.lookup (332600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1663 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 332600 332800 :=
  FiniteIntervals.of_fin 332600 200 complete_chunk1663

lemma complete_chunk1664 : ∀ i : Fin 200, Compatible (332800 + i.val) →
    (table.lookup (332800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1664 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 332800 333000 :=
  FiniteIntervals.of_fin 332800 200 complete_chunk1664

lemma complete_chunk1665 : ∀ i : Fin 200, Compatible (333000 + i.val) →
    (table.lookup (333000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1665 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 333000 333200 :=
  FiniteIntervals.of_fin 333000 200 complete_chunk1665

lemma complete_chunk1666 : ∀ i : Fin 200, Compatible (333200 + i.val) →
    (table.lookup (333200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1666 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 333200 333400 :=
  FiniteIntervals.of_fin 333200 200 complete_chunk1666

lemma complete_chunk1667 : ∀ i : Fin 200, Compatible (333400 + i.val) →
    (table.lookup (333400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1667 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 333400 333600 :=
  FiniteIntervals.of_fin 333400 200 complete_chunk1667

lemma complete_chunk1668 : ∀ i : Fin 200, Compatible (333600 + i.val) →
    (table.lookup (333600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1668 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 333600 333800 :=
  FiniteIntervals.of_fin 333600 200 complete_chunk1668

lemma complete_chunk1669 : ∀ i : Fin 200, Compatible (333800 + i.val) →
    (table.lookup (333800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1669 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 333800 334000 :=
  FiniteIntervals.of_fin 333800 200 complete_chunk1669

#print axioms interval_chunk1660
end Erdos184Work.PureFiveFilter4
