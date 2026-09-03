import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1720 : ∀ i : Fin 200, Compatible (344000 + i.val) →
    (table.lookup (344000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1720 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 344000 344200 :=
  FiniteIntervals.of_fin 344000 200 complete_chunk1720

lemma complete_chunk1721 : ∀ i : Fin 200, Compatible (344200 + i.val) →
    (table.lookup (344200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1721 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 344200 344400 :=
  FiniteIntervals.of_fin 344200 200 complete_chunk1721

lemma complete_chunk1722 : ∀ i : Fin 200, Compatible (344400 + i.val) →
    (table.lookup (344400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1722 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 344400 344600 :=
  FiniteIntervals.of_fin 344400 200 complete_chunk1722

lemma complete_chunk1723 : ∀ i : Fin 200, Compatible (344600 + i.val) →
    (table.lookup (344600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1723 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 344600 344800 :=
  FiniteIntervals.of_fin 344600 200 complete_chunk1723

lemma complete_chunk1724 : ∀ i : Fin 200, Compatible (344800 + i.val) →
    (table.lookup (344800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1724 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 344800 345000 :=
  FiniteIntervals.of_fin 344800 200 complete_chunk1724

lemma complete_chunk1725 : ∀ i : Fin 200, Compatible (345000 + i.val) →
    (table.lookup (345000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1725 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 345000 345200 :=
  FiniteIntervals.of_fin 345000 200 complete_chunk1725

lemma complete_chunk1726 : ∀ i : Fin 200, Compatible (345200 + i.val) →
    (table.lookup (345200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1726 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 345200 345400 :=
  FiniteIntervals.of_fin 345200 200 complete_chunk1726

lemma complete_chunk1727 : ∀ i : Fin 200, Compatible (345400 + i.val) →
    (table.lookup (345400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1727 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 345400 345600 :=
  FiniteIntervals.of_fin 345400 200 complete_chunk1727

lemma complete_chunk1728 : ∀ i : Fin 200, Compatible (345600 + i.val) →
    (table.lookup (345600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1728 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 345600 345800 :=
  FiniteIntervals.of_fin 345600 200 complete_chunk1728

lemma complete_chunk1729 : ∀ i : Fin 200, Compatible (345800 + i.val) →
    (table.lookup (345800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1729 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 345800 346000 :=
  FiniteIntervals.of_fin 345800 200 complete_chunk1729

#print axioms interval_chunk1720
end Erdos184Work.PureFiveFilter4
