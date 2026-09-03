import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1760 : ∀ i : Fin 200, Compatible (352000 + i.val) →
    (table.lookup (352000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1760 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 352000 352200 :=
  FiniteIntervals.of_fin 352000 200 complete_chunk1760

lemma complete_chunk1761 : ∀ i : Fin 200, Compatible (352200 + i.val) →
    (table.lookup (352200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1761 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 352200 352400 :=
  FiniteIntervals.of_fin 352200 200 complete_chunk1761

lemma complete_chunk1762 : ∀ i : Fin 200, Compatible (352400 + i.val) →
    (table.lookup (352400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1762 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 352400 352600 :=
  FiniteIntervals.of_fin 352400 200 complete_chunk1762

lemma complete_chunk1763 : ∀ i : Fin 200, Compatible (352600 + i.val) →
    (table.lookup (352600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1763 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 352600 352800 :=
  FiniteIntervals.of_fin 352600 200 complete_chunk1763

lemma complete_chunk1764 : ∀ i : Fin 200, Compatible (352800 + i.val) →
    (table.lookup (352800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1764 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 352800 353000 :=
  FiniteIntervals.of_fin 352800 200 complete_chunk1764

lemma complete_chunk1765 : ∀ i : Fin 200, Compatible (353000 + i.val) →
    (table.lookup (353000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1765 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 353000 353200 :=
  FiniteIntervals.of_fin 353000 200 complete_chunk1765

lemma complete_chunk1766 : ∀ i : Fin 200, Compatible (353200 + i.val) →
    (table.lookup (353200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1766 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 353200 353400 :=
  FiniteIntervals.of_fin 353200 200 complete_chunk1766

lemma complete_chunk1767 : ∀ i : Fin 200, Compatible (353400 + i.val) →
    (table.lookup (353400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1767 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 353400 353600 :=
  FiniteIntervals.of_fin 353400 200 complete_chunk1767

lemma complete_chunk1768 : ∀ i : Fin 200, Compatible (353600 + i.val) →
    (table.lookup (353600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1768 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 353600 353800 :=
  FiniteIntervals.of_fin 353600 200 complete_chunk1768

lemma complete_chunk1769 : ∀ i : Fin 200, Compatible (353800 + i.val) →
    (table.lookup (353800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1769 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 353800 354000 :=
  FiniteIntervals.of_fin 353800 200 complete_chunk1769

#print axioms interval_chunk1760
end Erdos184Work.PureFiveFilter4
