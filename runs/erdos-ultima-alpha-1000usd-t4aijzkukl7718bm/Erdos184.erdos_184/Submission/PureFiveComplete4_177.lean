import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1770 : ∀ i : Fin 200, Compatible (354000 + i.val) →
    (table.lookup (354000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1770 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 354000 354200 :=
  FiniteIntervals.of_fin 354000 200 complete_chunk1770

lemma complete_chunk1771 : ∀ i : Fin 200, Compatible (354200 + i.val) →
    (table.lookup (354200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1771 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 354200 354400 :=
  FiniteIntervals.of_fin 354200 200 complete_chunk1771

lemma complete_chunk1772 : ∀ i : Fin 200, Compatible (354400 + i.val) →
    (table.lookup (354400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1772 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 354400 354600 :=
  FiniteIntervals.of_fin 354400 200 complete_chunk1772

lemma complete_chunk1773 : ∀ i : Fin 200, Compatible (354600 + i.val) →
    (table.lookup (354600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1773 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 354600 354800 :=
  FiniteIntervals.of_fin 354600 200 complete_chunk1773

lemma complete_chunk1774 : ∀ i : Fin 200, Compatible (354800 + i.val) →
    (table.lookup (354800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1774 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 354800 355000 :=
  FiniteIntervals.of_fin 354800 200 complete_chunk1774

lemma complete_chunk1775 : ∀ i : Fin 200, Compatible (355000 + i.val) →
    (table.lookup (355000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1775 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 355000 355200 :=
  FiniteIntervals.of_fin 355000 200 complete_chunk1775

lemma complete_chunk1776 : ∀ i : Fin 200, Compatible (355200 + i.val) →
    (table.lookup (355200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1776 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 355200 355400 :=
  FiniteIntervals.of_fin 355200 200 complete_chunk1776

lemma complete_chunk1777 : ∀ i : Fin 200, Compatible (355400 + i.val) →
    (table.lookup (355400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1777 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 355400 355600 :=
  FiniteIntervals.of_fin 355400 200 complete_chunk1777

lemma complete_chunk1778 : ∀ i : Fin 200, Compatible (355600 + i.val) →
    (table.lookup (355600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1778 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 355600 355800 :=
  FiniteIntervals.of_fin 355600 200 complete_chunk1778

lemma complete_chunk1779 : ∀ i : Fin 200, Compatible (355800 + i.val) →
    (table.lookup (355800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1779 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 355800 356000 :=
  FiniteIntervals.of_fin 355800 200 complete_chunk1779

#print axioms interval_chunk1770
end Erdos184Work.PureFiveFilter4
