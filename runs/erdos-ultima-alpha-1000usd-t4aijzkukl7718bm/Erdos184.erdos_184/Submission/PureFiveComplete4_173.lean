import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1730 : ∀ i : Fin 200, Compatible (346000 + i.val) →
    (table.lookup (346000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1730 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 346000 346200 :=
  FiniteIntervals.of_fin 346000 200 complete_chunk1730

lemma complete_chunk1731 : ∀ i : Fin 200, Compatible (346200 + i.val) →
    (table.lookup (346200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1731 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 346200 346400 :=
  FiniteIntervals.of_fin 346200 200 complete_chunk1731

lemma complete_chunk1732 : ∀ i : Fin 200, Compatible (346400 + i.val) →
    (table.lookup (346400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1732 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 346400 346600 :=
  FiniteIntervals.of_fin 346400 200 complete_chunk1732

lemma complete_chunk1733 : ∀ i : Fin 200, Compatible (346600 + i.val) →
    (table.lookup (346600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1733 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 346600 346800 :=
  FiniteIntervals.of_fin 346600 200 complete_chunk1733

lemma complete_chunk1734 : ∀ i : Fin 200, Compatible (346800 + i.val) →
    (table.lookup (346800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1734 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 346800 347000 :=
  FiniteIntervals.of_fin 346800 200 complete_chunk1734

lemma complete_chunk1735 : ∀ i : Fin 200, Compatible (347000 + i.val) →
    (table.lookup (347000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1735 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 347000 347200 :=
  FiniteIntervals.of_fin 347000 200 complete_chunk1735

lemma complete_chunk1736 : ∀ i : Fin 200, Compatible (347200 + i.val) →
    (table.lookup (347200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1736 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 347200 347400 :=
  FiniteIntervals.of_fin 347200 200 complete_chunk1736

lemma complete_chunk1737 : ∀ i : Fin 200, Compatible (347400 + i.val) →
    (table.lookup (347400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1737 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 347400 347600 :=
  FiniteIntervals.of_fin 347400 200 complete_chunk1737

lemma complete_chunk1738 : ∀ i : Fin 200, Compatible (347600 + i.val) →
    (table.lookup (347600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1738 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 347600 347800 :=
  FiniteIntervals.of_fin 347600 200 complete_chunk1738

lemma complete_chunk1739 : ∀ i : Fin 200, Compatible (347800 + i.val) →
    (table.lookup (347800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1739 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 347800 348000 :=
  FiniteIntervals.of_fin 347800 200 complete_chunk1739

#print axioms interval_chunk1730
end Erdos184Work.PureFiveFilter4
