import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1800 : ∀ i : Fin 200, Compatible (360000 + i.val) →
    (table.lookup (360000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1800 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 360000 360200 :=
  FiniteIntervals.of_fin 360000 200 complete_chunk1800

lemma complete_chunk1801 : ∀ i : Fin 200, Compatible (360200 + i.val) →
    (table.lookup (360200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1801 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 360200 360400 :=
  FiniteIntervals.of_fin 360200 200 complete_chunk1801

lemma complete_chunk1802 : ∀ i : Fin 200, Compatible (360400 + i.val) →
    (table.lookup (360400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1802 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 360400 360600 :=
  FiniteIntervals.of_fin 360400 200 complete_chunk1802

lemma complete_chunk1803 : ∀ i : Fin 200, Compatible (360600 + i.val) →
    (table.lookup (360600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1803 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 360600 360800 :=
  FiniteIntervals.of_fin 360600 200 complete_chunk1803

lemma complete_chunk1804 : ∀ i : Fin 200, Compatible (360800 + i.val) →
    (table.lookup (360800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1804 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 360800 361000 :=
  FiniteIntervals.of_fin 360800 200 complete_chunk1804

lemma complete_chunk1805 : ∀ i : Fin 200, Compatible (361000 + i.val) →
    (table.lookup (361000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1805 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 361000 361200 :=
  FiniteIntervals.of_fin 361000 200 complete_chunk1805

lemma complete_chunk1806 : ∀ i : Fin 200, Compatible (361200 + i.val) →
    (table.lookup (361200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1806 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 361200 361400 :=
  FiniteIntervals.of_fin 361200 200 complete_chunk1806

lemma complete_chunk1807 : ∀ i : Fin 200, Compatible (361400 + i.val) →
    (table.lookup (361400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1807 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 361400 361600 :=
  FiniteIntervals.of_fin 361400 200 complete_chunk1807

lemma complete_chunk1808 : ∀ i : Fin 200, Compatible (361600 + i.val) →
    (table.lookup (361600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1808 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 361600 361800 :=
  FiniteIntervals.of_fin 361600 200 complete_chunk1808

lemma complete_chunk1809 : ∀ i : Fin 200, Compatible (361800 + i.val) →
    (table.lookup (361800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1809 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 361800 362000 :=
  FiniteIntervals.of_fin 361800 200 complete_chunk1809

#print axioms interval_chunk1800
end Erdos184Work.PureFiveFilter4
