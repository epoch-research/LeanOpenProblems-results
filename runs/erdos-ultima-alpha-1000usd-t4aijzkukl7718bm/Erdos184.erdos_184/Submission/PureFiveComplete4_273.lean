import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2730 : ∀ i : Fin 200, Compatible (546000 + i.val) →
    (table.lookup (546000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2730 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 546000 546200 :=
  FiniteIntervals.of_fin 546000 200 complete_chunk2730

lemma complete_chunk2731 : ∀ i : Fin 200, Compatible (546200 + i.val) →
    (table.lookup (546200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2731 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 546200 546400 :=
  FiniteIntervals.of_fin 546200 200 complete_chunk2731

lemma complete_chunk2732 : ∀ i : Fin 200, Compatible (546400 + i.val) →
    (table.lookup (546400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2732 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 546400 546600 :=
  FiniteIntervals.of_fin 546400 200 complete_chunk2732

lemma complete_chunk2733 : ∀ i : Fin 200, Compatible (546600 + i.val) →
    (table.lookup (546600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2733 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 546600 546800 :=
  FiniteIntervals.of_fin 546600 200 complete_chunk2733

lemma complete_chunk2734 : ∀ i : Fin 200, Compatible (546800 + i.val) →
    (table.lookup (546800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2734 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 546800 547000 :=
  FiniteIntervals.of_fin 546800 200 complete_chunk2734

lemma complete_chunk2735 : ∀ i : Fin 200, Compatible (547000 + i.val) →
    (table.lookup (547000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2735 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 547000 547200 :=
  FiniteIntervals.of_fin 547000 200 complete_chunk2735

lemma complete_chunk2736 : ∀ i : Fin 200, Compatible (547200 + i.val) →
    (table.lookup (547200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2736 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 547200 547400 :=
  FiniteIntervals.of_fin 547200 200 complete_chunk2736

lemma complete_chunk2737 : ∀ i : Fin 200, Compatible (547400 + i.val) →
    (table.lookup (547400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2737 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 547400 547600 :=
  FiniteIntervals.of_fin 547400 200 complete_chunk2737

lemma complete_chunk2738 : ∀ i : Fin 200, Compatible (547600 + i.val) →
    (table.lookup (547600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2738 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 547600 547800 :=
  FiniteIntervals.of_fin 547600 200 complete_chunk2738

lemma complete_chunk2739 : ∀ i : Fin 200, Compatible (547800 + i.val) →
    (table.lookup (547800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2739 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 547800 548000 :=
  FiniteIntervals.of_fin 547800 200 complete_chunk2739

#print axioms interval_chunk2730
end Erdos184Work.PureFiveFilter4
