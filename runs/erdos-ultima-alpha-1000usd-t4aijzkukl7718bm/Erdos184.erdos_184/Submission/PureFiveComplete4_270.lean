import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2700 : ∀ i : Fin 200, Compatible (540000 + i.val) →
    (table.lookup (540000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2700 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 540000 540200 :=
  FiniteIntervals.of_fin 540000 200 complete_chunk2700

lemma complete_chunk2701 : ∀ i : Fin 200, Compatible (540200 + i.val) →
    (table.lookup (540200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2701 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 540200 540400 :=
  FiniteIntervals.of_fin 540200 200 complete_chunk2701

lemma complete_chunk2702 : ∀ i : Fin 200, Compatible (540400 + i.val) →
    (table.lookup (540400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2702 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 540400 540600 :=
  FiniteIntervals.of_fin 540400 200 complete_chunk2702

lemma complete_chunk2703 : ∀ i : Fin 200, Compatible (540600 + i.val) →
    (table.lookup (540600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2703 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 540600 540800 :=
  FiniteIntervals.of_fin 540600 200 complete_chunk2703

lemma complete_chunk2704 : ∀ i : Fin 200, Compatible (540800 + i.val) →
    (table.lookup (540800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2704 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 540800 541000 :=
  FiniteIntervals.of_fin 540800 200 complete_chunk2704

lemma complete_chunk2705 : ∀ i : Fin 200, Compatible (541000 + i.val) →
    (table.lookup (541000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2705 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 541000 541200 :=
  FiniteIntervals.of_fin 541000 200 complete_chunk2705

lemma complete_chunk2706 : ∀ i : Fin 200, Compatible (541200 + i.val) →
    (table.lookup (541200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2706 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 541200 541400 :=
  FiniteIntervals.of_fin 541200 200 complete_chunk2706

lemma complete_chunk2707 : ∀ i : Fin 200, Compatible (541400 + i.val) →
    (table.lookup (541400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2707 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 541400 541600 :=
  FiniteIntervals.of_fin 541400 200 complete_chunk2707

lemma complete_chunk2708 : ∀ i : Fin 200, Compatible (541600 + i.val) →
    (table.lookup (541600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2708 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 541600 541800 :=
  FiniteIntervals.of_fin 541600 200 complete_chunk2708

lemma complete_chunk2709 : ∀ i : Fin 200, Compatible (541800 + i.val) →
    (table.lookup (541800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2709 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 541800 542000 :=
  FiniteIntervals.of_fin 541800 200 complete_chunk2709

#print axioms interval_chunk2700
end Erdos184Work.PureFiveFilter4
