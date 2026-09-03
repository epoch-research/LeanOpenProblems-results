import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2800 : ∀ i : Fin 200, Compatible (560000 + i.val) →
    (table.lookup (560000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2800 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 560000 560200 :=
  FiniteIntervals.of_fin 560000 200 complete_chunk2800

lemma complete_chunk2801 : ∀ i : Fin 200, Compatible (560200 + i.val) →
    (table.lookup (560200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2801 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 560200 560400 :=
  FiniteIntervals.of_fin 560200 200 complete_chunk2801

lemma complete_chunk2802 : ∀ i : Fin 200, Compatible (560400 + i.val) →
    (table.lookup (560400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2802 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 560400 560600 :=
  FiniteIntervals.of_fin 560400 200 complete_chunk2802

lemma complete_chunk2803 : ∀ i : Fin 200, Compatible (560600 + i.val) →
    (table.lookup (560600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2803 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 560600 560800 :=
  FiniteIntervals.of_fin 560600 200 complete_chunk2803

lemma complete_chunk2804 : ∀ i : Fin 200, Compatible (560800 + i.val) →
    (table.lookup (560800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2804 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 560800 561000 :=
  FiniteIntervals.of_fin 560800 200 complete_chunk2804

lemma complete_chunk2805 : ∀ i : Fin 200, Compatible (561000 + i.val) →
    (table.lookup (561000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2805 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 561000 561200 :=
  FiniteIntervals.of_fin 561000 200 complete_chunk2805

lemma complete_chunk2806 : ∀ i : Fin 200, Compatible (561200 + i.val) →
    (table.lookup (561200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2806 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 561200 561400 :=
  FiniteIntervals.of_fin 561200 200 complete_chunk2806

lemma complete_chunk2807 : ∀ i : Fin 200, Compatible (561400 + i.val) →
    (table.lookup (561400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2807 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 561400 561600 :=
  FiniteIntervals.of_fin 561400 200 complete_chunk2807

lemma complete_chunk2808 : ∀ i : Fin 200, Compatible (561600 + i.val) →
    (table.lookup (561600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2808 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 561600 561800 :=
  FiniteIntervals.of_fin 561600 200 complete_chunk2808

lemma complete_chunk2809 : ∀ i : Fin 200, Compatible (561800 + i.val) →
    (table.lookup (561800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2809 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 561800 562000 :=
  FiniteIntervals.of_fin 561800 200 complete_chunk2809

#print axioms interval_chunk2800
end Erdos184Work.PureFiveFilter4
