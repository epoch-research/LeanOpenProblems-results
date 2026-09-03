import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2680 : ∀ i : Fin 200, Compatible (536000 + i.val) →
    (table.lookup (536000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2680 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 536000 536200 :=
  FiniteIntervals.of_fin 536000 200 complete_chunk2680

lemma complete_chunk2681 : ∀ i : Fin 200, Compatible (536200 + i.val) →
    (table.lookup (536200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2681 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 536200 536400 :=
  FiniteIntervals.of_fin 536200 200 complete_chunk2681

lemma complete_chunk2682 : ∀ i : Fin 200, Compatible (536400 + i.val) →
    (table.lookup (536400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2682 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 536400 536600 :=
  FiniteIntervals.of_fin 536400 200 complete_chunk2682

lemma complete_chunk2683 : ∀ i : Fin 200, Compatible (536600 + i.val) →
    (table.lookup (536600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2683 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 536600 536800 :=
  FiniteIntervals.of_fin 536600 200 complete_chunk2683

lemma complete_chunk2684 : ∀ i : Fin 200, Compatible (536800 + i.val) →
    (table.lookup (536800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2684 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 536800 537000 :=
  FiniteIntervals.of_fin 536800 200 complete_chunk2684

lemma complete_chunk2685 : ∀ i : Fin 200, Compatible (537000 + i.val) →
    (table.lookup (537000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2685 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 537000 537200 :=
  FiniteIntervals.of_fin 537000 200 complete_chunk2685

lemma complete_chunk2686 : ∀ i : Fin 200, Compatible (537200 + i.val) →
    (table.lookup (537200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2686 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 537200 537400 :=
  FiniteIntervals.of_fin 537200 200 complete_chunk2686

lemma complete_chunk2687 : ∀ i : Fin 200, Compatible (537400 + i.val) →
    (table.lookup (537400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2687 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 537400 537600 :=
  FiniteIntervals.of_fin 537400 200 complete_chunk2687

lemma complete_chunk2688 : ∀ i : Fin 200, Compatible (537600 + i.val) →
    (table.lookup (537600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2688 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 537600 537800 :=
  FiniteIntervals.of_fin 537600 200 complete_chunk2688

lemma complete_chunk2689 : ∀ i : Fin 200, Compatible (537800 + i.val) →
    (table.lookup (537800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2689 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 537800 538000 :=
  FiniteIntervals.of_fin 537800 200 complete_chunk2689

#print axioms interval_chunk2680
end Erdos184Work.PureFiveFilter4
