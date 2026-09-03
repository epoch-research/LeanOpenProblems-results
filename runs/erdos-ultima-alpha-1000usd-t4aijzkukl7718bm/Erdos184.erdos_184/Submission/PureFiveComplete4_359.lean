import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3590 : ∀ i : Fin 200, Compatible (718000 + i.val) →
    (table.lookup (718000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3590 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 718000 718200 :=
  FiniteIntervals.of_fin 718000 200 complete_chunk3590

lemma complete_chunk3591 : ∀ i : Fin 200, Compatible (718200 + i.val) →
    (table.lookup (718200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3591 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 718200 718400 :=
  FiniteIntervals.of_fin 718200 200 complete_chunk3591

lemma complete_chunk3592 : ∀ i : Fin 200, Compatible (718400 + i.val) →
    (table.lookup (718400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3592 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 718400 718600 :=
  FiniteIntervals.of_fin 718400 200 complete_chunk3592

lemma complete_chunk3593 : ∀ i : Fin 200, Compatible (718600 + i.val) →
    (table.lookup (718600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3593 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 718600 718800 :=
  FiniteIntervals.of_fin 718600 200 complete_chunk3593

lemma complete_chunk3594 : ∀ i : Fin 200, Compatible (718800 + i.val) →
    (table.lookup (718800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3594 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 718800 719000 :=
  FiniteIntervals.of_fin 718800 200 complete_chunk3594

lemma complete_chunk3595 : ∀ i : Fin 200, Compatible (719000 + i.val) →
    (table.lookup (719000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3595 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 719000 719200 :=
  FiniteIntervals.of_fin 719000 200 complete_chunk3595

lemma complete_chunk3596 : ∀ i : Fin 200, Compatible (719200 + i.val) →
    (table.lookup (719200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3596 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 719200 719400 :=
  FiniteIntervals.of_fin 719200 200 complete_chunk3596

lemma complete_chunk3597 : ∀ i : Fin 200, Compatible (719400 + i.val) →
    (table.lookup (719400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3597 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 719400 719600 :=
  FiniteIntervals.of_fin 719400 200 complete_chunk3597

lemma complete_chunk3598 : ∀ i : Fin 200, Compatible (719600 + i.val) →
    (table.lookup (719600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3598 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 719600 719800 :=
  FiniteIntervals.of_fin 719600 200 complete_chunk3598

lemma complete_chunk3599 : ∀ i : Fin 200, Compatible (719800 + i.val) →
    (table.lookup (719800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3599 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 719800 720000 :=
  FiniteIntervals.of_fin 719800 200 complete_chunk3599

#print axioms interval_chunk3590
end Erdos184Work.PureFiveFilter4
