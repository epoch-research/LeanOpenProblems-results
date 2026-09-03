import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3570 : ∀ i : Fin 200, Compatible (714000 + i.val) →
    (table.lookup (714000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3570 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 714000 714200 :=
  FiniteIntervals.of_fin 714000 200 complete_chunk3570

lemma complete_chunk3571 : ∀ i : Fin 200, Compatible (714200 + i.val) →
    (table.lookup (714200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3571 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 714200 714400 :=
  FiniteIntervals.of_fin 714200 200 complete_chunk3571

lemma complete_chunk3572 : ∀ i : Fin 200, Compatible (714400 + i.val) →
    (table.lookup (714400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3572 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 714400 714600 :=
  FiniteIntervals.of_fin 714400 200 complete_chunk3572

lemma complete_chunk3573 : ∀ i : Fin 200, Compatible (714600 + i.val) →
    (table.lookup (714600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3573 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 714600 714800 :=
  FiniteIntervals.of_fin 714600 200 complete_chunk3573

lemma complete_chunk3574 : ∀ i : Fin 200, Compatible (714800 + i.val) →
    (table.lookup (714800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3574 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 714800 715000 :=
  FiniteIntervals.of_fin 714800 200 complete_chunk3574

lemma complete_chunk3575 : ∀ i : Fin 200, Compatible (715000 + i.val) →
    (table.lookup (715000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3575 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 715000 715200 :=
  FiniteIntervals.of_fin 715000 200 complete_chunk3575

lemma complete_chunk3576 : ∀ i : Fin 200, Compatible (715200 + i.val) →
    (table.lookup (715200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3576 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 715200 715400 :=
  FiniteIntervals.of_fin 715200 200 complete_chunk3576

lemma complete_chunk3577 : ∀ i : Fin 200, Compatible (715400 + i.val) →
    (table.lookup (715400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3577 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 715400 715600 :=
  FiniteIntervals.of_fin 715400 200 complete_chunk3577

lemma complete_chunk3578 : ∀ i : Fin 200, Compatible (715600 + i.val) →
    (table.lookup (715600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3578 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 715600 715800 :=
  FiniteIntervals.of_fin 715600 200 complete_chunk3578

lemma complete_chunk3579 : ∀ i : Fin 200, Compatible (715800 + i.val) →
    (table.lookup (715800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3579 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 715800 716000 :=
  FiniteIntervals.of_fin 715800 200 complete_chunk3579

#print axioms interval_chunk3570
end Erdos184Work.PureFiveFilter4
