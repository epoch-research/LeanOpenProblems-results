import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3490 : ∀ i : Fin 200, Compatible (698000 + i.val) →
    (table.lookup (698000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3490 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 698000 698200 :=
  FiniteIntervals.of_fin 698000 200 complete_chunk3490

lemma complete_chunk3491 : ∀ i : Fin 200, Compatible (698200 + i.val) →
    (table.lookup (698200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3491 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 698200 698400 :=
  FiniteIntervals.of_fin 698200 200 complete_chunk3491

lemma complete_chunk3492 : ∀ i : Fin 200, Compatible (698400 + i.val) →
    (table.lookup (698400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3492 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 698400 698600 :=
  FiniteIntervals.of_fin 698400 200 complete_chunk3492

lemma complete_chunk3493 : ∀ i : Fin 200, Compatible (698600 + i.val) →
    (table.lookup (698600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3493 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 698600 698800 :=
  FiniteIntervals.of_fin 698600 200 complete_chunk3493

lemma complete_chunk3494 : ∀ i : Fin 200, Compatible (698800 + i.val) →
    (table.lookup (698800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3494 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 698800 699000 :=
  FiniteIntervals.of_fin 698800 200 complete_chunk3494

lemma complete_chunk3495 : ∀ i : Fin 200, Compatible (699000 + i.val) →
    (table.lookup (699000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3495 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 699000 699200 :=
  FiniteIntervals.of_fin 699000 200 complete_chunk3495

lemma complete_chunk3496 : ∀ i : Fin 200, Compatible (699200 + i.val) →
    (table.lookup (699200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3496 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 699200 699400 :=
  FiniteIntervals.of_fin 699200 200 complete_chunk3496

lemma complete_chunk3497 : ∀ i : Fin 200, Compatible (699400 + i.val) →
    (table.lookup (699400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3497 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 699400 699600 :=
  FiniteIntervals.of_fin 699400 200 complete_chunk3497

lemma complete_chunk3498 : ∀ i : Fin 200, Compatible (699600 + i.val) →
    (table.lookup (699600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3498 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 699600 699800 :=
  FiniteIntervals.of_fin 699600 200 complete_chunk3498

lemma complete_chunk3499 : ∀ i : Fin 200, Compatible (699800 + i.val) →
    (table.lookup (699800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3499 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 699800 700000 :=
  FiniteIntervals.of_fin 699800 200 complete_chunk3499

#print axioms interval_chunk3490
end Erdos184Work.PureFiveFilter4
