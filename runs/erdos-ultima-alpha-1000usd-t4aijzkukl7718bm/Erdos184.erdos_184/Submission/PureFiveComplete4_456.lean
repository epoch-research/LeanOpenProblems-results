import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4560 : ∀ i : Fin 200, Compatible (912000 + i.val) →
    (table.lookup (912000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4560 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 912000 912200 :=
  FiniteIntervals.of_fin 912000 200 complete_chunk4560

lemma complete_chunk4561 : ∀ i : Fin 200, Compatible (912200 + i.val) →
    (table.lookup (912200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4561 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 912200 912400 :=
  FiniteIntervals.of_fin 912200 200 complete_chunk4561

lemma complete_chunk4562 : ∀ i : Fin 200, Compatible (912400 + i.val) →
    (table.lookup (912400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4562 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 912400 912600 :=
  FiniteIntervals.of_fin 912400 200 complete_chunk4562

lemma complete_chunk4563 : ∀ i : Fin 200, Compatible (912600 + i.val) →
    (table.lookup (912600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4563 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 912600 912800 :=
  FiniteIntervals.of_fin 912600 200 complete_chunk4563

lemma complete_chunk4564 : ∀ i : Fin 200, Compatible (912800 + i.val) →
    (table.lookup (912800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4564 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 912800 913000 :=
  FiniteIntervals.of_fin 912800 200 complete_chunk4564

lemma complete_chunk4565 : ∀ i : Fin 200, Compatible (913000 + i.val) →
    (table.lookup (913000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4565 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 913000 913200 :=
  FiniteIntervals.of_fin 913000 200 complete_chunk4565

lemma complete_chunk4566 : ∀ i : Fin 200, Compatible (913200 + i.val) →
    (table.lookup (913200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4566 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 913200 913400 :=
  FiniteIntervals.of_fin 913200 200 complete_chunk4566

lemma complete_chunk4567 : ∀ i : Fin 200, Compatible (913400 + i.val) →
    (table.lookup (913400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4567 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 913400 913600 :=
  FiniteIntervals.of_fin 913400 200 complete_chunk4567

lemma complete_chunk4568 : ∀ i : Fin 200, Compatible (913600 + i.val) →
    (table.lookup (913600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4568 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 913600 913800 :=
  FiniteIntervals.of_fin 913600 200 complete_chunk4568

lemma complete_chunk4569 : ∀ i : Fin 200, Compatible (913800 + i.val) →
    (table.lookup (913800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4569 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 913800 914000 :=
  FiniteIntervals.of_fin 913800 200 complete_chunk4569

#print axioms interval_chunk4560
end Erdos184Work.PureFiveFilter4
