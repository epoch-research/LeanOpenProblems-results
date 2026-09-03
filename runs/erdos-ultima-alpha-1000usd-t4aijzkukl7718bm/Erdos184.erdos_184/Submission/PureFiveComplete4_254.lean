import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2540 : ∀ i : Fin 200, Compatible (508000 + i.val) →
    (table.lookup (508000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2540 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 508000 508200 :=
  FiniteIntervals.of_fin 508000 200 complete_chunk2540

lemma complete_chunk2541 : ∀ i : Fin 200, Compatible (508200 + i.val) →
    (table.lookup (508200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2541 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 508200 508400 :=
  FiniteIntervals.of_fin 508200 200 complete_chunk2541

lemma complete_chunk2542 : ∀ i : Fin 200, Compatible (508400 + i.val) →
    (table.lookup (508400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2542 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 508400 508600 :=
  FiniteIntervals.of_fin 508400 200 complete_chunk2542

lemma complete_chunk2543 : ∀ i : Fin 200, Compatible (508600 + i.val) →
    (table.lookup (508600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2543 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 508600 508800 :=
  FiniteIntervals.of_fin 508600 200 complete_chunk2543

lemma complete_chunk2544 : ∀ i : Fin 200, Compatible (508800 + i.val) →
    (table.lookup (508800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2544 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 508800 509000 :=
  FiniteIntervals.of_fin 508800 200 complete_chunk2544

lemma complete_chunk2545 : ∀ i : Fin 200, Compatible (509000 + i.val) →
    (table.lookup (509000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2545 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 509000 509200 :=
  FiniteIntervals.of_fin 509000 200 complete_chunk2545

lemma complete_chunk2546 : ∀ i : Fin 200, Compatible (509200 + i.val) →
    (table.lookup (509200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2546 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 509200 509400 :=
  FiniteIntervals.of_fin 509200 200 complete_chunk2546

lemma complete_chunk2547 : ∀ i : Fin 200, Compatible (509400 + i.val) →
    (table.lookup (509400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2547 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 509400 509600 :=
  FiniteIntervals.of_fin 509400 200 complete_chunk2547

lemma complete_chunk2548 : ∀ i : Fin 200, Compatible (509600 + i.val) →
    (table.lookup (509600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2548 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 509600 509800 :=
  FiniteIntervals.of_fin 509600 200 complete_chunk2548

lemma complete_chunk2549 : ∀ i : Fin 200, Compatible (509800 + i.val) →
    (table.lookup (509800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2549 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 509800 510000 :=
  FiniteIntervals.of_fin 509800 200 complete_chunk2549

#print axioms interval_chunk2540
end Erdos184Work.PureFiveFilter4
