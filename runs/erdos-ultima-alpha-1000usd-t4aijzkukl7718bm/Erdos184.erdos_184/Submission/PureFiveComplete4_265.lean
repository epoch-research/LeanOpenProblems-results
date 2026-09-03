import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2650 : ∀ i : Fin 200, Compatible (530000 + i.val) →
    (table.lookup (530000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2650 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 530000 530200 :=
  FiniteIntervals.of_fin 530000 200 complete_chunk2650

lemma complete_chunk2651 : ∀ i : Fin 200, Compatible (530200 + i.val) →
    (table.lookup (530200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2651 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 530200 530400 :=
  FiniteIntervals.of_fin 530200 200 complete_chunk2651

lemma complete_chunk2652 : ∀ i : Fin 200, Compatible (530400 + i.val) →
    (table.lookup (530400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2652 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 530400 530600 :=
  FiniteIntervals.of_fin 530400 200 complete_chunk2652

lemma complete_chunk2653 : ∀ i : Fin 200, Compatible (530600 + i.val) →
    (table.lookup (530600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2653 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 530600 530800 :=
  FiniteIntervals.of_fin 530600 200 complete_chunk2653

lemma complete_chunk2654 : ∀ i : Fin 200, Compatible (530800 + i.val) →
    (table.lookup (530800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2654 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 530800 531000 :=
  FiniteIntervals.of_fin 530800 200 complete_chunk2654

lemma complete_chunk2655 : ∀ i : Fin 200, Compatible (531000 + i.val) →
    (table.lookup (531000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2655 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 531000 531200 :=
  FiniteIntervals.of_fin 531000 200 complete_chunk2655

lemma complete_chunk2656 : ∀ i : Fin 200, Compatible (531200 + i.val) →
    (table.lookup (531200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2656 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 531200 531400 :=
  FiniteIntervals.of_fin 531200 200 complete_chunk2656

lemma complete_chunk2657 : ∀ i : Fin 200, Compatible (531400 + i.val) →
    (table.lookup (531400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2657 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 531400 531600 :=
  FiniteIntervals.of_fin 531400 200 complete_chunk2657

lemma complete_chunk2658 : ∀ i : Fin 200, Compatible (531600 + i.val) →
    (table.lookup (531600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2658 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 531600 531800 :=
  FiniteIntervals.of_fin 531600 200 complete_chunk2658

lemma complete_chunk2659 : ∀ i : Fin 200, Compatible (531800 + i.val) →
    (table.lookup (531800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2659 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 531800 532000 :=
  FiniteIntervals.of_fin 531800 200 complete_chunk2659

#print axioms interval_chunk2650
end Erdos184Work.PureFiveFilter4
