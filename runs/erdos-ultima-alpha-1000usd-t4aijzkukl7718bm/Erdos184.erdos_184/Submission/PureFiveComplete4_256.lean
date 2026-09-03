import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2560 : ∀ i : Fin 200, Compatible (512000 + i.val) →
    (table.lookup (512000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2560 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 512000 512200 :=
  FiniteIntervals.of_fin 512000 200 complete_chunk2560

lemma complete_chunk2561 : ∀ i : Fin 200, Compatible (512200 + i.val) →
    (table.lookup (512200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2561 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 512200 512400 :=
  FiniteIntervals.of_fin 512200 200 complete_chunk2561

lemma complete_chunk2562 : ∀ i : Fin 200, Compatible (512400 + i.val) →
    (table.lookup (512400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2562 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 512400 512600 :=
  FiniteIntervals.of_fin 512400 200 complete_chunk2562

lemma complete_chunk2563 : ∀ i : Fin 200, Compatible (512600 + i.val) →
    (table.lookup (512600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2563 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 512600 512800 :=
  FiniteIntervals.of_fin 512600 200 complete_chunk2563

lemma complete_chunk2564 : ∀ i : Fin 200, Compatible (512800 + i.val) →
    (table.lookup (512800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2564 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 512800 513000 :=
  FiniteIntervals.of_fin 512800 200 complete_chunk2564

lemma complete_chunk2565 : ∀ i : Fin 200, Compatible (513000 + i.val) →
    (table.lookup (513000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2565 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 513000 513200 :=
  FiniteIntervals.of_fin 513000 200 complete_chunk2565

lemma complete_chunk2566 : ∀ i : Fin 200, Compatible (513200 + i.val) →
    (table.lookup (513200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2566 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 513200 513400 :=
  FiniteIntervals.of_fin 513200 200 complete_chunk2566

lemma complete_chunk2567 : ∀ i : Fin 200, Compatible (513400 + i.val) →
    (table.lookup (513400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2567 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 513400 513600 :=
  FiniteIntervals.of_fin 513400 200 complete_chunk2567

lemma complete_chunk2568 : ∀ i : Fin 200, Compatible (513600 + i.val) →
    (table.lookup (513600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2568 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 513600 513800 :=
  FiniteIntervals.of_fin 513600 200 complete_chunk2568

lemma complete_chunk2569 : ∀ i : Fin 200, Compatible (513800 + i.val) →
    (table.lookup (513800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2569 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 513800 514000 :=
  FiniteIntervals.of_fin 513800 200 complete_chunk2569

#print axioms interval_chunk2560
end Erdos184Work.PureFiveFilter4
