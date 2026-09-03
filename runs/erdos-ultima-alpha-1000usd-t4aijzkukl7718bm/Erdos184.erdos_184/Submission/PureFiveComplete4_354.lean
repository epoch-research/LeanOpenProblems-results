import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3540 : ∀ i : Fin 200, Compatible (708000 + i.val) →
    (table.lookup (708000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3540 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 708000 708200 :=
  FiniteIntervals.of_fin 708000 200 complete_chunk3540

lemma complete_chunk3541 : ∀ i : Fin 200, Compatible (708200 + i.val) →
    (table.lookup (708200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3541 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 708200 708400 :=
  FiniteIntervals.of_fin 708200 200 complete_chunk3541

lemma complete_chunk3542 : ∀ i : Fin 200, Compatible (708400 + i.val) →
    (table.lookup (708400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3542 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 708400 708600 :=
  FiniteIntervals.of_fin 708400 200 complete_chunk3542

lemma complete_chunk3543 : ∀ i : Fin 200, Compatible (708600 + i.val) →
    (table.lookup (708600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3543 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 708600 708800 :=
  FiniteIntervals.of_fin 708600 200 complete_chunk3543

lemma complete_chunk3544 : ∀ i : Fin 200, Compatible (708800 + i.val) →
    (table.lookup (708800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3544 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 708800 709000 :=
  FiniteIntervals.of_fin 708800 200 complete_chunk3544

lemma complete_chunk3545 : ∀ i : Fin 200, Compatible (709000 + i.val) →
    (table.lookup (709000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3545 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 709000 709200 :=
  FiniteIntervals.of_fin 709000 200 complete_chunk3545

lemma complete_chunk3546 : ∀ i : Fin 200, Compatible (709200 + i.val) →
    (table.lookup (709200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3546 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 709200 709400 :=
  FiniteIntervals.of_fin 709200 200 complete_chunk3546

lemma complete_chunk3547 : ∀ i : Fin 200, Compatible (709400 + i.val) →
    (table.lookup (709400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3547 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 709400 709600 :=
  FiniteIntervals.of_fin 709400 200 complete_chunk3547

lemma complete_chunk3548 : ∀ i : Fin 200, Compatible (709600 + i.val) →
    (table.lookup (709600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3548 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 709600 709800 :=
  FiniteIntervals.of_fin 709600 200 complete_chunk3548

lemma complete_chunk3549 : ∀ i : Fin 200, Compatible (709800 + i.val) →
    (table.lookup (709800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3549 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 709800 710000 :=
  FiniteIntervals.of_fin 709800 200 complete_chunk3549

#print axioms interval_chunk3540
end Erdos184Work.PureFiveFilter4
