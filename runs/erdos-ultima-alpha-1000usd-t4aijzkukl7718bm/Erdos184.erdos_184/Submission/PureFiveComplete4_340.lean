import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3400 : ∀ i : Fin 200, Compatible (680000 + i.val) →
    (table.lookup (680000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3400 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 680000 680200 :=
  FiniteIntervals.of_fin 680000 200 complete_chunk3400

lemma complete_chunk3401 : ∀ i : Fin 200, Compatible (680200 + i.val) →
    (table.lookup (680200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3401 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 680200 680400 :=
  FiniteIntervals.of_fin 680200 200 complete_chunk3401

lemma complete_chunk3402 : ∀ i : Fin 200, Compatible (680400 + i.val) →
    (table.lookup (680400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3402 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 680400 680600 :=
  FiniteIntervals.of_fin 680400 200 complete_chunk3402

lemma complete_chunk3403 : ∀ i : Fin 200, Compatible (680600 + i.val) →
    (table.lookup (680600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3403 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 680600 680800 :=
  FiniteIntervals.of_fin 680600 200 complete_chunk3403

lemma complete_chunk3404 : ∀ i : Fin 200, Compatible (680800 + i.val) →
    (table.lookup (680800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3404 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 680800 681000 :=
  FiniteIntervals.of_fin 680800 200 complete_chunk3404

lemma complete_chunk3405 : ∀ i : Fin 200, Compatible (681000 + i.val) →
    (table.lookup (681000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3405 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 681000 681200 :=
  FiniteIntervals.of_fin 681000 200 complete_chunk3405

lemma complete_chunk3406 : ∀ i : Fin 200, Compatible (681200 + i.val) →
    (table.lookup (681200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3406 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 681200 681400 :=
  FiniteIntervals.of_fin 681200 200 complete_chunk3406

lemma complete_chunk3407 : ∀ i : Fin 200, Compatible (681400 + i.val) →
    (table.lookup (681400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3407 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 681400 681600 :=
  FiniteIntervals.of_fin 681400 200 complete_chunk3407

lemma complete_chunk3408 : ∀ i : Fin 200, Compatible (681600 + i.val) →
    (table.lookup (681600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3408 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 681600 681800 :=
  FiniteIntervals.of_fin 681600 200 complete_chunk3408

lemma complete_chunk3409 : ∀ i : Fin 200, Compatible (681800 + i.val) →
    (table.lookup (681800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3409 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 681800 682000 :=
  FiniteIntervals.of_fin 681800 200 complete_chunk3409

#print axioms interval_chunk3400
end Erdos184Work.PureFiveFilter4
