import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3480 : ∀ i : Fin 200, Compatible (696000 + i.val) →
    (table.lookup (696000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3480 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 696000 696200 :=
  FiniteIntervals.of_fin 696000 200 complete_chunk3480

lemma complete_chunk3481 : ∀ i : Fin 200, Compatible (696200 + i.val) →
    (table.lookup (696200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3481 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 696200 696400 :=
  FiniteIntervals.of_fin 696200 200 complete_chunk3481

lemma complete_chunk3482 : ∀ i : Fin 200, Compatible (696400 + i.val) →
    (table.lookup (696400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3482 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 696400 696600 :=
  FiniteIntervals.of_fin 696400 200 complete_chunk3482

lemma complete_chunk3483 : ∀ i : Fin 200, Compatible (696600 + i.val) →
    (table.lookup (696600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3483 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 696600 696800 :=
  FiniteIntervals.of_fin 696600 200 complete_chunk3483

lemma complete_chunk3484 : ∀ i : Fin 200, Compatible (696800 + i.val) →
    (table.lookup (696800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3484 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 696800 697000 :=
  FiniteIntervals.of_fin 696800 200 complete_chunk3484

lemma complete_chunk3485 : ∀ i : Fin 200, Compatible (697000 + i.val) →
    (table.lookup (697000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3485 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 697000 697200 :=
  FiniteIntervals.of_fin 697000 200 complete_chunk3485

lemma complete_chunk3486 : ∀ i : Fin 200, Compatible (697200 + i.val) →
    (table.lookup (697200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3486 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 697200 697400 :=
  FiniteIntervals.of_fin 697200 200 complete_chunk3486

lemma complete_chunk3487 : ∀ i : Fin 200, Compatible (697400 + i.val) →
    (table.lookup (697400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3487 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 697400 697600 :=
  FiniteIntervals.of_fin 697400 200 complete_chunk3487

lemma complete_chunk3488 : ∀ i : Fin 200, Compatible (697600 + i.val) →
    (table.lookup (697600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3488 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 697600 697800 :=
  FiniteIntervals.of_fin 697600 200 complete_chunk3488

lemma complete_chunk3489 : ∀ i : Fin 200, Compatible (697800 + i.val) →
    (table.lookup (697800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3489 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 697800 698000 :=
  FiniteIntervals.of_fin 697800 200 complete_chunk3489

#print axioms interval_chunk3480
end Erdos184Work.PureFiveFilter4
