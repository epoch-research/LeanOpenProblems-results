import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3450 : ∀ i : Fin 200, Compatible (690000 + i.val) →
    (table.lookup (690000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3450 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 690000 690200 :=
  FiniteIntervals.of_fin 690000 200 complete_chunk3450

lemma complete_chunk3451 : ∀ i : Fin 200, Compatible (690200 + i.val) →
    (table.lookup (690200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3451 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 690200 690400 :=
  FiniteIntervals.of_fin 690200 200 complete_chunk3451

lemma complete_chunk3452 : ∀ i : Fin 200, Compatible (690400 + i.val) →
    (table.lookup (690400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3452 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 690400 690600 :=
  FiniteIntervals.of_fin 690400 200 complete_chunk3452

lemma complete_chunk3453 : ∀ i : Fin 200, Compatible (690600 + i.val) →
    (table.lookup (690600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3453 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 690600 690800 :=
  FiniteIntervals.of_fin 690600 200 complete_chunk3453

lemma complete_chunk3454 : ∀ i : Fin 200, Compatible (690800 + i.val) →
    (table.lookup (690800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3454 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 690800 691000 :=
  FiniteIntervals.of_fin 690800 200 complete_chunk3454

lemma complete_chunk3455 : ∀ i : Fin 200, Compatible (691000 + i.val) →
    (table.lookup (691000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3455 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 691000 691200 :=
  FiniteIntervals.of_fin 691000 200 complete_chunk3455

lemma complete_chunk3456 : ∀ i : Fin 200, Compatible (691200 + i.val) →
    (table.lookup (691200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3456 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 691200 691400 :=
  FiniteIntervals.of_fin 691200 200 complete_chunk3456

lemma complete_chunk3457 : ∀ i : Fin 200, Compatible (691400 + i.val) →
    (table.lookup (691400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3457 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 691400 691600 :=
  FiniteIntervals.of_fin 691400 200 complete_chunk3457

lemma complete_chunk3458 : ∀ i : Fin 200, Compatible (691600 + i.val) →
    (table.lookup (691600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3458 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 691600 691800 :=
  FiniteIntervals.of_fin 691600 200 complete_chunk3458

lemma complete_chunk3459 : ∀ i : Fin 200, Compatible (691800 + i.val) →
    (table.lookup (691800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3459 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 691800 692000 :=
  FiniteIntervals.of_fin 691800 200 complete_chunk3459

#print axioms interval_chunk3450
end Erdos184Work.PureFiveFilter4
