import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4340 : ∀ i : Fin 200, Compatible (868000 + i.val) →
    (table.lookup (868000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4340 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 868000 868200 :=
  FiniteIntervals.of_fin 868000 200 complete_chunk4340

lemma complete_chunk4341 : ∀ i : Fin 200, Compatible (868200 + i.val) →
    (table.lookup (868200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4341 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 868200 868400 :=
  FiniteIntervals.of_fin 868200 200 complete_chunk4341

lemma complete_chunk4342 : ∀ i : Fin 200, Compatible (868400 + i.val) →
    (table.lookup (868400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4342 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 868400 868600 :=
  FiniteIntervals.of_fin 868400 200 complete_chunk4342

lemma complete_chunk4343 : ∀ i : Fin 200, Compatible (868600 + i.val) →
    (table.lookup (868600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4343 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 868600 868800 :=
  FiniteIntervals.of_fin 868600 200 complete_chunk4343

lemma complete_chunk4344 : ∀ i : Fin 200, Compatible (868800 + i.val) →
    (table.lookup (868800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4344 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 868800 869000 :=
  FiniteIntervals.of_fin 868800 200 complete_chunk4344

lemma complete_chunk4345 : ∀ i : Fin 200, Compatible (869000 + i.val) →
    (table.lookup (869000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4345 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 869000 869200 :=
  FiniteIntervals.of_fin 869000 200 complete_chunk4345

lemma complete_chunk4346 : ∀ i : Fin 200, Compatible (869200 + i.val) →
    (table.lookup (869200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4346 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 869200 869400 :=
  FiniteIntervals.of_fin 869200 200 complete_chunk4346

lemma complete_chunk4347 : ∀ i : Fin 200, Compatible (869400 + i.val) →
    (table.lookup (869400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4347 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 869400 869600 :=
  FiniteIntervals.of_fin 869400 200 complete_chunk4347

lemma complete_chunk4348 : ∀ i : Fin 200, Compatible (869600 + i.val) →
    (table.lookup (869600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4348 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 869600 869800 :=
  FiniteIntervals.of_fin 869600 200 complete_chunk4348

lemma complete_chunk4349 : ∀ i : Fin 200, Compatible (869800 + i.val) →
    (table.lookup (869800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4349 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 869800 870000 :=
  FiniteIntervals.of_fin 869800 200 complete_chunk4349

#print axioms interval_chunk4340
end Erdos184Work.PureFiveFilter4
