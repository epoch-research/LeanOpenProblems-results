import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3430 : ∀ i : Fin 200, Compatible (686000 + i.val) →
    (table.lookup (686000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3430 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 686000 686200 :=
  FiniteIntervals.of_fin 686000 200 complete_chunk3430

lemma complete_chunk3431 : ∀ i : Fin 200, Compatible (686200 + i.val) →
    (table.lookup (686200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3431 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 686200 686400 :=
  FiniteIntervals.of_fin 686200 200 complete_chunk3431

lemma complete_chunk3432 : ∀ i : Fin 200, Compatible (686400 + i.val) →
    (table.lookup (686400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3432 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 686400 686600 :=
  FiniteIntervals.of_fin 686400 200 complete_chunk3432

lemma complete_chunk3433 : ∀ i : Fin 200, Compatible (686600 + i.val) →
    (table.lookup (686600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3433 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 686600 686800 :=
  FiniteIntervals.of_fin 686600 200 complete_chunk3433

lemma complete_chunk3434 : ∀ i : Fin 200, Compatible (686800 + i.val) →
    (table.lookup (686800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3434 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 686800 687000 :=
  FiniteIntervals.of_fin 686800 200 complete_chunk3434

lemma complete_chunk3435 : ∀ i : Fin 200, Compatible (687000 + i.val) →
    (table.lookup (687000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3435 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 687000 687200 :=
  FiniteIntervals.of_fin 687000 200 complete_chunk3435

lemma complete_chunk3436 : ∀ i : Fin 200, Compatible (687200 + i.val) →
    (table.lookup (687200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3436 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 687200 687400 :=
  FiniteIntervals.of_fin 687200 200 complete_chunk3436

lemma complete_chunk3437 : ∀ i : Fin 200, Compatible (687400 + i.val) →
    (table.lookup (687400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3437 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 687400 687600 :=
  FiniteIntervals.of_fin 687400 200 complete_chunk3437

lemma complete_chunk3438 : ∀ i : Fin 200, Compatible (687600 + i.val) →
    (table.lookup (687600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3438 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 687600 687800 :=
  FiniteIntervals.of_fin 687600 200 complete_chunk3438

lemma complete_chunk3439 : ∀ i : Fin 200, Compatible (687800 + i.val) →
    (table.lookup (687800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3439 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 687800 688000 :=
  FiniteIntervals.of_fin 687800 200 complete_chunk3439

#print axioms interval_chunk3430
end Erdos184Work.PureFiveFilter4
