import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4350 : ∀ i : Fin 200, Compatible (870000 + i.val) →
    (table.lookup (870000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4350 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 870000 870200 :=
  FiniteIntervals.of_fin 870000 200 complete_chunk4350

lemma complete_chunk4351 : ∀ i : Fin 200, Compatible (870200 + i.val) →
    (table.lookup (870200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4351 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 870200 870400 :=
  FiniteIntervals.of_fin 870200 200 complete_chunk4351

lemma complete_chunk4352 : ∀ i : Fin 200, Compatible (870400 + i.val) →
    (table.lookup (870400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4352 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 870400 870600 :=
  FiniteIntervals.of_fin 870400 200 complete_chunk4352

lemma complete_chunk4353 : ∀ i : Fin 200, Compatible (870600 + i.val) →
    (table.lookup (870600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4353 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 870600 870800 :=
  FiniteIntervals.of_fin 870600 200 complete_chunk4353

lemma complete_chunk4354 : ∀ i : Fin 200, Compatible (870800 + i.val) →
    (table.lookup (870800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4354 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 870800 871000 :=
  FiniteIntervals.of_fin 870800 200 complete_chunk4354

lemma complete_chunk4355 : ∀ i : Fin 200, Compatible (871000 + i.val) →
    (table.lookup (871000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4355 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 871000 871200 :=
  FiniteIntervals.of_fin 871000 200 complete_chunk4355

lemma complete_chunk4356 : ∀ i : Fin 200, Compatible (871200 + i.val) →
    (table.lookup (871200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4356 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 871200 871400 :=
  FiniteIntervals.of_fin 871200 200 complete_chunk4356

lemma complete_chunk4357 : ∀ i : Fin 200, Compatible (871400 + i.val) →
    (table.lookup (871400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4357 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 871400 871600 :=
  FiniteIntervals.of_fin 871400 200 complete_chunk4357

lemma complete_chunk4358 : ∀ i : Fin 200, Compatible (871600 + i.val) →
    (table.lookup (871600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4358 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 871600 871800 :=
  FiniteIntervals.of_fin 871600 200 complete_chunk4358

lemma complete_chunk4359 : ∀ i : Fin 200, Compatible (871800 + i.val) →
    (table.lookup (871800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4359 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 871800 872000 :=
  FiniteIntervals.of_fin 871800 200 complete_chunk4359

#print axioms interval_chunk4350
end Erdos184Work.PureFiveFilter4
