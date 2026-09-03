import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3330 : ∀ i : Fin 200, Compatible (666000 + i.val) →
    (table.lookup (666000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3330 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 666000 666200 :=
  FiniteIntervals.of_fin 666000 200 complete_chunk3330

lemma complete_chunk3331 : ∀ i : Fin 200, Compatible (666200 + i.val) →
    (table.lookup (666200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3331 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 666200 666400 :=
  FiniteIntervals.of_fin 666200 200 complete_chunk3331

lemma complete_chunk3332 : ∀ i : Fin 200, Compatible (666400 + i.val) →
    (table.lookup (666400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3332 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 666400 666600 :=
  FiniteIntervals.of_fin 666400 200 complete_chunk3332

lemma complete_chunk3333 : ∀ i : Fin 200, Compatible (666600 + i.val) →
    (table.lookup (666600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3333 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 666600 666800 :=
  FiniteIntervals.of_fin 666600 200 complete_chunk3333

lemma complete_chunk3334 : ∀ i : Fin 200, Compatible (666800 + i.val) →
    (table.lookup (666800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3334 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 666800 667000 :=
  FiniteIntervals.of_fin 666800 200 complete_chunk3334

lemma complete_chunk3335 : ∀ i : Fin 200, Compatible (667000 + i.val) →
    (table.lookup (667000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3335 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 667000 667200 :=
  FiniteIntervals.of_fin 667000 200 complete_chunk3335

lemma complete_chunk3336 : ∀ i : Fin 200, Compatible (667200 + i.val) →
    (table.lookup (667200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3336 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 667200 667400 :=
  FiniteIntervals.of_fin 667200 200 complete_chunk3336

lemma complete_chunk3337 : ∀ i : Fin 200, Compatible (667400 + i.val) →
    (table.lookup (667400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3337 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 667400 667600 :=
  FiniteIntervals.of_fin 667400 200 complete_chunk3337

lemma complete_chunk3338 : ∀ i : Fin 200, Compatible (667600 + i.val) →
    (table.lookup (667600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3338 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 667600 667800 :=
  FiniteIntervals.of_fin 667600 200 complete_chunk3338

lemma complete_chunk3339 : ∀ i : Fin 200, Compatible (667800 + i.val) →
    (table.lookup (667800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3339 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 667800 668000 :=
  FiniteIntervals.of_fin 667800 200 complete_chunk3339

#print axioms interval_chunk3330
end Erdos184Work.PureFiveFilter4
