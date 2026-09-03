import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2480 : ∀ i : Fin 200, Compatible (496000 + i.val) →
    (table.lookup (496000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2480 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 496000 496200 :=
  FiniteIntervals.of_fin 496000 200 complete_chunk2480

lemma complete_chunk2481 : ∀ i : Fin 200, Compatible (496200 + i.val) →
    (table.lookup (496200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2481 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 496200 496400 :=
  FiniteIntervals.of_fin 496200 200 complete_chunk2481

lemma complete_chunk2482 : ∀ i : Fin 200, Compatible (496400 + i.val) →
    (table.lookup (496400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2482 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 496400 496600 :=
  FiniteIntervals.of_fin 496400 200 complete_chunk2482

lemma complete_chunk2483 : ∀ i : Fin 200, Compatible (496600 + i.val) →
    (table.lookup (496600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2483 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 496600 496800 :=
  FiniteIntervals.of_fin 496600 200 complete_chunk2483

lemma complete_chunk2484 : ∀ i : Fin 200, Compatible (496800 + i.val) →
    (table.lookup (496800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2484 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 496800 497000 :=
  FiniteIntervals.of_fin 496800 200 complete_chunk2484

lemma complete_chunk2485 : ∀ i : Fin 200, Compatible (497000 + i.val) →
    (table.lookup (497000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2485 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 497000 497200 :=
  FiniteIntervals.of_fin 497000 200 complete_chunk2485

lemma complete_chunk2486 : ∀ i : Fin 200, Compatible (497200 + i.val) →
    (table.lookup (497200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2486 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 497200 497400 :=
  FiniteIntervals.of_fin 497200 200 complete_chunk2486

lemma complete_chunk2487 : ∀ i : Fin 200, Compatible (497400 + i.val) →
    (table.lookup (497400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2487 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 497400 497600 :=
  FiniteIntervals.of_fin 497400 200 complete_chunk2487

lemma complete_chunk2488 : ∀ i : Fin 200, Compatible (497600 + i.val) →
    (table.lookup (497600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2488 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 497600 497800 :=
  FiniteIntervals.of_fin 497600 200 complete_chunk2488

lemma complete_chunk2489 : ∀ i : Fin 200, Compatible (497800 + i.val) →
    (table.lookup (497800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2489 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 497800 498000 :=
  FiniteIntervals.of_fin 497800 200 complete_chunk2489

#print axioms interval_chunk2480
end Erdos184Work.PureFiveFilter4
