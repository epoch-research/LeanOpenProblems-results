import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2550 : ∀ i : Fin 200, Compatible (510000 + i.val) →
    (table.lookup (510000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2550 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 510000 510200 :=
  FiniteIntervals.of_fin 510000 200 complete_chunk2550

lemma complete_chunk2551 : ∀ i : Fin 200, Compatible (510200 + i.val) →
    (table.lookup (510200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2551 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 510200 510400 :=
  FiniteIntervals.of_fin 510200 200 complete_chunk2551

lemma complete_chunk2552 : ∀ i : Fin 200, Compatible (510400 + i.val) →
    (table.lookup (510400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2552 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 510400 510600 :=
  FiniteIntervals.of_fin 510400 200 complete_chunk2552

lemma complete_chunk2553 : ∀ i : Fin 200, Compatible (510600 + i.val) →
    (table.lookup (510600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2553 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 510600 510800 :=
  FiniteIntervals.of_fin 510600 200 complete_chunk2553

lemma complete_chunk2554 : ∀ i : Fin 200, Compatible (510800 + i.val) →
    (table.lookup (510800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2554 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 510800 511000 :=
  FiniteIntervals.of_fin 510800 200 complete_chunk2554

lemma complete_chunk2555 : ∀ i : Fin 200, Compatible (511000 + i.val) →
    (table.lookup (511000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2555 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 511000 511200 :=
  FiniteIntervals.of_fin 511000 200 complete_chunk2555

lemma complete_chunk2556 : ∀ i : Fin 200, Compatible (511200 + i.val) →
    (table.lookup (511200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2556 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 511200 511400 :=
  FiniteIntervals.of_fin 511200 200 complete_chunk2556

lemma complete_chunk2557 : ∀ i : Fin 200, Compatible (511400 + i.val) →
    (table.lookup (511400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2557 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 511400 511600 :=
  FiniteIntervals.of_fin 511400 200 complete_chunk2557

lemma complete_chunk2558 : ∀ i : Fin 200, Compatible (511600 + i.val) →
    (table.lookup (511600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2558 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 511600 511800 :=
  FiniteIntervals.of_fin 511600 200 complete_chunk2558

lemma complete_chunk2559 : ∀ i : Fin 200, Compatible (511800 + i.val) →
    (table.lookup (511800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2559 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 511800 512000 :=
  FiniteIntervals.of_fin 511800 200 complete_chunk2559

#print axioms interval_chunk2550
end Erdos184Work.PureFiveFilter4
