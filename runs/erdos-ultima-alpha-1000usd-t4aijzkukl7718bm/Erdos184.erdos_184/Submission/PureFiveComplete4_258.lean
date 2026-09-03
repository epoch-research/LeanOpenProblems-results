import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2580 : ∀ i : Fin 200, Compatible (516000 + i.val) →
    (table.lookup (516000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2580 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 516000 516200 :=
  FiniteIntervals.of_fin 516000 200 complete_chunk2580

lemma complete_chunk2581 : ∀ i : Fin 200, Compatible (516200 + i.val) →
    (table.lookup (516200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2581 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 516200 516400 :=
  FiniteIntervals.of_fin 516200 200 complete_chunk2581

lemma complete_chunk2582 : ∀ i : Fin 200, Compatible (516400 + i.val) →
    (table.lookup (516400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2582 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 516400 516600 :=
  FiniteIntervals.of_fin 516400 200 complete_chunk2582

lemma complete_chunk2583 : ∀ i : Fin 200, Compatible (516600 + i.val) →
    (table.lookup (516600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2583 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 516600 516800 :=
  FiniteIntervals.of_fin 516600 200 complete_chunk2583

lemma complete_chunk2584 : ∀ i : Fin 200, Compatible (516800 + i.val) →
    (table.lookup (516800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2584 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 516800 517000 :=
  FiniteIntervals.of_fin 516800 200 complete_chunk2584

lemma complete_chunk2585 : ∀ i : Fin 200, Compatible (517000 + i.val) →
    (table.lookup (517000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2585 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 517000 517200 :=
  FiniteIntervals.of_fin 517000 200 complete_chunk2585

lemma complete_chunk2586 : ∀ i : Fin 200, Compatible (517200 + i.val) →
    (table.lookup (517200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2586 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 517200 517400 :=
  FiniteIntervals.of_fin 517200 200 complete_chunk2586

lemma complete_chunk2587 : ∀ i : Fin 200, Compatible (517400 + i.val) →
    (table.lookup (517400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2587 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 517400 517600 :=
  FiniteIntervals.of_fin 517400 200 complete_chunk2587

lemma complete_chunk2588 : ∀ i : Fin 200, Compatible (517600 + i.val) →
    (table.lookup (517600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2588 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 517600 517800 :=
  FiniteIntervals.of_fin 517600 200 complete_chunk2588

lemma complete_chunk2589 : ∀ i : Fin 200, Compatible (517800 + i.val) →
    (table.lookup (517800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2589 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 517800 518000 :=
  FiniteIntervals.of_fin 517800 200 complete_chunk2589

#print axioms interval_chunk2580
end Erdos184Work.PureFiveFilter4
