import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2520 : ∀ i : Fin 200, Compatible (504000 + i.val) →
    (table.lookup (504000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2520 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 504000 504200 :=
  FiniteIntervals.of_fin 504000 200 complete_chunk2520

lemma complete_chunk2521 : ∀ i : Fin 200, Compatible (504200 + i.val) →
    (table.lookup (504200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2521 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 504200 504400 :=
  FiniteIntervals.of_fin 504200 200 complete_chunk2521

lemma complete_chunk2522 : ∀ i : Fin 200, Compatible (504400 + i.val) →
    (table.lookup (504400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2522 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 504400 504600 :=
  FiniteIntervals.of_fin 504400 200 complete_chunk2522

lemma complete_chunk2523 : ∀ i : Fin 200, Compatible (504600 + i.val) →
    (table.lookup (504600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2523 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 504600 504800 :=
  FiniteIntervals.of_fin 504600 200 complete_chunk2523

lemma complete_chunk2524 : ∀ i : Fin 200, Compatible (504800 + i.val) →
    (table.lookup (504800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2524 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 504800 505000 :=
  FiniteIntervals.of_fin 504800 200 complete_chunk2524

lemma complete_chunk2525 : ∀ i : Fin 200, Compatible (505000 + i.val) →
    (table.lookup (505000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2525 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 505000 505200 :=
  FiniteIntervals.of_fin 505000 200 complete_chunk2525

lemma complete_chunk2526 : ∀ i : Fin 200, Compatible (505200 + i.val) →
    (table.lookup (505200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2526 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 505200 505400 :=
  FiniteIntervals.of_fin 505200 200 complete_chunk2526

lemma complete_chunk2527 : ∀ i : Fin 200, Compatible (505400 + i.val) →
    (table.lookup (505400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2527 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 505400 505600 :=
  FiniteIntervals.of_fin 505400 200 complete_chunk2527

lemma complete_chunk2528 : ∀ i : Fin 200, Compatible (505600 + i.val) →
    (table.lookup (505600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2528 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 505600 505800 :=
  FiniteIntervals.of_fin 505600 200 complete_chunk2528

lemma complete_chunk2529 : ∀ i : Fin 200, Compatible (505800 + i.val) →
    (table.lookup (505800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2529 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 505800 506000 :=
  FiniteIntervals.of_fin 505800 200 complete_chunk2529

#print axioms interval_chunk2520
end Erdos184Work.PureFiveFilter4
