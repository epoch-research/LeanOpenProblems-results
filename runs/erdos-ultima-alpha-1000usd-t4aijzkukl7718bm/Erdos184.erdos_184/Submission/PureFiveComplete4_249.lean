import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2490 : ∀ i : Fin 200, Compatible (498000 + i.val) →
    (table.lookup (498000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2490 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 498000 498200 :=
  FiniteIntervals.of_fin 498000 200 complete_chunk2490

lemma complete_chunk2491 : ∀ i : Fin 200, Compatible (498200 + i.val) →
    (table.lookup (498200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2491 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 498200 498400 :=
  FiniteIntervals.of_fin 498200 200 complete_chunk2491

lemma complete_chunk2492 : ∀ i : Fin 200, Compatible (498400 + i.val) →
    (table.lookup (498400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2492 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 498400 498600 :=
  FiniteIntervals.of_fin 498400 200 complete_chunk2492

lemma complete_chunk2493 : ∀ i : Fin 200, Compatible (498600 + i.val) →
    (table.lookup (498600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2493 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 498600 498800 :=
  FiniteIntervals.of_fin 498600 200 complete_chunk2493

lemma complete_chunk2494 : ∀ i : Fin 200, Compatible (498800 + i.val) →
    (table.lookup (498800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2494 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 498800 499000 :=
  FiniteIntervals.of_fin 498800 200 complete_chunk2494

lemma complete_chunk2495 : ∀ i : Fin 200, Compatible (499000 + i.val) →
    (table.lookup (499000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2495 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 499000 499200 :=
  FiniteIntervals.of_fin 499000 200 complete_chunk2495

lemma complete_chunk2496 : ∀ i : Fin 200, Compatible (499200 + i.val) →
    (table.lookup (499200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2496 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 499200 499400 :=
  FiniteIntervals.of_fin 499200 200 complete_chunk2496

lemma complete_chunk2497 : ∀ i : Fin 200, Compatible (499400 + i.val) →
    (table.lookup (499400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2497 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 499400 499600 :=
  FiniteIntervals.of_fin 499400 200 complete_chunk2497

lemma complete_chunk2498 : ∀ i : Fin 200, Compatible (499600 + i.val) →
    (table.lookup (499600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2498 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 499600 499800 :=
  FiniteIntervals.of_fin 499600 200 complete_chunk2498

lemma complete_chunk2499 : ∀ i : Fin 200, Compatible (499800 + i.val) →
    (table.lookup (499800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2499 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 499800 500000 :=
  FiniteIntervals.of_fin 499800 200 complete_chunk2499

#print axioms interval_chunk2490
end Erdos184Work.PureFiveFilter4
