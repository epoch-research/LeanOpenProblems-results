import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2440 : ∀ i : Fin 200, Compatible (488000 + i.val) →
    (table.lookup (488000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2440 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 488000 488200 :=
  FiniteIntervals.of_fin 488000 200 complete_chunk2440

lemma complete_chunk2441 : ∀ i : Fin 200, Compatible (488200 + i.val) →
    (table.lookup (488200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2441 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 488200 488400 :=
  FiniteIntervals.of_fin 488200 200 complete_chunk2441

lemma complete_chunk2442 : ∀ i : Fin 200, Compatible (488400 + i.val) →
    (table.lookup (488400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2442 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 488400 488600 :=
  FiniteIntervals.of_fin 488400 200 complete_chunk2442

lemma complete_chunk2443 : ∀ i : Fin 200, Compatible (488600 + i.val) →
    (table.lookup (488600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2443 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 488600 488800 :=
  FiniteIntervals.of_fin 488600 200 complete_chunk2443

lemma complete_chunk2444 : ∀ i : Fin 200, Compatible (488800 + i.val) →
    (table.lookup (488800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2444 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 488800 489000 :=
  FiniteIntervals.of_fin 488800 200 complete_chunk2444

lemma complete_chunk2445 : ∀ i : Fin 200, Compatible (489000 + i.val) →
    (table.lookup (489000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2445 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 489000 489200 :=
  FiniteIntervals.of_fin 489000 200 complete_chunk2445

lemma complete_chunk2446 : ∀ i : Fin 200, Compatible (489200 + i.val) →
    (table.lookup (489200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2446 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 489200 489400 :=
  FiniteIntervals.of_fin 489200 200 complete_chunk2446

lemma complete_chunk2447 : ∀ i : Fin 200, Compatible (489400 + i.val) →
    (table.lookup (489400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2447 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 489400 489600 :=
  FiniteIntervals.of_fin 489400 200 complete_chunk2447

lemma complete_chunk2448 : ∀ i : Fin 200, Compatible (489600 + i.val) →
    (table.lookup (489600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2448 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 489600 489800 :=
  FiniteIntervals.of_fin 489600 200 complete_chunk2448

lemma complete_chunk2449 : ∀ i : Fin 200, Compatible (489800 + i.val) →
    (table.lookup (489800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2449 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 489800 490000 :=
  FiniteIntervals.of_fin 489800 200 complete_chunk2449

#print axioms interval_chunk2440
end Erdos184Work.PureFiveFilter4
