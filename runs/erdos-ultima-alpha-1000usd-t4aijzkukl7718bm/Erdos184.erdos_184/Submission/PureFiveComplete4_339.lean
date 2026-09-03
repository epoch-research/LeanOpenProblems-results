import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3390 : ∀ i : Fin 200, Compatible (678000 + i.val) →
    (table.lookup (678000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3390 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 678000 678200 :=
  FiniteIntervals.of_fin 678000 200 complete_chunk3390

lemma complete_chunk3391 : ∀ i : Fin 200, Compatible (678200 + i.val) →
    (table.lookup (678200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3391 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 678200 678400 :=
  FiniteIntervals.of_fin 678200 200 complete_chunk3391

lemma complete_chunk3392 : ∀ i : Fin 200, Compatible (678400 + i.val) →
    (table.lookup (678400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3392 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 678400 678600 :=
  FiniteIntervals.of_fin 678400 200 complete_chunk3392

lemma complete_chunk3393 : ∀ i : Fin 200, Compatible (678600 + i.val) →
    (table.lookup (678600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3393 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 678600 678800 :=
  FiniteIntervals.of_fin 678600 200 complete_chunk3393

lemma complete_chunk3394 : ∀ i : Fin 200, Compatible (678800 + i.val) →
    (table.lookup (678800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3394 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 678800 679000 :=
  FiniteIntervals.of_fin 678800 200 complete_chunk3394

lemma complete_chunk3395 : ∀ i : Fin 200, Compatible (679000 + i.val) →
    (table.lookup (679000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3395 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 679000 679200 :=
  FiniteIntervals.of_fin 679000 200 complete_chunk3395

lemma complete_chunk3396 : ∀ i : Fin 200, Compatible (679200 + i.val) →
    (table.lookup (679200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3396 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 679200 679400 :=
  FiniteIntervals.of_fin 679200 200 complete_chunk3396

lemma complete_chunk3397 : ∀ i : Fin 200, Compatible (679400 + i.val) →
    (table.lookup (679400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3397 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 679400 679600 :=
  FiniteIntervals.of_fin 679400 200 complete_chunk3397

lemma complete_chunk3398 : ∀ i : Fin 200, Compatible (679600 + i.val) →
    (table.lookup (679600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3398 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 679600 679800 :=
  FiniteIntervals.of_fin 679600 200 complete_chunk3398

lemma complete_chunk3399 : ∀ i : Fin 200, Compatible (679800 + i.val) →
    (table.lookup (679800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3399 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 679800 680000 :=
  FiniteIntervals.of_fin 679800 200 complete_chunk3399

#print axioms interval_chunk3390
end Erdos184Work.PureFiveFilter4
