import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2530 : ∀ i : Fin 200, Compatible (506000 + i.val) →
    (table.lookup (506000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2530 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 506000 506200 :=
  FiniteIntervals.of_fin 506000 200 complete_chunk2530

lemma complete_chunk2531 : ∀ i : Fin 200, Compatible (506200 + i.val) →
    (table.lookup (506200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2531 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 506200 506400 :=
  FiniteIntervals.of_fin 506200 200 complete_chunk2531

lemma complete_chunk2532 : ∀ i : Fin 200, Compatible (506400 + i.val) →
    (table.lookup (506400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2532 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 506400 506600 :=
  FiniteIntervals.of_fin 506400 200 complete_chunk2532

lemma complete_chunk2533 : ∀ i : Fin 200, Compatible (506600 + i.val) →
    (table.lookup (506600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2533 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 506600 506800 :=
  FiniteIntervals.of_fin 506600 200 complete_chunk2533

lemma complete_chunk2534 : ∀ i : Fin 200, Compatible (506800 + i.val) →
    (table.lookup (506800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2534 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 506800 507000 :=
  FiniteIntervals.of_fin 506800 200 complete_chunk2534

lemma complete_chunk2535 : ∀ i : Fin 200, Compatible (507000 + i.val) →
    (table.lookup (507000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2535 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 507000 507200 :=
  FiniteIntervals.of_fin 507000 200 complete_chunk2535

lemma complete_chunk2536 : ∀ i : Fin 200, Compatible (507200 + i.val) →
    (table.lookup (507200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2536 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 507200 507400 :=
  FiniteIntervals.of_fin 507200 200 complete_chunk2536

lemma complete_chunk2537 : ∀ i : Fin 200, Compatible (507400 + i.val) →
    (table.lookup (507400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2537 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 507400 507600 :=
  FiniteIntervals.of_fin 507400 200 complete_chunk2537

lemma complete_chunk2538 : ∀ i : Fin 200, Compatible (507600 + i.val) →
    (table.lookup (507600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2538 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 507600 507800 :=
  FiniteIntervals.of_fin 507600 200 complete_chunk2538

lemma complete_chunk2539 : ∀ i : Fin 200, Compatible (507800 + i.val) →
    (table.lookup (507800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2539 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 507800 508000 :=
  FiniteIntervals.of_fin 507800 200 complete_chunk2539

#print axioms interval_chunk2530
end Erdos184Work.PureFiveFilter4
