import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2460 : ∀ i : Fin 200, Compatible (492000 + i.val) →
    (table.lookup (492000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2460 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 492000 492200 :=
  FiniteIntervals.of_fin 492000 200 complete_chunk2460

lemma complete_chunk2461 : ∀ i : Fin 200, Compatible (492200 + i.val) →
    (table.lookup (492200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2461 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 492200 492400 :=
  FiniteIntervals.of_fin 492200 200 complete_chunk2461

lemma complete_chunk2462 : ∀ i : Fin 200, Compatible (492400 + i.val) →
    (table.lookup (492400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2462 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 492400 492600 :=
  FiniteIntervals.of_fin 492400 200 complete_chunk2462

lemma complete_chunk2463 : ∀ i : Fin 200, Compatible (492600 + i.val) →
    (table.lookup (492600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2463 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 492600 492800 :=
  FiniteIntervals.of_fin 492600 200 complete_chunk2463

lemma complete_chunk2464 : ∀ i : Fin 200, Compatible (492800 + i.val) →
    (table.lookup (492800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2464 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 492800 493000 :=
  FiniteIntervals.of_fin 492800 200 complete_chunk2464

lemma complete_chunk2465 : ∀ i : Fin 200, Compatible (493000 + i.val) →
    (table.lookup (493000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2465 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 493000 493200 :=
  FiniteIntervals.of_fin 493000 200 complete_chunk2465

lemma complete_chunk2466 : ∀ i : Fin 200, Compatible (493200 + i.val) →
    (table.lookup (493200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2466 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 493200 493400 :=
  FiniteIntervals.of_fin 493200 200 complete_chunk2466

lemma complete_chunk2467 : ∀ i : Fin 200, Compatible (493400 + i.val) →
    (table.lookup (493400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2467 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 493400 493600 :=
  FiniteIntervals.of_fin 493400 200 complete_chunk2467

lemma complete_chunk2468 : ∀ i : Fin 200, Compatible (493600 + i.val) →
    (table.lookup (493600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2468 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 493600 493800 :=
  FiniteIntervals.of_fin 493600 200 complete_chunk2468

lemma complete_chunk2469 : ∀ i : Fin 200, Compatible (493800 + i.val) →
    (table.lookup (493800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2469 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 493800 494000 :=
  FiniteIntervals.of_fin 493800 200 complete_chunk2469

#print axioms interval_chunk2460
end Erdos184Work.PureFiveFilter4
