import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3470 : ∀ i : Fin 200, Compatible (694000 + i.val) →
    (table.lookup (694000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3470 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 694000 694200 :=
  FiniteIntervals.of_fin 694000 200 complete_chunk3470

lemma complete_chunk3471 : ∀ i : Fin 200, Compatible (694200 + i.val) →
    (table.lookup (694200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3471 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 694200 694400 :=
  FiniteIntervals.of_fin 694200 200 complete_chunk3471

lemma complete_chunk3472 : ∀ i : Fin 200, Compatible (694400 + i.val) →
    (table.lookup (694400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3472 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 694400 694600 :=
  FiniteIntervals.of_fin 694400 200 complete_chunk3472

lemma complete_chunk3473 : ∀ i : Fin 200, Compatible (694600 + i.val) →
    (table.lookup (694600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3473 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 694600 694800 :=
  FiniteIntervals.of_fin 694600 200 complete_chunk3473

lemma complete_chunk3474 : ∀ i : Fin 200, Compatible (694800 + i.val) →
    (table.lookup (694800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3474 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 694800 695000 :=
  FiniteIntervals.of_fin 694800 200 complete_chunk3474

lemma complete_chunk3475 : ∀ i : Fin 200, Compatible (695000 + i.val) →
    (table.lookup (695000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3475 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 695000 695200 :=
  FiniteIntervals.of_fin 695000 200 complete_chunk3475

lemma complete_chunk3476 : ∀ i : Fin 200, Compatible (695200 + i.val) →
    (table.lookup (695200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3476 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 695200 695400 :=
  FiniteIntervals.of_fin 695200 200 complete_chunk3476

lemma complete_chunk3477 : ∀ i : Fin 200, Compatible (695400 + i.val) →
    (table.lookup (695400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3477 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 695400 695600 :=
  FiniteIntervals.of_fin 695400 200 complete_chunk3477

lemma complete_chunk3478 : ∀ i : Fin 200, Compatible (695600 + i.val) →
    (table.lookup (695600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3478 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 695600 695800 :=
  FiniteIntervals.of_fin 695600 200 complete_chunk3478

lemma complete_chunk3479 : ∀ i : Fin 200, Compatible (695800 + i.val) →
    (table.lookup (695800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3479 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 695800 696000 :=
  FiniteIntervals.of_fin 695800 200 complete_chunk3479

#print axioms interval_chunk3470
end Erdos184Work.PureFiveFilter4
