import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2430 : ∀ i : Fin 200, Compatible (486000 + i.val) →
    (table.lookup (486000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2430 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 486000 486200 :=
  FiniteIntervals.of_fin 486000 200 complete_chunk2430

lemma complete_chunk2431 : ∀ i : Fin 200, Compatible (486200 + i.val) →
    (table.lookup (486200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2431 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 486200 486400 :=
  FiniteIntervals.of_fin 486200 200 complete_chunk2431

lemma complete_chunk2432 : ∀ i : Fin 200, Compatible (486400 + i.val) →
    (table.lookup (486400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2432 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 486400 486600 :=
  FiniteIntervals.of_fin 486400 200 complete_chunk2432

lemma complete_chunk2433 : ∀ i : Fin 200, Compatible (486600 + i.val) →
    (table.lookup (486600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2433 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 486600 486800 :=
  FiniteIntervals.of_fin 486600 200 complete_chunk2433

lemma complete_chunk2434 : ∀ i : Fin 200, Compatible (486800 + i.val) →
    (table.lookup (486800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2434 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 486800 487000 :=
  FiniteIntervals.of_fin 486800 200 complete_chunk2434

lemma complete_chunk2435 : ∀ i : Fin 200, Compatible (487000 + i.val) →
    (table.lookup (487000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2435 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 487000 487200 :=
  FiniteIntervals.of_fin 487000 200 complete_chunk2435

lemma complete_chunk2436 : ∀ i : Fin 200, Compatible (487200 + i.val) →
    (table.lookup (487200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2436 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 487200 487400 :=
  FiniteIntervals.of_fin 487200 200 complete_chunk2436

lemma complete_chunk2437 : ∀ i : Fin 200, Compatible (487400 + i.val) →
    (table.lookup (487400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2437 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 487400 487600 :=
  FiniteIntervals.of_fin 487400 200 complete_chunk2437

lemma complete_chunk2438 : ∀ i : Fin 200, Compatible (487600 + i.val) →
    (table.lookup (487600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2438 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 487600 487800 :=
  FiniteIntervals.of_fin 487600 200 complete_chunk2438

lemma complete_chunk2439 : ∀ i : Fin 200, Compatible (487800 + i.val) →
    (table.lookup (487800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2439 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 487800 488000 :=
  FiniteIntervals.of_fin 487800 200 complete_chunk2439

#print axioms interval_chunk2430
end Erdos184Work.PureFiveFilter4
