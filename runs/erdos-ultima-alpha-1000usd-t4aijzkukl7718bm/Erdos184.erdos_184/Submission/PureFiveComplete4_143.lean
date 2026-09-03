import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1430 : ∀ i : Fin 200, Compatible (286000 + i.val) →
    (table.lookup (286000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1430 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 286000 286200 :=
  FiniteIntervals.of_fin 286000 200 complete_chunk1430

lemma complete_chunk1431 : ∀ i : Fin 200, Compatible (286200 + i.val) →
    (table.lookup (286200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1431 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 286200 286400 :=
  FiniteIntervals.of_fin 286200 200 complete_chunk1431

lemma complete_chunk1432 : ∀ i : Fin 200, Compatible (286400 + i.val) →
    (table.lookup (286400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1432 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 286400 286600 :=
  FiniteIntervals.of_fin 286400 200 complete_chunk1432

lemma complete_chunk1433 : ∀ i : Fin 200, Compatible (286600 + i.val) →
    (table.lookup (286600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1433 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 286600 286800 :=
  FiniteIntervals.of_fin 286600 200 complete_chunk1433

lemma complete_chunk1434 : ∀ i : Fin 200, Compatible (286800 + i.val) →
    (table.lookup (286800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1434 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 286800 287000 :=
  FiniteIntervals.of_fin 286800 200 complete_chunk1434

lemma complete_chunk1435 : ∀ i : Fin 200, Compatible (287000 + i.val) →
    (table.lookup (287000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1435 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 287000 287200 :=
  FiniteIntervals.of_fin 287000 200 complete_chunk1435

lemma complete_chunk1436 : ∀ i : Fin 200, Compatible (287200 + i.val) →
    (table.lookup (287200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1436 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 287200 287400 :=
  FiniteIntervals.of_fin 287200 200 complete_chunk1436

lemma complete_chunk1437 : ∀ i : Fin 200, Compatible (287400 + i.val) →
    (table.lookup (287400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1437 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 287400 287600 :=
  FiniteIntervals.of_fin 287400 200 complete_chunk1437

lemma complete_chunk1438 : ∀ i : Fin 200, Compatible (287600 + i.val) →
    (table.lookup (287600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1438 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 287600 287800 :=
  FiniteIntervals.of_fin 287600 200 complete_chunk1438

lemma complete_chunk1439 : ∀ i : Fin 200, Compatible (287800 + i.val) →
    (table.lookup (287800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1439 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 287800 288000 :=
  FiniteIntervals.of_fin 287800 200 complete_chunk1439

#print axioms interval_chunk1430
end Erdos184Work.PureFiveFilter4
