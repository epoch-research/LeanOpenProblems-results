import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1470 : ∀ i : Fin 200, Compatible (294000 + i.val) →
    (table.lookup (294000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1470 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 294000 294200 :=
  FiniteIntervals.of_fin 294000 200 complete_chunk1470

lemma complete_chunk1471 : ∀ i : Fin 200, Compatible (294200 + i.val) →
    (table.lookup (294200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1471 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 294200 294400 :=
  FiniteIntervals.of_fin 294200 200 complete_chunk1471

lemma complete_chunk1472 : ∀ i : Fin 200, Compatible (294400 + i.val) →
    (table.lookup (294400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1472 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 294400 294600 :=
  FiniteIntervals.of_fin 294400 200 complete_chunk1472

lemma complete_chunk1473 : ∀ i : Fin 200, Compatible (294600 + i.val) →
    (table.lookup (294600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1473 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 294600 294800 :=
  FiniteIntervals.of_fin 294600 200 complete_chunk1473

lemma complete_chunk1474 : ∀ i : Fin 200, Compatible (294800 + i.val) →
    (table.lookup (294800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1474 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 294800 295000 :=
  FiniteIntervals.of_fin 294800 200 complete_chunk1474

lemma complete_chunk1475 : ∀ i : Fin 200, Compatible (295000 + i.val) →
    (table.lookup (295000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1475 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 295000 295200 :=
  FiniteIntervals.of_fin 295000 200 complete_chunk1475

lemma complete_chunk1476 : ∀ i : Fin 200, Compatible (295200 + i.val) →
    (table.lookup (295200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1476 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 295200 295400 :=
  FiniteIntervals.of_fin 295200 200 complete_chunk1476

lemma complete_chunk1477 : ∀ i : Fin 200, Compatible (295400 + i.val) →
    (table.lookup (295400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1477 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 295400 295600 :=
  FiniteIntervals.of_fin 295400 200 complete_chunk1477

lemma complete_chunk1478 : ∀ i : Fin 200, Compatible (295600 + i.val) →
    (table.lookup (295600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1478 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 295600 295800 :=
  FiniteIntervals.of_fin 295600 200 complete_chunk1478

lemma complete_chunk1479 : ∀ i : Fin 200, Compatible (295800 + i.val) →
    (table.lookup (295800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1479 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 295800 296000 :=
  FiniteIntervals.of_fin 295800 200 complete_chunk1479

#print axioms interval_chunk1470
end Erdos184Work.PureFiveFilter4
