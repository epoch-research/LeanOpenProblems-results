import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2450 : ∀ i : Fin 200, Compatible (490000 + i.val) →
    (table.lookup (490000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2450 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 490000 490200 :=
  FiniteIntervals.of_fin 490000 200 complete_chunk2450

lemma complete_chunk2451 : ∀ i : Fin 200, Compatible (490200 + i.val) →
    (table.lookup (490200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2451 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 490200 490400 :=
  FiniteIntervals.of_fin 490200 200 complete_chunk2451

lemma complete_chunk2452 : ∀ i : Fin 200, Compatible (490400 + i.val) →
    (table.lookup (490400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2452 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 490400 490600 :=
  FiniteIntervals.of_fin 490400 200 complete_chunk2452

lemma complete_chunk2453 : ∀ i : Fin 200, Compatible (490600 + i.val) →
    (table.lookup (490600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2453 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 490600 490800 :=
  FiniteIntervals.of_fin 490600 200 complete_chunk2453

lemma complete_chunk2454 : ∀ i : Fin 200, Compatible (490800 + i.val) →
    (table.lookup (490800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2454 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 490800 491000 :=
  FiniteIntervals.of_fin 490800 200 complete_chunk2454

lemma complete_chunk2455 : ∀ i : Fin 200, Compatible (491000 + i.val) →
    (table.lookup (491000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2455 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 491000 491200 :=
  FiniteIntervals.of_fin 491000 200 complete_chunk2455

lemma complete_chunk2456 : ∀ i : Fin 200, Compatible (491200 + i.val) →
    (table.lookup (491200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2456 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 491200 491400 :=
  FiniteIntervals.of_fin 491200 200 complete_chunk2456

lemma complete_chunk2457 : ∀ i : Fin 200, Compatible (491400 + i.val) →
    (table.lookup (491400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2457 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 491400 491600 :=
  FiniteIntervals.of_fin 491400 200 complete_chunk2457

lemma complete_chunk2458 : ∀ i : Fin 200, Compatible (491600 + i.val) →
    (table.lookup (491600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2458 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 491600 491800 :=
  FiniteIntervals.of_fin 491600 200 complete_chunk2458

lemma complete_chunk2459 : ∀ i : Fin 200, Compatible (491800 + i.val) →
    (table.lookup (491800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2459 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 491800 492000 :=
  FiniteIntervals.of_fin 491800 200 complete_chunk2459

#print axioms interval_chunk2450
end Erdos184Work.PureFiveFilter4
