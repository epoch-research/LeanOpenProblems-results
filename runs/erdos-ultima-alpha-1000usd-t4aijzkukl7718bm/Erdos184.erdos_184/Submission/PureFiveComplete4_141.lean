import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1410 : ∀ i : Fin 200, Compatible (282000 + i.val) →
    (table.lookup (282000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1410 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 282000 282200 :=
  FiniteIntervals.of_fin 282000 200 complete_chunk1410

lemma complete_chunk1411 : ∀ i : Fin 200, Compatible (282200 + i.val) →
    (table.lookup (282200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1411 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 282200 282400 :=
  FiniteIntervals.of_fin 282200 200 complete_chunk1411

lemma complete_chunk1412 : ∀ i : Fin 200, Compatible (282400 + i.val) →
    (table.lookup (282400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1412 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 282400 282600 :=
  FiniteIntervals.of_fin 282400 200 complete_chunk1412

lemma complete_chunk1413 : ∀ i : Fin 200, Compatible (282600 + i.val) →
    (table.lookup (282600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1413 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 282600 282800 :=
  FiniteIntervals.of_fin 282600 200 complete_chunk1413

lemma complete_chunk1414 : ∀ i : Fin 200, Compatible (282800 + i.val) →
    (table.lookup (282800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1414 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 282800 283000 :=
  FiniteIntervals.of_fin 282800 200 complete_chunk1414

lemma complete_chunk1415 : ∀ i : Fin 200, Compatible (283000 + i.val) →
    (table.lookup (283000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1415 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 283000 283200 :=
  FiniteIntervals.of_fin 283000 200 complete_chunk1415

lemma complete_chunk1416 : ∀ i : Fin 200, Compatible (283200 + i.val) →
    (table.lookup (283200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1416 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 283200 283400 :=
  FiniteIntervals.of_fin 283200 200 complete_chunk1416

lemma complete_chunk1417 : ∀ i : Fin 200, Compatible (283400 + i.val) →
    (table.lookup (283400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1417 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 283400 283600 :=
  FiniteIntervals.of_fin 283400 200 complete_chunk1417

lemma complete_chunk1418 : ∀ i : Fin 200, Compatible (283600 + i.val) →
    (table.lookup (283600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1418 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 283600 283800 :=
  FiniteIntervals.of_fin 283600 200 complete_chunk1418

lemma complete_chunk1419 : ∀ i : Fin 200, Compatible (283800 + i.val) →
    (table.lookup (283800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1419 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 283800 284000 :=
  FiniteIntervals.of_fin 283800 200 complete_chunk1419

#print axioms interval_chunk1410
end Erdos184Work.PureFiveFilter4
