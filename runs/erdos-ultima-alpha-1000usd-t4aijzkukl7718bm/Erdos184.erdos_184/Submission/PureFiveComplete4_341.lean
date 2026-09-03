import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3410 : ∀ i : Fin 200, Compatible (682000 + i.val) →
    (table.lookup (682000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3410 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 682000 682200 :=
  FiniteIntervals.of_fin 682000 200 complete_chunk3410

lemma complete_chunk3411 : ∀ i : Fin 200, Compatible (682200 + i.val) →
    (table.lookup (682200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3411 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 682200 682400 :=
  FiniteIntervals.of_fin 682200 200 complete_chunk3411

lemma complete_chunk3412 : ∀ i : Fin 200, Compatible (682400 + i.val) →
    (table.lookup (682400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3412 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 682400 682600 :=
  FiniteIntervals.of_fin 682400 200 complete_chunk3412

lemma complete_chunk3413 : ∀ i : Fin 200, Compatible (682600 + i.val) →
    (table.lookup (682600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3413 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 682600 682800 :=
  FiniteIntervals.of_fin 682600 200 complete_chunk3413

lemma complete_chunk3414 : ∀ i : Fin 200, Compatible (682800 + i.val) →
    (table.lookup (682800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3414 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 682800 683000 :=
  FiniteIntervals.of_fin 682800 200 complete_chunk3414

lemma complete_chunk3415 : ∀ i : Fin 200, Compatible (683000 + i.val) →
    (table.lookup (683000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3415 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 683000 683200 :=
  FiniteIntervals.of_fin 683000 200 complete_chunk3415

lemma complete_chunk3416 : ∀ i : Fin 200, Compatible (683200 + i.val) →
    (table.lookup (683200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3416 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 683200 683400 :=
  FiniteIntervals.of_fin 683200 200 complete_chunk3416

lemma complete_chunk3417 : ∀ i : Fin 200, Compatible (683400 + i.val) →
    (table.lookup (683400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3417 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 683400 683600 :=
  FiniteIntervals.of_fin 683400 200 complete_chunk3417

lemma complete_chunk3418 : ∀ i : Fin 200, Compatible (683600 + i.val) →
    (table.lookup (683600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3418 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 683600 683800 :=
  FiniteIntervals.of_fin 683600 200 complete_chunk3418

lemma complete_chunk3419 : ∀ i : Fin 200, Compatible (683800 + i.val) →
    (table.lookup (683800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3419 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 683800 684000 :=
  FiniteIntervals.of_fin 683800 200 complete_chunk3419

#print axioms interval_chunk3410
end Erdos184Work.PureFiveFilter4
