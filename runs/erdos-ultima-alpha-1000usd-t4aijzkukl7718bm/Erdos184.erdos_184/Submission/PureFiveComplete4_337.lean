import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3370 : ∀ i : Fin 200, Compatible (674000 + i.val) →
    (table.lookup (674000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3370 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 674000 674200 :=
  FiniteIntervals.of_fin 674000 200 complete_chunk3370

lemma complete_chunk3371 : ∀ i : Fin 200, Compatible (674200 + i.val) →
    (table.lookup (674200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3371 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 674200 674400 :=
  FiniteIntervals.of_fin 674200 200 complete_chunk3371

lemma complete_chunk3372 : ∀ i : Fin 200, Compatible (674400 + i.val) →
    (table.lookup (674400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3372 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 674400 674600 :=
  FiniteIntervals.of_fin 674400 200 complete_chunk3372

lemma complete_chunk3373 : ∀ i : Fin 200, Compatible (674600 + i.val) →
    (table.lookup (674600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3373 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 674600 674800 :=
  FiniteIntervals.of_fin 674600 200 complete_chunk3373

lemma complete_chunk3374 : ∀ i : Fin 200, Compatible (674800 + i.val) →
    (table.lookup (674800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3374 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 674800 675000 :=
  FiniteIntervals.of_fin 674800 200 complete_chunk3374

lemma complete_chunk3375 : ∀ i : Fin 200, Compatible (675000 + i.val) →
    (table.lookup (675000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3375 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 675000 675200 :=
  FiniteIntervals.of_fin 675000 200 complete_chunk3375

lemma complete_chunk3376 : ∀ i : Fin 200, Compatible (675200 + i.val) →
    (table.lookup (675200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3376 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 675200 675400 :=
  FiniteIntervals.of_fin 675200 200 complete_chunk3376

lemma complete_chunk3377 : ∀ i : Fin 200, Compatible (675400 + i.val) →
    (table.lookup (675400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3377 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 675400 675600 :=
  FiniteIntervals.of_fin 675400 200 complete_chunk3377

lemma complete_chunk3378 : ∀ i : Fin 200, Compatible (675600 + i.val) →
    (table.lookup (675600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3378 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 675600 675800 :=
  FiniteIntervals.of_fin 675600 200 complete_chunk3378

lemma complete_chunk3379 : ∀ i : Fin 200, Compatible (675800 + i.val) →
    (table.lookup (675800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3379 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 675800 676000 :=
  FiniteIntervals.of_fin 675800 200 complete_chunk3379

#print axioms interval_chunk3370
end Erdos184Work.PureFiveFilter4
