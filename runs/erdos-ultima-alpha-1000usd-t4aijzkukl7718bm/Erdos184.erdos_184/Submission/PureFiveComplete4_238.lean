import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2380 : ∀ i : Fin 200, Compatible (476000 + i.val) →
    (table.lookup (476000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2380 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 476000 476200 :=
  FiniteIntervals.of_fin 476000 200 complete_chunk2380

lemma complete_chunk2381 : ∀ i : Fin 200, Compatible (476200 + i.val) →
    (table.lookup (476200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2381 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 476200 476400 :=
  FiniteIntervals.of_fin 476200 200 complete_chunk2381

lemma complete_chunk2382 : ∀ i : Fin 200, Compatible (476400 + i.val) →
    (table.lookup (476400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2382 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 476400 476600 :=
  FiniteIntervals.of_fin 476400 200 complete_chunk2382

lemma complete_chunk2383 : ∀ i : Fin 200, Compatible (476600 + i.val) →
    (table.lookup (476600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2383 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 476600 476800 :=
  FiniteIntervals.of_fin 476600 200 complete_chunk2383

lemma complete_chunk2384 : ∀ i : Fin 200, Compatible (476800 + i.val) →
    (table.lookup (476800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2384 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 476800 477000 :=
  FiniteIntervals.of_fin 476800 200 complete_chunk2384

lemma complete_chunk2385 : ∀ i : Fin 200, Compatible (477000 + i.val) →
    (table.lookup (477000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2385 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 477000 477200 :=
  FiniteIntervals.of_fin 477000 200 complete_chunk2385

lemma complete_chunk2386 : ∀ i : Fin 200, Compatible (477200 + i.val) →
    (table.lookup (477200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2386 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 477200 477400 :=
  FiniteIntervals.of_fin 477200 200 complete_chunk2386

lemma complete_chunk2387 : ∀ i : Fin 200, Compatible (477400 + i.val) →
    (table.lookup (477400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2387 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 477400 477600 :=
  FiniteIntervals.of_fin 477400 200 complete_chunk2387

lemma complete_chunk2388 : ∀ i : Fin 200, Compatible (477600 + i.val) →
    (table.lookup (477600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2388 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 477600 477800 :=
  FiniteIntervals.of_fin 477600 200 complete_chunk2388

lemma complete_chunk2389 : ∀ i : Fin 200, Compatible (477800 + i.val) →
    (table.lookup (477800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2389 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 477800 478000 :=
  FiniteIntervals.of_fin 477800 200 complete_chunk2389

#print axioms interval_chunk2380
end Erdos184Work.PureFiveFilter4
