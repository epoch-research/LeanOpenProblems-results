import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1460 : ∀ i : Fin 200, Compatible (292000 + i.val) →
    (table.lookup (292000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1460 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 292000 292200 :=
  FiniteIntervals.of_fin 292000 200 complete_chunk1460

lemma complete_chunk1461 : ∀ i : Fin 200, Compatible (292200 + i.val) →
    (table.lookup (292200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1461 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 292200 292400 :=
  FiniteIntervals.of_fin 292200 200 complete_chunk1461

lemma complete_chunk1462 : ∀ i : Fin 200, Compatible (292400 + i.val) →
    (table.lookup (292400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1462 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 292400 292600 :=
  FiniteIntervals.of_fin 292400 200 complete_chunk1462

lemma complete_chunk1463 : ∀ i : Fin 200, Compatible (292600 + i.val) →
    (table.lookup (292600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1463 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 292600 292800 :=
  FiniteIntervals.of_fin 292600 200 complete_chunk1463

lemma complete_chunk1464 : ∀ i : Fin 200, Compatible (292800 + i.val) →
    (table.lookup (292800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1464 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 292800 293000 :=
  FiniteIntervals.of_fin 292800 200 complete_chunk1464

lemma complete_chunk1465 : ∀ i : Fin 200, Compatible (293000 + i.val) →
    (table.lookup (293000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1465 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 293000 293200 :=
  FiniteIntervals.of_fin 293000 200 complete_chunk1465

lemma complete_chunk1466 : ∀ i : Fin 200, Compatible (293200 + i.val) →
    (table.lookup (293200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1466 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 293200 293400 :=
  FiniteIntervals.of_fin 293200 200 complete_chunk1466

lemma complete_chunk1467 : ∀ i : Fin 200, Compatible (293400 + i.val) →
    (table.lookup (293400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1467 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 293400 293600 :=
  FiniteIntervals.of_fin 293400 200 complete_chunk1467

lemma complete_chunk1468 : ∀ i : Fin 200, Compatible (293600 + i.val) →
    (table.lookup (293600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1468 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 293600 293800 :=
  FiniteIntervals.of_fin 293600 200 complete_chunk1468

lemma complete_chunk1469 : ∀ i : Fin 200, Compatible (293800 + i.val) →
    (table.lookup (293800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1469 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 293800 294000 :=
  FiniteIntervals.of_fin 293800 200 complete_chunk1469

#print axioms interval_chunk1460
end Erdos184Work.PureFiveFilter4
