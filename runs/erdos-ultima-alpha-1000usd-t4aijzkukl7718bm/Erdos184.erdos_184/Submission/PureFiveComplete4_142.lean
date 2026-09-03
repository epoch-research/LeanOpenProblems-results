import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1420 : ∀ i : Fin 200, Compatible (284000 + i.val) →
    (table.lookup (284000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1420 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 284000 284200 :=
  FiniteIntervals.of_fin 284000 200 complete_chunk1420

lemma complete_chunk1421 : ∀ i : Fin 200, Compatible (284200 + i.val) →
    (table.lookup (284200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1421 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 284200 284400 :=
  FiniteIntervals.of_fin 284200 200 complete_chunk1421

lemma complete_chunk1422 : ∀ i : Fin 200, Compatible (284400 + i.val) →
    (table.lookup (284400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1422 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 284400 284600 :=
  FiniteIntervals.of_fin 284400 200 complete_chunk1422

lemma complete_chunk1423 : ∀ i : Fin 200, Compatible (284600 + i.val) →
    (table.lookup (284600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1423 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 284600 284800 :=
  FiniteIntervals.of_fin 284600 200 complete_chunk1423

lemma complete_chunk1424 : ∀ i : Fin 200, Compatible (284800 + i.val) →
    (table.lookup (284800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1424 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 284800 285000 :=
  FiniteIntervals.of_fin 284800 200 complete_chunk1424

lemma complete_chunk1425 : ∀ i : Fin 200, Compatible (285000 + i.val) →
    (table.lookup (285000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1425 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 285000 285200 :=
  FiniteIntervals.of_fin 285000 200 complete_chunk1425

lemma complete_chunk1426 : ∀ i : Fin 200, Compatible (285200 + i.val) →
    (table.lookup (285200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1426 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 285200 285400 :=
  FiniteIntervals.of_fin 285200 200 complete_chunk1426

lemma complete_chunk1427 : ∀ i : Fin 200, Compatible (285400 + i.val) →
    (table.lookup (285400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1427 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 285400 285600 :=
  FiniteIntervals.of_fin 285400 200 complete_chunk1427

lemma complete_chunk1428 : ∀ i : Fin 200, Compatible (285600 + i.val) →
    (table.lookup (285600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1428 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 285600 285800 :=
  FiniteIntervals.of_fin 285600 200 complete_chunk1428

lemma complete_chunk1429 : ∀ i : Fin 200, Compatible (285800 + i.val) →
    (table.lookup (285800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1429 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 285800 286000 :=
  FiniteIntervals.of_fin 285800 200 complete_chunk1429

#print axioms interval_chunk1420
end Erdos184Work.PureFiveFilter4
