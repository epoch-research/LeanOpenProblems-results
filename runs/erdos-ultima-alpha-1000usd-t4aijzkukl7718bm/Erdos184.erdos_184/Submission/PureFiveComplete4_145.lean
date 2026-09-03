import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1450 : ∀ i : Fin 200, Compatible (290000 + i.val) →
    (table.lookup (290000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1450 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 290000 290200 :=
  FiniteIntervals.of_fin 290000 200 complete_chunk1450

lemma complete_chunk1451 : ∀ i : Fin 200, Compatible (290200 + i.val) →
    (table.lookup (290200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1451 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 290200 290400 :=
  FiniteIntervals.of_fin 290200 200 complete_chunk1451

lemma complete_chunk1452 : ∀ i : Fin 200, Compatible (290400 + i.val) →
    (table.lookup (290400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1452 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 290400 290600 :=
  FiniteIntervals.of_fin 290400 200 complete_chunk1452

lemma complete_chunk1453 : ∀ i : Fin 200, Compatible (290600 + i.val) →
    (table.lookup (290600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1453 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 290600 290800 :=
  FiniteIntervals.of_fin 290600 200 complete_chunk1453

lemma complete_chunk1454 : ∀ i : Fin 200, Compatible (290800 + i.val) →
    (table.lookup (290800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1454 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 290800 291000 :=
  FiniteIntervals.of_fin 290800 200 complete_chunk1454

lemma complete_chunk1455 : ∀ i : Fin 200, Compatible (291000 + i.val) →
    (table.lookup (291000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1455 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 291000 291200 :=
  FiniteIntervals.of_fin 291000 200 complete_chunk1455

lemma complete_chunk1456 : ∀ i : Fin 200, Compatible (291200 + i.val) →
    (table.lookup (291200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1456 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 291200 291400 :=
  FiniteIntervals.of_fin 291200 200 complete_chunk1456

lemma complete_chunk1457 : ∀ i : Fin 200, Compatible (291400 + i.val) →
    (table.lookup (291400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1457 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 291400 291600 :=
  FiniteIntervals.of_fin 291400 200 complete_chunk1457

lemma complete_chunk1458 : ∀ i : Fin 200, Compatible (291600 + i.val) →
    (table.lookup (291600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1458 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 291600 291800 :=
  FiniteIntervals.of_fin 291600 200 complete_chunk1458

lemma complete_chunk1459 : ∀ i : Fin 200, Compatible (291800 + i.val) →
    (table.lookup (291800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1459 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 291800 292000 :=
  FiniteIntervals.of_fin 291800 200 complete_chunk1459

#print axioms interval_chunk1450
end Erdos184Work.PureFiveFilter4
