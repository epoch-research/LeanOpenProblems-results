import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1500 : ∀ i : Fin 200, Compatible (300000 + i.val) →
    (table.lookup (300000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1500 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 300000 300200 :=
  FiniteIntervals.of_fin 300000 200 complete_chunk1500

lemma complete_chunk1501 : ∀ i : Fin 200, Compatible (300200 + i.val) →
    (table.lookup (300200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1501 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 300200 300400 :=
  FiniteIntervals.of_fin 300200 200 complete_chunk1501

lemma complete_chunk1502 : ∀ i : Fin 200, Compatible (300400 + i.val) →
    (table.lookup (300400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1502 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 300400 300600 :=
  FiniteIntervals.of_fin 300400 200 complete_chunk1502

lemma complete_chunk1503 : ∀ i : Fin 200, Compatible (300600 + i.val) →
    (table.lookup (300600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1503 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 300600 300800 :=
  FiniteIntervals.of_fin 300600 200 complete_chunk1503

lemma complete_chunk1504 : ∀ i : Fin 200, Compatible (300800 + i.val) →
    (table.lookup (300800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1504 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 300800 301000 :=
  FiniteIntervals.of_fin 300800 200 complete_chunk1504

lemma complete_chunk1505 : ∀ i : Fin 200, Compatible (301000 + i.val) →
    (table.lookup (301000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1505 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 301000 301200 :=
  FiniteIntervals.of_fin 301000 200 complete_chunk1505

lemma complete_chunk1506 : ∀ i : Fin 200, Compatible (301200 + i.val) →
    (table.lookup (301200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1506 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 301200 301400 :=
  FiniteIntervals.of_fin 301200 200 complete_chunk1506

lemma complete_chunk1507 : ∀ i : Fin 200, Compatible (301400 + i.val) →
    (table.lookup (301400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1507 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 301400 301600 :=
  FiniteIntervals.of_fin 301400 200 complete_chunk1507

lemma complete_chunk1508 : ∀ i : Fin 200, Compatible (301600 + i.val) →
    (table.lookup (301600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1508 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 301600 301800 :=
  FiniteIntervals.of_fin 301600 200 complete_chunk1508

lemma complete_chunk1509 : ∀ i : Fin 200, Compatible (301800 + i.val) →
    (table.lookup (301800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1509 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 301800 302000 :=
  FiniteIntervals.of_fin 301800 200 complete_chunk1509

#print axioms interval_chunk1500
end Erdos184Work.PureFiveFilter4
