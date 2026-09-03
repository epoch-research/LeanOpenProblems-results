import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1520 : ∀ i : Fin 200, Compatible (304000 + i.val) →
    (table.lookup (304000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1520 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 304000 304200 :=
  FiniteIntervals.of_fin 304000 200 complete_chunk1520

lemma complete_chunk1521 : ∀ i : Fin 200, Compatible (304200 + i.val) →
    (table.lookup (304200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1521 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 304200 304400 :=
  FiniteIntervals.of_fin 304200 200 complete_chunk1521

lemma complete_chunk1522 : ∀ i : Fin 200, Compatible (304400 + i.val) →
    (table.lookup (304400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1522 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 304400 304600 :=
  FiniteIntervals.of_fin 304400 200 complete_chunk1522

lemma complete_chunk1523 : ∀ i : Fin 200, Compatible (304600 + i.val) →
    (table.lookup (304600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1523 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 304600 304800 :=
  FiniteIntervals.of_fin 304600 200 complete_chunk1523

lemma complete_chunk1524 : ∀ i : Fin 200, Compatible (304800 + i.val) →
    (table.lookup (304800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1524 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 304800 305000 :=
  FiniteIntervals.of_fin 304800 200 complete_chunk1524

lemma complete_chunk1525 : ∀ i : Fin 200, Compatible (305000 + i.val) →
    (table.lookup (305000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1525 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 305000 305200 :=
  FiniteIntervals.of_fin 305000 200 complete_chunk1525

lemma complete_chunk1526 : ∀ i : Fin 200, Compatible (305200 + i.val) →
    (table.lookup (305200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1526 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 305200 305400 :=
  FiniteIntervals.of_fin 305200 200 complete_chunk1526

lemma complete_chunk1527 : ∀ i : Fin 200, Compatible (305400 + i.val) →
    (table.lookup (305400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1527 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 305400 305600 :=
  FiniteIntervals.of_fin 305400 200 complete_chunk1527

lemma complete_chunk1528 : ∀ i : Fin 200, Compatible (305600 + i.val) →
    (table.lookup (305600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1528 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 305600 305800 :=
  FiniteIntervals.of_fin 305600 200 complete_chunk1528

lemma complete_chunk1529 : ∀ i : Fin 200, Compatible (305800 + i.val) →
    (table.lookup (305800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1529 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 305800 306000 :=
  FiniteIntervals.of_fin 305800 200 complete_chunk1529

#print axioms interval_chunk1520
end Erdos184Work.PureFiveFilter4
