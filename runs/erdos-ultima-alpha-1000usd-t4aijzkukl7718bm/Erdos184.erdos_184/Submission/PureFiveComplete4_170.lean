import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1700 : ∀ i : Fin 200, Compatible (340000 + i.val) →
    (table.lookup (340000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1700 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 340000 340200 :=
  FiniteIntervals.of_fin 340000 200 complete_chunk1700

lemma complete_chunk1701 : ∀ i : Fin 200, Compatible (340200 + i.val) →
    (table.lookup (340200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1701 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 340200 340400 :=
  FiniteIntervals.of_fin 340200 200 complete_chunk1701

lemma complete_chunk1702 : ∀ i : Fin 200, Compatible (340400 + i.val) →
    (table.lookup (340400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1702 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 340400 340600 :=
  FiniteIntervals.of_fin 340400 200 complete_chunk1702

lemma complete_chunk1703 : ∀ i : Fin 200, Compatible (340600 + i.val) →
    (table.lookup (340600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1703 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 340600 340800 :=
  FiniteIntervals.of_fin 340600 200 complete_chunk1703

lemma complete_chunk1704 : ∀ i : Fin 200, Compatible (340800 + i.val) →
    (table.lookup (340800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1704 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 340800 341000 :=
  FiniteIntervals.of_fin 340800 200 complete_chunk1704

lemma complete_chunk1705 : ∀ i : Fin 200, Compatible (341000 + i.val) →
    (table.lookup (341000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1705 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 341000 341200 :=
  FiniteIntervals.of_fin 341000 200 complete_chunk1705

lemma complete_chunk1706 : ∀ i : Fin 200, Compatible (341200 + i.val) →
    (table.lookup (341200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1706 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 341200 341400 :=
  FiniteIntervals.of_fin 341200 200 complete_chunk1706

lemma complete_chunk1707 : ∀ i : Fin 200, Compatible (341400 + i.val) →
    (table.lookup (341400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1707 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 341400 341600 :=
  FiniteIntervals.of_fin 341400 200 complete_chunk1707

lemma complete_chunk1708 : ∀ i : Fin 200, Compatible (341600 + i.val) →
    (table.lookup (341600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1708 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 341600 341800 :=
  FiniteIntervals.of_fin 341600 200 complete_chunk1708

lemma complete_chunk1709 : ∀ i : Fin 200, Compatible (341800 + i.val) →
    (table.lookup (341800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1709 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 341800 342000 :=
  FiniteIntervals.of_fin 341800 200 complete_chunk1709

#print axioms interval_chunk1700
end Erdos184Work.PureFiveFilter4
