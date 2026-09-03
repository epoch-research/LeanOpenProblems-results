import Submission.PureFiveFilter1
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter1
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk0 : ∀ i : Fin 1000, Compatible (0 + i.val) →
    (table.lookup (0 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 0 1000 :=
  FiniteIntervals.of_fin 0 1000 complete_chunk0

lemma complete_chunk1 : ∀ i : Fin 1000, Compatible (1000 + i.val) →
    (table.lookup (1000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1000 2000 :=
  FiniteIntervals.of_fin 1000 1000 complete_chunk1

lemma complete_chunk2 : ∀ i : Fin 1000, Compatible (2000 + i.val) →
    (table.lookup (2000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 2000 3000 :=
  FiniteIntervals.of_fin 2000 1000 complete_chunk2

lemma complete_chunk3 : ∀ i : Fin 888, Compatible (3000 + i.val) →
    (table.lookup (3000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 3000 3888 :=
  FiniteIntervals.of_fin 3000 888 complete_chunk3

#print axioms interval_chunk0
end Erdos184Work.PureFiveFilter1
