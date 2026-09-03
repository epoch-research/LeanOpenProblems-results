import Submission.PureFiveFilter2
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter2
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

lemma complete_chunk3 : ∀ i : Fin 1000, Compatible (3000 + i.val) →
    (table.lookup (3000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 3000 4000 :=
  FiniteIntervals.of_fin 3000 1000 complete_chunk3

lemma complete_chunk4 : ∀ i : Fin 1000, Compatible (4000 + i.val) →
    (table.lookup (4000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 4000 5000 :=
  FiniteIntervals.of_fin 4000 1000 complete_chunk4

lemma complete_chunk5 : ∀ i : Fin 1000, Compatible (5000 + i.val) →
    (table.lookup (5000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 5000 6000 :=
  FiniteIntervals.of_fin 5000 1000 complete_chunk5

lemma complete_chunk6 : ∀ i : Fin 1000, Compatible (6000 + i.val) →
    (table.lookup (6000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 6000 7000 :=
  FiniteIntervals.of_fin 6000 1000 complete_chunk6

lemma complete_chunk7 : ∀ i : Fin 1000, Compatible (7000 + i.val) →
    (table.lookup (7000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk7 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 7000 8000 :=
  FiniteIntervals.of_fin 7000 1000 complete_chunk7

lemma complete_chunk8 : ∀ i : Fin 1000, Compatible (8000 + i.val) →
    (table.lookup (8000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk8 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 8000 9000 :=
  FiniteIntervals.of_fin 8000 1000 complete_chunk8

lemma complete_chunk9 : ∀ i : Fin 1000, Compatible (9000 + i.val) →
    (table.lookup (9000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk9 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 9000 10000 :=
  FiniteIntervals.of_fin 9000 1000 complete_chunk9

#print axioms interval_chunk0
end Erdos184Work.PureFiveFilter2
