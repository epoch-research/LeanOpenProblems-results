import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk0 : ∀ i : Fin 200, Compatible (0 + i.val) →
    (table.lookup (0 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 0 200 :=
  FiniteIntervals.of_fin 0 200 complete_chunk0

lemma complete_chunk1 : ∀ i : Fin 200, Compatible (200 + i.val) →
    (table.lookup (200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 200 400 :=
  FiniteIntervals.of_fin 200 200 complete_chunk1

lemma complete_chunk2 : ∀ i : Fin 200, Compatible (400 + i.val) →
    (table.lookup (400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 400 600 :=
  FiniteIntervals.of_fin 400 200 complete_chunk2

lemma complete_chunk3 : ∀ i : Fin 200, Compatible (600 + i.val) →
    (table.lookup (600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 600 800 :=
  FiniteIntervals.of_fin 600 200 complete_chunk3

lemma complete_chunk4 : ∀ i : Fin 200, Compatible (800 + i.val) →
    (table.lookup (800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 800 1000 :=
  FiniteIntervals.of_fin 800 200 complete_chunk4

lemma complete_chunk5 : ∀ i : Fin 200, Compatible (1000 + i.val) →
    (table.lookup (1000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1000 1200 :=
  FiniteIntervals.of_fin 1000 200 complete_chunk5

lemma complete_chunk6 : ∀ i : Fin 200, Compatible (1200 + i.val) →
    (table.lookup (1200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1200 1400 :=
  FiniteIntervals.of_fin 1200 200 complete_chunk6

lemma complete_chunk7 : ∀ i : Fin 200, Compatible (1400 + i.val) →
    (table.lookup (1400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk7 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1400 1600 :=
  FiniteIntervals.of_fin 1400 200 complete_chunk7

lemma complete_chunk8 : ∀ i : Fin 200, Compatible (1600 + i.val) →
    (table.lookup (1600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk8 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1600 1800 :=
  FiniteIntervals.of_fin 1600 200 complete_chunk8

lemma complete_chunk9 : ∀ i : Fin 200, Compatible (1800 + i.val) →
    (table.lookup (1800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk9 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1800 2000 :=
  FiniteIntervals.of_fin 1800 200 complete_chunk9

#print axioms interval_chunk0
end Erdos184Work.PureFiveFilter3
