import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5810 : ∀ i : Fin 200, Compatible (1162000 + i.val) →
    (table.lookup (1162000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5810 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1162000 1162200 :=
  FiniteIntervals.of_fin 1162000 200 complete_chunk5810

lemma complete_chunk5811 : ∀ i : Fin 200, Compatible (1162200 + i.val) →
    (table.lookup (1162200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5811 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1162200 1162400 :=
  FiniteIntervals.of_fin 1162200 200 complete_chunk5811

lemma complete_chunk5812 : ∀ i : Fin 200, Compatible (1162400 + i.val) →
    (table.lookup (1162400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5812 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1162400 1162600 :=
  FiniteIntervals.of_fin 1162400 200 complete_chunk5812

lemma complete_chunk5813 : ∀ i : Fin 200, Compatible (1162600 + i.val) →
    (table.lookup (1162600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5813 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1162600 1162800 :=
  FiniteIntervals.of_fin 1162600 200 complete_chunk5813

lemma complete_chunk5814 : ∀ i : Fin 200, Compatible (1162800 + i.val) →
    (table.lookup (1162800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5814 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1162800 1163000 :=
  FiniteIntervals.of_fin 1162800 200 complete_chunk5814

lemma complete_chunk5815 : ∀ i : Fin 200, Compatible (1163000 + i.val) →
    (table.lookup (1163000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5815 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1163000 1163200 :=
  FiniteIntervals.of_fin 1163000 200 complete_chunk5815

lemma complete_chunk5816 : ∀ i : Fin 200, Compatible (1163200 + i.val) →
    (table.lookup (1163200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5816 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1163200 1163400 :=
  FiniteIntervals.of_fin 1163200 200 complete_chunk5816

lemma complete_chunk5817 : ∀ i : Fin 200, Compatible (1163400 + i.val) →
    (table.lookup (1163400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5817 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1163400 1163600 :=
  FiniteIntervals.of_fin 1163400 200 complete_chunk5817

lemma complete_chunk5818 : ∀ i : Fin 200, Compatible (1163600 + i.val) →
    (table.lookup (1163600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5818 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1163600 1163800 :=
  FiniteIntervals.of_fin 1163600 200 complete_chunk5818

lemma complete_chunk5819 : ∀ i : Fin 200, Compatible (1163800 + i.val) →
    (table.lookup (1163800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5819 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1163800 1164000 :=
  FiniteIntervals.of_fin 1163800 200 complete_chunk5819

#print axioms interval_chunk5810
end Erdos184Work.PureFiveFilter4
