import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk810 : ∀ i : Fin 200, Compatible (162000 + i.val) →
    (table.lookup (162000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk810 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 162000 162200 :=
  FiniteIntervals.of_fin 162000 200 complete_chunk810

lemma complete_chunk811 : ∀ i : Fin 200, Compatible (162200 + i.val) →
    (table.lookup (162200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk811 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 162200 162400 :=
  FiniteIntervals.of_fin 162200 200 complete_chunk811

lemma complete_chunk812 : ∀ i : Fin 200, Compatible (162400 + i.val) →
    (table.lookup (162400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk812 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 162400 162600 :=
  FiniteIntervals.of_fin 162400 200 complete_chunk812

lemma complete_chunk813 : ∀ i : Fin 200, Compatible (162600 + i.val) →
    (table.lookup (162600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk813 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 162600 162800 :=
  FiniteIntervals.of_fin 162600 200 complete_chunk813

lemma complete_chunk814 : ∀ i : Fin 200, Compatible (162800 + i.val) →
    (table.lookup (162800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk814 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 162800 163000 :=
  FiniteIntervals.of_fin 162800 200 complete_chunk814

lemma complete_chunk815 : ∀ i : Fin 200, Compatible (163000 + i.val) →
    (table.lookup (163000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk815 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 163000 163200 :=
  FiniteIntervals.of_fin 163000 200 complete_chunk815

lemma complete_chunk816 : ∀ i : Fin 200, Compatible (163200 + i.val) →
    (table.lookup (163200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk816 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 163200 163400 :=
  FiniteIntervals.of_fin 163200 200 complete_chunk816

lemma complete_chunk817 : ∀ i : Fin 200, Compatible (163400 + i.val) →
    (table.lookup (163400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk817 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 163400 163600 :=
  FiniteIntervals.of_fin 163400 200 complete_chunk817

lemma complete_chunk818 : ∀ i : Fin 200, Compatible (163600 + i.val) →
    (table.lookup (163600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk818 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 163600 163800 :=
  FiniteIntervals.of_fin 163600 200 complete_chunk818

lemma complete_chunk819 : ∀ i : Fin 200, Compatible (163800 + i.val) →
    (table.lookup (163800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk819 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 163800 164000 :=
  FiniteIntervals.of_fin 163800 200 complete_chunk819

#print axioms interval_chunk810
end Erdos184Work.PureFiveFilter4
