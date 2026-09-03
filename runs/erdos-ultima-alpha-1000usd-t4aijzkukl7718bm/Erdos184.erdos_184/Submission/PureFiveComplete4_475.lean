import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4750 : ∀ i : Fin 200, Compatible (950000 + i.val) →
    (table.lookup (950000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4750 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 950000 950200 :=
  FiniteIntervals.of_fin 950000 200 complete_chunk4750

lemma complete_chunk4751 : ∀ i : Fin 200, Compatible (950200 + i.val) →
    (table.lookup (950200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4751 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 950200 950400 :=
  FiniteIntervals.of_fin 950200 200 complete_chunk4751

lemma complete_chunk4752 : ∀ i : Fin 200, Compatible (950400 + i.val) →
    (table.lookup (950400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4752 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 950400 950600 :=
  FiniteIntervals.of_fin 950400 200 complete_chunk4752

lemma complete_chunk4753 : ∀ i : Fin 200, Compatible (950600 + i.val) →
    (table.lookup (950600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4753 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 950600 950800 :=
  FiniteIntervals.of_fin 950600 200 complete_chunk4753

lemma complete_chunk4754 : ∀ i : Fin 200, Compatible (950800 + i.val) →
    (table.lookup (950800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4754 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 950800 951000 :=
  FiniteIntervals.of_fin 950800 200 complete_chunk4754

lemma complete_chunk4755 : ∀ i : Fin 200, Compatible (951000 + i.val) →
    (table.lookup (951000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4755 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 951000 951200 :=
  FiniteIntervals.of_fin 951000 200 complete_chunk4755

lemma complete_chunk4756 : ∀ i : Fin 200, Compatible (951200 + i.val) →
    (table.lookup (951200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4756 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 951200 951400 :=
  FiniteIntervals.of_fin 951200 200 complete_chunk4756

lemma complete_chunk4757 : ∀ i : Fin 200, Compatible (951400 + i.val) →
    (table.lookup (951400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4757 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 951400 951600 :=
  FiniteIntervals.of_fin 951400 200 complete_chunk4757

lemma complete_chunk4758 : ∀ i : Fin 200, Compatible (951600 + i.val) →
    (table.lookup (951600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4758 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 951600 951800 :=
  FiniteIntervals.of_fin 951600 200 complete_chunk4758

lemma complete_chunk4759 : ∀ i : Fin 200, Compatible (951800 + i.val) →
    (table.lookup (951800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4759 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 951800 952000 :=
  FiniteIntervals.of_fin 951800 200 complete_chunk4759

#print axioms interval_chunk4750
end Erdos184Work.PureFiveFilter4
