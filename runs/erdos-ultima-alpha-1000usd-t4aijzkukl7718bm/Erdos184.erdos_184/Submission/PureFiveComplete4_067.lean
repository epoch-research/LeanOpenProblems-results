import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk670 : ∀ i : Fin 200, Compatible (134000 + i.val) →
    (table.lookup (134000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk670 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 134000 134200 :=
  FiniteIntervals.of_fin 134000 200 complete_chunk670

lemma complete_chunk671 : ∀ i : Fin 200, Compatible (134200 + i.val) →
    (table.lookup (134200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk671 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 134200 134400 :=
  FiniteIntervals.of_fin 134200 200 complete_chunk671

lemma complete_chunk672 : ∀ i : Fin 200, Compatible (134400 + i.val) →
    (table.lookup (134400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk672 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 134400 134600 :=
  FiniteIntervals.of_fin 134400 200 complete_chunk672

lemma complete_chunk673 : ∀ i : Fin 200, Compatible (134600 + i.val) →
    (table.lookup (134600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk673 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 134600 134800 :=
  FiniteIntervals.of_fin 134600 200 complete_chunk673

lemma complete_chunk674 : ∀ i : Fin 200, Compatible (134800 + i.val) →
    (table.lookup (134800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk674 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 134800 135000 :=
  FiniteIntervals.of_fin 134800 200 complete_chunk674

lemma complete_chunk675 : ∀ i : Fin 200, Compatible (135000 + i.val) →
    (table.lookup (135000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk675 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 135000 135200 :=
  FiniteIntervals.of_fin 135000 200 complete_chunk675

lemma complete_chunk676 : ∀ i : Fin 200, Compatible (135200 + i.val) →
    (table.lookup (135200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk676 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 135200 135400 :=
  FiniteIntervals.of_fin 135200 200 complete_chunk676

lemma complete_chunk677 : ∀ i : Fin 200, Compatible (135400 + i.val) →
    (table.lookup (135400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk677 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 135400 135600 :=
  FiniteIntervals.of_fin 135400 200 complete_chunk677

lemma complete_chunk678 : ∀ i : Fin 200, Compatible (135600 + i.val) →
    (table.lookup (135600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk678 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 135600 135800 :=
  FiniteIntervals.of_fin 135600 200 complete_chunk678

lemma complete_chunk679 : ∀ i : Fin 200, Compatible (135800 + i.val) →
    (table.lookup (135800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk679 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 135800 136000 :=
  FiniteIntervals.of_fin 135800 200 complete_chunk679

#print axioms interval_chunk670
end Erdos184Work.PureFiveFilter4
