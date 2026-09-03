import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5670 : ∀ i : Fin 200, Compatible (1134000 + i.val) →
    (table.lookup (1134000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5670 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1134000 1134200 :=
  FiniteIntervals.of_fin 1134000 200 complete_chunk5670

lemma complete_chunk5671 : ∀ i : Fin 200, Compatible (1134200 + i.val) →
    (table.lookup (1134200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5671 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1134200 1134400 :=
  FiniteIntervals.of_fin 1134200 200 complete_chunk5671

lemma complete_chunk5672 : ∀ i : Fin 200, Compatible (1134400 + i.val) →
    (table.lookup (1134400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5672 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1134400 1134600 :=
  FiniteIntervals.of_fin 1134400 200 complete_chunk5672

lemma complete_chunk5673 : ∀ i : Fin 200, Compatible (1134600 + i.val) →
    (table.lookup (1134600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5673 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1134600 1134800 :=
  FiniteIntervals.of_fin 1134600 200 complete_chunk5673

lemma complete_chunk5674 : ∀ i : Fin 200, Compatible (1134800 + i.val) →
    (table.lookup (1134800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5674 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1134800 1135000 :=
  FiniteIntervals.of_fin 1134800 200 complete_chunk5674

lemma complete_chunk5675 : ∀ i : Fin 200, Compatible (1135000 + i.val) →
    (table.lookup (1135000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5675 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1135000 1135200 :=
  FiniteIntervals.of_fin 1135000 200 complete_chunk5675

lemma complete_chunk5676 : ∀ i : Fin 200, Compatible (1135200 + i.val) →
    (table.lookup (1135200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5676 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1135200 1135400 :=
  FiniteIntervals.of_fin 1135200 200 complete_chunk5676

lemma complete_chunk5677 : ∀ i : Fin 200, Compatible (1135400 + i.val) →
    (table.lookup (1135400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5677 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1135400 1135600 :=
  FiniteIntervals.of_fin 1135400 200 complete_chunk5677

lemma complete_chunk5678 : ∀ i : Fin 200, Compatible (1135600 + i.val) →
    (table.lookup (1135600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5678 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1135600 1135800 :=
  FiniteIntervals.of_fin 1135600 200 complete_chunk5678

lemma complete_chunk5679 : ∀ i : Fin 200, Compatible (1135800 + i.val) →
    (table.lookup (1135800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5679 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1135800 1136000 :=
  FiniteIntervals.of_fin 1135800 200 complete_chunk5679

#print axioms interval_chunk5670
end Erdos184Work.PureFiveFilter4
