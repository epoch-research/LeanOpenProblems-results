import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5750 : ∀ i : Fin 200, Compatible (1150000 + i.val) →
    (table.lookup (1150000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5750 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1150000 1150200 :=
  FiniteIntervals.of_fin 1150000 200 complete_chunk5750

lemma complete_chunk5751 : ∀ i : Fin 200, Compatible (1150200 + i.val) →
    (table.lookup (1150200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5751 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1150200 1150400 :=
  FiniteIntervals.of_fin 1150200 200 complete_chunk5751

lemma complete_chunk5752 : ∀ i : Fin 200, Compatible (1150400 + i.val) →
    (table.lookup (1150400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5752 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1150400 1150600 :=
  FiniteIntervals.of_fin 1150400 200 complete_chunk5752

lemma complete_chunk5753 : ∀ i : Fin 200, Compatible (1150600 + i.val) →
    (table.lookup (1150600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5753 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1150600 1150800 :=
  FiniteIntervals.of_fin 1150600 200 complete_chunk5753

lemma complete_chunk5754 : ∀ i : Fin 200, Compatible (1150800 + i.val) →
    (table.lookup (1150800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5754 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1150800 1151000 :=
  FiniteIntervals.of_fin 1150800 200 complete_chunk5754

lemma complete_chunk5755 : ∀ i : Fin 200, Compatible (1151000 + i.val) →
    (table.lookup (1151000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5755 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1151000 1151200 :=
  FiniteIntervals.of_fin 1151000 200 complete_chunk5755

lemma complete_chunk5756 : ∀ i : Fin 200, Compatible (1151200 + i.val) →
    (table.lookup (1151200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5756 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1151200 1151400 :=
  FiniteIntervals.of_fin 1151200 200 complete_chunk5756

lemma complete_chunk5757 : ∀ i : Fin 200, Compatible (1151400 + i.val) →
    (table.lookup (1151400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5757 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1151400 1151600 :=
  FiniteIntervals.of_fin 1151400 200 complete_chunk5757

lemma complete_chunk5758 : ∀ i : Fin 200, Compatible (1151600 + i.val) →
    (table.lookup (1151600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5758 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1151600 1151800 :=
  FiniteIntervals.of_fin 1151600 200 complete_chunk5758

lemma complete_chunk5759 : ∀ i : Fin 200, Compatible (1151800 + i.val) →
    (table.lookup (1151800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5759 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1151800 1152000 :=
  FiniteIntervals.of_fin 1151800 200 complete_chunk5759

#print axioms interval_chunk5750
end Erdos184Work.PureFiveFilter4
