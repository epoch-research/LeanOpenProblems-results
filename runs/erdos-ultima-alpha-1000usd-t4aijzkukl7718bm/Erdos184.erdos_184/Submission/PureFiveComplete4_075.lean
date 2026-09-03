import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk750 : ∀ i : Fin 200, Compatible (150000 + i.val) →
    (table.lookup (150000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk750 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 150000 150200 :=
  FiniteIntervals.of_fin 150000 200 complete_chunk750

lemma complete_chunk751 : ∀ i : Fin 200, Compatible (150200 + i.val) →
    (table.lookup (150200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk751 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 150200 150400 :=
  FiniteIntervals.of_fin 150200 200 complete_chunk751

lemma complete_chunk752 : ∀ i : Fin 200, Compatible (150400 + i.val) →
    (table.lookup (150400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk752 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 150400 150600 :=
  FiniteIntervals.of_fin 150400 200 complete_chunk752

lemma complete_chunk753 : ∀ i : Fin 200, Compatible (150600 + i.val) →
    (table.lookup (150600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk753 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 150600 150800 :=
  FiniteIntervals.of_fin 150600 200 complete_chunk753

lemma complete_chunk754 : ∀ i : Fin 200, Compatible (150800 + i.val) →
    (table.lookup (150800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk754 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 150800 151000 :=
  FiniteIntervals.of_fin 150800 200 complete_chunk754

lemma complete_chunk755 : ∀ i : Fin 200, Compatible (151000 + i.val) →
    (table.lookup (151000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk755 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 151000 151200 :=
  FiniteIntervals.of_fin 151000 200 complete_chunk755

lemma complete_chunk756 : ∀ i : Fin 200, Compatible (151200 + i.val) →
    (table.lookup (151200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk756 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 151200 151400 :=
  FiniteIntervals.of_fin 151200 200 complete_chunk756

lemma complete_chunk757 : ∀ i : Fin 200, Compatible (151400 + i.val) →
    (table.lookup (151400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk757 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 151400 151600 :=
  FiniteIntervals.of_fin 151400 200 complete_chunk757

lemma complete_chunk758 : ∀ i : Fin 200, Compatible (151600 + i.val) →
    (table.lookup (151600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk758 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 151600 151800 :=
  FiniteIntervals.of_fin 151600 200 complete_chunk758

lemma complete_chunk759 : ∀ i : Fin 200, Compatible (151800 + i.val) →
    (table.lookup (151800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk759 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 151800 152000 :=
  FiniteIntervals.of_fin 151800 200 complete_chunk759

#print axioms interval_chunk750
end Erdos184Work.PureFiveFilter4
