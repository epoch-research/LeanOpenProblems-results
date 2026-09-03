import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk740 : ∀ i : Fin 200, Compatible (148000 + i.val) →
    (table.lookup (148000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk740 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 148000 148200 :=
  FiniteIntervals.of_fin 148000 200 complete_chunk740

lemma complete_chunk741 : ∀ i : Fin 200, Compatible (148200 + i.val) →
    (table.lookup (148200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk741 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 148200 148400 :=
  FiniteIntervals.of_fin 148200 200 complete_chunk741

lemma complete_chunk742 : ∀ i : Fin 200, Compatible (148400 + i.val) →
    (table.lookup (148400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk742 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 148400 148600 :=
  FiniteIntervals.of_fin 148400 200 complete_chunk742

lemma complete_chunk743 : ∀ i : Fin 200, Compatible (148600 + i.val) →
    (table.lookup (148600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk743 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 148600 148800 :=
  FiniteIntervals.of_fin 148600 200 complete_chunk743

lemma complete_chunk744 : ∀ i : Fin 200, Compatible (148800 + i.val) →
    (table.lookup (148800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk744 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 148800 149000 :=
  FiniteIntervals.of_fin 148800 200 complete_chunk744

lemma complete_chunk745 : ∀ i : Fin 200, Compatible (149000 + i.val) →
    (table.lookup (149000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk745 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 149000 149200 :=
  FiniteIntervals.of_fin 149000 200 complete_chunk745

lemma complete_chunk746 : ∀ i : Fin 200, Compatible (149200 + i.val) →
    (table.lookup (149200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk746 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 149200 149400 :=
  FiniteIntervals.of_fin 149200 200 complete_chunk746

lemma complete_chunk747 : ∀ i : Fin 200, Compatible (149400 + i.val) →
    (table.lookup (149400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk747 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 149400 149600 :=
  FiniteIntervals.of_fin 149400 200 complete_chunk747

lemma complete_chunk748 : ∀ i : Fin 200, Compatible (149600 + i.val) →
    (table.lookup (149600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk748 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 149600 149800 :=
  FiniteIntervals.of_fin 149600 200 complete_chunk748

lemma complete_chunk749 : ∀ i : Fin 200, Compatible (149800 + i.val) →
    (table.lookup (149800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk749 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 149800 150000 :=
  FiniteIntervals.of_fin 149800 200 complete_chunk749

#print axioms interval_chunk740
end Erdos184Work.PureFiveFilter4
