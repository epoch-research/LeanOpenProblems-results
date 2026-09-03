import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5740 : ∀ i : Fin 200, Compatible (1148000 + i.val) →
    (table.lookup (1148000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5740 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1148000 1148200 :=
  FiniteIntervals.of_fin 1148000 200 complete_chunk5740

lemma complete_chunk5741 : ∀ i : Fin 200, Compatible (1148200 + i.val) →
    (table.lookup (1148200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5741 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1148200 1148400 :=
  FiniteIntervals.of_fin 1148200 200 complete_chunk5741

lemma complete_chunk5742 : ∀ i : Fin 200, Compatible (1148400 + i.val) →
    (table.lookup (1148400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5742 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1148400 1148600 :=
  FiniteIntervals.of_fin 1148400 200 complete_chunk5742

lemma complete_chunk5743 : ∀ i : Fin 200, Compatible (1148600 + i.val) →
    (table.lookup (1148600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5743 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1148600 1148800 :=
  FiniteIntervals.of_fin 1148600 200 complete_chunk5743

lemma complete_chunk5744 : ∀ i : Fin 200, Compatible (1148800 + i.val) →
    (table.lookup (1148800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5744 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1148800 1149000 :=
  FiniteIntervals.of_fin 1148800 200 complete_chunk5744

lemma complete_chunk5745 : ∀ i : Fin 200, Compatible (1149000 + i.val) →
    (table.lookup (1149000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5745 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1149000 1149200 :=
  FiniteIntervals.of_fin 1149000 200 complete_chunk5745

lemma complete_chunk5746 : ∀ i : Fin 200, Compatible (1149200 + i.val) →
    (table.lookup (1149200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5746 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1149200 1149400 :=
  FiniteIntervals.of_fin 1149200 200 complete_chunk5746

lemma complete_chunk5747 : ∀ i : Fin 200, Compatible (1149400 + i.val) →
    (table.lookup (1149400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5747 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1149400 1149600 :=
  FiniteIntervals.of_fin 1149400 200 complete_chunk5747

lemma complete_chunk5748 : ∀ i : Fin 200, Compatible (1149600 + i.val) →
    (table.lookup (1149600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5748 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1149600 1149800 :=
  FiniteIntervals.of_fin 1149600 200 complete_chunk5748

lemma complete_chunk5749 : ∀ i : Fin 200, Compatible (1149800 + i.val) →
    (table.lookup (1149800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5749 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1149800 1150000 :=
  FiniteIntervals.of_fin 1149800 200 complete_chunk5749

#print axioms interval_chunk5740
end Erdos184Work.PureFiveFilter4
