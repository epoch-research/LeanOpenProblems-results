import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk830 : ∀ i : Fin 200, Compatible (166000 + i.val) →
    (table.lookup (166000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk830 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 166000 166200 :=
  FiniteIntervals.of_fin 166000 200 complete_chunk830

lemma complete_chunk831 : ∀ i : Fin 200, Compatible (166200 + i.val) →
    (table.lookup (166200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk831 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 166200 166400 :=
  FiniteIntervals.of_fin 166200 200 complete_chunk831

lemma complete_chunk832 : ∀ i : Fin 200, Compatible (166400 + i.val) →
    (table.lookup (166400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk832 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 166400 166600 :=
  FiniteIntervals.of_fin 166400 200 complete_chunk832

lemma complete_chunk833 : ∀ i : Fin 200, Compatible (166600 + i.val) →
    (table.lookup (166600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk833 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 166600 166800 :=
  FiniteIntervals.of_fin 166600 200 complete_chunk833

lemma complete_chunk834 : ∀ i : Fin 200, Compatible (166800 + i.val) →
    (table.lookup (166800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk834 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 166800 167000 :=
  FiniteIntervals.of_fin 166800 200 complete_chunk834

lemma complete_chunk835 : ∀ i : Fin 200, Compatible (167000 + i.val) →
    (table.lookup (167000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk835 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 167000 167200 :=
  FiniteIntervals.of_fin 167000 200 complete_chunk835

lemma complete_chunk836 : ∀ i : Fin 200, Compatible (167200 + i.val) →
    (table.lookup (167200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk836 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 167200 167400 :=
  FiniteIntervals.of_fin 167200 200 complete_chunk836

lemma complete_chunk837 : ∀ i : Fin 200, Compatible (167400 + i.val) →
    (table.lookup (167400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk837 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 167400 167600 :=
  FiniteIntervals.of_fin 167400 200 complete_chunk837

lemma complete_chunk838 : ∀ i : Fin 200, Compatible (167600 + i.val) →
    (table.lookup (167600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk838 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 167600 167800 :=
  FiniteIntervals.of_fin 167600 200 complete_chunk838

lemma complete_chunk839 : ∀ i : Fin 200, Compatible (167800 + i.val) →
    (table.lookup (167800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk839 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 167800 168000 :=
  FiniteIntervals.of_fin 167800 200 complete_chunk839

#print axioms interval_chunk830
end Erdos184Work.PureFiveFilter4
