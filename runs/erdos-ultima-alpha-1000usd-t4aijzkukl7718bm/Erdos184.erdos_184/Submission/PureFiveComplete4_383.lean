import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3830 : ∀ i : Fin 200, Compatible (766000 + i.val) →
    (table.lookup (766000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3830 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 766000 766200 :=
  FiniteIntervals.of_fin 766000 200 complete_chunk3830

lemma complete_chunk3831 : ∀ i : Fin 200, Compatible (766200 + i.val) →
    (table.lookup (766200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3831 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 766200 766400 :=
  FiniteIntervals.of_fin 766200 200 complete_chunk3831

lemma complete_chunk3832 : ∀ i : Fin 200, Compatible (766400 + i.val) →
    (table.lookup (766400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3832 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 766400 766600 :=
  FiniteIntervals.of_fin 766400 200 complete_chunk3832

lemma complete_chunk3833 : ∀ i : Fin 200, Compatible (766600 + i.val) →
    (table.lookup (766600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3833 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 766600 766800 :=
  FiniteIntervals.of_fin 766600 200 complete_chunk3833

lemma complete_chunk3834 : ∀ i : Fin 200, Compatible (766800 + i.val) →
    (table.lookup (766800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3834 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 766800 767000 :=
  FiniteIntervals.of_fin 766800 200 complete_chunk3834

lemma complete_chunk3835 : ∀ i : Fin 200, Compatible (767000 + i.val) →
    (table.lookup (767000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3835 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 767000 767200 :=
  FiniteIntervals.of_fin 767000 200 complete_chunk3835

lemma complete_chunk3836 : ∀ i : Fin 200, Compatible (767200 + i.val) →
    (table.lookup (767200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3836 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 767200 767400 :=
  FiniteIntervals.of_fin 767200 200 complete_chunk3836

lemma complete_chunk3837 : ∀ i : Fin 200, Compatible (767400 + i.val) →
    (table.lookup (767400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3837 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 767400 767600 :=
  FiniteIntervals.of_fin 767400 200 complete_chunk3837

lemma complete_chunk3838 : ∀ i : Fin 200, Compatible (767600 + i.val) →
    (table.lookup (767600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3838 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 767600 767800 :=
  FiniteIntervals.of_fin 767600 200 complete_chunk3838

lemma complete_chunk3839 : ∀ i : Fin 200, Compatible (767800 + i.val) →
    (table.lookup (767800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3839 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 767800 768000 :=
  FiniteIntervals.of_fin 767800 200 complete_chunk3839

#print axioms interval_chunk3830
end Erdos184Work.PureFiveFilter4
