import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2830 : ∀ i : Fin 200, Compatible (566000 + i.val) →
    (table.lookup (566000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2830 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 566000 566200 :=
  FiniteIntervals.of_fin 566000 200 complete_chunk2830

lemma complete_chunk2831 : ∀ i : Fin 200, Compatible (566200 + i.val) →
    (table.lookup (566200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2831 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 566200 566400 :=
  FiniteIntervals.of_fin 566200 200 complete_chunk2831

lemma complete_chunk2832 : ∀ i : Fin 200, Compatible (566400 + i.val) →
    (table.lookup (566400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2832 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 566400 566600 :=
  FiniteIntervals.of_fin 566400 200 complete_chunk2832

lemma complete_chunk2833 : ∀ i : Fin 200, Compatible (566600 + i.val) →
    (table.lookup (566600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2833 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 566600 566800 :=
  FiniteIntervals.of_fin 566600 200 complete_chunk2833

lemma complete_chunk2834 : ∀ i : Fin 200, Compatible (566800 + i.val) →
    (table.lookup (566800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2834 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 566800 567000 :=
  FiniteIntervals.of_fin 566800 200 complete_chunk2834

lemma complete_chunk2835 : ∀ i : Fin 200, Compatible (567000 + i.val) →
    (table.lookup (567000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2835 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 567000 567200 :=
  FiniteIntervals.of_fin 567000 200 complete_chunk2835

lemma complete_chunk2836 : ∀ i : Fin 200, Compatible (567200 + i.val) →
    (table.lookup (567200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2836 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 567200 567400 :=
  FiniteIntervals.of_fin 567200 200 complete_chunk2836

lemma complete_chunk2837 : ∀ i : Fin 200, Compatible (567400 + i.val) →
    (table.lookup (567400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2837 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 567400 567600 :=
  FiniteIntervals.of_fin 567400 200 complete_chunk2837

lemma complete_chunk2838 : ∀ i : Fin 200, Compatible (567600 + i.val) →
    (table.lookup (567600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2838 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 567600 567800 :=
  FiniteIntervals.of_fin 567600 200 complete_chunk2838

lemma complete_chunk2839 : ∀ i : Fin 200, Compatible (567800 + i.val) →
    (table.lookup (567800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2839 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 567800 568000 :=
  FiniteIntervals.of_fin 567800 200 complete_chunk2839

#print axioms interval_chunk2830
end Erdos184Work.PureFiveFilter4
