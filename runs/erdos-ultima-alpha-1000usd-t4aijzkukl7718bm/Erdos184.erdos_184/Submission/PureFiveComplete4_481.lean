import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4810 : ∀ i : Fin 200, Compatible (962000 + i.val) →
    (table.lookup (962000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4810 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 962000 962200 :=
  FiniteIntervals.of_fin 962000 200 complete_chunk4810

lemma complete_chunk4811 : ∀ i : Fin 200, Compatible (962200 + i.val) →
    (table.lookup (962200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4811 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 962200 962400 :=
  FiniteIntervals.of_fin 962200 200 complete_chunk4811

lemma complete_chunk4812 : ∀ i : Fin 200, Compatible (962400 + i.val) →
    (table.lookup (962400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4812 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 962400 962600 :=
  FiniteIntervals.of_fin 962400 200 complete_chunk4812

lemma complete_chunk4813 : ∀ i : Fin 200, Compatible (962600 + i.val) →
    (table.lookup (962600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4813 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 962600 962800 :=
  FiniteIntervals.of_fin 962600 200 complete_chunk4813

lemma complete_chunk4814 : ∀ i : Fin 200, Compatible (962800 + i.val) →
    (table.lookup (962800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4814 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 962800 963000 :=
  FiniteIntervals.of_fin 962800 200 complete_chunk4814

lemma complete_chunk4815 : ∀ i : Fin 200, Compatible (963000 + i.val) →
    (table.lookup (963000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4815 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 963000 963200 :=
  FiniteIntervals.of_fin 963000 200 complete_chunk4815

lemma complete_chunk4816 : ∀ i : Fin 200, Compatible (963200 + i.val) →
    (table.lookup (963200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4816 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 963200 963400 :=
  FiniteIntervals.of_fin 963200 200 complete_chunk4816

lemma complete_chunk4817 : ∀ i : Fin 200, Compatible (963400 + i.val) →
    (table.lookup (963400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4817 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 963400 963600 :=
  FiniteIntervals.of_fin 963400 200 complete_chunk4817

lemma complete_chunk4818 : ∀ i : Fin 200, Compatible (963600 + i.val) →
    (table.lookup (963600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4818 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 963600 963800 :=
  FiniteIntervals.of_fin 963600 200 complete_chunk4818

lemma complete_chunk4819 : ∀ i : Fin 200, Compatible (963800 + i.val) →
    (table.lookup (963800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4819 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 963800 964000 :=
  FiniteIntervals.of_fin 963800 200 complete_chunk4819

#print axioms interval_chunk4810
end Erdos184Work.PureFiveFilter4
