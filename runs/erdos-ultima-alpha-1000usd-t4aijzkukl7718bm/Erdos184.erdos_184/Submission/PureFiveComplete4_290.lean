import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2900 : ∀ i : Fin 200, Compatible (580000 + i.val) →
    (table.lookup (580000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2900 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 580000 580200 :=
  FiniteIntervals.of_fin 580000 200 complete_chunk2900

lemma complete_chunk2901 : ∀ i : Fin 200, Compatible (580200 + i.val) →
    (table.lookup (580200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2901 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 580200 580400 :=
  FiniteIntervals.of_fin 580200 200 complete_chunk2901

lemma complete_chunk2902 : ∀ i : Fin 200, Compatible (580400 + i.val) →
    (table.lookup (580400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2902 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 580400 580600 :=
  FiniteIntervals.of_fin 580400 200 complete_chunk2902

lemma complete_chunk2903 : ∀ i : Fin 200, Compatible (580600 + i.val) →
    (table.lookup (580600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2903 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 580600 580800 :=
  FiniteIntervals.of_fin 580600 200 complete_chunk2903

lemma complete_chunk2904 : ∀ i : Fin 200, Compatible (580800 + i.val) →
    (table.lookup (580800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2904 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 580800 581000 :=
  FiniteIntervals.of_fin 580800 200 complete_chunk2904

lemma complete_chunk2905 : ∀ i : Fin 200, Compatible (581000 + i.val) →
    (table.lookup (581000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2905 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 581000 581200 :=
  FiniteIntervals.of_fin 581000 200 complete_chunk2905

lemma complete_chunk2906 : ∀ i : Fin 200, Compatible (581200 + i.val) →
    (table.lookup (581200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2906 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 581200 581400 :=
  FiniteIntervals.of_fin 581200 200 complete_chunk2906

lemma complete_chunk2907 : ∀ i : Fin 200, Compatible (581400 + i.val) →
    (table.lookup (581400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2907 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 581400 581600 :=
  FiniteIntervals.of_fin 581400 200 complete_chunk2907

lemma complete_chunk2908 : ∀ i : Fin 200, Compatible (581600 + i.val) →
    (table.lookup (581600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2908 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 581600 581800 :=
  FiniteIntervals.of_fin 581600 200 complete_chunk2908

lemma complete_chunk2909 : ∀ i : Fin 200, Compatible (581800 + i.val) →
    (table.lookup (581800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2909 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 581800 582000 :=
  FiniteIntervals.of_fin 581800 200 complete_chunk2909

#print axioms interval_chunk2900
end Erdos184Work.PureFiveFilter4
