import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4930 : ∀ i : Fin 200, Compatible (986000 + i.val) →
    (table.lookup (986000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4930 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 986000 986200 :=
  FiniteIntervals.of_fin 986000 200 complete_chunk4930

lemma complete_chunk4931 : ∀ i : Fin 200, Compatible (986200 + i.val) →
    (table.lookup (986200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4931 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 986200 986400 :=
  FiniteIntervals.of_fin 986200 200 complete_chunk4931

lemma complete_chunk4932 : ∀ i : Fin 200, Compatible (986400 + i.val) →
    (table.lookup (986400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4932 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 986400 986600 :=
  FiniteIntervals.of_fin 986400 200 complete_chunk4932

lemma complete_chunk4933 : ∀ i : Fin 200, Compatible (986600 + i.val) →
    (table.lookup (986600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4933 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 986600 986800 :=
  FiniteIntervals.of_fin 986600 200 complete_chunk4933

lemma complete_chunk4934 : ∀ i : Fin 200, Compatible (986800 + i.val) →
    (table.lookup (986800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4934 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 986800 987000 :=
  FiniteIntervals.of_fin 986800 200 complete_chunk4934

lemma complete_chunk4935 : ∀ i : Fin 200, Compatible (987000 + i.val) →
    (table.lookup (987000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4935 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 987000 987200 :=
  FiniteIntervals.of_fin 987000 200 complete_chunk4935

lemma complete_chunk4936 : ∀ i : Fin 200, Compatible (987200 + i.val) →
    (table.lookup (987200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4936 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 987200 987400 :=
  FiniteIntervals.of_fin 987200 200 complete_chunk4936

lemma complete_chunk4937 : ∀ i : Fin 200, Compatible (987400 + i.val) →
    (table.lookup (987400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4937 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 987400 987600 :=
  FiniteIntervals.of_fin 987400 200 complete_chunk4937

lemma complete_chunk4938 : ∀ i : Fin 200, Compatible (987600 + i.val) →
    (table.lookup (987600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4938 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 987600 987800 :=
  FiniteIntervals.of_fin 987600 200 complete_chunk4938

lemma complete_chunk4939 : ∀ i : Fin 200, Compatible (987800 + i.val) →
    (table.lookup (987800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4939 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 987800 988000 :=
  FiniteIntervals.of_fin 987800 200 complete_chunk4939

#print axioms interval_chunk4930
end Erdos184Work.PureFiveFilter4
