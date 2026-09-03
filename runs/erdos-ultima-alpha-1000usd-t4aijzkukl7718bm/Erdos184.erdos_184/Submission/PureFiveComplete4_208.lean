import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2080 : ∀ i : Fin 200, Compatible (416000 + i.val) →
    (table.lookup (416000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2080 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 416000 416200 :=
  FiniteIntervals.of_fin 416000 200 complete_chunk2080

lemma complete_chunk2081 : ∀ i : Fin 200, Compatible (416200 + i.val) →
    (table.lookup (416200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2081 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 416200 416400 :=
  FiniteIntervals.of_fin 416200 200 complete_chunk2081

lemma complete_chunk2082 : ∀ i : Fin 200, Compatible (416400 + i.val) →
    (table.lookup (416400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2082 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 416400 416600 :=
  FiniteIntervals.of_fin 416400 200 complete_chunk2082

lemma complete_chunk2083 : ∀ i : Fin 200, Compatible (416600 + i.val) →
    (table.lookup (416600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2083 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 416600 416800 :=
  FiniteIntervals.of_fin 416600 200 complete_chunk2083

lemma complete_chunk2084 : ∀ i : Fin 200, Compatible (416800 + i.val) →
    (table.lookup (416800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2084 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 416800 417000 :=
  FiniteIntervals.of_fin 416800 200 complete_chunk2084

lemma complete_chunk2085 : ∀ i : Fin 200, Compatible (417000 + i.val) →
    (table.lookup (417000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2085 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 417000 417200 :=
  FiniteIntervals.of_fin 417000 200 complete_chunk2085

lemma complete_chunk2086 : ∀ i : Fin 200, Compatible (417200 + i.val) →
    (table.lookup (417200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2086 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 417200 417400 :=
  FiniteIntervals.of_fin 417200 200 complete_chunk2086

lemma complete_chunk2087 : ∀ i : Fin 200, Compatible (417400 + i.val) →
    (table.lookup (417400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2087 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 417400 417600 :=
  FiniteIntervals.of_fin 417400 200 complete_chunk2087

lemma complete_chunk2088 : ∀ i : Fin 200, Compatible (417600 + i.val) →
    (table.lookup (417600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2088 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 417600 417800 :=
  FiniteIntervals.of_fin 417600 200 complete_chunk2088

lemma complete_chunk2089 : ∀ i : Fin 200, Compatible (417800 + i.val) →
    (table.lookup (417800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2089 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 417800 418000 :=
  FiniteIntervals.of_fin 417800 200 complete_chunk2089

#print axioms interval_chunk2080
end Erdos184Work.PureFiveFilter4
