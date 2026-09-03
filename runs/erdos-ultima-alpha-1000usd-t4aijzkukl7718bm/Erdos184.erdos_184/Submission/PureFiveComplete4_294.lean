import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2940 : ∀ i : Fin 200, Compatible (588000 + i.val) →
    (table.lookup (588000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2940 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 588000 588200 :=
  FiniteIntervals.of_fin 588000 200 complete_chunk2940

lemma complete_chunk2941 : ∀ i : Fin 200, Compatible (588200 + i.val) →
    (table.lookup (588200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2941 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 588200 588400 :=
  FiniteIntervals.of_fin 588200 200 complete_chunk2941

lemma complete_chunk2942 : ∀ i : Fin 200, Compatible (588400 + i.val) →
    (table.lookup (588400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2942 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 588400 588600 :=
  FiniteIntervals.of_fin 588400 200 complete_chunk2942

lemma complete_chunk2943 : ∀ i : Fin 200, Compatible (588600 + i.val) →
    (table.lookup (588600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2943 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 588600 588800 :=
  FiniteIntervals.of_fin 588600 200 complete_chunk2943

lemma complete_chunk2944 : ∀ i : Fin 200, Compatible (588800 + i.val) →
    (table.lookup (588800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2944 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 588800 589000 :=
  FiniteIntervals.of_fin 588800 200 complete_chunk2944

lemma complete_chunk2945 : ∀ i : Fin 200, Compatible (589000 + i.val) →
    (table.lookup (589000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2945 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 589000 589200 :=
  FiniteIntervals.of_fin 589000 200 complete_chunk2945

lemma complete_chunk2946 : ∀ i : Fin 200, Compatible (589200 + i.val) →
    (table.lookup (589200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2946 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 589200 589400 :=
  FiniteIntervals.of_fin 589200 200 complete_chunk2946

lemma complete_chunk2947 : ∀ i : Fin 200, Compatible (589400 + i.val) →
    (table.lookup (589400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2947 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 589400 589600 :=
  FiniteIntervals.of_fin 589400 200 complete_chunk2947

lemma complete_chunk2948 : ∀ i : Fin 200, Compatible (589600 + i.val) →
    (table.lookup (589600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2948 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 589600 589800 :=
  FiniteIntervals.of_fin 589600 200 complete_chunk2948

lemma complete_chunk2949 : ∀ i : Fin 200, Compatible (589800 + i.val) →
    (table.lookup (589800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2949 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 589800 590000 :=
  FiniteIntervals.of_fin 589800 200 complete_chunk2949

#print axioms interval_chunk2940
end Erdos184Work.PureFiveFilter4
