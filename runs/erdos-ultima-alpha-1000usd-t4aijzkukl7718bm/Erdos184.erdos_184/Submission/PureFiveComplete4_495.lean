import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4950 : ∀ i : Fin 200, Compatible (990000 + i.val) →
    (table.lookup (990000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4950 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 990000 990200 :=
  FiniteIntervals.of_fin 990000 200 complete_chunk4950

lemma complete_chunk4951 : ∀ i : Fin 200, Compatible (990200 + i.val) →
    (table.lookup (990200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4951 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 990200 990400 :=
  FiniteIntervals.of_fin 990200 200 complete_chunk4951

lemma complete_chunk4952 : ∀ i : Fin 200, Compatible (990400 + i.val) →
    (table.lookup (990400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4952 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 990400 990600 :=
  FiniteIntervals.of_fin 990400 200 complete_chunk4952

lemma complete_chunk4953 : ∀ i : Fin 200, Compatible (990600 + i.val) →
    (table.lookup (990600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4953 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 990600 990800 :=
  FiniteIntervals.of_fin 990600 200 complete_chunk4953

lemma complete_chunk4954 : ∀ i : Fin 200, Compatible (990800 + i.val) →
    (table.lookup (990800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4954 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 990800 991000 :=
  FiniteIntervals.of_fin 990800 200 complete_chunk4954

lemma complete_chunk4955 : ∀ i : Fin 200, Compatible (991000 + i.val) →
    (table.lookup (991000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4955 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 991000 991200 :=
  FiniteIntervals.of_fin 991000 200 complete_chunk4955

lemma complete_chunk4956 : ∀ i : Fin 200, Compatible (991200 + i.val) →
    (table.lookup (991200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4956 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 991200 991400 :=
  FiniteIntervals.of_fin 991200 200 complete_chunk4956

lemma complete_chunk4957 : ∀ i : Fin 200, Compatible (991400 + i.val) →
    (table.lookup (991400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4957 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 991400 991600 :=
  FiniteIntervals.of_fin 991400 200 complete_chunk4957

lemma complete_chunk4958 : ∀ i : Fin 200, Compatible (991600 + i.val) →
    (table.lookup (991600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4958 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 991600 991800 :=
  FiniteIntervals.of_fin 991600 200 complete_chunk4958

lemma complete_chunk4959 : ∀ i : Fin 200, Compatible (991800 + i.val) →
    (table.lookup (991800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4959 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 991800 992000 :=
  FiniteIntervals.of_fin 991800 200 complete_chunk4959

#print axioms interval_chunk4950
end Erdos184Work.PureFiveFilter4
