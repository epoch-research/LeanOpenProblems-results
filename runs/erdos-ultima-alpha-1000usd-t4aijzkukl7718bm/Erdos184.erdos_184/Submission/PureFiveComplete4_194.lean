import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1940 : ∀ i : Fin 200, Compatible (388000 + i.val) →
    (table.lookup (388000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1940 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 388000 388200 :=
  FiniteIntervals.of_fin 388000 200 complete_chunk1940

lemma complete_chunk1941 : ∀ i : Fin 200, Compatible (388200 + i.val) →
    (table.lookup (388200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1941 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 388200 388400 :=
  FiniteIntervals.of_fin 388200 200 complete_chunk1941

lemma complete_chunk1942 : ∀ i : Fin 200, Compatible (388400 + i.val) →
    (table.lookup (388400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1942 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 388400 388600 :=
  FiniteIntervals.of_fin 388400 200 complete_chunk1942

lemma complete_chunk1943 : ∀ i : Fin 200, Compatible (388600 + i.val) →
    (table.lookup (388600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1943 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 388600 388800 :=
  FiniteIntervals.of_fin 388600 200 complete_chunk1943

lemma complete_chunk1944 : ∀ i : Fin 200, Compatible (388800 + i.val) →
    (table.lookup (388800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1944 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 388800 389000 :=
  FiniteIntervals.of_fin 388800 200 complete_chunk1944

lemma complete_chunk1945 : ∀ i : Fin 200, Compatible (389000 + i.val) →
    (table.lookup (389000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1945 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 389000 389200 :=
  FiniteIntervals.of_fin 389000 200 complete_chunk1945

lemma complete_chunk1946 : ∀ i : Fin 200, Compatible (389200 + i.val) →
    (table.lookup (389200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1946 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 389200 389400 :=
  FiniteIntervals.of_fin 389200 200 complete_chunk1946

lemma complete_chunk1947 : ∀ i : Fin 200, Compatible (389400 + i.val) →
    (table.lookup (389400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1947 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 389400 389600 :=
  FiniteIntervals.of_fin 389400 200 complete_chunk1947

lemma complete_chunk1948 : ∀ i : Fin 200, Compatible (389600 + i.val) →
    (table.lookup (389600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1948 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 389600 389800 :=
  FiniteIntervals.of_fin 389600 200 complete_chunk1948

lemma complete_chunk1949 : ∀ i : Fin 200, Compatible (389800 + i.val) →
    (table.lookup (389800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1949 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 389800 390000 :=
  FiniteIntervals.of_fin 389800 200 complete_chunk1949

#print axioms interval_chunk1940
end Erdos184Work.PureFiveFilter4
