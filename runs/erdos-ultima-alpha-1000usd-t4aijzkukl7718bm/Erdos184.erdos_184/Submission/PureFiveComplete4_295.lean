import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2950 : ∀ i : Fin 200, Compatible (590000 + i.val) →
    (table.lookup (590000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2950 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 590000 590200 :=
  FiniteIntervals.of_fin 590000 200 complete_chunk2950

lemma complete_chunk2951 : ∀ i : Fin 200, Compatible (590200 + i.val) →
    (table.lookup (590200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2951 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 590200 590400 :=
  FiniteIntervals.of_fin 590200 200 complete_chunk2951

lemma complete_chunk2952 : ∀ i : Fin 200, Compatible (590400 + i.val) →
    (table.lookup (590400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2952 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 590400 590600 :=
  FiniteIntervals.of_fin 590400 200 complete_chunk2952

lemma complete_chunk2953 : ∀ i : Fin 200, Compatible (590600 + i.val) →
    (table.lookup (590600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2953 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 590600 590800 :=
  FiniteIntervals.of_fin 590600 200 complete_chunk2953

lemma complete_chunk2954 : ∀ i : Fin 200, Compatible (590800 + i.val) →
    (table.lookup (590800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2954 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 590800 591000 :=
  FiniteIntervals.of_fin 590800 200 complete_chunk2954

lemma complete_chunk2955 : ∀ i : Fin 200, Compatible (591000 + i.val) →
    (table.lookup (591000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2955 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 591000 591200 :=
  FiniteIntervals.of_fin 591000 200 complete_chunk2955

lemma complete_chunk2956 : ∀ i : Fin 200, Compatible (591200 + i.val) →
    (table.lookup (591200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2956 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 591200 591400 :=
  FiniteIntervals.of_fin 591200 200 complete_chunk2956

lemma complete_chunk2957 : ∀ i : Fin 200, Compatible (591400 + i.val) →
    (table.lookup (591400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2957 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 591400 591600 :=
  FiniteIntervals.of_fin 591400 200 complete_chunk2957

lemma complete_chunk2958 : ∀ i : Fin 200, Compatible (591600 + i.val) →
    (table.lookup (591600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2958 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 591600 591800 :=
  FiniteIntervals.of_fin 591600 200 complete_chunk2958

lemma complete_chunk2959 : ∀ i : Fin 200, Compatible (591800 + i.val) →
    (table.lookup (591800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2959 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 591800 592000 :=
  FiniteIntervals.of_fin 591800 200 complete_chunk2959

#print axioms interval_chunk2950
end Erdos184Work.PureFiveFilter4
