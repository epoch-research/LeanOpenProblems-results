import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5950 : ∀ i : Fin 200, Compatible (1190000 + i.val) →
    (table.lookup (1190000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5950 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1190000 1190200 :=
  FiniteIntervals.of_fin 1190000 200 complete_chunk5950

lemma complete_chunk5951 : ∀ i : Fin 200, Compatible (1190200 + i.val) →
    (table.lookup (1190200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5951 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1190200 1190400 :=
  FiniteIntervals.of_fin 1190200 200 complete_chunk5951

lemma complete_chunk5952 : ∀ i : Fin 200, Compatible (1190400 + i.val) →
    (table.lookup (1190400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5952 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1190400 1190600 :=
  FiniteIntervals.of_fin 1190400 200 complete_chunk5952

lemma complete_chunk5953 : ∀ i : Fin 200, Compatible (1190600 + i.val) →
    (table.lookup (1190600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5953 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1190600 1190800 :=
  FiniteIntervals.of_fin 1190600 200 complete_chunk5953

lemma complete_chunk5954 : ∀ i : Fin 200, Compatible (1190800 + i.val) →
    (table.lookup (1190800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5954 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1190800 1191000 :=
  FiniteIntervals.of_fin 1190800 200 complete_chunk5954

lemma complete_chunk5955 : ∀ i : Fin 200, Compatible (1191000 + i.val) →
    (table.lookup (1191000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5955 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1191000 1191200 :=
  FiniteIntervals.of_fin 1191000 200 complete_chunk5955

lemma complete_chunk5956 : ∀ i : Fin 200, Compatible (1191200 + i.val) →
    (table.lookup (1191200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5956 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1191200 1191400 :=
  FiniteIntervals.of_fin 1191200 200 complete_chunk5956

lemma complete_chunk5957 : ∀ i : Fin 200, Compatible (1191400 + i.val) →
    (table.lookup (1191400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5957 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1191400 1191600 :=
  FiniteIntervals.of_fin 1191400 200 complete_chunk5957

lemma complete_chunk5958 : ∀ i : Fin 200, Compatible (1191600 + i.val) →
    (table.lookup (1191600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5958 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1191600 1191800 :=
  FiniteIntervals.of_fin 1191600 200 complete_chunk5958

lemma complete_chunk5959 : ∀ i : Fin 200, Compatible (1191800 + i.val) →
    (table.lookup (1191800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5959 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1191800 1192000 :=
  FiniteIntervals.of_fin 1191800 200 complete_chunk5959

#print axioms interval_chunk5950
end Erdos184Work.PureFiveFilter4
