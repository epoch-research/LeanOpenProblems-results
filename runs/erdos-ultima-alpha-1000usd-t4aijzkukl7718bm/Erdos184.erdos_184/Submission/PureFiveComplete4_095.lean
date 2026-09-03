import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk950 : ∀ i : Fin 200, Compatible (190000 + i.val) →
    (table.lookup (190000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk950 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 190000 190200 :=
  FiniteIntervals.of_fin 190000 200 complete_chunk950

lemma complete_chunk951 : ∀ i : Fin 200, Compatible (190200 + i.val) →
    (table.lookup (190200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk951 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 190200 190400 :=
  FiniteIntervals.of_fin 190200 200 complete_chunk951

lemma complete_chunk952 : ∀ i : Fin 200, Compatible (190400 + i.val) →
    (table.lookup (190400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk952 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 190400 190600 :=
  FiniteIntervals.of_fin 190400 200 complete_chunk952

lemma complete_chunk953 : ∀ i : Fin 200, Compatible (190600 + i.val) →
    (table.lookup (190600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk953 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 190600 190800 :=
  FiniteIntervals.of_fin 190600 200 complete_chunk953

lemma complete_chunk954 : ∀ i : Fin 200, Compatible (190800 + i.val) →
    (table.lookup (190800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk954 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 190800 191000 :=
  FiniteIntervals.of_fin 190800 200 complete_chunk954

lemma complete_chunk955 : ∀ i : Fin 200, Compatible (191000 + i.val) →
    (table.lookup (191000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk955 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 191000 191200 :=
  FiniteIntervals.of_fin 191000 200 complete_chunk955

lemma complete_chunk956 : ∀ i : Fin 200, Compatible (191200 + i.val) →
    (table.lookup (191200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk956 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 191200 191400 :=
  FiniteIntervals.of_fin 191200 200 complete_chunk956

lemma complete_chunk957 : ∀ i : Fin 200, Compatible (191400 + i.val) →
    (table.lookup (191400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk957 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 191400 191600 :=
  FiniteIntervals.of_fin 191400 200 complete_chunk957

lemma complete_chunk958 : ∀ i : Fin 200, Compatible (191600 + i.val) →
    (table.lookup (191600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk958 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 191600 191800 :=
  FiniteIntervals.of_fin 191600 200 complete_chunk958

lemma complete_chunk959 : ∀ i : Fin 200, Compatible (191800 + i.val) →
    (table.lookup (191800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk959 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 191800 192000 :=
  FiniteIntervals.of_fin 191800 200 complete_chunk959

#print axioms interval_chunk950
end Erdos184Work.PureFiveFilter4
