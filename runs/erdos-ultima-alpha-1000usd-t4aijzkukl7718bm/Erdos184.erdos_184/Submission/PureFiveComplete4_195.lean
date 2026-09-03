import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1950 : ∀ i : Fin 200, Compatible (390000 + i.val) →
    (table.lookup (390000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1950 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 390000 390200 :=
  FiniteIntervals.of_fin 390000 200 complete_chunk1950

lemma complete_chunk1951 : ∀ i : Fin 200, Compatible (390200 + i.val) →
    (table.lookup (390200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1951 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 390200 390400 :=
  FiniteIntervals.of_fin 390200 200 complete_chunk1951

lemma complete_chunk1952 : ∀ i : Fin 200, Compatible (390400 + i.val) →
    (table.lookup (390400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1952 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 390400 390600 :=
  FiniteIntervals.of_fin 390400 200 complete_chunk1952

lemma complete_chunk1953 : ∀ i : Fin 200, Compatible (390600 + i.val) →
    (table.lookup (390600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1953 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 390600 390800 :=
  FiniteIntervals.of_fin 390600 200 complete_chunk1953

lemma complete_chunk1954 : ∀ i : Fin 200, Compatible (390800 + i.val) →
    (table.lookup (390800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1954 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 390800 391000 :=
  FiniteIntervals.of_fin 390800 200 complete_chunk1954

lemma complete_chunk1955 : ∀ i : Fin 200, Compatible (391000 + i.val) →
    (table.lookup (391000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1955 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 391000 391200 :=
  FiniteIntervals.of_fin 391000 200 complete_chunk1955

lemma complete_chunk1956 : ∀ i : Fin 200, Compatible (391200 + i.val) →
    (table.lookup (391200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1956 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 391200 391400 :=
  FiniteIntervals.of_fin 391200 200 complete_chunk1956

lemma complete_chunk1957 : ∀ i : Fin 200, Compatible (391400 + i.val) →
    (table.lookup (391400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1957 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 391400 391600 :=
  FiniteIntervals.of_fin 391400 200 complete_chunk1957

lemma complete_chunk1958 : ∀ i : Fin 200, Compatible (391600 + i.val) →
    (table.lookup (391600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1958 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 391600 391800 :=
  FiniteIntervals.of_fin 391600 200 complete_chunk1958

lemma complete_chunk1959 : ∀ i : Fin 200, Compatible (391800 + i.val) →
    (table.lookup (391800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1959 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 391800 392000 :=
  FiniteIntervals.of_fin 391800 200 complete_chunk1959

#print axioms interval_chunk1950
end Erdos184Work.PureFiveFilter4
