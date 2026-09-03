import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3950 : ∀ i : Fin 200, Compatible (790000 + i.val) →
    (table.lookup (790000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3950 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 790000 790200 :=
  FiniteIntervals.of_fin 790000 200 complete_chunk3950

lemma complete_chunk3951 : ∀ i : Fin 200, Compatible (790200 + i.val) →
    (table.lookup (790200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3951 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 790200 790400 :=
  FiniteIntervals.of_fin 790200 200 complete_chunk3951

lemma complete_chunk3952 : ∀ i : Fin 200, Compatible (790400 + i.val) →
    (table.lookup (790400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3952 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 790400 790600 :=
  FiniteIntervals.of_fin 790400 200 complete_chunk3952

lemma complete_chunk3953 : ∀ i : Fin 200, Compatible (790600 + i.val) →
    (table.lookup (790600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3953 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 790600 790800 :=
  FiniteIntervals.of_fin 790600 200 complete_chunk3953

lemma complete_chunk3954 : ∀ i : Fin 200, Compatible (790800 + i.val) →
    (table.lookup (790800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3954 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 790800 791000 :=
  FiniteIntervals.of_fin 790800 200 complete_chunk3954

lemma complete_chunk3955 : ∀ i : Fin 200, Compatible (791000 + i.val) →
    (table.lookup (791000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3955 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 791000 791200 :=
  FiniteIntervals.of_fin 791000 200 complete_chunk3955

lemma complete_chunk3956 : ∀ i : Fin 200, Compatible (791200 + i.val) →
    (table.lookup (791200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3956 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 791200 791400 :=
  FiniteIntervals.of_fin 791200 200 complete_chunk3956

lemma complete_chunk3957 : ∀ i : Fin 200, Compatible (791400 + i.val) →
    (table.lookup (791400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3957 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 791400 791600 :=
  FiniteIntervals.of_fin 791400 200 complete_chunk3957

lemma complete_chunk3958 : ∀ i : Fin 200, Compatible (791600 + i.val) →
    (table.lookup (791600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3958 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 791600 791800 :=
  FiniteIntervals.of_fin 791600 200 complete_chunk3958

lemma complete_chunk3959 : ∀ i : Fin 200, Compatible (791800 + i.val) →
    (table.lookup (791800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3959 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 791800 792000 :=
  FiniteIntervals.of_fin 791800 200 complete_chunk3959

#print axioms interval_chunk3950
end Erdos184Work.PureFiveFilter4
