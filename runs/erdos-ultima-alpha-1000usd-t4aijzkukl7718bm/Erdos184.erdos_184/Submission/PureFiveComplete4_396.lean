import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3960 : ∀ i : Fin 200, Compatible (792000 + i.val) →
    (table.lookup (792000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3960 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 792000 792200 :=
  FiniteIntervals.of_fin 792000 200 complete_chunk3960

lemma complete_chunk3961 : ∀ i : Fin 200, Compatible (792200 + i.val) →
    (table.lookup (792200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3961 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 792200 792400 :=
  FiniteIntervals.of_fin 792200 200 complete_chunk3961

lemma complete_chunk3962 : ∀ i : Fin 200, Compatible (792400 + i.val) →
    (table.lookup (792400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3962 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 792400 792600 :=
  FiniteIntervals.of_fin 792400 200 complete_chunk3962

lemma complete_chunk3963 : ∀ i : Fin 200, Compatible (792600 + i.val) →
    (table.lookup (792600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3963 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 792600 792800 :=
  FiniteIntervals.of_fin 792600 200 complete_chunk3963

lemma complete_chunk3964 : ∀ i : Fin 200, Compatible (792800 + i.val) →
    (table.lookup (792800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3964 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 792800 793000 :=
  FiniteIntervals.of_fin 792800 200 complete_chunk3964

lemma complete_chunk3965 : ∀ i : Fin 200, Compatible (793000 + i.val) →
    (table.lookup (793000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3965 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 793000 793200 :=
  FiniteIntervals.of_fin 793000 200 complete_chunk3965

lemma complete_chunk3966 : ∀ i : Fin 200, Compatible (793200 + i.val) →
    (table.lookup (793200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3966 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 793200 793400 :=
  FiniteIntervals.of_fin 793200 200 complete_chunk3966

lemma complete_chunk3967 : ∀ i : Fin 200, Compatible (793400 + i.val) →
    (table.lookup (793400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3967 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 793400 793600 :=
  FiniteIntervals.of_fin 793400 200 complete_chunk3967

lemma complete_chunk3968 : ∀ i : Fin 200, Compatible (793600 + i.val) →
    (table.lookup (793600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3968 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 793600 793800 :=
  FiniteIntervals.of_fin 793600 200 complete_chunk3968

lemma complete_chunk3969 : ∀ i : Fin 200, Compatible (793800 + i.val) →
    (table.lookup (793800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3969 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 793800 794000 :=
  FiniteIntervals.of_fin 793800 200 complete_chunk3969

#print axioms interval_chunk3960
end Erdos184Work.PureFiveFilter4
