import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk190 : ∀ i : Fin 200, Compatible (38000 + i.val) →
    (table.lookup (38000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk190 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 38000 38200 :=
  FiniteIntervals.of_fin 38000 200 complete_chunk190

lemma complete_chunk191 : ∀ i : Fin 200, Compatible (38200 + i.val) →
    (table.lookup (38200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk191 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 38200 38400 :=
  FiniteIntervals.of_fin 38200 200 complete_chunk191

lemma complete_chunk192 : ∀ i : Fin 200, Compatible (38400 + i.val) →
    (table.lookup (38400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk192 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 38400 38600 :=
  FiniteIntervals.of_fin 38400 200 complete_chunk192

lemma complete_chunk193 : ∀ i : Fin 200, Compatible (38600 + i.val) →
    (table.lookup (38600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk193 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 38600 38800 :=
  FiniteIntervals.of_fin 38600 200 complete_chunk193

lemma complete_chunk194 : ∀ i : Fin 200, Compatible (38800 + i.val) →
    (table.lookup (38800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk194 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 38800 39000 :=
  FiniteIntervals.of_fin 38800 200 complete_chunk194

lemma complete_chunk195 : ∀ i : Fin 200, Compatible (39000 + i.val) →
    (table.lookup (39000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk195 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 39000 39200 :=
  FiniteIntervals.of_fin 39000 200 complete_chunk195

lemma complete_chunk196 : ∀ i : Fin 200, Compatible (39200 + i.val) →
    (table.lookup (39200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk196 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 39200 39400 :=
  FiniteIntervals.of_fin 39200 200 complete_chunk196

lemma complete_chunk197 : ∀ i : Fin 200, Compatible (39400 + i.val) →
    (table.lookup (39400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk197 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 39400 39600 :=
  FiniteIntervals.of_fin 39400 200 complete_chunk197

lemma complete_chunk198 : ∀ i : Fin 200, Compatible (39600 + i.val) →
    (table.lookup (39600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk198 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 39600 39800 :=
  FiniteIntervals.of_fin 39600 200 complete_chunk198

lemma complete_chunk199 : ∀ i : Fin 200, Compatible (39800 + i.val) →
    (table.lookup (39800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk199 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 39800 40000 :=
  FiniteIntervals.of_fin 39800 200 complete_chunk199

#print axioms interval_chunk190
end Erdos184Work.PureFiveFilter3
