import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk240 : ∀ i : Fin 200, Compatible (48000 + i.val) →
    (table.lookup (48000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk240 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 48000 48200 :=
  FiniteIntervals.of_fin 48000 200 complete_chunk240

lemma complete_chunk241 : ∀ i : Fin 200, Compatible (48200 + i.val) →
    (table.lookup (48200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk241 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 48200 48400 :=
  FiniteIntervals.of_fin 48200 200 complete_chunk241

lemma complete_chunk242 : ∀ i : Fin 200, Compatible (48400 + i.val) →
    (table.lookup (48400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk242 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 48400 48600 :=
  FiniteIntervals.of_fin 48400 200 complete_chunk242

lemma complete_chunk243 : ∀ i : Fin 200, Compatible (48600 + i.val) →
    (table.lookup (48600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk243 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 48600 48800 :=
  FiniteIntervals.of_fin 48600 200 complete_chunk243

lemma complete_chunk244 : ∀ i : Fin 200, Compatible (48800 + i.val) →
    (table.lookup (48800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk244 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 48800 49000 :=
  FiniteIntervals.of_fin 48800 200 complete_chunk244

lemma complete_chunk245 : ∀ i : Fin 200, Compatible (49000 + i.val) →
    (table.lookup (49000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk245 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 49000 49200 :=
  FiniteIntervals.of_fin 49000 200 complete_chunk245

lemma complete_chunk246 : ∀ i : Fin 200, Compatible (49200 + i.val) →
    (table.lookup (49200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk246 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 49200 49400 :=
  FiniteIntervals.of_fin 49200 200 complete_chunk246

lemma complete_chunk247 : ∀ i : Fin 200, Compatible (49400 + i.val) →
    (table.lookup (49400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk247 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 49400 49600 :=
  FiniteIntervals.of_fin 49400 200 complete_chunk247

lemma complete_chunk248 : ∀ i : Fin 200, Compatible (49600 + i.val) →
    (table.lookup (49600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk248 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 49600 49800 :=
  FiniteIntervals.of_fin 49600 200 complete_chunk248

lemma complete_chunk249 : ∀ i : Fin 200, Compatible (49800 + i.val) →
    (table.lookup (49800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk249 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 49800 50000 :=
  FiniteIntervals.of_fin 49800 200 complete_chunk249

#print axioms interval_chunk240
end Erdos184Work.PureFiveFilter3
