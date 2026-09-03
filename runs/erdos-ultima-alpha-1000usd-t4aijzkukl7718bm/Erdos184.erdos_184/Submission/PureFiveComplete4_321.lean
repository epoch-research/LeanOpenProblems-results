import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3210 : ∀ i : Fin 200, Compatible (642000 + i.val) →
    (table.lookup (642000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3210 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 642000 642200 :=
  FiniteIntervals.of_fin 642000 200 complete_chunk3210

lemma complete_chunk3211 : ∀ i : Fin 200, Compatible (642200 + i.val) →
    (table.lookup (642200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3211 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 642200 642400 :=
  FiniteIntervals.of_fin 642200 200 complete_chunk3211

lemma complete_chunk3212 : ∀ i : Fin 200, Compatible (642400 + i.val) →
    (table.lookup (642400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3212 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 642400 642600 :=
  FiniteIntervals.of_fin 642400 200 complete_chunk3212

lemma complete_chunk3213 : ∀ i : Fin 200, Compatible (642600 + i.val) →
    (table.lookup (642600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3213 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 642600 642800 :=
  FiniteIntervals.of_fin 642600 200 complete_chunk3213

lemma complete_chunk3214 : ∀ i : Fin 200, Compatible (642800 + i.val) →
    (table.lookup (642800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3214 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 642800 643000 :=
  FiniteIntervals.of_fin 642800 200 complete_chunk3214

lemma complete_chunk3215 : ∀ i : Fin 200, Compatible (643000 + i.val) →
    (table.lookup (643000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3215 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 643000 643200 :=
  FiniteIntervals.of_fin 643000 200 complete_chunk3215

lemma complete_chunk3216 : ∀ i : Fin 200, Compatible (643200 + i.val) →
    (table.lookup (643200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3216 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 643200 643400 :=
  FiniteIntervals.of_fin 643200 200 complete_chunk3216

lemma complete_chunk3217 : ∀ i : Fin 200, Compatible (643400 + i.val) →
    (table.lookup (643400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3217 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 643400 643600 :=
  FiniteIntervals.of_fin 643400 200 complete_chunk3217

lemma complete_chunk3218 : ∀ i : Fin 200, Compatible (643600 + i.val) →
    (table.lookup (643600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3218 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 643600 643800 :=
  FiniteIntervals.of_fin 643600 200 complete_chunk3218

lemma complete_chunk3219 : ∀ i : Fin 200, Compatible (643800 + i.val) →
    (table.lookup (643800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3219 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 643800 644000 :=
  FiniteIntervals.of_fin 643800 200 complete_chunk3219

#print axioms interval_chunk3210
end Erdos184Work.PureFiveFilter4
