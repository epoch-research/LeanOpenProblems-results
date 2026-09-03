import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6210 : ∀ i : Fin 200, Compatible (1242000 + i.val) →
    (table.lookup (1242000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6210 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1242000 1242200 :=
  FiniteIntervals.of_fin 1242000 200 complete_chunk6210

lemma complete_chunk6211 : ∀ i : Fin 200, Compatible (1242200 + i.val) →
    (table.lookup (1242200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6211 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1242200 1242400 :=
  FiniteIntervals.of_fin 1242200 200 complete_chunk6211

lemma complete_chunk6212 : ∀ i : Fin 200, Compatible (1242400 + i.val) →
    (table.lookup (1242400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6212 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1242400 1242600 :=
  FiniteIntervals.of_fin 1242400 200 complete_chunk6212

lemma complete_chunk6213 : ∀ i : Fin 200, Compatible (1242600 + i.val) →
    (table.lookup (1242600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6213 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1242600 1242800 :=
  FiniteIntervals.of_fin 1242600 200 complete_chunk6213

lemma complete_chunk6214 : ∀ i : Fin 200, Compatible (1242800 + i.val) →
    (table.lookup (1242800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6214 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1242800 1243000 :=
  FiniteIntervals.of_fin 1242800 200 complete_chunk6214

lemma complete_chunk6215 : ∀ i : Fin 200, Compatible (1243000 + i.val) →
    (table.lookup (1243000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6215 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1243000 1243200 :=
  FiniteIntervals.of_fin 1243000 200 complete_chunk6215

lemma complete_chunk6216 : ∀ i : Fin 200, Compatible (1243200 + i.val) →
    (table.lookup (1243200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6216 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1243200 1243400 :=
  FiniteIntervals.of_fin 1243200 200 complete_chunk6216

lemma complete_chunk6217 : ∀ i : Fin 200, Compatible (1243400 + i.val) →
    (table.lookup (1243400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6217 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1243400 1243600 :=
  FiniteIntervals.of_fin 1243400 200 complete_chunk6217

lemma complete_chunk6218 : ∀ i : Fin 200, Compatible (1243600 + i.val) →
    (table.lookup (1243600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6218 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1243600 1243800 :=
  FiniteIntervals.of_fin 1243600 200 complete_chunk6218

lemma complete_chunk6219 : ∀ i : Fin 200, Compatible (1243800 + i.val) →
    (table.lookup (1243800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6219 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1243800 1244000 :=
  FiniteIntervals.of_fin 1243800 200 complete_chunk6219

#print axioms interval_chunk6210
end Erdos184Work.PureFiveFilter4
