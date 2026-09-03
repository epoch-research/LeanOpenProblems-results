import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1210 : ∀ i : Fin 200, Compatible (242000 + i.val) →
    (table.lookup (242000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1210 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 242000 242200 :=
  FiniteIntervals.of_fin 242000 200 complete_chunk1210

lemma complete_chunk1211 : ∀ i : Fin 200, Compatible (242200 + i.val) →
    (table.lookup (242200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1211 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 242200 242400 :=
  FiniteIntervals.of_fin 242200 200 complete_chunk1211

lemma complete_chunk1212 : ∀ i : Fin 200, Compatible (242400 + i.val) →
    (table.lookup (242400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1212 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 242400 242600 :=
  FiniteIntervals.of_fin 242400 200 complete_chunk1212

lemma complete_chunk1213 : ∀ i : Fin 200, Compatible (242600 + i.val) →
    (table.lookup (242600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1213 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 242600 242800 :=
  FiniteIntervals.of_fin 242600 200 complete_chunk1213

lemma complete_chunk1214 : ∀ i : Fin 200, Compatible (242800 + i.val) →
    (table.lookup (242800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1214 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 242800 243000 :=
  FiniteIntervals.of_fin 242800 200 complete_chunk1214

lemma complete_chunk1215 : ∀ i : Fin 200, Compatible (243000 + i.val) →
    (table.lookup (243000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1215 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 243000 243200 :=
  FiniteIntervals.of_fin 243000 200 complete_chunk1215

lemma complete_chunk1216 : ∀ i : Fin 200, Compatible (243200 + i.val) →
    (table.lookup (243200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1216 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 243200 243400 :=
  FiniteIntervals.of_fin 243200 200 complete_chunk1216

lemma complete_chunk1217 : ∀ i : Fin 200, Compatible (243400 + i.val) →
    (table.lookup (243400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1217 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 243400 243600 :=
  FiniteIntervals.of_fin 243400 200 complete_chunk1217

lemma complete_chunk1218 : ∀ i : Fin 200, Compatible (243600 + i.val) →
    (table.lookup (243600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1218 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 243600 243800 :=
  FiniteIntervals.of_fin 243600 200 complete_chunk1218

lemma complete_chunk1219 : ∀ i : Fin 200, Compatible (243800 + i.val) →
    (table.lookup (243800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1219 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 243800 244000 :=
  FiniteIntervals.of_fin 243800 200 complete_chunk1219

#print axioms interval_chunk1210
end Erdos184Work.PureFiveFilter4
