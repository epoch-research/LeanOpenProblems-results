import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1270 : ∀ i : Fin 200, Compatible (254000 + i.val) →
    (table.lookup (254000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1270 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 254000 254200 :=
  FiniteIntervals.of_fin 254000 200 complete_chunk1270

lemma complete_chunk1271 : ∀ i : Fin 200, Compatible (254200 + i.val) →
    (table.lookup (254200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1271 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 254200 254400 :=
  FiniteIntervals.of_fin 254200 200 complete_chunk1271

lemma complete_chunk1272 : ∀ i : Fin 200, Compatible (254400 + i.val) →
    (table.lookup (254400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1272 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 254400 254600 :=
  FiniteIntervals.of_fin 254400 200 complete_chunk1272

lemma complete_chunk1273 : ∀ i : Fin 200, Compatible (254600 + i.val) →
    (table.lookup (254600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1273 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 254600 254800 :=
  FiniteIntervals.of_fin 254600 200 complete_chunk1273

lemma complete_chunk1274 : ∀ i : Fin 200, Compatible (254800 + i.val) →
    (table.lookup (254800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1274 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 254800 255000 :=
  FiniteIntervals.of_fin 254800 200 complete_chunk1274

lemma complete_chunk1275 : ∀ i : Fin 200, Compatible (255000 + i.val) →
    (table.lookup (255000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1275 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 255000 255200 :=
  FiniteIntervals.of_fin 255000 200 complete_chunk1275

lemma complete_chunk1276 : ∀ i : Fin 200, Compatible (255200 + i.val) →
    (table.lookup (255200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1276 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 255200 255400 :=
  FiniteIntervals.of_fin 255200 200 complete_chunk1276

lemma complete_chunk1277 : ∀ i : Fin 200, Compatible (255400 + i.val) →
    (table.lookup (255400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1277 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 255400 255600 :=
  FiniteIntervals.of_fin 255400 200 complete_chunk1277

lemma complete_chunk1278 : ∀ i : Fin 200, Compatible (255600 + i.val) →
    (table.lookup (255600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1278 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 255600 255800 :=
  FiniteIntervals.of_fin 255600 200 complete_chunk1278

lemma complete_chunk1279 : ∀ i : Fin 200, Compatible (255800 + i.val) →
    (table.lookup (255800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1279 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 255800 256000 :=
  FiniteIntervals.of_fin 255800 200 complete_chunk1279

#print axioms interval_chunk1270
end Erdos184Work.PureFiveFilter4
