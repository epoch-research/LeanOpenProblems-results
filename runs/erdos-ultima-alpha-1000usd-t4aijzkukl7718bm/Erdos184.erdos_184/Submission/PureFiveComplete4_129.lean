import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1290 : ∀ i : Fin 200, Compatible (258000 + i.val) →
    (table.lookup (258000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1290 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 258000 258200 :=
  FiniteIntervals.of_fin 258000 200 complete_chunk1290

lemma complete_chunk1291 : ∀ i : Fin 200, Compatible (258200 + i.val) →
    (table.lookup (258200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1291 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 258200 258400 :=
  FiniteIntervals.of_fin 258200 200 complete_chunk1291

lemma complete_chunk1292 : ∀ i : Fin 200, Compatible (258400 + i.val) →
    (table.lookup (258400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1292 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 258400 258600 :=
  FiniteIntervals.of_fin 258400 200 complete_chunk1292

lemma complete_chunk1293 : ∀ i : Fin 200, Compatible (258600 + i.val) →
    (table.lookup (258600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1293 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 258600 258800 :=
  FiniteIntervals.of_fin 258600 200 complete_chunk1293

lemma complete_chunk1294 : ∀ i : Fin 200, Compatible (258800 + i.val) →
    (table.lookup (258800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1294 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 258800 259000 :=
  FiniteIntervals.of_fin 258800 200 complete_chunk1294

lemma complete_chunk1295 : ∀ i : Fin 200, Compatible (259000 + i.val) →
    (table.lookup (259000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1295 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 259000 259200 :=
  FiniteIntervals.of_fin 259000 200 complete_chunk1295

lemma complete_chunk1296 : ∀ i : Fin 200, Compatible (259200 + i.val) →
    (table.lookup (259200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1296 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 259200 259400 :=
  FiniteIntervals.of_fin 259200 200 complete_chunk1296

lemma complete_chunk1297 : ∀ i : Fin 200, Compatible (259400 + i.val) →
    (table.lookup (259400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1297 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 259400 259600 :=
  FiniteIntervals.of_fin 259400 200 complete_chunk1297

lemma complete_chunk1298 : ∀ i : Fin 200, Compatible (259600 + i.val) →
    (table.lookup (259600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1298 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 259600 259800 :=
  FiniteIntervals.of_fin 259600 200 complete_chunk1298

lemma complete_chunk1299 : ∀ i : Fin 200, Compatible (259800 + i.val) →
    (table.lookup (259800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1299 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 259800 260000 :=
  FiniteIntervals.of_fin 259800 200 complete_chunk1299

#print axioms interval_chunk1290
end Erdos184Work.PureFiveFilter4
