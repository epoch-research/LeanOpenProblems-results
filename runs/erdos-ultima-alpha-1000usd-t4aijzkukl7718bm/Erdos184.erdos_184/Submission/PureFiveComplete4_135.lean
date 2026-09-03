import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1350 : ∀ i : Fin 200, Compatible (270000 + i.val) →
    (table.lookup (270000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1350 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 270000 270200 :=
  FiniteIntervals.of_fin 270000 200 complete_chunk1350

lemma complete_chunk1351 : ∀ i : Fin 200, Compatible (270200 + i.val) →
    (table.lookup (270200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1351 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 270200 270400 :=
  FiniteIntervals.of_fin 270200 200 complete_chunk1351

lemma complete_chunk1352 : ∀ i : Fin 200, Compatible (270400 + i.val) →
    (table.lookup (270400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1352 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 270400 270600 :=
  FiniteIntervals.of_fin 270400 200 complete_chunk1352

lemma complete_chunk1353 : ∀ i : Fin 200, Compatible (270600 + i.val) →
    (table.lookup (270600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1353 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 270600 270800 :=
  FiniteIntervals.of_fin 270600 200 complete_chunk1353

lemma complete_chunk1354 : ∀ i : Fin 200, Compatible (270800 + i.val) →
    (table.lookup (270800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1354 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 270800 271000 :=
  FiniteIntervals.of_fin 270800 200 complete_chunk1354

lemma complete_chunk1355 : ∀ i : Fin 200, Compatible (271000 + i.val) →
    (table.lookup (271000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1355 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 271000 271200 :=
  FiniteIntervals.of_fin 271000 200 complete_chunk1355

lemma complete_chunk1356 : ∀ i : Fin 200, Compatible (271200 + i.val) →
    (table.lookup (271200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1356 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 271200 271400 :=
  FiniteIntervals.of_fin 271200 200 complete_chunk1356

lemma complete_chunk1357 : ∀ i : Fin 200, Compatible (271400 + i.val) →
    (table.lookup (271400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1357 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 271400 271600 :=
  FiniteIntervals.of_fin 271400 200 complete_chunk1357

lemma complete_chunk1358 : ∀ i : Fin 200, Compatible (271600 + i.val) →
    (table.lookup (271600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1358 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 271600 271800 :=
  FiniteIntervals.of_fin 271600 200 complete_chunk1358

lemma complete_chunk1359 : ∀ i : Fin 200, Compatible (271800 + i.val) →
    (table.lookup (271800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1359 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 271800 272000 :=
  FiniteIntervals.of_fin 271800 200 complete_chunk1359

#print axioms interval_chunk1350
end Erdos184Work.PureFiveFilter4
