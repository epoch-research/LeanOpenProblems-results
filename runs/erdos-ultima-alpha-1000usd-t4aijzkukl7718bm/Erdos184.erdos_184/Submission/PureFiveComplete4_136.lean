import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1360 : ∀ i : Fin 200, Compatible (272000 + i.val) →
    (table.lookup (272000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1360 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 272000 272200 :=
  FiniteIntervals.of_fin 272000 200 complete_chunk1360

lemma complete_chunk1361 : ∀ i : Fin 200, Compatible (272200 + i.val) →
    (table.lookup (272200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1361 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 272200 272400 :=
  FiniteIntervals.of_fin 272200 200 complete_chunk1361

lemma complete_chunk1362 : ∀ i : Fin 200, Compatible (272400 + i.val) →
    (table.lookup (272400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1362 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 272400 272600 :=
  FiniteIntervals.of_fin 272400 200 complete_chunk1362

lemma complete_chunk1363 : ∀ i : Fin 200, Compatible (272600 + i.val) →
    (table.lookup (272600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1363 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 272600 272800 :=
  FiniteIntervals.of_fin 272600 200 complete_chunk1363

lemma complete_chunk1364 : ∀ i : Fin 200, Compatible (272800 + i.val) →
    (table.lookup (272800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1364 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 272800 273000 :=
  FiniteIntervals.of_fin 272800 200 complete_chunk1364

lemma complete_chunk1365 : ∀ i : Fin 200, Compatible (273000 + i.val) →
    (table.lookup (273000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1365 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 273000 273200 :=
  FiniteIntervals.of_fin 273000 200 complete_chunk1365

lemma complete_chunk1366 : ∀ i : Fin 200, Compatible (273200 + i.val) →
    (table.lookup (273200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1366 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 273200 273400 :=
  FiniteIntervals.of_fin 273200 200 complete_chunk1366

lemma complete_chunk1367 : ∀ i : Fin 200, Compatible (273400 + i.val) →
    (table.lookup (273400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1367 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 273400 273600 :=
  FiniteIntervals.of_fin 273400 200 complete_chunk1367

lemma complete_chunk1368 : ∀ i : Fin 200, Compatible (273600 + i.val) →
    (table.lookup (273600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1368 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 273600 273800 :=
  FiniteIntervals.of_fin 273600 200 complete_chunk1368

lemma complete_chunk1369 : ∀ i : Fin 200, Compatible (273800 + i.val) →
    (table.lookup (273800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1369 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 273800 274000 :=
  FiniteIntervals.of_fin 273800 200 complete_chunk1369

#print axioms interval_chunk1360
end Erdos184Work.PureFiveFilter4
