import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1370 : ∀ i : Fin 200, Compatible (274000 + i.val) →
    (table.lookup (274000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1370 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 274000 274200 :=
  FiniteIntervals.of_fin 274000 200 complete_chunk1370

lemma complete_chunk1371 : ∀ i : Fin 200, Compatible (274200 + i.val) →
    (table.lookup (274200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1371 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 274200 274400 :=
  FiniteIntervals.of_fin 274200 200 complete_chunk1371

lemma complete_chunk1372 : ∀ i : Fin 200, Compatible (274400 + i.val) →
    (table.lookup (274400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1372 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 274400 274600 :=
  FiniteIntervals.of_fin 274400 200 complete_chunk1372

lemma complete_chunk1373 : ∀ i : Fin 200, Compatible (274600 + i.val) →
    (table.lookup (274600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1373 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 274600 274800 :=
  FiniteIntervals.of_fin 274600 200 complete_chunk1373

lemma complete_chunk1374 : ∀ i : Fin 200, Compatible (274800 + i.val) →
    (table.lookup (274800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1374 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 274800 275000 :=
  FiniteIntervals.of_fin 274800 200 complete_chunk1374

lemma complete_chunk1375 : ∀ i : Fin 200, Compatible (275000 + i.val) →
    (table.lookup (275000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1375 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 275000 275200 :=
  FiniteIntervals.of_fin 275000 200 complete_chunk1375

lemma complete_chunk1376 : ∀ i : Fin 200, Compatible (275200 + i.val) →
    (table.lookup (275200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1376 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 275200 275400 :=
  FiniteIntervals.of_fin 275200 200 complete_chunk1376

lemma complete_chunk1377 : ∀ i : Fin 200, Compatible (275400 + i.val) →
    (table.lookup (275400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1377 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 275400 275600 :=
  FiniteIntervals.of_fin 275400 200 complete_chunk1377

lemma complete_chunk1378 : ∀ i : Fin 200, Compatible (275600 + i.val) →
    (table.lookup (275600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1378 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 275600 275800 :=
  FiniteIntervals.of_fin 275600 200 complete_chunk1378

lemma complete_chunk1379 : ∀ i : Fin 200, Compatible (275800 + i.val) →
    (table.lookup (275800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1379 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 275800 276000 :=
  FiniteIntervals.of_fin 275800 200 complete_chunk1379

#print axioms interval_chunk1370
end Erdos184Work.PureFiveFilter4
