import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1340 : ∀ i : Fin 200, Compatible (268000 + i.val) →
    (table.lookup (268000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1340 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 268000 268200 :=
  FiniteIntervals.of_fin 268000 200 complete_chunk1340

lemma complete_chunk1341 : ∀ i : Fin 200, Compatible (268200 + i.val) →
    (table.lookup (268200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1341 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 268200 268400 :=
  FiniteIntervals.of_fin 268200 200 complete_chunk1341

lemma complete_chunk1342 : ∀ i : Fin 200, Compatible (268400 + i.val) →
    (table.lookup (268400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1342 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 268400 268600 :=
  FiniteIntervals.of_fin 268400 200 complete_chunk1342

lemma complete_chunk1343 : ∀ i : Fin 200, Compatible (268600 + i.val) →
    (table.lookup (268600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1343 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 268600 268800 :=
  FiniteIntervals.of_fin 268600 200 complete_chunk1343

lemma complete_chunk1344 : ∀ i : Fin 200, Compatible (268800 + i.val) →
    (table.lookup (268800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1344 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 268800 269000 :=
  FiniteIntervals.of_fin 268800 200 complete_chunk1344

lemma complete_chunk1345 : ∀ i : Fin 200, Compatible (269000 + i.val) →
    (table.lookup (269000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1345 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 269000 269200 :=
  FiniteIntervals.of_fin 269000 200 complete_chunk1345

lemma complete_chunk1346 : ∀ i : Fin 200, Compatible (269200 + i.val) →
    (table.lookup (269200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1346 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 269200 269400 :=
  FiniteIntervals.of_fin 269200 200 complete_chunk1346

lemma complete_chunk1347 : ∀ i : Fin 200, Compatible (269400 + i.val) →
    (table.lookup (269400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1347 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 269400 269600 :=
  FiniteIntervals.of_fin 269400 200 complete_chunk1347

lemma complete_chunk1348 : ∀ i : Fin 200, Compatible (269600 + i.val) →
    (table.lookup (269600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1348 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 269600 269800 :=
  FiniteIntervals.of_fin 269600 200 complete_chunk1348

lemma complete_chunk1349 : ∀ i : Fin 200, Compatible (269800 + i.val) →
    (table.lookup (269800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1349 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 269800 270000 :=
  FiniteIntervals.of_fin 269800 200 complete_chunk1349

#print axioms interval_chunk1340
end Erdos184Work.PureFiveFilter4
