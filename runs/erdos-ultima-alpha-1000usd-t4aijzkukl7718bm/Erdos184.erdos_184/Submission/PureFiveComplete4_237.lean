import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2370 : ∀ i : Fin 200, Compatible (474000 + i.val) →
    (table.lookup (474000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2370 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 474000 474200 :=
  FiniteIntervals.of_fin 474000 200 complete_chunk2370

lemma complete_chunk2371 : ∀ i : Fin 200, Compatible (474200 + i.val) →
    (table.lookup (474200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2371 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 474200 474400 :=
  FiniteIntervals.of_fin 474200 200 complete_chunk2371

lemma complete_chunk2372 : ∀ i : Fin 200, Compatible (474400 + i.val) →
    (table.lookup (474400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2372 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 474400 474600 :=
  FiniteIntervals.of_fin 474400 200 complete_chunk2372

lemma complete_chunk2373 : ∀ i : Fin 200, Compatible (474600 + i.val) →
    (table.lookup (474600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2373 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 474600 474800 :=
  FiniteIntervals.of_fin 474600 200 complete_chunk2373

lemma complete_chunk2374 : ∀ i : Fin 200, Compatible (474800 + i.val) →
    (table.lookup (474800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2374 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 474800 475000 :=
  FiniteIntervals.of_fin 474800 200 complete_chunk2374

lemma complete_chunk2375 : ∀ i : Fin 200, Compatible (475000 + i.val) →
    (table.lookup (475000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2375 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 475000 475200 :=
  FiniteIntervals.of_fin 475000 200 complete_chunk2375

lemma complete_chunk2376 : ∀ i : Fin 200, Compatible (475200 + i.val) →
    (table.lookup (475200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2376 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 475200 475400 :=
  FiniteIntervals.of_fin 475200 200 complete_chunk2376

lemma complete_chunk2377 : ∀ i : Fin 200, Compatible (475400 + i.val) →
    (table.lookup (475400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2377 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 475400 475600 :=
  FiniteIntervals.of_fin 475400 200 complete_chunk2377

lemma complete_chunk2378 : ∀ i : Fin 200, Compatible (475600 + i.val) →
    (table.lookup (475600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2378 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 475600 475800 :=
  FiniteIntervals.of_fin 475600 200 complete_chunk2378

lemma complete_chunk2379 : ∀ i : Fin 200, Compatible (475800 + i.val) →
    (table.lookup (475800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2379 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 475800 476000 :=
  FiniteIntervals.of_fin 475800 200 complete_chunk2379

#print axioms interval_chunk2370
end Erdos184Work.PureFiveFilter4
