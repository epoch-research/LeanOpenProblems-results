import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5340 : ∀ i : Fin 200, Compatible (1068000 + i.val) →
    (table.lookup (1068000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5340 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1068000 1068200 :=
  FiniteIntervals.of_fin 1068000 200 complete_chunk5340

lemma complete_chunk5341 : ∀ i : Fin 200, Compatible (1068200 + i.val) →
    (table.lookup (1068200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5341 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1068200 1068400 :=
  FiniteIntervals.of_fin 1068200 200 complete_chunk5341

lemma complete_chunk5342 : ∀ i : Fin 200, Compatible (1068400 + i.val) →
    (table.lookup (1068400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5342 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1068400 1068600 :=
  FiniteIntervals.of_fin 1068400 200 complete_chunk5342

lemma complete_chunk5343 : ∀ i : Fin 200, Compatible (1068600 + i.val) →
    (table.lookup (1068600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5343 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1068600 1068800 :=
  FiniteIntervals.of_fin 1068600 200 complete_chunk5343

lemma complete_chunk5344 : ∀ i : Fin 200, Compatible (1068800 + i.val) →
    (table.lookup (1068800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5344 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1068800 1069000 :=
  FiniteIntervals.of_fin 1068800 200 complete_chunk5344

lemma complete_chunk5345 : ∀ i : Fin 200, Compatible (1069000 + i.val) →
    (table.lookup (1069000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5345 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1069000 1069200 :=
  FiniteIntervals.of_fin 1069000 200 complete_chunk5345

lemma complete_chunk5346 : ∀ i : Fin 200, Compatible (1069200 + i.val) →
    (table.lookup (1069200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5346 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1069200 1069400 :=
  FiniteIntervals.of_fin 1069200 200 complete_chunk5346

lemma complete_chunk5347 : ∀ i : Fin 200, Compatible (1069400 + i.val) →
    (table.lookup (1069400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5347 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1069400 1069600 :=
  FiniteIntervals.of_fin 1069400 200 complete_chunk5347

lemma complete_chunk5348 : ∀ i : Fin 200, Compatible (1069600 + i.val) →
    (table.lookup (1069600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5348 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1069600 1069800 :=
  FiniteIntervals.of_fin 1069600 200 complete_chunk5348

lemma complete_chunk5349 : ∀ i : Fin 200, Compatible (1069800 + i.val) →
    (table.lookup (1069800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5349 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1069800 1070000 :=
  FiniteIntervals.of_fin 1069800 200 complete_chunk5349

#print axioms interval_chunk5340
end Erdos184Work.PureFiveFilter4
